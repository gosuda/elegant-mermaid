import Elegant.Kinds.Common
import Elegant.Lanes
import Elegant.StyledMeasure

set_option autoImplicit false

/-! Gitgraph model adapter. Branches are the `group` boxes of the model-stage dump and commits are
its `node` boxes, each commit under its branch box; routes are the links between commits (a dotted
route is a cherry-pick); the labels of a branch or of a commit are its measured texts. The adapter
reads the honoured config keys `showBranches`, `showCommitLabel` and `rotateCommitLabel`, measures
every label, runs the lanes family and assembles the layout dump as Go's `decodedGitgraph.dump`
does.

The decode is strict where Go is lenient only on inputs the Go front end never writes: a branch box
with a parent, a commit whose parent is not a branch box of the dump, a route end that is not a
commit and a label owner that is neither a branch nor a commit are all a domain error. -/

namespace Elegant
namespace Kinds
namespace Gitgraph

open Common

/-- Where the geometry of a dump label lives in the family result. -/
inductive Slot where
  | branch (b : Nat)
  | commit (i : Nat)
  | tag (i k : Nat)
  deriving DecidableEq, Repr

structure Decoded where
  graph : Lanes.GitInput
  slots : List Slot
  captions : List Lanes.Caption

def isTrueValue : ConfigValue → Bool
  | .boolean b => b
  | .string s => s == "true"
  | .integer _ => false

def configFlag (o : Options) (key : String) (fallback : Bool) : Bool :=
  match o.config.find? (·.1 == key) with
  | some (_, v) => isTrueValue v
  | none => fallback

def laneOrderOf (shape : String) : Int :=
  if shape.startsWith "branch:" then ((shape.drop 7).toInt?).getD 0 else 0

def commitKind (shape : String) : String := if shape == "" then "commit" else shape

def measureRole : TextRole → Measure.Role
  | .body => .body
  | _ => .label

def measureCaption (profile : Profile) (role : TextRole) (text : String) :
    Except LayoutError Lanes.Caption := do
  let lineHeight := LayoutConst.line_h.get profile
  let metric ← match profile with
    | .cell => pure Measure.Metric.cell
    | .vector => (measureRole role).metric
  match StyledMeasure.wrap metric I32_MAX text.toList with
  | .error _ => throw .overflow
  | .ok lines => return ⟨lines, lines.foldl (fun w l => max w l.width) 0,
      (lines.length : Int) * lineHeight, role⟩

def laneIndex (m : Model) (id : String) : Option Nat :=
  (m.boxes.filter (·.role == .group)).findIdx? (·.id == id)

def commitIndex (m : Model) (id : String) : Option Nat :=
  (m.boxes.filter (·.role == .node)).findIdx? (·.id == id)

/-- The label slot of the label at position `j`: a branch label, the commit label, or a tag. -/
def slotOf (m : Model) (j : Nat) (l : ModelLabel) : Except LayoutError Slot :=
  match laneIndex m l.owner with
  | some b => pure (.branch b)
  | none =>
    match commitIndex m l.owner with
    | none => throw .domain
    | some i =>
      let earlier := ((m.labels.take j).filter fun k =>
        (laneIndex m k.owner).isNone && commitIndex m k.owner == some i).length
      if configFlag m.options "showCommitLabel" true && earlier == 0 then pure (.commit i)
      else pure (.tag i (earlier - (if configFlag m.options "showCommitLabel" true then 1 else 0)))

def labelOfSlot (slots : List Slot) (captions : List Lanes.Caption) (s : Slot) :
    List Lanes.Caption :=
  ((slots.zip captions).filter fun (t, _) => t == s).map (·.2)

def tagsOf (slots : List Slot) (captions : List Lanes.Caption) (i : Nat) : List Lanes.Caption :=
  (slots.zip captions).filterMap fun (s, cap) =>
    match s with
    | .tag i' _ => if i' == i then some cap else none
    | _ => none

/-- A branch box stands at the top of the dump: it has no parent. -/
def groupsRooted (m : Model) : Bool := m.boxes.all fun b => b.role != .group || b.parent == ""

def decode (m : Model) : Except LayoutError Decoded := do
  if !groupsRooted m then throw .domain
  let captions ← m.labels.mapM fun l =>
    measureCaption m.profile (if (laneIndex m l.owner).isSome then .label else .body) l.text
  let slots ← m.labels.zipIdx.mapM fun (l, j) => slotOf m j l
  let branches := ((m.boxes.filter (·.role == .group)).zipIdx).map fun (b, k) =>
    ({ id := b.id, order := laneOrderOf b.shape,
       label := (labelOfSlot slots captions (.branch k)).getLast? } : Lanes.Branch)
  let commits ← ((m.boxes.filter (·.role == .node)).zipIdx).mapM fun (b, i) => do
    match laneIndex m b.parent with
    | none => throw .domain
    | some lane =>
      return ({ id := b.id, branch := lane, kind := commitKind b.shape,
                label := (labelOfSlot slots captions (.commit i)).head?,
                tags := tagsOf slots captions i } : Lanes.Commit)
  let links ← m.routes.mapM fun r => do
    match commitIndex m r.fromId, commitIndex m r.toId with
    | some src, some dst => return ({ id := r.id, src, dst, pick := r.stroke == "dotted" } : Lanes.Link)
    | _, _ => throw .domain
  return { graph := { direction := m.options.direction
                      showBranches := configFlag m.options "showBranches" true
                      rotateLabels := configFlag m.options "rotateCommitLabel" true
                      branches, commits, links },
           slots, captions }

def sliceRect (res : Lanes.GitResult) : Slot → Rect
  | .branch b => res.branchLabels.getD b Lanes.zeroRect
  | .commit i => res.commitLabels.getD i Lanes.zeroRect
  | .tag i k => (res.tagLabels.getD i []).getD k Lanes.zeroRect

/-- The caption whose lines the dump lists for a label: the stored caption of its slot. -/
def slotCaption (d : Decoded) : Slot → Option Lanes.Caption
  | .branch b => (d.graph.branches[b]?).bind (·.label)
  | .commit i => (d.graph.commits[i]?).bind (·.label)
  | .tag i k => ((d.graph.commits[i]?).map (·.tags)).bind (·[k]?)

def boxRect (m : Model) (res : Lanes.GitResult) (b : ModelBox) : Rect :=
  match b.role with
  | .group => ((laneIndex m b.id).bind (res.lanes[·]?)).getD Lanes.zeroRect
  | .node =>
    match (commitIndex m b.id).bind (res.points[·]?) with
    | some p => ⟨p.x, p.y, 0, 0⟩
    | none => Lanes.zeroRect

def dumpBox (m : Model) (res : Lanes.GitResult) (b : ModelBox) : Box :=
  ⟨b.id, b.role.id, boxRect m res b, b.parent, b.exclusive⟩

def dumpBoxes (m : Model) (res : Lanes.GitResult) : List Box := m.boxes.map (dumpBox m res)

def dumpRoutes (m : Model) (res : Lanes.GitResult) : List Route :=
  m.routes.zipIdx.map fun (r, i) => ⟨r.id, r.fromId, r.toId, r.orthogonal, res.routes.getD i []⟩

def dumpLabels (m : Model) (d : Decoded) (res : Lanes.GitResult) : List SceneLabel :=
  (m.labels.zip d.slots).map fun (l, s) =>
    let lines := ((slotCaption d s).map (·.lines)).getD []
    { id := l.id, owner := l.owner, rect := sliceRect res s,
      lines := lines.map fun ln => String.ofList ln.text, text := l.text }

def sceneOf (m : Model) (d : Decoded) (res : Lanes.GitResult) : Scene :=
  { kind := m.kind, profile := m.profile, options := m.options, canvas := res.canvas,
    boxes := dumpBoxes m res, routes := dumpRoutes m res, labels := dumpLabels m d res,
    items := res.groups }

def scene (m : Model) : Except LayoutError Scene := do
  let d ← decode m
  let res ← Lanes.gitgraph d.graph m.profile
  return sceneOf m d res

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match scene m with
  | .error e => .error (.geometry e)
  | .ok s => .ok { scene := s, budgetExhausted := false }

end Gitgraph
end Kinds
end Elegant

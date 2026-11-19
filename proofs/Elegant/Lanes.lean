import Elegant.Model
import Elegant.Scene
import Elegant.Measure
import Elegant.LanesConsts
import ElegantGeometry.Route

set_option autoImplicit false

/-! Lean reference of the lanes layout family for `gitgraph` (`spec/layout/lanes.md`): the lane
order, the commit levels and the commit axis, the lane axis, the text placement beside or around
each commit, the lane frames, the connectors, the extent, and the frame that shifts everything into
the canvas margin. It computes the same integers as the Go family `lanes.GitGraph`. Every phase is
a fold over a declaration list, so the family has no fuel loop. -/

namespace Elegant
namespace Lanes

/-! ### Small helpers -/

def zeroRect : Rect := ⟨0, 0, 0, 0⟩

def half (v : Int) : Int := Int.fdiv v 2

def absI (v : Int) : Int := max v (-v)

/-! ### The family input -/

/-- One measured text: its wrapped lines, the widest line, the height, and the text role. -/
structure Caption where
  lines : List Measure.Line
  w : Int
  h : Int
  role : TextRole

structure Branch where
  id : String
  order : Int
  label : Option Caption

structure Commit where
  id : String
  branch : Nat
  kind : String
  label : Option Caption
  tags : List Caption

structure Link where
  id : String
  src : Nat
  dst : Nat
  pick : Bool

structure GitInput where
  direction : Direction
  showBranches : Bool
  rotateLabels : Bool
  branches : List Branch
  commits : List Commit
  links : List Link

/-- Every commit names a branch and every link joins two commits. -/
structure GitInput.WF (g : GitInput) : Prop where
  branch : ∀ cm ∈ g.commits, cm.branch < g.branches.length
  link : ∀ l ∈ g.links, l.src < g.commits.length ∧ l.dst < g.commits.length

/-! ### Lane order -/

/-- The lane key `(order, declaration index)` as a total preorder on branch indices. -/
def laneKeyLe (order : Nat → Int) (a b : Nat) : Bool :=
  decide (order a < order b ∨ (order a = order b ∧ a ≤ b))

def orderOf (g : GitInput) (b : Nat) : Int := ((g.branches[b]?).map (·.order)).getD 0

/-- The branch indices from the first lane to the last. -/
def laneOrder (g : GitInput) : List Nat :=
  (List.range g.branches.length).mergeSort (laneKeyLe (orderOf g))

/-- The lane position of a branch. -/
def rankOf (g : GitInput) (b : Nat) : Nat := (laneOrder g).idxOf b

/-! ### Axes -/

def vertical (d : Direction) : Bool := d == .TB || d == .BT

/-- The point at `commitAxis` along the commit axis and `laneAxis` along the lane axis. -/
def atPoint (d : Direction) (maxStep commitAxis laneAxis : Int) : Point :=
  match d with
  | .TB => ⟨laneAxis, commitAxis⟩
  | .BT => ⟨laneAxis, maxStep - commitAxis⟩
  | _ => ⟨commitAxis, laneAxis⟩

/-! ### Commit levels and the commit axis -/

def parentsOf (g : GitInput) (i : Nat) : List Nat :=
  (g.links.filter fun l => !l.pick && decide (l.src < l.dst) && l.dst == i).map (·.src)

/-- A list built front to back: element `k` is `f` of the elements before it and of `k`. -/
def buildUp {α : Type} (f : List α → Nat → α) : Nat → List α
  | 0 => []
  | k + 1 =>
    let s := buildUp f k
    s ++ [f s k]

def branchOf (g : GitInput) (i : Nat) : Nat := ((g.commits[i]?).map (·.branch)).getD 0

/-- The level that a commit of branch `b` leaves behind it: one past its own, else `acc`. -/
def floorStep (b : Nat) (acc : Nat) (x : Commit × Nat) : Nat :=
  if x.1.branch == b then x.2 + 1 else acc

/-- One past the level of the latest earlier commit on branch `b`, zero when there is none. -/
def laneFloor (g : GitInput) (s : List Nat) (b : Nat) : Nat :=
  (g.commits.zip s).foldl (floorStep b) 0

/-- The level of commit `k`: one more than its deepest parent and than its predecessor on its lane. -/
def levelStep (g : GitInput) (s : List Nat) (k : Nat) : Nat :=
  (parentsOf g k).foldl (fun acc p => max acc (s.getD p 0 + 1)) (laneFloor g s (branchOf g k))

def levelsUpTo (g : GitInput) : Nat → List Nat := buildUp (levelStep g)

def commitLevels (g : GitInput) : List Nat := levelsUpTo g g.commits.length

def levelCount (levels : List Nat) : Nat := levels.foldl (fun acc l => max acc (l + 1)) 0

/-- The widest text of a commit, tags with their plate. -/
def textWidth (c : GitConsts) (cm : Commit) : Int :=
  cm.tags.foldl (fun w t => max w (t.w + 2 * c.tagPad)) ((cm.label.map (·.w)).getD 0)

/-- The widest text of each level; zero under the vertical directions. -/
def reachOf (g : GitInput) (c : GitConsts) (levels : List Nat) : List Int :=
  if vertical g.direction then List.replicate (levelCount levels) 0
  else (List.range (levelCount levels)).map fun l =>
    (g.commits.zip levels).foldl (fun acc (cm, lv) => if lv == l then max acc (textWidth c cm) else acc) 0

def levelGap (d : Direction) (c : GitConsts) (before after : Int) : Int :=
  if vertical d then c.commitStep else max c.commitStep (half (before + after + 1) + c.labelGap)

/-- The commit axis of level `k`: zero for the first, else the previous one plus the level gap. -/
def axisStep (d : Direction) (c : GitConsts) (reach : List Int) (a : List Int) (k : Nat) : Int :=
  if k == 0 then 0 else a.getD (k - 1) 0 + levelGap d c (reach.getD (k - 1) 0) (reach.getD k 0)

def levelAxis (d : Direction) (c : GitConsts) (reach : List Int) : List Int :=
  buildUp (axisStep d c reach) reach.length

def turnBack (d : Direction) (c : GitConsts) (reach : List Int) (levels : List Nat) (i : Nat) : Int :=
  if vertical d then half c.commitStep
  else max (half c.commitStep) (half (reach.getD (levels.getD i 0) 0) + half (c.labelGap + 1))

/-! ### Text placement -/

def besideTags (c : GitConsts) (at_ : Point) : Int → List Caption → List Rect
  | _, [] => []
  | cursor, t :: ts =>
    ⟨at_.x + cursor, at_.y - half t.h, t.w, t.h⟩ ::
      besideTags c at_ (cursor + t.w + c.labelOffset) ts

/-- The label and tag boxes right of the commit, each `labelOffset` after the previous one. -/
def placeBeside (c : GitConsts) (cm : Commit) (at_ : Point) : Rect × List Rect :=
  match cm.label with
  | some l =>
    (⟨at_.x + c.labelOffset, at_.y - half l.h, l.w, l.h⟩,
      besideTags c at_ (c.labelOffset + l.w + c.labelOffset) cm.tags)
  | none => (zeroRect, besideTags c at_ c.labelOffset cm.tags)

def sideExtent (c : GitConsts) (cm : Commit) : Int :=
  let (label, tags) := placeBeside c cm ⟨0, 0⟩
  let first := match cm.label with | some _ => label.x + label.w | none => 0
  tags.foldl (fun e t => max e (t.x + t.w)) first

def aboveTags (c : GitConsts) (at_ : Point) : Int → List Caption → List Rect
  | _, [] => []
  | raised, t :: ts =>
    ⟨at_.x - half t.w, at_.y - c.tagOffset - raised - t.h, t.w, t.h⟩ ::
      aboveTags c at_ (raised + t.h + 2 * c.tagPad) ts

def placeTexts (d : Direction) (c : GitConsts) (cm : Commit) (at_ : Point) : Rect × List Rect :=
  if vertical d then placeBeside c cm at_
  else
    (match cm.label with
      | some l => ⟨at_.x - half l.w, at_.y + c.labelOffset, l.w, l.h⟩
      | none => zeroRect,
     aboveTags c at_ 0 cm.tags)

/-! ### The lane axis -/

def shownLabel (g : GitInput) (br : Branch) : Option Caption :=
  if g.showBranches then br.label else none

def widestPlate (g : GitInput) (c : GitConsts) : Int :=
  g.branches.foldl (fun w br =>
    match shownLabel g br with
    | some l => max w (l.w + 2 * c.branchPadX)
    | none => w) 0

def pitchOf (g : GitInput) (c : GitConsts) : Int :=
  let base := c.lanePitch + (if g.rotateLabels then c.rotationExtra else 0)
  if vertical g.direction then
    max (base + g.commits.foldl (fun w cm => max w (sideExtent c cm)) 0)
      (widestPlate g c + c.labelGap)
  else base

/-- The tallest commit label of a branch with its offset. -/
def labelBand (g : GitInput) (c : GitConsts) (b : Nat) : Int :=
  g.commits.foldl (fun band cm =>
    match cm.label with
    | some l => if cm.branch == b then max band (c.labelOffset + l.h) else band
    | none => band) 0

def tagStack (c : GitConsts) (tags : List Caption) : Int :=
  2 * c.tagPad * ((tags.length : Int) - 1) + (tags.map (·.h)).sum

/-- The tallest tag stack of a branch with its offset and plate. -/
def tagBand (g : GitInput) (c : GitConsts) (b : Nat) : Int :=
  g.commits.foldl (fun band cm =>
    if cm.branch == b && !cm.tags.isEmpty then max band (c.tagOffset + c.tagPad + tagStack c cm.tags)
    else band) 0

def laneGap (g : GitInput) (c : GitConsts) (pitch : Int) (upper lower : Nat) : Int :=
  if vertical g.direction then pitch else max pitch (labelBand g c upper + tagBand g c lower)

/-- The lane axis of lane position `k`: zero for the first, else the previous one plus the gap. -/
def laneAxisStep (g : GitInput) (c : GitConsts) (pitch : Int) (order : List Nat) (a : List Int)
    (k : Nat) : Int :=
  if k == 0 then 0
  else a.getD (k - 1) 0 + laneGap g c pitch (order.getD (k - 1) 0) (order.getD k 0)

def laneAxesOf (g : GitInput) (c : GitConsts) (pitch : Int) : List Int :=
  buildUp (laneAxisStep g c pitch (laneOrder g)) g.branches.length

/-! ### Lane frames and connectors -/

def laneBand (from_ to_ : Point) : Rect :=
  ⟨min from_.x to_.x, min from_.y to_.y, absI (to_.x - from_.x), absI (to_.y - from_.y)⟩

def anchorLabel (d : Direction) (profile : Profile) (from_ : Point) (w h : Int) : Rect :=
  match d with
  | .TB => ⟨from_.x - half w, from_.y - h, w, h⟩
  | .BT => ⟨from_.x - half w, from_.y + (if profile == .cell then 1 else 0), w, h⟩
  | _ => ⟨from_.x - w, from_.y - half h, w, h⟩

/-! ### The quantities of an input -/

def reachG (g : GitInput) (c : GitConsts) : List Int := reachOf g c (commitLevels g)

def axisG (g : GitInput) (c : GitConsts) : List Int := levelAxis g.direction c (reachG g c)

/-- The commit-axis position of each commit. -/
def stepsG (g : GitInput) (c : GitConsts) : List Int :=
  (commitLevels g).map fun lv => (axisG g c).getD lv 0

def maxStepG (g : GitInput) (c : GitConsts) : Int :=
  (axisG g c).getD (levelCount (commitLevels g) - 1) 0

/-- The quantities every placement reads, computed once per input. -/
structure Shape where
  levels : List Nat
  reach : List Int
  steps : List Int
  maxStep : Int
  laneAxes : List Int

def Shape.of (g : GitInput) (c : GitConsts) : Shape :=
  { levels := commitLevels g, reach := reachG g c, steps := stepsG g c, maxStep := maxStepG g c,
    laneAxes := laneAxesOf g c (pitchOf g c) }

def Shape.laneAxis (sh : Shape) (g : GitInput) (b : Nat) : Int :=
  sh.laneAxes.getD (rankOf g b) 0

def Shape.pointAt (sh : Shape) (g : GitInput) (commitAxis laneAxis : Int) : Point :=
  atPoint g.direction sh.maxStep commitAxis laneAxis

def Shape.commitPoint (sh : Shape) (g : GitInput) (i : Nat) : Point :=
  sh.pointAt g (sh.steps.getD i 0) (sh.laneAxis g (branchOf g i))

def Shape.routeOf (sh : Shape) (g : GitInput) (c : GitConsts) (l : Link) : List Point :=
  let fromLane := sh.laneAxis g (branchOf g l.src)
  let toLane := sh.laneAxis g (branchOf g l.dst)
  let start := sh.steps.getD l.src 0
  let end_ := sh.steps.getD l.dst 0
  if branchOf g l.src == branchOf g l.dst then
    [sh.pointAt g start fromLane, sh.pointAt g end_ toLane]
  else
    let turn := end_ - turnBack g.direction c sh.reach sh.levels l.dst
    [sh.pointAt g start fromLane, sh.pointAt g turn fromLane, sh.pointAt g turn toLane,
      sh.pointAt g end_ toLane]

/-! ### The plan before the frame -/

structure Plan where
  points : List Point
  labels : List Rect
  tags : List (List Rect)
  starts : List Point
  ends : List Point
  lanes : List Rect
  plates : List Rect
  routes : List (List Point)

def Plan.build (g : GitInput) (c : GitConsts) (profile : Profile) : Plan :=
  let sh := Shape.of g c
  let points := (List.range g.commits.length).map (sh.commitPoint g)
  let texts := (g.commits.zip points).map fun (cm, pt) => placeTexts g.direction c cm pt
  let nB := g.branches.length
  let starts := (List.range nB).map fun b => sh.pointAt g (-c.labelGap) (sh.laneAxis g b)
  let ends := (List.range nB).map fun b =>
    sh.pointAt g (sh.maxStep + half c.commitStep) (sh.laneAxis g b)
  { points := points, labels := texts.map (·.1), tags := texts.map (·.2),
    starts := starts, ends := ends,
    lanes := (starts.zip ends).map fun (s, e) => laneBand s e,
    plates := (g.branches.zip starts).map fun (br, s) =>
      match shownLabel g br with
      | some l => anchorLabel g.direction profile s (l.w + 2 * c.branchPadX) (l.h + 2 * c.branchPadY)
      | none => zeroRect,
    routes := g.links.map (sh.routeOf g c) }

/-! ### The extent -/

def pointBox (profile : Profile) (v : Point) : Rect :=
  match profile with
  | .cell => ⟨v.x, v.y, 1, 1⟩
  | .vector => ⟨v.x, v.y, 0, 0⟩

def markerBox (c : GitConsts) (profile : Profile) (v : Point) : Rect :=
  match profile with
  | .cell => ⟨v.x, v.y, 1, 1⟩
  | .vector => ⟨v.x - c.commitRadius, v.y - c.commitRadius, 2 * c.commitRadius, 2 * c.commitRadius⟩

def tagPlate (c : GitConsts) (t : Rect) : Rect :=
  ⟨t.x - c.tagPad, t.y - c.tagPad, t.w + 2 * c.tagPad, t.h + 2 * c.tagPad⟩

def Plan.branchParts (g : GitInput) (profile : Profile) (p : Plan) : List Rect :=
  (List.range g.branches.length).flatMap fun b =>
    [p.lanes.getD b zeroRect, pointBox profile (p.starts.getD b ⟨0, 0⟩),
      pointBox profile (p.ends.getD b ⟨0, 0⟩)] ++
      (match (g.branches[b]?).bind (shownLabel g) with
        | some _ => [p.plates.getD b zeroRect]
        | none => [])

def Plan.commitParts (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan) :
    List Rect :=
  g.commits.zipIdx.flatMap fun (cm, i) =>
    [markerBox c profile (p.points.getD i ⟨0, 0⟩)] ++
      (match cm.label with
        | some _ => [p.labels.getD i zeroRect]
        | none => []) ++
      ((p.tags.getD i []).map (tagPlate c))

def Plan.routeParts (profile : Profile) (p : Plan) : List Rect :=
  p.routes.flatMap fun r => r.map (pointBox profile)

def Plan.parts (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan) : List Rect :=
  p.branchParts g profile ++ p.commitParts g c profile ++ p.routeParts profile

def Plan.extent (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan) : Rect :=
  match p.parts g c profile with
  | [] => zeroRect
  | r :: rest => rest.foldl Rect.unionRaw r

/-! ### The frame: shift into the margin and check the coordinate limit -/

def shiftPoint (dx dy : Int) (v : Point) : Point := ⟨v.x + dx, v.y + dy⟩

def shiftRect (dx dy : Int) (b : Rect) : Rect := ⟨b.x + dx, b.y + dy, b.w, b.h⟩

def pointValues (dx dy : Int) (v : Point) : List Int := [v.x + dx, v.y + dy]

def rectValues (dx dy : Int) (b : Rect) : List Int := [b.x + dx, b.y + dy, b.w, b.h]

def withinLimit (v : Int) : Bool := decide (absI v ≤ COORD_LIMIT)

/-! ### The scene items -/

def cellSymbol : String → String
  | "commit" => "disc"
  | "reverse" => "ring"
  | "highlight" => "diamond"
  | "merge" => "bullseye"
  | "merge-reverse" => "bullseye"
  | "merge-highlight" => "bullseye"
  | "cherry-pick" => "diamond-hollow"
  | _ => ""

def fin12 (n : Nat) : Fin 12 := ⟨n % 12, Nat.mod_lt _ (by decide)⟩

def plain (style : String) : Paint := { style := style }

def runsOf (lines : List Measure.Line) : List (List TextRun) :=
  lines.map fun l => [⟨String.ofList l.text, false, false⟩]

def textItem (cap : Caption) (rect : Rect) (align : Align) : Primitive :=
  .text { rect := rect, role := cap.role, size := 14, align := align, style := "text",
          lines := runsOf cap.lines }

def commitAlign (d : Direction) : Align := if vertical d then .start else .middle

def crossItems (at_ : Point) (d : Int) : List Primitive :=
  [.polyline [⟨at_.x - d, at_.y - d⟩, ⟨at_.x + d, at_.y + d⟩] 0 (plain "ink-line"),
   .polyline [⟨at_.x - d, at_.y + d⟩, ⟨at_.x + d, at_.y - d⟩] 0 (plain "ink-line")]

def cherryItems (at_ : Point) (d : Int) : List Primitive :=
  let dot := half d
  let left : Point := ⟨at_.x - d, at_.y - dot⟩
  let right : Point := ⟨at_.x + d, at_.y - dot⟩
  let stem : Point := ⟨at_.x, at_.y + d⟩
  [.polyline [left, stem] 0 (plain "ink-line"), .polyline [right, stem] 0 (plain "ink-line"),
   .ellipse left.x left.y dot dot (plain "ink"), .ellipse right.x right.y dot dot (plain "ink")]

def isMergeKind (kind : String) : Bool :=
  kind == "merge" || kind == "merge-reverse" || kind == "merge-highlight"

def decoration (kind : String) (at_ : Point) (r : Int) : List Primitive :=
  let d := half r
  if kind == "cherry-pick" then cherryItems at_ d
  else
    (if kind == "reverse" || kind == "merge-reverse" then crossItems at_ d
      else if kind == "highlight" || kind == "merge-highlight" then
        [.rect ⟨at_.x - d, at_.y - d, 2 * d, 2 * d⟩ (plain "mark-hollow")]
      else []) ++
    (if isMergeKind kind then [.ellipse at_.x at_.y d d (plain "mark-hollow")] else [])

def glyphItems (kind : String) (at_ : Point) (series : Fin 12) (r : Int) : List Primitive :=
  let body : Paint := { style := "series", series := series }
  let shape : Primitive :=
    if kind == "highlight" || kind == "merge-highlight" then
      .rect ⟨at_.x - r, at_.y - r, 2 * r, 2 * r⟩ body
    else .ellipse at_.x at_.y r r body
  shape :: decoration kind at_ r

def tagBox (c : GitConsts) (text : Rect) : Primitive :=
  .roundRect ⟨text.x - c.tagPad, text.y - c.tagPad, text.w + 2 * c.tagPad, text.h + 2 * c.tagPad⟩
    c.tagPad (plain "note")

/-- The lane items of branch `b`: its line, then its plate (vector only) and its text. -/
def laneItems (g : GitInput) (c : GitConsts) (profile : Profile) (b : Nat) (br : Branch)
    (start end_ : Point) (plate textRect : Rect) : List Primitive :=
  if !g.showBranches then []
  else
    let r := rankOf g b
    let line : Paint :=
      { style := "series-line", series := fin12 r
        width := if profile == .cell then .normal else .emphasis
        line := [LineStyle.solid, .dashed, .dotted].getD (r % 3) .solid }
    let items : List Primitive := [.polyline [start, end_] 0 line]
    match br.label with
    | none => items
    | some cap =>
      (if profile == .cell then items
        else items ++ [.roundRect plate c.cornerRadius { style := "series-tint", series := fin12 r }]) ++
        [textItem cap textRect .middle]

def edgeItems (c : GitConsts) (l : Link) (route : List Point) : List Primitive :=
  let shape : Paint := if l.pick then { style := "edge", line := .dotted } else plain "edge"
  [.polyline route c.cornerRadius shape]

def markerItems (g : GitInput) (c : GitConsts) (profile : Profile) (cm : Commit) (at_ : Point)
    (tagRects : List Rect) : List Primitive :=
  match profile with
  | .cell => [.symbolRef (cellSymbol cm.kind) at_ "mark"]
  | .vector =>
    glyphItems cm.kind at_ (fin12 (rankOf g cm.branch)) c.commitRadius ++ tagRects.map (tagBox c)

def commitItems (g : GitInput) (c : GitConsts) (profile : Profile) (cm : Commit) (at_ : Point)
    (labelRect : Rect) (tagRects : List Rect) : List Primitive :=
  markerItems g c profile cm at_ tagRects ++
    (match cm.label with
      | some cap => [textItem cap labelRect (commitAlign g.direction)]
      | none => []) ++
    (cm.tags.zip tagRects).map fun (cap, r) => textItem cap r (commitAlign g.direction)

/-! ### The result -/

structure GitResult where
  canvas : Size
  lanes : List Rect
  points : List Point
  routes : List (List Point)
  branchLabels : List Rect
  commitLabels : List Rect
  tagLabels : List (List Rect)
  groups : List Group

def branchText (g : GitInput) (c : GitConsts) (p : Plan) (b : Nat) (br : Branch) : Rect :=
  match shownLabel g br with
  | some l =>
    let outer := p.plates.getD b zeroRect
    ⟨outer.x + c.branchPadX, outer.y + c.branchPadY, l.w, l.h⟩
  | none => zeroRect

def Plan.branchTexts (g : GitInput) (c : GitConsts) (p : Plan) : List Rect :=
  g.branches.zipIdx.map fun (br, b) => branchText g c p b br

def paint (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan) (dx dy : Int)
    (points : List Point) (routes : List (List Point))
    (branchLabels commitLabels : List Rect) (tagLabels : List (List Rect)) : List Group :=
  let laneGroups := g.branches.zipIdx.map fun (br, b) =>
    { role := GroupRole.group, owner := br.id,
      items := laneItems g c profile b br
        (shiftPoint dx dy (p.starts.getD b ⟨0, 0⟩)) (shiftPoint dx dy (p.ends.getD b ⟨0, 0⟩))
        (shiftRect dx dy (p.plates.getD b zeroRect)) (branchLabels.getD b zeroRect) : Group }
  let edgeGroups := g.links.zipIdx.map fun (l, i) =>
    { role := GroupRole.edge, owner := l.id, items := edgeItems c l (routes.getD i []) : Group }
  let commitGroups := g.commits.zipIdx.map fun (cm, i) =>
    { role := GroupRole.node, owner := cm.id,
      items := commitItems g c profile cm (points.getD i ⟨0, 0⟩) (commitLabels.getD i zeroRect)
        (tagLabels.getD i []) : Group }
  laneGroups ++ edgeGroups ++ commitGroups

def Plan.dx (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan) : Int :=
  c.canvasMargin - (p.extent g c profile).x

def Plan.dy (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan) : Int :=
  c.canvasMargin - (p.extent g c profile).y

/-- The result of a plan, shifted into the canvas margin. -/
def Plan.frame (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan) : GitResult :=
  let dx := p.dx g c profile
  let dy := p.dy g c profile
  let ext := p.extent g c profile
  let points := p.points.map (shiftPoint dx dy)
  let routes := p.routes.map (·.map (shiftPoint dx dy))
  let branchLabels := (p.branchTexts g c).map (shiftRect dx dy)
  let commitLabels := p.labels.map (shiftRect dx dy)
  let tagLabels := p.tags.map (·.map (shiftRect dx dy))
  { canvas := ⟨ext.w + 2 * c.canvasMargin, ext.h + 2 * c.canvasMargin⟩
    lanes := p.lanes.map (shiftRect dx dy)
    points := points, routes := routes, branchLabels := branchLabels,
    commitLabels := commitLabels, tagLabels := tagLabels,
    groups := paint g c profile p dx dy points routes branchLabels commitLabels tagLabels }

/-- Every value that Go passes to its coordinate-limit check. -/
def Plan.checked (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan) : List Int :=
  let dx := p.dx g c profile
  let dy := p.dy g c profile
  let ext := p.extent g c profile
  [ext.w + 2 * c.canvasMargin, ext.h + 2 * c.canvasMargin] ++
    (p.lanes.flatMap (rectValues dx dy)) ++ ((p.branchTexts g c).flatMap (rectValues dx dy)) ++
    (p.points.flatMap (pointValues dx dy)) ++ (p.labels.flatMap (rectValues dx dy)) ++
    (p.tags.flatMap fun ts => ts.flatMap (rectValues dx dy)) ++
    (p.routes.flatMap fun r => r.flatMap (pointValues dx dy))

/-- The lane frames, points, routes, label boxes, canvas and scene items of a gitgraph. -/
def gitgraph (g : GitInput) (profile : Profile) : Except LayoutError GitResult := do
  if g.direction == .RL then throw .domain
  let c ← GitConsts.load profile
  let p := Plan.build g c profile
  if (p.checked g c profile).all withinLimit then return p.frame g c profile
  else throw .overflow

namespace Timeline

structure Card where
  id : String
  caption : Caption

structure Event extends Card where
  link : String

structure Period extends Card where
  sectionIndex : Int
  events : List Event

structure Input where
  direction : Direction
  title : Option Card
  sections : List Card
  periods : List Period

structure Plan where
  title : Rect
  sections : List Rect
  periods : List Rect
  events : List (List Rect)
  routes : List (List (List Point))
  axisStart : Point
  axisEnd : Point

def members (g : Input) (s : Int) : List Nat :=
  g.periods.zipIdx.filterMap fun (p, i) => if p.sectionIndex == s then some i else none

def span (g : Input) (s : Nat) : Nat := max 1 (members g s).length

def first (g : Input) (s : Nat) : Nat :=
  (members g (-1)).length + ((List.range s).map (span g)).sum

def slot (g : Input) (i : Nat) (p : Period) : Nat :=
  if p.sectionIndex < 0 then (members g (-1)).idxOf i
  else first g p.sectionIndex.toNat + (members g p.sectionIndex).idxOf i

def horizontal (g : Input) : Bool := g.direction == .LR

def cardWidth (g : Input) (c : TimelineConsts) : Int :=
  let base := g.periods.foldl (fun w p =>
    p.events.foldl (fun w e => max w (e.caption.w + 2 * c.cardPadding))
      (max w (p.caption.w + 2 * c.cardPadding))) c.cardWidth
  g.sections.zipIdx.foldl (fun w (s, i) =>
    let n : Int := if horizontal g then span g i else 1
    let need := s.caption.w + 2 * c.cardPadding - (n - 1) * c.columnGap
    if 0 < need then max w (Int.fdiv (need + n - 1) n) else w) base

def periodHeight (g : Input) (c : TimelineConsts) : Int :=
  g.periods.foldl (fun h p => max h (p.caption.h + 2 * c.cardPadding)) 0

def sectionHeight (g : Input) (c : TimelineConsts) : Int :=
  g.sections.foldl (fun h s => max h (s.caption.h + 2 * c.cardPadding)) 0

def contentTop (g : Input) (c : TimelineConsts) : Int :=
  (g.title.map fun t => t.caption.h + c.eventGap).getD 0

def eventHeight (c : TimelineConsts) (e : Event) : Int := e.caption.h + 2 * c.cardPadding

def eventRects (c : TimelineConsts) (x w top : Int) : List Event → List Rect
  | [] => []
  | e :: es =>
    let h := eventHeight c e
    ⟨x, top, w, h⟩ :: eventRects c x w (top + h + c.eventGap) es

def elbow (a b : Point) (x : Int) : List Point :=
  if a.y == b.y then [a, b] else [a, ⟨x, a.y⟩, ⟨x, b.y⟩, b]

def periodColumn (c : TimelineConsts) (width height y : Int) (index : Nat) : Rect :=
  ⟨c.leftMargin + (index : Int) * (width + c.columnGap), y, width, height⟩

def horizontalPlan (g : Input) (c : TimelineConsts) : Plan :=
  let w := cardWidth g c
  let ph := periodHeight g c
  let sh := sectionHeight g c
  let top := contentTop g c
  let py := top + if g.sections.isEmpty then 0 else sh + c.sectionGap
  let column := fun (i : Nat) => c.leftMargin + (i : Int) * (w + c.columnGap)
  let sections := g.sections.zipIdx.map fun (_, i) =>
    (⟨column (first g i), top,
      (span g i : Int) * (w + c.columnGap) - c.columnGap, sh⟩ : Rect)
  let periods := g.periods.zipIdx.map fun (p, i) =>
    periodColumn c w ph py (slot g i p)
  let events := (g.periods.zip periods).map fun (p, r) =>
    eventRects c r.x w (py + ph + c.sectionGap) p.events
  let routes := (periods.zip events).map fun (r, es) =>
    (es.foldl (fun (state : Rect × List (List Point)) b =>
      let x := r.x + half w
      (b, state.2 ++ [[⟨x, state.1.y + state.1.h⟩, ⟨x, b.y⟩]])) (r, [])).2
  let right := (sections ++ periods).foldl (fun a r => max a (r.x + r.w)) c.leftMargin
  let title := (g.title.map fun t =>
    (⟨c.leftMargin + half (right - c.leftMargin - t.caption.w), 0,
      t.caption.w, t.caption.h⟩ : Rect)).getD zeroRect
  { title, sections, periods, events, routes,
    axisStart := ⟨0, py + ph + half c.sectionGap⟩
    axisEnd := ⟨right + c.columnGap, py + ph + half c.sectionGap⟩ }

structure VerticalState where
  y : Int
  sections : List Rect
  periods : List Rect
  events : List (List Rect)
  routes : List (List (List Point))

def verticalRow (g : Input) (c : TimelineConsts) (i : Nat) (state : VerticalState) :
    VerticalState :=
  let w := cardWidth g c
  let ph := periodHeight g c
  let p := g.periods[i]?
  let es := (p.map (·.events)).getD []
  let r : Rect := ⟨c.leftMargin, state.y, w, ph⟩
  let eventX := c.leftMargin + w + c.columnGap
  let rects := eventRects c eventX w state.y es
  let source : Point := ⟨r.x + r.w, r.y + half ph⟩
  let routes := rects.map fun b =>
    elbow source ⟨b.x, b.y + half b.h⟩ (c.leftMargin + w + half c.columnGap)
  let bottom := rects.foldl (fun v b => max v (b.y + b.h)) (r.y + r.h)
  { state with y := bottom + c.sectionGap
               periods := state.periods.set i r
               events := state.events.set i rects
               routes := state.routes.set i routes }

def verticalPlan (g : Input) (c : TimelineConsts) : Plan :=
  let w := cardWidth g c
  let sh := sectionHeight g c
  let top := contentTop g c
  let initial : VerticalState :=
    { y := top, sections := List.replicate g.sections.length zeroRect
      periods := List.replicate g.periods.length zeroRect
      events := List.replicate g.periods.length []
      routes := List.replicate g.periods.length [] }
  let initial := (members g (-1)).foldl (fun st i => verticalRow g c i st) initial
  let result := (List.range g.sections.length).foldl (fun (st : VerticalState) (s : Nat) =>
    let rect : Rect := ⟨c.leftMargin, st.y, w, sh⟩
    let st := { st with y := st.y + sh + c.sectionGap, sections := st.sections.set s rect }
    (members g (s : Int)).foldl (fun st i => verticalRow g c i st) st) initial
  let right := c.leftMargin + 2 * w + c.columnGap
  let title := (g.title.map fun t =>
    (⟨c.leftMargin + half (right - c.leftMargin - t.caption.w), 0,
      t.caption.w, t.caption.h⟩ : Rect)).getD zeroRect
  let x := c.leftMargin + w + half c.columnGap
  { title, sections := result.sections, periods := result.periods
    events := result.events, routes := result.routes
    axisStart := ⟨x, top⟩
    axisEnd := ⟨x, max top (result.y - c.sectionGap) + c.sectionGap⟩ }

def plan (g : Input) (c : TimelineConsts) : Plan :=
  if horizontal g then horizontalPlan g c else verticalPlan g c

def Plan.parts (g : Input) (profile : Profile) (p : Plan) : List Rect :=
  [pointBox profile p.axisStart, pointBox profile p.axisEnd] ++
  (if g.title.isSome then [p.title] else []) ++
  p.sections ++ p.periods ++ p.events.flatten ++
  (p.routes.flatten.flatten.map (pointBox profile))

def Plan.extent (g : Input) (profile : Profile) (p : Plan) : Rect :=
  match p.parts g profile with
  | [] => zeroRect
  | r :: rs => rs.foldl Rect.unionRaw r

def Plan.shift (p : Plan) (dx dy : Int) : Plan :=
  { title := shiftRect dx dy p.title
    sections := p.sections.map (shiftRect dx dy)
    periods := p.periods.map (shiftRect dx dy)
    events := p.events.map (·.map (shiftRect dx dy))
    routes := p.routes.map (·.map (·.map (shiftPoint dx dy)))
    axisStart := shiftPoint dx dy p.axisStart
    axisEnd := shiftPoint dx dy p.axisEnd }

def captionItem (cap : Caption) (r : Rect) : Primitive :=
  .text { rect := r, role := cap.role, size := if cap.role == .title then 16 else 14
          align := .middle, style := "text", lines := runsOf cap.lines }

def captionRect (cap : Caption) (r : Rect) : Rect :=
  let h := (cap.lines.length : Int) * Int.fdiv cap.h (max 1 cap.lines.length)
  ⟨r.x, r.y + half (r.h - h), r.w, h⟩

def cardGroup (profile : Profile) (c : TimelineConsts) (kind : Nat)
    (series : Nat) (card : Card) (r : Rect) : Group :=
  let paint : Paint :=
    { style := if kind == 2 then "node" else "series-tint"
      series := fin12 series
      width := if kind == 0 then .emphasis else .normal }
  let shape := if profile == .cell && kind != 1 then Primitive.rect r paint
    else Primitive.roundRect r c.cornerRadius paint
  { role := .node, owner := card.id
    items := [shape, captionItem card.caption (captionRect card.caption r)] }

def series (g : Input) (i : Nat) (p : Period) : Nat :=
  if g.sections.isEmpty then i else if p.sectionIndex < 0 then 0 else p.sectionIndex.toNat

def paint (g : Input) (profile : Profile) (c : TimelineConsts) (p : Plan) : List Group :=
  let axis : Group :=
    { role := .decor, owner := ""
      items := [.polyline [p.axisStart, p.axisEnd] 0 { style := "edge", width := .emphasis },
        .markerRef "point" p.axisEnd (if horizontal g then .positiveX else .positiveY)] }
  let edges := (g.periods.zip p.routes).flatMap fun (period, routes) =>
    (period.events.zip routes).map fun (e, route) =>
      ({ role := .edge, owner := e.link
         items := [.polyline route c.cornerRadius { style := "edge", line := .dotted }] } : Group)
  let title := (g.title.toList).map fun t =>
    ({ role := .node, owner := t.id, items := [captionItem t.caption p.title] } : Group)
  let sections := (g.sections.zip p.sections).zipIdx.map fun ((s, r), i) =>
    cardGroup profile c 0 i s r
  let nodes := ((g.periods.zip p.periods).zipIdx).flatMap fun ((period, r), i) =>
    cardGroup profile c 1 (series g i period) period.toCard r ::
      (period.events.zip (p.events.getD i [])).map fun (e, b) =>
        cardGroup profile c 2 0 e.toCard b
  axis :: (edges ++ title ++ sections ++ nodes)

structure Result where
  canvas : Size
  geometry : Plan
  groups : List Group

def layout (g : Input) (profile : Profile) : Except LayoutError Result := do
  if !(g.periods.all fun p => decide (-1 ≤ p.sectionIndex ∧ p.sectionIndex < (g.sections.length : Int))) then
    throw .domain
  let c := TimelineConsts.load profile
  let raw := plan g c
  let ext := raw.extent g profile
  let p := raw.shift (c.canvasMargin - ext.x) (c.canvasMargin - ext.y)
  let canvas : Size := ⟨ext.w + 2 * c.canvasMargin, ext.h + 2 * c.canvasMargin⟩
  let values := [canvas.w, canvas.h] ++
    ((if g.title.isSome then [p.title] else []) ++ p.sections ++ p.periods ++ p.events.flatten).flatMap
      (rectValues 0 0) ++ p.routes.flatten.flatten.flatMap (pointValues 0 0) ++
      pointValues 0 0 p.axisStart ++ pointValues 0 0 p.axisEnd
  if !values.all withinLimit then throw .overflow
  return { canvas, geometry := p, groups := paint g profile c p }

end Timeline

namespace Eventmodeling

structure Lane where
  id : String
  index : Int
  caption : Option Caption

structure Frame where
  id : String
  lane : Nat
  category : String
  name : Caption
  data : Option Caption

structure Relation where
  id : String
  src : Nat
  dst : Nat

structure Input where
  lanes : List Lane
  frames : List Frame
  relations : List Relation

structure Plan where
  frames : List Rect
  laneY : List Int
  laneH : List Int
  corridors : List Int
  maxR : Int
  routes : List (List Point)

def order (g : Input) : List Nat :=
  (List.range g.lanes.length).mergeSort
    (laneKeyLe fun i => ((g.lanes[i]?).map (·.index)).getD 0)

def rank (g : Input) (i : Nat) : Nat := (order g).idxOf i

def clamp (v lo hi : Int) : Int := max lo (min hi v)

def frameSize (c : EventConsts) (f : Frame) : Size :=
  let w := max f.name.w ((f.data.map (·.w)).getD 0)
  let h := f.name.h + ((f.data.map fun d => c.lineHeight + d.h).getD 0)
  ⟨clamp w c.boxMinWidth c.boxMaxWidth + 2 * c.boxPadding,
    clamp h c.boxMinHeight c.boxMaxHeight + 2 * c.boxPadding⟩

def gutter (g : Input) (c : EventConsts) : Int :=
  g.lanes.foldl (fun w l =>
    match l.caption with
    | none => w
    | some cap => max w (4 * c.lanePadding + cap.w)) c.contentStartX

def columnWalk (c : EventConsts) (reach : Int) (floor : List Int) : List Frame → List Rect
  | [] => []
  | f :: fs =>
    let size := frameSize c f
    let x := max (reach - c.boxOverlap + c.boxPadding) (floor.getD f.lane 0)
    let r := x + size.w + c.boxPadding
    ⟨x, 0, size.w, size.h⟩ :: columnWalk c r (floor.set f.lane r) fs

def columns (g : Input) (c : EventConsts) : List Rect :=
  columnWalk c (gutter g c + c.boxOverlap - c.boxPadding)
    (List.replicate g.lanes.length 0) g.frames

def laneHeight (g : Input) (c : EventConsts) (frames : List Rect) (i : Nat) : Int :=
  let labelH := ((g.lanes[i]?).bind (·.caption)).map (·.h)
  let h := (g.frames.zip frames).foldl (fun h (f, r) =>
    if f.lane == i then max h r.h else h) (max c.laneMinHeight (labelH.getD 0))
  h + 2 * c.lanePadding

def bandWalk (height : Nat → Int) (gap width top : Int) : List Nat → List (Nat × Rect)
  | [] => []
  | i :: rest =>
    (i, ⟨0, top, width, height i⟩) ::
      bandWalk height gap width (top + height i + gap) rest

def laneBands (g : Input) (c : EventConsts) (frames : List Rect) : List (Nat × Rect) :=
  let maxR := frames.foldl (fun a r => max a (r.x + r.w + c.boxPadding)) 0
  bandWalk (laneHeight g c frames) c.laneGap (maxR + c.lanePadding) 0 (order g)

def rows (g : Input) (c : EventConsts) (frames : List Rect) : Plan :=
  let initial := (List.replicate g.lanes.length (0 : Int),
    List.replicate g.lanes.length (0 : Int), [half c.lanePadding])
  let state := (laneBands g c frames).foldl
    (fun (st : List Int × List Int × List Int) (i, b) =>
      (st.1.set i b.y, st.2.1.set i b.h, st.2.2 ++ [b.y + b.h + half c.laneGap])) initial
  let fs := (g.frames.zip frames).map fun (f, r) =>
    { r with y := state.1.getD f.lane 0 + c.lanePadding }
  { frames := fs, laneY := state.1, laneH := state.2.1, corridors := state.2.2,
    maxR := fs.foldl (fun a r => max a (r.x + r.w + c.boxPadding)) 0, routes := [] }

def hits (p : Plan) (r : Relation) (path : List Point) : Except LayoutError Bool := do
  if !(path.flatMap (pointValues 0 0)).all withinLimit then throw .overflow
  let mut hit := false
  for (b, i) in p.frames.zipIdx do
    if i != r.src && i != r.dst then
      if !([b.x, b.y, b.w, b.h, b.x + b.w, b.y + b.h].all withinLimit) then
        throw .overflow
      if Polyline.hitsRectB path b then hit := true
  return hit

def straightThrough (a b c : Point) : Bool :=
  (b.x - a.x) * (c.y - b.y) - (b.y - a.y) * (c.x - b.x) == 0 &&
    decide (0 < (b.x - a.x) * (c.x - b.x) + (b.y - a.y) * (c.y - b.y))

def tidyPush : List Point → Point → List Point
  | [], p => [p]
  | [a], p => if a == p then [a] else [p, a]
  | a :: b :: rest, p =>
    if a == p then a :: b :: rest
    else if straightThrough b a p then tidyPush (b :: rest) p
    else p :: a :: b :: rest

def tidy (points : List Point) : List Point :=
  (points.foldl tidyPush []).reverse

def route (g : Input) (profile : Profile) (p : Plan) (r : Relation) :
    Except LayoutError (List Point) := do
  let src := p.frames.getD r.src zeroRect
  let dst := p.frames.getD r.dst zeroRect
  let a := rank g (((g.frames[r.src]?).map (·.lane)).getD 0)
  let b := rank g (((g.frames[r.dst]?).map (·.lane)).getD 0)
  let start : Point := ⟨src.x + Int.fdiv (2 * src.w) 3,
    if a < b then src.y + src.h else src.y⟩
  let finish : Point := ⟨dst.x + Int.fdiv dst.w 3,
    if b < a then dst.y + dst.h else dst.y⟩
  let ca := p.corridors.getD (if a < b then a + 1 else a) 0
  let cb := p.corridors.getD (if b < a then b + 1 else b) 0
  if profile == .vector && a != b then
    if !(← hits p r [start, finish]) then return [start, finish]
  let mut column := p.maxR
  if !(← hits p r [⟨start.x, ca⟩, ⟨start.x, cb⟩]) then column := start.x
  else if !(← hits p r [⟨finish.x, ca⟩, ⟨finish.x, cb⟩]) then column := finish.x
  return tidy [start, ⟨start.x, ca⟩, ⟨column, ca⟩, ⟨column, cb⟩,
    ⟨finish.x, cb⟩, finish]

def laneRect (c : EventConsts) (p : Plan) (i : Nat) : Rect :=
  ⟨0, p.laneY.getD i 0, p.maxR + c.lanePadding, p.laneH.getD i 0⟩

def labelRect (g : Input) (c : EventConsts) (p : Plan) (i : Nat) : Rect :=
  match (g.lanes[i]?).bind (·.caption) with
  | none => zeroRect
  | some cap => ⟨2 * c.lanePadding, p.laneY.getD i 0 + c.lanePadding, cap.w, cap.h⟩

def frameTexts (g : Input) (c : EventConsts) (p : Plan) (i : Nat) : Rect × Rect :=
  let b := p.frames.getD i zeroRect
  match g.frames[i]? with
  | none => (zeroRect, zeroRect)
  | some f =>
    let total := f.name.h + ((f.data.map fun d => c.lineHeight + d.h).getD 0)
    let top := b.y + c.boxPadding + max 0 (half (b.h - 2 * c.boxPadding - total))
    (⟨b.x + c.boxPadding, top, b.w - 2 * c.boxPadding, f.name.h⟩,
      (f.data.map fun d =>
        (⟨b.x + c.boxPadding, top + f.name.h + c.lineHeight,
          b.w - 2 * c.boxPadding, d.h⟩ : Rect)).getD zeroRect)

def extent (g : Input) (c : EventConsts) (p : Plan) : Rect :=
  let lanes := (List.range g.lanes.length).flatMap fun i => [laneRect c p i, labelRect g c p i]
  let frames := (List.range g.frames.length).flatMap fun i =>
    let texts := frameTexts g c p i
    [p.frames.getD i zeroRect, texts.1, texts.2]
  let points := p.routes.flatten.map fun v => (⟨v.x, v.y, 0, 0⟩ : Rect)
  (lanes ++ frames ++ points).foldl Rect.unionRaw zeroRect

def style : String → String
  | "command" => "note"
  | "readmodel" => "success"
  | "event" => "warning"
  | "processor" => "mark-hollow"
  | _ => "node"

def axis (a b : Point) : MarkerAxis :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  if absI dy ≤ absI dx then if dx < 0 then .negativeX else .positiveX
  else if dy < 0 then .negativeY else .positiveY

structure Result where
  canvas : Size
  lanes : List Rect
  labels : List Rect
  frames : List Rect
  routes : List (List Point)
  groups : List Group

def layout (g : Input) (profile : Profile) : Except LayoutError Result := do
  if !(g.frames.all fun f => decide (f.lane < g.lanes.length)) ||
      !(g.relations.all fun r => decide (r.src < g.frames.length ∧ r.dst < g.frames.length)) then
    throw .domain
  let c := EventConsts.load profile
  let raw := rows g c (columns g c)
  let routes ← g.relations.mapM (route g profile raw)
  let p := { raw with routes }
  let ext := extent g c p
  let dx := c.canvasMargin - ext.x
  let dy := c.canvasMargin - ext.y
  let lanes := (List.range g.lanes.length).map fun i => shiftRect dx dy (laneRect c p i)
  let labels := (List.range g.lanes.length).map fun i => shiftRect dx dy (labelRect g c p i)
  let frames := p.frames.map (shiftRect dx dy)
  let routes := routes.map (·.map (shiftPoint dx dy))
  let canvas : Size := ⟨ext.w + 2 * c.canvasMargin, ext.h + 2 * c.canvasMargin⟩
  let values := [canvas.w, canvas.h] ++ (lanes ++ labels ++ frames).flatMap (rectValues 0 0) ++
    routes.flatten.flatMap (pointValues 0 0) ++
    (List.range g.frames.length).flatMap (fun i =>
      let ts := frameTexts g c p i
      rectValues dx dy ts.1 ++ rectValues dx dy ts.2)
  if !values.all withinLimit then throw .overflow
  let laneGroups := g.lanes.zipIdx.filterMap fun (l, i) =>
    if l.id == "" then none else some
      { role := GroupRole.group, owner := l.id
        items := (if profile == .vector then [Primitive.rect (lanes.getD i zeroRect) (plain "band")] else []) ++
          [.rect (lanes.getD i zeroRect) (plain "group")] ++
          (l.caption.toList.map fun cap => textItem cap (labels.getD i zeroRect) .start) : Group }
  let edges := (g.relations.zip routes).map fun (r, points) =>
    { role := GroupRole.edge, owner := r.id
      items := [.polyline points c.cornerRadius (plain "edge")] ++
        (if points.length < 2 then [] else
          [.markerRef "point" (points.getLast?.getD ⟨0, 0⟩)
            (axis (points.getD (points.length - 2) ⟨0, 0⟩) (points.getLast?.getD ⟨0, 0⟩))]) : Group }
  let nodes := g.frames.zipIdx.map fun (f, i) =>
    let ts := frameTexts g c p i
    { role := GroupRole.node, owner := f.id
      items := [.roundRect (frames.getD i zeroRect) c.cornerRadius (plain (style f.category)),
        textItem f.name (shiftRect dx dy ts.1) .middle] ++
        (f.data.toList.map fun cap => textItem cap (shiftRect dx dy ts.2) .start) : Group }
  return { canvas, lanes, labels, frames, routes, groups := laneGroups ++ edges ++ nodes }

end Eventmodeling

end Lanes
end Elegant

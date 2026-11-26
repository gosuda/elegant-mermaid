import Elegant.Gen.Layoutconst
import Elegant.Kinds.Common
import Elegant.Tree
import ElegantGeometry.Trig

set_option autoImplicit false

/-! Mindmap model adapter, following Go's `layout.layoutMindmap`. The boxes are the model boxes
in declaration order; the parent of a box is the `from` end of the route that targets it (the last
such route wins). A box takes the measured size of its label text, capped at `maxNodeWidth`, and
the tree family places the boxes and the elbow routes. After placement the adapter moves the layout
inside the canvas margin and paints the display list: one polyline for every route, one shape and
one text for every box. -/

namespace Elegant
namespace Kinds
namespace Mindmap

open Common

structure Consts where
  padding : Int
  maxWidth : Int
  levelGap : Int
  siblingGap : Int
  lineHeight : Int
  margin : Int
  corner : Int
  deriving DecidableEq, Repr

def baseConsts (profile : Profile) : Consts :=
  { padding := LayoutConst.mindmap_padding.get profile
    maxWidth := LayoutConst.mindmap_max_node_width.get profile
    levelGap := LayoutConst.mindmap_level_gap.get profile
    siblingGap := LayoutConst.mindmap_sibling_gap.get profile
    lineHeight := LayoutConst.line_h.get profile
    margin := LayoutConst.canvas_margin.get profile
    corner := LayoutConst.corner_radius.get profile }

def pixelUnits : Int := 64

/-- A configured pixel size, in units. -/
def configUnits : ConfigValue → Except LayoutError Int
  | .integer v => if 0 ≤ v ∧ v * pixelUnits ≤ COORD_LIMIT then .ok (v * pixelUnits) else .error .overflow
  | .string s =>
    match s.toInt? with
    | some v => if 0 ≤ v ∧ v * pixelUnits ≤ COORD_LIMIT then .ok (v * pixelUnits) else .error .overflow
    | none => .error .overflow
  | .boolean _ => .error .overflow

def applyConfig (c : Consts) : List (String × ConfigValue) → Except LayoutError Consts
  | [] => .ok c
  | (key, value) :: rest =>
    if key == "padding" then
      match configUnits value with
      | .ok px => applyConfig { c with padding := px } rest
      | .error e => .error e
    else if key == "maxNodeWidth" then
      match configUnits value with
      | .ok px => applyConfig { c with maxWidth := px } rest
      | .error e => .error e
    else applyConfig c rest

def load (m : Model) : Except LayoutError Consts :=
  match m.options.profile with
  | .vector => applyConfig (baseConsts .vector) m.options.config
  | .cell => .ok (baseConsts .cell)

/-- Go's `mindmapLimits`: nodes, then edges, then the bytes of the label texts. -/
def limitFailure (m : Model) : Option LayoutFailure :=
  let l := m.options.limits
  let textBytes := m.labels.foldl (fun n lb => n + lb.text.utf8ByteSize) 0
  if l.maxNodes < m.boxes.length then some (.tooLarge l.maxNodes m.boxes.length)
  else if l.maxEdges < m.routes.length then some (.tooLarge l.maxEdges m.routes.length)
  else if l.maxTextBytes < textBytes then some (.tooLarge l.maxTextBytes textBytes)
  else none

def boxIndex (m : Model) (id : String) : Nat := (m.boxes.findIdx? (·.id == id)).getD 0

/-- The parent of every box: the source of the last route that targets it. -/
def parents (m : Model) : List (Option Nat) :=
  m.routes.foldl (fun ps r => ps.set (boxIndex m r.toId) (some (boxIndex m r.fromId)))
    (m.boxes.map fun _ => none)

/-- Every relation must describe the parent edge that the tree family lays out. A general
well-formed model can still contain two different parents for one child. Such a model is not
a mindmap: keeping its last parent while emitting both relations would put one route off-port. -/
def treeRelations (m : Model) : Bool :=
  let ps := parents m
  m.routes.all fun r =>
    match m.boxes[boxIndex m r.fromId]?, m.boxes[boxIndex m r.toId]?,
        ps[boxIndex m r.toId]? with
    | some fromBox, some toBox, some (some parent) =>
      fromBox.id == r.fromId && toBox.id == r.toId && parent == boxIndex m r.fromId
    | _, _, _ => false

structure Measured where
  lines : List Measure.Line
  width : Int
  height : Int

def measureBox (m : Model) (c : Consts) (metric : Measure.Metric) (b : ModelBox) :
    Except LayoutError Measured :=
  match StyledMeasure.wrap metric (max (c.maxWidth - 2 * c.padding) 1) (boxText m b).toList with
  | .error _ => .error .overflow
  | .ok lines =>
    let w := min c.maxWidth (widest lines + 2 * c.padding)
    let h := ((max lines.length 1 : Nat) : Int) * c.lineHeight + 2 * c.padding
    if COORD_LIMIT < h ∨ COORD_LIMIT < w then .error .overflow
    else .ok ⟨lines, max w 1, max h 1⟩

/-! ### Drawing -/

def runsOf (lines : List Measure.Line) : List (List TextRun) :=
  lines.map fun l => [⟨String.ofList l.text, false, false⟩]

def nodePaint : Paint := { style := "node" }

def cloudBumps : Int := 8
def cloudBase : Int := 27525
def cloudControl : Int := 35062
def bangSpikes : Int := 8
def bangInner : Int := 20316
def unitQ15 : Int := 32768
def turnQ16 : Int := 65536

def centreOf (r : Rect) : Point := ⟨r.x + Int.fdiv r.w 2, r.y + Int.fdiv r.h 2⟩

def polar (r : Rect) (centre : Point) (angle factor : Int) : Point :=
  let rx := Int.fdiv r.w 2
  let ry := Int.fdiv r.h 2
  ⟨centre.x + Int.fdiv (rx * cosQ15 angle * factor) (2 ^ 30),
   centre.y + Int.fdiv (ry * sinQ15 angle * factor) (2 ^ 30)⟩

def hexagonPoints (r : Rect) (centre : Point) : List Point :=
  let inset := min (Int.fdiv r.h 4) (Int.fdiv r.w 4)
  let right := r.x + r.w
  let bottom := r.y + r.h
  [⟨r.x + inset, r.y⟩, ⟨right - inset, r.y⟩, ⟨right, centre.y⟩,
   ⟨right - inset, bottom⟩, ⟨r.x + inset, bottom⟩, ⟨r.x, centre.y⟩]

def bangPoints (r : Rect) (centre : Point) : List Point :=
  (List.range (2 * bangSpikes.toNat)).map fun (k : Nat) =>
    polar r centre ((k : Int) * turnQ16 / (2 * bangSpikes)) (if k % 2 == 1 then bangInner else unitQ15)

def cloudCommands (r : Rect) (centre : Point) : List PathCommand :=
  let step := turnQ16 / cloudBumps
  [PathCommand.M (polar r centre 0 cloudBase)] ++
    (List.range cloudBumps.toNat).map (fun (k : Nat) =>
      let from_ := (k : Int) * step
      PathCommand.C (polar r centre (from_ + step / 3) cloudControl)
        (polar r centre (from_ + 2 * step / 3) cloudControl)
        (polar r centre (from_ + step) cloudBase)) ++ [PathCommand.Z]

def cellShape (shape : String) (r : Rect) : List Primitive :=
  match shape with
  | "defaultMindmapNode" => []
  | "rounded" | "mindmapCircle" => [.roundRect r 0 nodePaint]
  | "cloud" => [.roundRect r 0 { nodePaint with line := .dotted }]
  | "bang" => [.rect r { nodePaint with line := .double }]
  | "hexagon" => [.rect r { nodePaint with width := .emphasis }]
  | _ => [.rect r nodePaint]

def vectorShape (c : Consts) (shape : String) (r : Rect) : List Primitive :=
  let centre := centreOf r
  match shape with
  | "defaultMindmapNode" => [.roundRect r c.corner { style := "band" }]
  | "rounded" => [.roundRect r c.corner nodePaint]
  | "mindmapCircle" => [.ellipse centre.x centre.y (Int.fdiv r.w 2) (Int.fdiv r.h 2) nodePaint]
  | "hexagon" => [.polygon (hexagonPoints r centre) nodePaint]
  | "bang" => [.polygon (bangPoints r centre) nodePaint]
  | "cloud" => [.path (cloudCommands r centre) nodePaint]
  | _ => [.rect r nodePaint]

def textItem (c : Consts) (r : Rect) (lines : List Measure.Line) : Primitive :=
  let height := (lines.length : Int) * c.lineHeight
  .text { rect := ⟨r.x, r.y + Int.fdiv (r.h - height) 2, r.w, height⟩, role := .label, size := 14,
          align := .middle, style := "text", lines := runsOf lines }

def edgeGroups (c : Consts) (routes : List Route) : List Group :=
  routes.map fun r => ⟨.edge, r.id, [.polyline r.points c.corner { style := "edge" }]⟩

def nodeGroups (m : Model) (c : Consts) (boxes : List Box) (lines : List (List Measure.Line)) :
    List Group :=
  (m.boxes.zip boxes).zipIdx.map fun ((mb, b), i) =>
    let shape :=
      if m.profile == .cell then cellShape mb.shape b.rect else vectorShape c mb.shape b.rect
    ⟨.node, mb.id, shape ++ [textItem c b.rect (lines.getD i [])]⟩

/-! ### The layout -/

def liftGeometry {α : Type} : Except LayoutError α → Except LayoutFailure α
  | .ok a => .ok a
  | .error e => .error (.geometry e)

def build (m : Model) (c : Consts) (measured : List Measured) (canvas : Size)
    (placed : Tree.Layout) : Scene :=
  let boxes : List Box := (m.boxes.zip placed.boxes).map fun (b, r) =>
    ⟨b.id, b.role.id, r, "", b.exclusive⟩
  let routes : List Route := m.routes.map fun r =>
    ⟨r.id, r.fromId, r.toId, r.orthogonal, placed.routes.getD (boxIndex m r.toId) []⟩
  { kind := m.kind, profile := m.profile, options := m.options, canvas := canvas
    boxes := boxes, routes := routes, labels := []
    items := edgeGroups c routes ++ nodeGroups m c boxes (measured.map (·.lines)) }

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match limitFailure m with
  | some failure => .error failure
  | none => do
    if !treeRelations m then throw (.geometry .domain)
    let c ← liftGeometry (load m)
    let metric ← liftGeometry (labelMetric m.options.profile m.options.fontFamily)
    let measured ← liftGeometry (m.boxes.mapM (measureBox m c metric))
    let ps := parents m
    let nodes : List Tree.Node := (measured.zip ps).map fun (s, p) => ⟨p, s.width, s.height⟩
    let placed ← liftGeometry (Tree.mindmap nodes ⟨c.levelGap, c.siblingGap⟩)
    let (canvas, shifted) ← liftGeometry (Tree.normalize c.margin placed)
    pure { scene := (build m c measured canvas shifted).projectCellAttachments (routeMarkers m),
           budgetExhausted := false }

theorem treeRelations_spec {m : Model} (h : treeRelations m = true)
    {r : ModelRoute} (hr : r ∈ m.routes) :
    ∃ fromBox toBox parent,
      m.boxes[boxIndex m r.fromId]? = some fromBox ∧
      m.boxes[boxIndex m r.toId]? = some toBox ∧
      (parents m)[boxIndex m r.toId]? = some (some parent) ∧
      fromBox.id = r.fromId ∧ toBox.id = r.toId ∧ parent = boxIndex m r.fromId := by
  have he := List.all_eq_true.mp h r hr
  cases hf : m.boxes[boxIndex m r.fromId]? with
  | none => simp [hf] at he
  | some fromBox =>
    cases ht : m.boxes[boxIndex m r.toId]? with
    | none => simp [hf, ht] at he
    | some toBox =>
      cases hp : (parents m)[boxIndex m r.toId]? with
      | none => simp [hf, ht, hp] at he
      | some p =>
        cases p with
        | none => simp [hf, ht, hp] at he
        | some parent =>
          refine ⟨fromBox, toBox, parent, rfl, rfl, rfl, ?_⟩
          simpa only [hf, ht, hp, Bool.and_eq_true, beq_iff_eq, and_assoc] using he

theorem parents_length (m : Model) : (parents m).length = m.boxes.length := by
  have aux : ∀ (routes : List ModelRoute) (ps : List (Option Nat)),
      (routes.foldl (fun ps r =>
        ps.set (boxIndex m r.toId) (some (boxIndex m r.fromId))) ps).length = ps.length := by
    intro routes
    induction routes with
    | nil => intro ps; rfl
    | cons r rest ih =>
      intro ps
      simp only [List.foldl_cons, ih, List.length_set]
  simpa only [parents, List.length_map] using aux m.routes (m.boxes.map fun _ => none)

theorem measureBox_dims {m : Model} {c : Consts} {metric : Measure.Metric}
    {b : ModelBox} {s : Measured} (h : measureBox m c metric b = .ok s) :
    1 ≤ s.width ∧ 1 ≤ s.height := by
  unfold measureBox at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · have he := Except.ok.inj h
      cases he
      constructor <;> exact Int.le_max_right _ _


theorem applyConfig_fixed :
    ∀ (entries : List (String × ConfigValue)) (c out : Consts),
      applyConfig c entries = .ok out →
      out.levelGap = c.levelGap ∧ out.siblingGap = c.siblingGap ∧ out.margin = c.margin := by
  intro entries
  induction entries with
  | nil =>
    intro c out h
    have he := Except.ok.inj h
    cases he
    exact ⟨rfl, rfl, rfl⟩
  | cons entry rest ih =>
    obtain ⟨key, value⟩ := entry
    intro c out h
    unfold applyConfig at h
    split at h
    · cases hu : configUnits value with
      | error e => rw [hu] at h; cases h
      | ok px =>
        rw [hu] at h
        exact ih { c with padding := px } out h
    · split at h
      · cases hu : configUnits value with
        | error e => rw [hu] at h; cases h
        | ok px =>
          rw [hu] at h
          exact ih { c with maxWidth := px } out h
      · exact ih _ _ h

theorem load_fixed {m : Model} {c : Consts} (h : load m = .ok c) :
    c.levelGap = (baseConsts m.options.profile).levelGap ∧
    c.siblingGap = (baseConsts m.options.profile).siblingGap ∧
    c.margin = (baseConsts m.options.profile).margin := by
  unfold load at h
  cases hp : m.options.profile with
  | vector =>
    rw [hp] at h
    simpa only [hp] using applyConfig_fixed _ _ _ h
  | cell =>
    rw [hp] at h
    have he := Except.ok.inj h
    cases he
    exact ⟨rfl, rfl, rfl⟩

theorem load_nonneg {m : Model} {c : Consts} (h : load m = .ok c) :
    0 ≤ c.levelGap ∧ 1 ≤ c.siblingGap ∧ 0 ≤ c.margin := by
  obtain ⟨hl, hs, hm⟩ := load_fixed h
  rw [hl, hs, hm]
  cases m.options.profile <;> decide

end Mindmap
end Kinds
end Elegant

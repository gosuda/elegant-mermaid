import Elegant.Kinds.Common
import Elegant.Layered.LayeredAdmission
import ElegantGeometry.Trig

set_option autoImplicit false

/-! Agentflow model adapter. Every node, and every collapsed group (a node-role box with the
`collapsedGroup` shape), is sized from its label wrapped at `agentflow.wrapping_width` plus
`agentflow.padding` on every side, floored by `agentflow.min_node_width`. Framed shapes reserve
one further default padding on each horizontal side for their interior rules. A collapsed group adds
one line and the vertical padding for its summary row. Expanded groups are clusters and carry
no size. Edges ask for the minimum length the dump gives. Per-kind spacing, wrap width and
canvas margin come from the family's kind parameters (`agentflow.node_spacing`,
`agentflow.rank_spacing`, `agentflow.diagram_padding`). The optional integer
`flowchart.padding` model option preserves the authored pixel padding, including zero. -/

namespace Elegant
namespace Kinds
namespace Agentflow

open Common

def lineHeight : Profile → Int
  | .vector => Measure.Role.label.lineHeightPx * 64
  | .cell => 1

/-- Widest wrapped line and the height of all wrapped lines; an empty text has height zero. -/
def measured (profile : Profile) (text : String) (fontFamily : Bool := false) :
    Except LayoutError (Int × Int) := do
  let metric ← labelMetric profile fontFamily
  let lines ← StyledMeasure.wrap metric (LayoutConst.agentflow_wrapping_width.get profile) text.toList
  let height ← Measure.checkedI32 ((lines.length : Int) * lineHeight profile)
  pure (widest lines, height)

def isFramed (shape : String) : Bool :=
  shape == "subroutine" || shape == "subprocess" || shape == "subproc" ||
    shape == "framed-rectangle"

/-- Absence retains the family default; an explicit zero remains an authored override. -/
def configuredPadding (options : Options) : Except LayoutError (Option Int) :=
  match options.config.find? (fun entry => entry.1 == "flowchart.padding") with
  | none => pure none
  | some (_, .integer value) => do
    if value < 0 then throw .domain
    pure (some (← Measure.checkedI32 value))
  | some _ => throw .domain

def paddingUnits (profile : Profile) (authored : Option Int) :
    Except LayoutError (Int × Int) := do
  match authored with
  | none =>
    let padding := LayoutConst.agentflow_padding.get profile
    pure (padding, padding)
  | some padding =>
    if padding < 0 then throw .domain
    let padding ← Measure.checkedI32 padding
    match profile with
    | .vector =>
      let padding ← Measure.checkedI32 (padding * 64)
      pure (padding, padding)
    | .cell =>
      let x ← Measure.checkedI32 (Measure.ceilDiv padding 8)
      let y ← Measure.checkedI32 (Measure.ceilDiv padding 16)
      pure (max x 1, max y 1)

def contentSize (profile : Profile) (text : String) (fontFamily : Bool := false)
    (shape : String := "") (authoredPadding : Option Int := none) :
    Except LayoutError Size := do
  let (width, height) ← measured profile text fontFamily
  let (paddingX, paddingY) ← paddingUnits profile authoredPadding
  let inset := if isFramed shape then LayoutConst.agentflow_padding.get profile else 0
  let paddingX ← Measure.checkedI32 (paddingX + inset)
  let width ← Measure.checkedI32 (width + 2 * paddingX)
  let height ← Measure.checkedI32 (height + 2 * paddingY)
  pure ⟨max width (LayoutConst.agentflow_min_node_width.get profile), height⟩

-- Fifteen cell columns previously met the framed node's interior vertical rule.
#guard (contentSize .cell "abcdefghijklmno" false "").toOption = some ⟨17, 3⟩
#guard (contentSize .cell "abcdefghijklmno" false "subroutine").toOption = some ⟨19, 3⟩
#guard ["subroutine", "subprocess", "subproc", "framed-rectangle"].all fun shape =>
  decide ((contentSize .cell "abcdefghijklmno" false shape).toOption = some ⟨19, 3⟩)
#guard (configuredPadding {}).toOption = some none
#guard (configuredPadding { config := [("flowchart.padding", .integer 0)] }).toOption =
  some (some 0)
#guard (paddingUnits .vector none).toOption = some (512, 512)
#guard (paddingUnits .vector (some 0)).toOption = some (0, 0)
#guard (paddingUnits .cell (some 0)).toOption = some (1, 1)
#guard (paddingUnits .cell (some 17)).toOption = some (3, 2)
#guard match paddingUnits .vector (some (-1)) with
  | .error .domain => true
  | _ => false
#guard match paddingUnits .vector (some I32_MAX) with
  | .error .overflow => true
  | _ => false
#guard (contentSize .cell "A" false "" (some 64)).toOption = some ⟨17, 9⟩
#guard (contentSize .cell "abcdefghijklmno" false "subroutine" (some 64)).toOption = some ⟨33, 9⟩

def boxSize (profile : Profile) (b : ModelBox) (text : String) (fontFamily : Bool := false)
    (authoredPadding : Option Int := none) :
    Except LayoutError Size := do
  let size ← contentSize profile text fontFamily b.shape authoredPadding
  if b.shape == "collapsedGroup" then
    let (_, paddingY) ← paddingUnits profile authoredPadding
    let height ← Measure.checkedI32 (size.h + lineHeight profile)
    let height ← Measure.checkedI32 (height + paddingY)
    pure ⟨size.w, height⟩
  else pure size

def sizes (m : Model) : Except LayoutError (List (String × Size)) := do
  let padding ← configuredPadding m.options
  (m.boxes.filter fun b => b.role == .node).mapM fun b => do
    let size ← boxSize m.options.profile b (boxText m b) m.options.fontFamily padding
    pure (b.id, withFamilyMinimum m.options.profile size)

#guard (sizes {
    kind := "agentflow"
    options := { profile := .cell }
    boxes := [{ id := "A" }] }).toOption = some [("A", ⟨15, 3⟩)]
#guard (sizes {
    kind := "agentflow"
    options := { profile := .cell, config := [("flowchart.padding", .integer 64)] }
    boxes := [{ id := "A" }] }).toOption = some [("A", ⟨17, 9⟩)]
#guard match sizes {
    kind := "agentflow"
    options := { config := [("flowchart.padding", .integer (-1))] } } with
  | .error .domain => true
  | _ => false

def input (m : Model) (fixed : List (String × Size)) : Layered.Input :=
  { kind := m.kind
    boxes := m.boxes
    routes := m.routes
    texts := m.boxes.map (boxText m)
    edges := m.routes.map fun r => edgeOptions (max r.minLength 1) r
    labels := m.labels
    fixedSizes := fixed }

/-! ### Node outlines

`shapeScene` redraws every node group as the Go adapter does: the outline of the node's shape,
then the group's text items. A collapsed group moves its text up by half of one line plus the
vertical padding. The layout dump is not touched. -/

def plain : Paint := { style := "node" }

def polygonOf (points : List (Int × Int)) : List Primitive :=
  [.polygon (points.map fun p => ⟨p.1, p.2⟩) plain]

def framed (profile : Profile) (r : Rect) : List Primitive :=
  let inset := min (LayoutConst.agentflow_padding.get profile) (Int.tdiv r.w 3)
  .rect r plain ::
    [r.x + inset, r.x + r.w - inset].map fun x =>
      .polyline [⟨x, r.y⟩, ⟨x, r.y + r.h⟩] 0 { style := "rule" }

def documentOutline (r : Rect) : Except LayoutError (List Primitive) := do
  let amplitude := Int.tdiv r.h 8
  let baseline := r.y + r.h - amplitude
  let wave ← (List.range 33).mapM fun (i : Nat) => do
    let index : Int := i
    let x ← Measure.checkedI32 (r.x + Int.fdiv (r.w * index) 32)
    let y ← Measure.checkedI32 (baseline + Int.fdiv (amplitude * sinQ15 (index * 2048)) 32768)
    pure (Point.mk x y)
  let lineX := r.x + Int.tdiv r.w 22
  pure [.polygon ([⟨r.x, r.y⟩, ⟨r.x, baseline⟩] ++ wave ++ [⟨r.x + r.w, r.y⟩]) plain,
    .polyline [⟨lineX, r.y⟩, ⟨lineX, baseline⟩] 0 { style := "rule" }]

def collapsedIndicator (profile : Profile) (r : Rect) : List Primitive :=
  let padding := LayoutConst.agentflow_padding.get profile
  let height := lineHeight profile
  let y := r.y + r.h - padding - 2 * height
  let centre := r.x + Int.tdiv r.w 2
  .polyline [⟨r.x + padding, y⟩, ⟨r.x + r.w - padding, y⟩] 0 { style := "rule", line := .dotted } ::
    [-padding, 0, padding].map fun offset =>
      match profile with
      | .cell => .symbolRef "disc" ⟨centre + offset, y + height⟩ "ink"
      | .vector =>
        let radius := Int.tdiv (padding * 5) 16
        .ellipse (centre + offset) (y + height) radius radius { style := "ink" }

def roundedOutline (profile : Profile) (name : String) (r : Rect) : List Primitive :=
  let collapsed := name == "collapsedGroup"
  .roundRect r (LayoutConst.corner_radius.get profile) { style := if collapsed then "group" else "node" } ::
    (if collapsed then collapsedIndicator profile r else [])

def outline (profile : Profile) (name : String) (r : Rect) :
    Except LayoutError (List Primitive) :=
  let right := r.x + r.w
  let bottom := r.y + r.h
  let cx := r.x + Int.tdiv r.w 2
  let cy := r.y + Int.tdiv r.h 2
  match name with
  | "diamond" => pure (polygonOf [(cx, r.y), (right, cy), (cx, bottom), (r.x, cy)])
  | "hexagon" | "hex" =>
    let inset := min (Int.tdiv r.h 4) (Int.tdiv r.w 4)
    pure (polygonOf [(r.x + inset, r.y), (right - inset, r.y), (right, cy),
      (right - inset, bottom), (r.x + inset, bottom), (r.x, cy)])
  | "lean-right" =>
    let inset := min (Int.tdiv r.h 2) (Int.tdiv r.w 3)
    pure (polygonOf [(r.x + inset, r.y), (right, r.y), (right - inset, bottom), (r.x, bottom)])
  | "subroutine" | "subprocess" | "subproc" | "framed-rectangle" => pure (framed profile r)
  | "lin-doc" | "lined-document" => documentOutline r
  | "connector" => pure [.ellipse cx cy (Int.tdiv r.w 2) (Int.tdiv r.h 2) plain]
  | _ => pure (roundedOutline profile name r)

def shiftedText (profile : Profile) (shape : String) (item : Primitive) : Option Primitive :=
  match item with
  | .text t =>
    if shape == "collapsedGroup" then
      let lift := Int.tdiv (lineHeight profile + LayoutConst.agentflow_padding.get profile) 2
      some (.text { t with rect := { t.rect with y := t.rect.y - lift } })
    else some item
  | _ => none

def shapedGroup (profile : Profile) (shape : String) (r : Rect) (g : Group) :
    Except LayoutError Group := do
  let shapes ← outline profile shape r
  pure { g with items := shapes ++ g.items.filterMap (shiftedText profile shape) }

def shapeScene (m : Model) (s : Scene) : Except LayoutError Scene := do
  let items ← s.items.mapM fun g =>
    match m.boxes.find? (fun b => b.id == g.owner && b.role == .node),
        s.boxes.find? (fun b => b.id == g.owner) with
    | some b, some placed => shapedGroup m.options.profile b.shape placed.rect g
    | _, _ => pure g
  pure { s with items := items }

theorem shapeScene_layoutDump {m : Model} {s s' : Scene} (h : shapeScene m s = .ok s') :
    s'.layoutDump = s.layoutDump := by
  unfold shapeScene at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h
    subst h
    rfl

/-- Adapter entrypoint: the family runs only on an admissible input (nonempty box
ids, no box id naming a route id, exclusive fixed-size boxes, positive fixed sizes);
otherwise `.error (.geometry .domain)`. -/
def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match sizes m with
  | .error e => .error (.geometry e)
  | .ok fixed =>
    match Layered.admit (input m fixed) (Layered.layoutFamily (input m fixed) m.options) with
    | .error e => .error e
    | .ok result =>
      match shapeScene m (result.scene.projectCellAttachments (routeMarkers m)) with
      | .error e => .error (.geometry e)
      | .ok scene => .ok { result with scene := scene }

/-- Agentflow validity reduces to the family's: the adapter fixes sizes, projects cell
attachments, and redraws node outlines, which keeps the layout dump. A successful run also
records that the built input passed the admission guard. -/
theorem layout_valid_of_family
    (hfam : ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
      Layered.layoutFamily inp o = .ok res → Validator.check res.scene.layoutDump = true)
    {m : Model} {r : Layered.FamilyResult} (h : layout m = .ok r) :
    Validator.check r.scene.layoutDump = true := by
  unfold layout at h
  cases hs : sizes m with
  | error e => simp [hs] at h
  | ok fixed =>
    cases ha : Layered.admit (input m fixed)
        (Layered.layoutFamily (input m fixed) m.options) with
    | error e => simp [hs, ha] at h
    | ok res =>
      cases hd : shapeScene m (res.scene.projectCellAttachments (routeMarkers m)) with
      | error e => simp [hs, ha, hd] at h
      | ok scene =>
        simp only [hs, ha, hd, Except.ok.injEq] at h
        subst h
        show Validator.check scene.layoutDump = true
        rw [shapeScene_layoutDump hd, Scene.projectCellAttachments_layoutDump]
        exact hfam _ _ _ (Layered.admit_ok ha).2

end Agentflow
end Kinds
end Elegant

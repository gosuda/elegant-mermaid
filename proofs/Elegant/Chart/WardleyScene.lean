import Elegant.Chart.WardleyPlace
import Elegant.Chart.WardleyItems

set_option autoImplicit false

namespace Elegant.Chart.Wardley

structure Constants where
  geometry : GeometryConstants
  labels : LabelConstants
  fonts : FontConstants
  paint : PaintConstants


def endpoint (g : Geometry) (id : String) : Except LayoutError Point :=
  match g.lookup.points[id]? with
  | some p => .ok p
  | none => .error .domain

theorem endpoint_lookup (g : Geometry) (id : String) (point : Point)
    (h : endpoint g id = .ok point) : g.lookup.points[id]? = some point := by
  unfold endpoint at h
  cases hp : g.lookup.points[id]? with
  | none => simp [hp] at h
  | some value =>
      simp only [hp, Except.ok.injEq] at h
      subst value
      rfl

theorem endpoint_declaration (c : GeometryConstants) (input : Input)
    (id : String) (point : Point)
    (h : endpoint (arrange c input) id = .ok point) :
    (∃ entry ∈ (input.nodes.zip (arrange c input).positions).zipIdx,
      id = "n" ++ toString entry.2 ∧ point = entry.1.2) ∨
    (∃ entry ∈ (arrange c input).ghosts.zipIdx,
      id = "tg" ++ toString entry.2 ∧ point = entry.1) :=
  arrange_lookup_points_sound c input id point (endpoint_lookup _ _ _ h)

def boxRect (g : Geometry) (annotationBox : Rect) (id : String) : Except LayoutError Rect :=
  if id = "plot" then .ok g.plot
  else if id = "ab" then .ok annotationBox
  else match g.lookup.rectangles[id]? with
    | some r => .ok r
    | none => .error .domain

def markerAxis (dx dy : Int) : MarkerAxis :=
  if max dx (-dx) ≥ max dy (-dy) then
    if dx ≥ 0 then .positiveX else .negativeX
  else if dy ≥ 0 then .positiveY else .negativeY

def arrowhead (cell : Bool) (source target : Point) (reach : Int) :
    Except LayoutError (Point × MarkerAxis) := do
  let dx := target.x - source.x
  let dy := target.y - source.y
  let axis := markerAxis dx dy
  if dx = 0 ∧ dy = 0 then return (target, axis)
  if cell then
    let p := match axis with
      | .positiveX => ⟨target.x - 1, target.y⟩
      | .negativeX => ⟨target.x + 1, target.y⟩
      | .positiveY => ⟨target.x, target.y - 1⟩
      | .negativeY => ⟨target.x, target.y + 1⟩
    return (p, axis)
  let length ← Rect.isqrt (dx * dx + dy * dy)
  return (⟨target.x - Int.fdiv (2 * dx * reach + length) (2 * length),
    target.y - Int.fdiv (2 * dy * reach + length) (2 * length)⟩, axis)

def textItems (labels : List PlacedLabel) (owner : String) : List Primitive :=
  (labels.filter fun l => l.shown && l.measured.model.owner == owner).map fun l =>
    let role := match l.measured.role with
      | .title => TextRole.title | .label => TextRole.label | .body => TextRole.body
    let style := match l.measured.kind with
      | .axisX | .axisY | .stage => "text-muted" | _ => "text"
    .text {
      rect := l.rect
      role := role
      size := l.measured.size
      align := l.align
      style := style
      lines := l.measured.lines.map fun line => [⟨String.ofList line.text, false, false⟩] }

def routeItems (c : Constants) (cell : Bool) (g : Geometry)
    (labels : List PlacedLabel) (r : ModelRoute) : Except LayoutError (List Primitive) := do
  let a ← endpoint g r.fromId
  let b ← endpoint g r.toId
  let line := if r.stroke = "dashed" then LineStyle.dashed else
    if r.stroke = "dotted" then .dotted else .solid
  let mut items := [pathThrough [a, b] false { style := "edge", line }]
  let reach := fun id => match g.lookup.nodes[id]? with
    | some n => nodeReach c.labels cell n
    | none => c.labels.nodeRadius
  if r.markerStart = "point" then
    let (p, axis) ← arrowhead cell b a (reach r.fromId)
    items := items ++ [.markerRef "point" p axis]
  if r.markerEnd = "point" then
    let (p, axis) ← arrowhead cell a b (reach r.toId)
    items := items ++ [.markerRef "point" p axis]
  return items ++ textItems labels r.id

private def group (role : GroupRole) (owner : String) (items : List Primitive) : List Group :=
  if items.isEmpty then [] else [⟨role, owner, items⟩]

def groups (c : Constants) (cell : Bool) (input : Input) (g : Geometry)
    (box : Rect) (labels : List PlacedLabel) (routes : List ModelRoute) :
    Except LayoutError (List Group) := do
  let edges ← routes.mapM fun r => do
    return group .edge r.id (← routeItems c cell g labels r)
  let pipelines := g.frames.zipIdx.flatMap fun (r, i) =>
    group .node ("pl" ++ toString i) (frameItems c.paint r)
  let nodes := (input.nodes.zip g.positions).zipIdx.flatMap fun (entry, i) =>
    let id := "n" ++ toString i
    group .node id (nodeItems c.paint cell entry.1 entry.2 ++ textItems labels id)
  let ghosts := g.ghosts.zipIdx.flatMap fun (p, i) =>
    group .node ("tg" ++ toString i) (ghostItems c.paint cell p)
  let forces := g.accelerators.zipIdx.flatMap fun (r, i) =>
    let id := "ac" ++ toString i
    group .node id (forceItems c.paint false r ++ textItems labels id)
  let reverseForces := g.deaccelerators.zipIdx.flatMap fun (r, i) =>
    let id := "de" ++ toString i
    group .node id (forceItems c.paint true r ++ textItems labels id)
  let annotations := g.annotations.zipIdx.flatMap fun (p, i) =>
    let id := "an" ++ toString i
    group .node id (annotationItems c.paint cell p ++ textItems labels id)
  let boxed := if input.box.isSome && !(boxedAnnotations (labels.map (·.measured))).isEmpty then
    group .node "ab" ([.rect box { style := "note" }] ++ textItems labels "ab") else []
  return group .decor "" (decorItems g.plot input) ++ edges.flatten ++
    group .node "plot" (textItems labels "plot") ++ pipelines ++ nodes ++ ghosts ++ forces ++
    reverseForces ++ annotations ++ boxed

def routeGeometry (g : Geometry) (r : ModelRoute) : Except LayoutError Route := do
  let a ← endpoint g r.fromId
  let b ← endpoint g r.toId
  XY.checkMagnitude [a.x, a.y, b.x, b.y]
  return {
    id := r.id
    fromId := r.fromId
    toId := r.toId
    orthogonal := r.orthogonal
    points := [a, b] }

/-- Assemble geometry without changing model-stage containment, exclusivity, or edge metadata. -/
def layoutWith (c : Constants) (input : Input) (m : Model) : Except LayoutError Scene := do
  let cell := m.profile == .cell
  let g := arrange c.geometry input
  let measured ← measureLabels c.fonts cell m.labels m.options.fontFamily
  let (annotationBox, labels) ← placeLabels c.labels cell input g m.routes measured
  let boxes ← m.boxes.mapM fun b => do
    let rect ← boxRect g annotationBox b.id
    XY.checkRect rect
    return { id := b.id, role := b.role.id, rect, parent := b.parent, exclusive := b.exclusive : Box }
  let routes ← m.routes.mapM (routeGeometry g)
  let canvas := labels.foldl (fun size l => if l.shown then
      ⟨max size.w (l.rect.x + l.rect.w), max size.h (l.rect.y + l.rect.h)⟩ else size) g.canvas
  let canvas := if input.box.isSome && !(boxedAnnotations measured).isEmpty then
      ⟨max canvas.w (annotationBox.x + annotationBox.w), max canvas.h (annotationBox.y + annotationBox.h)⟩
    else canvas
  XY.checkMagnitude [canvas.w, canvas.h]
  labels.forM fun l => XY.checkRect l.rect
  let items ← groups c cell input g annotationBox labels m.routes
  return {
    kind := "wardley"
    profile := m.profile
    options := { m.options with direction := .TB }
    canvas := canvas
    boxes := boxes
    routes := routes
    labels := labels.map PlacedLabel.dump
    items := items }

end Elegant.Chart.Wardley

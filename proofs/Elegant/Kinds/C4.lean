import Elegant.Kinds.Common
import Elegant.Layered.VisibilityRoute

set_option autoImplicit false

/-! C4 model adapter. Elements are plain nodes sized from their text by the family, boundaries
are groups, and every relation is a route of minimum length one. After the family layout the
adapter does what the Go adapter does: the directional relations (`Rel_Up`, `Rel_Down`,
`Rel_Left`, `Rel_Right`, carried by the dump as `from_side` and `to_side`) are re-routed on the
visibility grid between the pinned ports (`RerouteEndpoints`), the cell canvas grows by one
cell on the right or the bottom when a re-routed point lies on its edge, and the person and
database outlines replace the plain frame of their node (`c4ShapeScene`). The re-routed dump
is accepted only when the validator accepts it. -/

namespace Elegant
namespace Kinds
namespace C4

open Common

def input (m : Model) : Layered.Input :=
  { kind := m.kind
    boxes := m.boxes
    routes := m.routes
    texts := m.boxes.map (boxText m)
    edges := m.routes.map (edgeOptions 1)
    labels := m.labels }

/-! ### Endpoint sides

A pinned side fixes a port of the box and the stub tip one unit outside it. The route is the
shortest grid path between the tips (or between every port of a free end), framed by the two
stubs. Every exclusive box that is not an ancestor of an endpoint and every text box of the
scene is an obstacle. -/

def stubOf (rect : Rect) (index : Nat) (dx dy : Int) : Option (Point × Point) :=
  (Layered.Visibility.ports rect)[index]?.map fun p => (p, ⟨p.x + dx, p.y + dy⟩)

def stub (rect : Rect) : Side → Option (Point × Point)
  | .none => none
  | .left => stubOf rect 0 (-1) 0
  | .right => stubOf rect 1 1 0
  | .top => stubOf rect 2 0 (-1)
  | .bottom => stubOf rect 3 0 1

def searchPoints (rect : Rect) : Option (Point × Point) → List Point
  | none => Layered.Visibility.ports rect
  | some (_, tip) => [tip]

def stubClear (grid : Layered.Visibility.Grid) : Option (Point × Point) → Bool
  | none => true
  | some (port, tip) => grid.clear port tip

def forcedRoute (obstacles : List Rect) (bound source target : Rect) (fromSide toSide : Side) :
    Except LayoutError (List Point) :=
  let first := stub source fromSide
  let last := stub target toSide
  let starts := searchPoints source first
  let ends := searchPoints target last
  let grid := Layered.Visibility.newGrid obstacles (starts ++ ends) (some bound)
  if !(stubClear grid first && stubClear grid last) then .error .domain
  else
    match grid.shortest starts ends with
    | none => .error .domain
    | some points => .ok ((first.map (·.1)).toList ++ points ++ (last.map (·.1)).toList)

def forced (r : ModelRoute) : Bool := r.fromSide != .none || r.toSide != .none

def ancestors (boxes : List ModelBox) : Nat → String → List String
  | 0, _ => []
  | fuel + 1, id =>
    match boxes.find? (·.id == id) with
    | none => []
    | some b => if b.parent == "" then [] else b.parent :: ancestors boxes fuel b.parent

def obstacleRects (m : Model) (s : Scene) (r : ModelRoute) : Except LayoutError (List Rect) :=
  let hidden := ancestors m.boxes 64 r.fromId ++ ancestors m.boxes 64 r.toId
  (m.boxes.filter fun b => b.exclusive && !hidden.contains b.id).mapM fun b =>
    match s.boxes.find? (·.id == b.id) with
    | some box => .ok box.rect
    | none => .error .domain

def textRects (s : Scene) : List Rect :=
  s.items.flatMap fun g => g.items.filterMap fun
    | .text t => some t.rect
    | _ => none

def sideAxis (a b : Point) : MarkerAxis :=
  if b.x < a.x then .negativeX
  else if a.x < b.x then .positiveX
  else if b.y < a.y then .negativeY
  else .positiveY

def markerEnds (edge : Layered.EdgeOptions) (points : List Point) (index : Nat) :
    Option (Point × Point) :=
  if index = 0 ∧ edge.markerStart ≠ "" then
    match points with
    | a :: b :: _ => some (b, a)
    | _ => none
  else
    match points.reverse with
    | b :: a :: _ => some (a, b)
    | _ => none

def rerouteItems (edge : Layered.EdgeOptions) (points : List Point) (items : List Primitive) :
    Except LayoutError (List Primitive) := do
  let (_, out) ← items.foldlM
    (fun (acc : Nat × List Primitive) item =>
      match item with
      | .polyline _ corner paint => pure (acc.1, acc.2 ++ [.polyline points corner paint])
      | .markerRef name _ _ =>
        match markerEnds edge points acc.1 with
        | some (a, b) => pure (acc.1 + 1, acc.2 ++ [.markerRef name b (sideAxis a b)])
        | none => throw .domain
      | other => pure (acc.1, acc.2 ++ [other]))
    (0, [])
  pure out

def rerouteOne (m : Model) (r : ModelRoute) (s : Scene) : Except LayoutError Scene := do
  let some source := s.boxes.find? (·.id == r.fromId) | throw .domain
  let some target := s.boxes.find? (·.id == r.toId) | throw .domain
  let obstacles ← obstacleRects m s r
  let bound : Rect := ⟨0, 0, s.canvas.w, s.canvas.h⟩
  let points ← forcedRoute (obstacles ++ textRects s) bound source.rect target.rect
    r.fromSide r.toSide
  let items ← s.items.mapM fun g =>
    if g.role == .edge && g.owner == r.id then do
      pure { g with items := ← rerouteItems (edgeOptions 1 r) points g.items }
    else pure g
  pure { s with
    routes := s.routes.map fun x => if x.id == r.id then { x with points := points } else x
    items := items }

def rerouteAll (m : Model) (s : Scene) : Except LayoutError Scene :=
  m.routes.foldlM (fun acc r => if forced r then rerouteOne m r acc else pure acc) s

def fitCanvas (s : Scene) : Except LayoutError Scene :=
  if s.profile = .cell then do
    let points := s.routes.flatMap (·.points)
    let w ← Measure.checkedI32 (points.foldl (fun w p => max w (p.x + 1)) s.canvas.w)
    let h ← Measure.checkedI32 (points.foldl (fun h p => max h (p.y + 1)) s.canvas.h)
    pure { s with canvas := ⟨w, h⟩ }
  else pure s

def checked (s : Scene) : Except LayoutError Scene :=
  if Validator.check s.layoutDump = true then pure s else throw .domain

def rerouteEndpoints (m : Model) (s : Scene) : Except LayoutError Scene :=
  if m.routes.any forced then rerouteAll m s >>= fitCanvas >>= checked else pure s

theorem checked_valid {s s' : Scene} (h : checked s = .ok s') :
    Validator.check s'.layoutDump = true := by
  unfold checked at h
  split at h
  · rename_i hc
    cases h
    exact hc
  · cases h

theorem rerouteEndpoints_valid {m : Model} {s s' : Scene} (h : rerouteEndpoints m s = .ok s')
    (hs : Validator.check s.layoutDump = true) : Validator.check s'.layoutDump = true := by
  unfold rerouteEndpoints at h
  cases hb : m.routes.any forced with
  | false =>
    simp only [hb] at h
    cases h
    exact hs
  | true =>
    simp only [hb, ite_true] at h
    cases hr : rerouteAll m s with
    | error e => simp [hr, bind, Except.bind] at h
    | ok routed =>
      cases hf : fitCanvas routed with
      | error e => simp [hr, hf, bind, Except.bind] at h
      | ok fit =>
        simp only [hr, hf, bind, Except.bind] at h
        exact checked_valid h

/-! ### Node outlines

`shapeScene` redraws the node groups of person and database elements as the Go adapter does:
the first frame item of the group is replaced by the outline, sized from the gap between the
top of the box and its first text line. The layout dump is not touched. -/

def plain : Paint := { style := "node" }

def textTopGap (items : List Primitive) (top : Int) : Int :=
  let gaps := items.filterMap fun
    | .text t => some (t.rect.y - top)
    | _ => none
  match gaps with
  | [] => 0
  | g :: rest => max 0 (rest.foldl min g)

def personOutline (profile : Profile) (rect : Rect) (gap : Int) :
    Except LayoutError (List Primitive) := do
  let w := rect.w
  let h := rect.h
  let r := max 0 (min (min (max 1024 (min (Int.tdiv (w * 23) 100) 3584)) (Int.tdiv w 2))
    (min (Int.tdiv h 2) (Int.tdiv gap 2)))
  let offset := Int.tdiv (r * 173) 100
  let bodyY ← Measure.checkedI32 (rect.y + offset)
  let bodyH ← Measure.checkedI32 (h - offset)
  let corner ← match profile with
    | .cell => pure 0
    | .vector => Measure.checkedI32 (min (Int.tdiv (w * 177) 1000) (Int.tdiv (bodyH * 45) 100))
  let cx ← Measure.checkedI32 (rect.x + Int.tdiv w 2)
  let cy ← Measure.checkedI32 (rect.y + r)
  let radius ← Measure.checkedI32 r
  pure [.roundRect ⟨rect.x, bodyY, w, bodyH⟩ corner plain, .ellipse cx cy radius radius plain]

def cylinderPath (rect : Rect) (radius : Int) : Except LayoutError Primitive := do
  let left := rect.x
  let top := rect.y
  let right := left + rect.w
  let bottom := top + rect.h
  let centre := left + Int.tdiv rect.w 2
  let dx := Int.tdiv (rect.w * 552) 2000
  let dy := Int.tdiv (radius * 552) 1000
  let raw : List (Int × Int) :=
    [(left, top + radius), (left, bottom - radius), (left, bottom - radius + dy),
     (centre - dx, bottom), (centre, bottom), (centre + dx, bottom),
     (right, bottom - radius + dy), (right, bottom - radius), (right, top + radius),
     (right, top + radius - dy), (centre + dx, top), (centre, top), (centre - dx, top),
     (left, top + radius - dy), (left, top + radius)]
  let points ← raw.mapM fun p => do
    pure (Point.mk (← Measure.checkedI32 p.1) (← Measure.checkedI32 p.2))
  match points with
  | [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14] =>
    pure (.path [.M p0, .L p1, .C p2 p3 p4, .C p5 p6 p7, .L p8, .C p9 p10 p11, .C p12 p13 p14, .Z]
      plain)
  | _ => throw .domain

def cylinderOutline (profile : Profile) (rect : Rect) (gap : Int) :
    Except LayoutError (List Primitive) := do
  let w := rect.w
  let r := max 0 (min (min (Int.tdiv (w * 1600) (8000 + w)) (Int.tdiv rect.h 4)) (Int.tdiv gap 2))
  let outer ← match profile with
    | .cell => pure (Primitive.roundRect rect 0 plain)
    | .vector => cylinderPath rect r
  let cx ← Measure.checkedI32 (rect.x + Int.tdiv w 2)
  let cy ← Measure.checkedI32 (rect.y + r)
  let rx ← Measure.checkedI32
    (match profile with
      | .cell => Int.tdiv (max (w - 1) 0) 2
      | .vector => Int.tdiv w 2)
  let ry ← Measure.checkedI32 r
  pure ([outer, .ellipse cx cy rx ry plain] ++
    match profile with
    | .cell => [.symbolRef "database" ⟨cx, rect.y⟩ "node"]
    | .vector => [])

def isFrame (rect : Rect) : Primitive → Bool
  | .rect r _ => r == rect
  | .roundRect r _ _ => r == rect
  | _ => false

def replaceFrame (rect : Rect) (shapes : List Primitive) : List Primitive → List Primitive
  | [] => []
  | item :: rest =>
    if isFrame rect item then shapes ++ rest else item :: replaceFrame rect shapes rest

def shapedGroup (profile : Profile) (shape : String) (rect : Rect) (g : Group) :
    Except LayoutError Group :=
  let gap := textTopGap g.items rect.y
  match shape with
  | "person" => do
    let shapes ← personOutline profile rect gap
    pure { g with items := replaceFrame rect shapes g.items }
  | "cyl" => do
    let shapes ← cylinderOutline profile rect gap
    pure { g with items := replaceFrame rect shapes g.items }
  | _ => pure g

def shapeScene (m : Model) (s : Scene) : Except LayoutError Scene := do
  let items ← s.items.mapM fun g =>
    if g.role != .node then pure g
    else
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

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match Layered.layoutFamily (input m) m.options with
  | .error e => .error e
  | .ok result =>
    match rerouteEndpoints m result.scene with
    | .error e => .error (.geometry e)
    | .ok routed =>
      match shapeScene m routed with
      | .error e => .error (.geometry e)
      | .ok shaped => .ok { result with scene := shaped.projectCellAttachments (routeMarkers m) }

/-- C4 validity reduces to the family's: the adapter re-routes the pinned relations only when
the validator accepts the result, redraws node outlines, and projects cell attachments, and
neither of the last two touches the layout dump. -/
theorem layout_valid_of_family
    (hfam : ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
      Layered.layoutFamily inp o = .ok res → Validator.check res.scene.layoutDump = true)
    {m : Model} {r : Layered.FamilyResult} (h : layout m = .ok r) :
    Validator.check r.scene.layoutDump = true := by
  unfold layout at h
  cases hf : Layered.layoutFamily (input m) m.options with
  | error e => simp [hf] at h
  | ok res =>
    cases hr : rerouteEndpoints m res.scene with
    | error e => simp [hf, hr] at h
    | ok routed =>
      cases hs : shapeScene m routed with
      | error e => simp [hf, hr, hs] at h
      | ok shaped =>
        simp only [hf, hr, hs, Except.ok.injEq] at h
        subst h
        show Validator.check (shaped.projectCellAttachments (routeMarkers m)).layoutDump = true
        rw [Scene.projectCellAttachments_layoutDump, shapeScene_layoutDump hs]
        exact rerouteEndpoints_valid hr (hfam _ _ _ hf)

end C4
end Kinds
end Elegant

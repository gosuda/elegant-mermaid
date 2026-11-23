import Elegant.Scene
import Elegant.Measure
import Elegant.Layered.Pipeline

set_option autoImplicit false

/-! Lane-band pinning for the swimlane kind. The layered family lays the whole diagram out; this
pass then pins every top-level lane (a root group) to one band on the cross axis: x for `TB` and
`BT`, y for `LR` and `RL`. Bands are consecutive in lane order with no gap. A band is as thick as
the title band, two clearances (cluster padding plus routing gutter) and the content extent of its
boxes and of the routes with both ends in the lane, all read from the unpinned layout. Root nodes
share one band after the last lane, without title band or outer clearance. Every box, label,
route point and display-list primitive moves by its band's shift; a route between two lanes
moves each endpoint with its own lane (`Move.ends`), and a primitive coordinate equal to the
route's first or last point follows it. The frames are then stretched to their bands, the origin
is restored, labels that now meet a foreign frame or an unrelated node move to a strip past the
geometry, and the canvas grows along the cross axis. Mirrors `pinBands` of the Go swimlane layout. -/

namespace Elegant
namespace Layered
namespace LaneBands

inductive Axis where
  | x | y
  deriving DecidableEq, Repr

def Axis.ofDirection : Direction → Axis
  | .LR => .y
  | .RL => .y
  | .TB => .x
  | .BT => .x

def Axis.point : Axis → Point → Int
  | .x, p => p.x
  | .y, p => p.y

def Axis.withPoint : Axis → Point → Int → Point
  | .x, p, v => { p with x := v }
  | .y, p, v => { p with y := v }

def Axis.start : Axis → Rect → Int
  | .x, r => r.x
  | .y, r => r.y

def Axis.length : Axis → Rect → Int
  | .x, r => r.w
  | .y, r => r.h

def Axis.withStart : Axis → Rect → Int → Rect
  | .x, r, v => { r with x := v }
  | .y, r, v => { r with y := v }

def Axis.withLength : Axis → Rect → Int → Rect
  | .x, r, v => { r with w := v }
  | .y, r, v => { r with h := v }

def Axis.extent : Axis → Size → Int
  | .x, s => s.w
  | .y, s => s.h

def Axis.withExtent : Axis → Size → Int → Size
  | .x, s, v => { s with w := v }
  | .y, s, v => { s with h := v }

/-- The title band, the clearance on each side of a lane's content (padding plus gutter), and
the routing gutter alone. -/
structure Spacing where
  title : Int
  clear : Int
  slot : Int
  deriving Repr

def spacingOf (profile : Profile) : Except LayoutError Spacing :=
  let slot := LayoutConst.slot.get profile
  .ok ⟨LayoutConst.line_h.get profile, LayoutConst.cluster_pad.get profile + slot, slot⟩

/-- The least and greatest of a list of coordinates; `none` for the empty list. -/
def bounds : List Int → Option (Int × Int)
  | [] => none
  | v :: rest => some (rest.foldl min v, rest.foldl max v)

def laneOfAux (boxes : List ModelBox) : Nat → String → Option (String × Bool)
  | 0, _ => none
  | n + 1, current =>
    match boxes.find? (fun b => b.id == current) with
    | none => none
    | some b =>
      if b.parent == "" then some (current, b.role == .group)
      else laneOfAux boxes n b.parent

/-- The root of a box's parent chain, and whether that root is a group. -/
def laneOf (boxes : List ModelBox) (id : String) : Option (String × Bool) :=
  laneOfAux boxes (boxes.length + 1) id

def inLane (boxes : List ModelBox) (id lane : String) : Bool :=
  match laneOf boxes id with
  | some (found, isGroup) => isGroup && found == lane
  | none => false

structure Band where
  id : String
  members : List String
  shift : Int
  start : Int
  thickness : Int
  deriving Repr

/-- Cross-axis coordinates of the members' boxes and of the routes inside the lane. -/
def contentValues (boxes : List ModelBox) (s : Scene) (axis : Axis) (lane : String)
    (members : List String) : List Int :=
  members.flatMap (fun id =>
    match s.boxes.find? (fun b => b.id == id) with
    | none => []
    | some b => [axis.start b.rect, axis.start b.rect + axis.length b.rect]) ++
  s.routes.flatMap (fun r =>
    if inLane boxes r.fromId lane && inLane boxes r.toId lane then r.points.map axis.point
    else [])

def laneBand (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing) (lane : String)
    (start : Int) : Band :=
  let members := (boxes.filter fun b => inLane boxes b.id lane).map (·.id)
  let extent := (bounds (contentValues boxes s axis lane members)).getD (start, start)
  { id := lane, members := members, start := start
    thickness := sp.title + 2 * sp.clear + (extent.2 - extent.1)
    shift := start + sp.title + sp.clear - extent.1 }

def looseBand (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing)
    (loose : List String) (start : Int) : Band :=
  match bounds (contentValues boxes s axis "" loose) with
  | none => { id := "", members := loose, shift := 0, start := start, thickness := 0 }
  | some (lo, hi) =>
    { id := "", members := loose, start := start
      thickness := hi - lo
      shift := start + sp.clear - lo }

def layLanes (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing) :
    List String → Int → List Band
  | [], _ => []
  | lane :: rest, start =>
    let band := laneBand boxes s axis sp lane start
    band :: layLanes boxes s axis sp rest (start + band.thickness)

def firstLaneStart (s : Scene) (lanes : List String) (axis : Axis) : Int :=
  match bounds (lanes.filterMap fun lane =>
      (s.boxes.find? (fun b => b.id == lane)).map fun b => axis.start b.rect) with
  | none => 0
  | some (lo, _) => lo

def looseNodes (boxes : List ModelBox) : List String :=
  (boxes.filter fun b => b.parent == "" && b.role == .node).map (·.id)

def layBands (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing)
    (lanes : List String) : List Band :=
  let start := firstLaneStart s lanes axis
  let bands := layLanes boxes s axis sp lanes start
  let loose := looseNodes boxes
  if loose.isEmpty then bands
  else bands ++ [looseBand boxes s axis sp loose (start + (bands.map (·.thickness)).sum)]

structure RouteDelta where
  id : String
  fromDelta : Int
  toDelta : Int
  first : Int
  last : Int
  deriving Repr

inductive Move where
  | constant (delta : Int)
  | ends (route : RouteDelta)

def Move.offset : Move → Int → Int
  | .constant delta, _ => delta
  | .ends r, v => if v = r.first then r.fromDelta else if v = r.last then r.toDelta else 0

def Move.apply (m : Move) (v : Int) : Except LayoutError Int :=
  Measure.checkedI32 (v + m.offset v)

def routeMove (r : RouteDelta) : Move :=
  if r.fromDelta = r.toDelta then .constant r.fromDelta else .ends r

def Move.rect (m : Move) (axis : Axis) (r : Rect) : Except LayoutError Rect := do
  pure (axis.withStart r (← m.apply (axis.start r)))

def Move.point (m : Move) (axis : Axis) (p : Point) : Except LayoutError Point := do
  pure (axis.withPoint p (← m.apply (axis.point p)))

def Move.command (m : Move) (axis : Axis) : PathCommand → Except LayoutError PathCommand
  | .M p => do pure (.M (← m.point axis p))
  | .L p => do pure (.L (← m.point axis p))
  | .C c1 c2 p => do pure (.C (← m.point axis c1) (← m.point axis c2) (← m.point axis p))
  | .A c r a w => do pure (.A (← m.point axis c) r a w)
  | .Z => pure .Z

def Move.primitive (m : Move) (axis : Axis) : Primitive → Except LayoutError Primitive
  | .rect r p => do pure (.rect (← m.rect axis r) p)
  | .roundRect r radius p => do pure (.roundRect (← m.rect axis r) radius p)
  | .ellipse cx cy rx ry p => do
    match axis with
    | .x => pure (.ellipse (← m.apply cx) cy rx ry p)
    | .y => pure (.ellipse cx (← m.apply cy) rx ry p)
  | .polygon points p => do pure (.polygon (← points.mapM (m.point axis)) p)
  | .polyline points corner p => do pure (.polyline (← points.mapM (m.point axis)) corner p)
  | .path commands p => do pure (.path (← commands.mapM (m.command axis)) p)
  | .text t => do pure (.text { t with rect := ← m.rect axis t.rect })
  | .markerRef name pt axisName => do pure (.markerRef name (← m.point axis pt) axisName)
  | .symbolRef symbol pt style => do pure (.symbolRef symbol (← m.point axis pt) style)

structure Pin where
  axis : Axis
  boxes : List (String × Int)
  routes : List RouteDelta

def Pin.boxDelta (p : Pin) (id : String) : Int :=
  ((p.boxes.find? (fun e => e.1 == id)).map (·.2)).getD 0

def Pin.route (p : Pin) (id : String) : Option RouteDelta :=
  p.routes.find? (fun r => r.id == id)

def Pin.labelDelta (p : Pin) (owner : String) : Int :=
  match p.route owner with
  | none => p.boxDelta owner
  | some r => if r.fromDelta = r.toDelta then r.fromDelta else 0

def bandShift (bands : List Band) (id : String) : Int :=
  ((bands.find? (fun b => b.id == id || b.members.contains id)).map (·.shift)).getD 0

def buildPin (axis : Axis) (bands : List Band) (s : Scene) : Pin :=
  { axis := axis
    boxes := bands.flatMap fun b => (b.id, b.shift) :: b.members.map fun member => (member, b.shift)
    routes := s.routes.filterMap fun r =>
      match r.points.head?, r.points.getLast? with
      | some first, some last =>
        some ⟨r.id, bandShift bands r.fromId, bandShift bands r.toId, axis.point first,
          axis.point last⟩
      | _, _ => none }

def moveGroup (pin : Pin) (g : Group) : Except LayoutError Group := do
  let move := match g.role with
    | .edge =>
      match pin.route g.owner with
      | some d => routeMove d
      | none => Move.constant 0
    | _ => Move.constant (pin.boxDelta g.owner)
  pure { g with items := ← g.items.mapM (move.primitive pin.axis) }

def placeRect (axis : Axis) (start thickness : Int) (r : Rect) : Rect :=
  axis.withLength (axis.withStart r start) thickness

def placeItem (place : Rect → Rect) : Primitive → Primitive
  | .rect r p => .rect (place r) p
  | item => item

def replaceFrame (axis : Axis) (band : Band) (s : Scene) : Except LayoutError Scene :=
  match s.boxes.findIdx? (fun b => b.id == band.id) with
  | none => pure s
  | some index => do
    let start ← Measure.checkedI32 band.start
    let thickness ← Measure.checkedI32 band.thickness
    let place := placeRect axis start thickness
    let boxes := s.boxes.mapIdx fun j b => if j = index then { b with rect := place b.rect } else b
    let items :=
      match s.items.findIdx? (fun g => g.owner == band.id) with
      | none => s.items
      | some gi => s.items.mapIdx fun j g =>
          if j = gi then { g with items := g.items.map (placeItem place) } else g
    pure { s with boxes := boxes, items := items }

def applyPin (pin : Pin) (bands : List Band) (s : Scene) : Except LayoutError Scene := do
  let boxes ← s.boxes.mapM fun b => do
    pure { b with rect := ← (Move.constant (pin.boxDelta b.id)).rect pin.axis b.rect }
  let labels ← s.labels.mapM fun l => do
    pure { l with rect := ← (Move.constant (pin.labelDelta l.owner)).rect pin.axis l.rect }
  let routes ← s.routes.mapM fun r =>
    match pin.route r.id with
    | none => pure r
    | some d => do pure { r with points := ← r.points.mapM ((routeMove d).point pin.axis) }
  let items ← s.items.mapM (moveGroup pin)
  bands.foldlM (fun scene band => replaceFrame pin.axis band scene)
    { s with boxes := boxes, labels := labels, routes := routes, items := items }

def commandValues (axis : Axis) : PathCommand → List Int
  | .M p => [axis.point p]
  | .L p => [axis.point p]
  | .C c1 c2 p => [axis.point c1, axis.point c2, axis.point p]
  | .A c _ _ _ => [axis.point c]
  | .Z => []

def rectValues (axis : Axis) (r : Rect) : List Int :=
  [axis.start r, axis.start r + axis.length r]

def primitiveValues (axis : Axis) : Primitive → List Int
  | .rect r _ => rectValues axis r
  | .roundRect r _ _ => rectValues axis r
  | .ellipse cx cy _ _ _ => [match axis with | .x => cx | .y => cy]
  | .polygon points _ => points.map axis.point
  | .polyline points _ _ => points.map axis.point
  | .path commands _ => commands.flatMap (commandValues axis)
  | .text t => rectValues axis t.rect
  | .markerRef _ pt _ => [axis.point pt]
  | .symbolRef _ pt _ => [axis.point pt]

/-- Every cross-axis coordinate of the scene. Box and label rectangles contribute their far edge
only when `farEdges` is set; display-list rectangles always contribute both edges. -/
def geometryValues (axis : Axis) (farEdges : Bool) (s : Scene) : List Int :=
  let edges := fun (r : Rect) => if farEdges then rectValues axis r else [axis.start r]
  s.boxes.flatMap (fun b => edges b.rect) ++
  s.routes.flatMap (fun r => r.points.map axis.point) ++
  s.labels.flatMap (fun l => edges l.rect) ++
  s.items.flatMap (fun g => g.items.flatMap (primitiveValues axis))

def shiftAll (axis : Axis) (delta : Int) (s : Scene) : Except LayoutError Scene := do
  let move := Move.constant delta
  let boxes ← s.boxes.mapM fun b => do pure { b with rect := ← move.rect axis b.rect }
  let labels ← s.labels.mapM fun l => do pure { l with rect := ← move.rect axis l.rect }
  let routes ← s.routes.mapM fun r => do pure { r with points := ← r.points.mapM (move.point axis) }
  let items ← s.items.mapM fun g => do pure { g with items := ← g.items.mapM (move.primitive axis) }
  pure { s with boxes := boxes, labels := labels, routes := routes, items := items }

def restoreOrigin (axis : Axis) (s : Scene) : Except LayoutError Scene :=
  match bounds (geometryValues axis false s) with
  | none => pure s
  | some (lo, _) => if lo < 0 then shiftAll axis (-lo) s else pure s

def highest (axis : Axis) (s : Scene) : Int :=
  max 0 (((bounds (geometryValues axis true s)).map (·.2)).getD 0)

def meetsInterior (outer inner : Rect) : Bool :=
  decide (max outer.x inner.x < min (outer.x + outer.w) (inner.x + inner.w) ∧
    max outer.y inner.y < min (outer.y + outer.h) (inner.y + inner.h))

def strictlyInside (outer inner : Rect) : Bool :=
  decide (outer.x < inner.x ∧ inner.x + inner.w < outer.x + outer.w ∧
    outer.y < inner.y ∧ inner.y + inner.h < outer.y + outer.h)

def addAncestors (boxes : List Box) : Nat → String → List String → List String
  | 0, _, acc => acc
  | n + 1, id, acc =>
    match boxes.find? (fun b => b.id == id) with
    | none => acc
    | some b =>
      if acc.contains b.parent then acc else addAncestors boxes n b.parent (b.parent :: acc)

def ownerAncestors (s : Scene) (l : SceneLabel) : List String :=
  let fuel := s.boxes.length + 2
  match s.routes.find? (fun r => r.id == l.owner) with
  | some r => addAncestors s.boxes fuel r.toId (addAncestors s.boxes fuel r.fromId [])
  | none => addAncestors s.boxes fuel l.owner []

def overlapsForeignFrame (frame : Box) (label : Rect) : Bool :=
  frame.role == "group" && meetsInterior frame.rect label && !strictlyInside frame.rect label

def hitsUnrelatedNode (node : Box) (l : SceneLabel) (ancestors : List String) : Bool :=
  node.exclusive && node.id != l.owner && !ancestors.contains node.id &&
    meetsInterior node.rect l.rect

def needsRelocation (s : Scene) (l : SceneLabel) : Bool :=
  let ancestors := ownerAncestors s l
  s.boxes.any fun b => overlapsForeignFrame b l.rect || hitsUnrelatedNode b l ancestors

structure LabelRelocation where
  owner : String
  before : Rect
  after : Rect
  deriving DecidableEq, Repr

/-- One native scan: reserve the greatest checked end of the labels intersecting this candidate. -/
def bumpedStrip (axis : Axis) (gap : Int) (rect : Rect) :
    List LabelRelocation → Int → Except LayoutError Int
  | [], start => pure start
  | previous :: rest, start => do
    if meetsInterior rect previous.after then
      let next ← Measure.checkedI64
        (axis.start previous.after + axis.length previous.after + gap)
      bumpedStrip axis gap rect rest (max start next)
    else bumpedStrip axis gap rect rest start

/-- A touched rectangle lies wholly before the next candidate. Removing it makes the native
repeat-until-free search structurally terminating without a retry limit. -/
def vacantStrip (axis : Axis) (gap : Int) (rect : Rect) (remaining : List LabelRelocation) :
    Except LayoutError Rect :=
  if _hit : remaining.any (fun previous => meetsInterior rect previous.after) = true then do
    let next ← bumpedStrip axis gap rect remaining (axis.start rect)
    let next ← Measure.checkedI32 next
    vacantStrip axis gap (axis.withStart rect next)
      (remaining.filter fun previous => !meetsInterior rect previous.after)
  else pure rect
termination_by remaining.length
decreasing_by
  simp only [List.unattach_filter, List.unattach_attach]
  apply List.length_filter_lt_length_iff_exists.mpr
  obtain ⟨previous, member, overlap⟩ := List.any_eq_true.mp _hit
  exact ⟨previous, member, by simp [overlap]⟩

def vacantLabelStrip (axis : Axis) (strip gap : Int) (rect : Rect)
    (moved : List LabelRelocation) : Except LayoutError Rect :=
  if gap < 0 then throw .domain
  else vacantStrip axis gap (axis.withStart rect strip) moved

def moveOffendingLabels (axis : Axis) (strip gap : Int) (s : Scene) :
    List SceneLabel → List LabelRelocation →
      Except LayoutError (List SceneLabel × List LabelRelocation)
  | [], moved => pure ([], moved)
  | label :: rest, moved => do
    if needsRelocation s label then
      let rect ← vacantLabelStrip axis strip gap label.rect moved
      let (labels, moved) ← moveOffendingLabels axis strip gap s rest
        (moved ++ [⟨label.owner, label.rect, rect⟩])
      pure ({ label with rect := rect } :: labels, moved)
    else
      let (labels, moved) ← moveOffendingLabels axis strip gap s rest moved
      pure (label :: labels, moved)

def moveMatchingText (moved : List LabelRelocation) (owner : String) : Primitive → Primitive
  | .text text =>
    match moved.find? (fun change => change.owner == owner && change.before == text.rect) with
    | some change => .text { text with rect := change.after }
    | none => .text text
  | item => item

-- Equal rectangles alone do not identify a label's display-list text.
#guard
  let text : SceneText := {
    rect := ⟨2, 4, 3, 1⟩
    role := .label
    size := 1
    align := .start
    style := "label"
    lines := [[{ text := "Yes" }]] }
  let moved := [LabelRelocation.mk "edge-a" text.rect ⟨20, 4, 3, 1⟩]
  decide (moveMatchingText moved "edge-a" (.text text) =
    .text { text with rect := ⟨20, 4, 3, 1⟩ }) &&
  decide (moveMatchingText moved "edge-b" (.text text) = .text text)

/-- Place offenders in declaration order, preserving their rank positions. Text moves only
when both its owner and its original rectangle identify the relocated label. -/
def relocateLabels (axis : Axis) (strip gap : Int) (s : Scene) : Except LayoutError Scene := do
  let (labels, moved) ← moveOffendingLabels axis strip gap s s.labels []
  let items := s.items.map fun g =>
    { g with items := g.items.map (moveMatchingText moved g.owner) }
  pure { s with labels := labels, items := items }

#guard (vacantLabelStrip .x 20 1 ⟨0, 4, 2, 1⟩
    [⟨"a", ⟨0, 0, 0, 0⟩, ⟨20, 4, 3, 1⟩⟩,
     ⟨"b", ⟨0, 0, 0, 0⟩, ⟨24, 4, 2, 1⟩⟩]).toOption = some ⟨27, 4, 2, 1⟩
#guard (vacantLabelStrip .y 20 1 ⟨4, 0, 1, 2⟩
    [⟨"a", ⟨0, 0, 0, 0⟩, ⟨4, 20, 1, 3⟩⟩,
     ⟨"b", ⟨0, 0, 0, 0⟩, ⟨4, 24, 1, 2⟩⟩]).toOption = some ⟨4, 27, 1, 2⟩
#guard (vacantLabelStrip .x 20 1 ⟨0, 4, 2, 1⟩
    [⟨"a", ⟨0, 0, 0, 0⟩, ⟨20, 10, 3, 1⟩⟩]).toOption = some ⟨20, 4, 2, 1⟩
#guard match vacantLabelStrip .x (I32_MAX - 1) 1 ⟨0, 4, 3, 1⟩
    [⟨"a", ⟨0, 0, 0, 0⟩, ⟨I32_MAX - 1, 4, 2, 1⟩⟩] with
  | .error .overflow => true
  | _ => false

def growCanvas (axis : Axis) (canvas : Size) (s : Scene) : Except LayoutError Scene := do
  let grown ← Measure.checkedI32 (highest axis s)
  pure { s with canvas := axis.withExtent canvas (max (axis.extent canvas) grown) }

def lanesOf (boxes : List ModelBox) : List String :=
  (boxes.filter fun b => b.role == .group && b.parent == "").map (·.id)

def Axis.other : Axis → Axis
  | .x => .y
  | .y => .x

/-- Every bump preserves the starting lower bound and clears every rectangle touched by
the current candidate. The checked arithmetic cannot hide a required reservation. -/
theorem bumpedStrip_bounds {axis : Axis} {gap : Int} {rect : Rect}
    {moved : List LabelRelocation} {start next : Int}
    (h : bumpedStrip axis gap rect moved start = .ok next) :
    start ≤ next ∧ ∀ previous ∈ moved, meetsInterior rect previous.after = true →
      axis.start previous.after + axis.length previous.after + gap ≤ next := by
  induction moved generalizing start with
  | nil =>
    simp only [bumpedStrip, pure, Except.pure, Except.ok.injEq] at h
    subst next
    exact ⟨Int.le_refl _, by simp⟩
  | cons previous rest ih =>
    by_cases overlap : meetsInterior rect previous.after = true
    · simp only [bumpedStrip, overlap, ↓reduceIte] at h
      cases checked : Measure.checkedI64
          (axis.start previous.after + axis.length previous.after + gap) with
      | error error => simp [checked, bind, Except.bind] at h
      | ok bound =>
        have value := Measure.checkedI64_ok checked
        simp only [checked, bind, Except.bind] at h
        have bounds := ih h
        refine ⟨Int.le_trans (Int.le_max_left _ _) bounds.1, ?_⟩
        intro other member touched
        rcases List.mem_cons.mp member with same | member
        · subst other
          rw [← value]
          exact Int.le_trans (Int.le_max_right _ _) bounds.1
        · exact bounds.2 other member touched
    · simp only [bumpedStrip, overlap] at h
      have bounds := ih h
      refine ⟨bounds.1, ?_⟩
      intro other member touched
      rcases List.mem_cons.mp member with same | member
      · subst other
        exact False.elim (overlap touched)
      · exact bounds.2 other member touched

/-- A successful search moves only forward, keeps the rank interval and dimensions, and
has no interior overlap with any prior moved label. -/
theorem vacantStrip_spec {axis : Axis} {gap : Int} {rect result : Rect}
    {remaining : List LabelRelocation} (hgap : 0 ≤ gap)
    (h : vacantStrip axis gap rect remaining = .ok result) :
    axis.start rect ≤ axis.start result ∧
    axis.other.start result = axis.other.start rect ∧
    result.w = rect.w ∧ result.h = rect.h ∧
    ∀ previous ∈ remaining, meetsInterior result previous.after = false := by
  rw [vacantStrip] at h
  split at h
  · rename_i hit
    cases bumped : bumpedStrip axis gap rect remaining (axis.start rect) with
    | error error => simp [bumped, bind, Except.bind] at h
    | ok next =>
      cases checked : Measure.checkedI32 next with
      | error error => simp [bumped, checked, bind, Except.bind] at h
      | ok start =>
        have value := Measure.checkedI32_ok checked
        have bounds := bumpedStrip_bounds bumped
        simp only [bumped, checked, bind, Except.bind] at h
        have preserved := vacantStrip_spec hgap h
        have coordinates :
            axis.start (axis.withStart rect start) = start ∧
            axis.other.start (axis.withStart rect start) = axis.other.start rect ∧
            (axis.withStart rect start).w = rect.w ∧
            (axis.withStart rect start).h = rect.h := by
          cases axis <;> exact ⟨rfl, rfl, rfl, rfl⟩
        have forward : start ≤ axis.start result := by
          simpa only [coordinates.1] using preserved.1
        refine ⟨by omega, ?_, ?_, ?_, ?_⟩
        · exact preserved.2.1.trans coordinates.2.1
        · exact preserved.2.2.1.trans coordinates.2.2.1
        · exact preserved.2.2.2.1.trans coordinates.2.2.2
        · intro previous member
          by_cases touched : meetsInterior rect previous.after = true
          · have passed := bounds.2 previous member touched
            have clear : axis.start previous.after + axis.length previous.after ≤
                axis.start result := by omega
            cases axis <;> simp only [Axis.start, Axis.length] at clear
            all_goals
              simp only [meetsInterior, decide_eq_false_iff_not]
              omega
          · apply preserved.2.2.2.2 previous
            exact List.mem_filter.mpr ⟨member, by simp [touched]⟩
  · rename_i noHit
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst result
    refine ⟨Int.le_refl _, rfl, rfl, rfl, ?_⟩
    intro previous member
    apply Bool.eq_false_of_ne_true
    intro touched
    exact noHit (List.any_eq_true.mpr ⟨previous, member, touched⟩)
termination_by remaining.length
decreasing_by
  apply List.length_filter_lt_length_iff_exists.mpr
  have hit : remaining.any (fun previous => meetsInterior rect previous.after) = true :=
    by assumption
  obtain ⟨previous, member, overlap⟩ := List.any_eq_true.mp hit
  exact ⟨previous, member, by simp [overlap]⟩

/-- The public strip operation admits only nonnegative gaps and returns an unchanged rank
interval at or beyond the base strip, clear of every prior relocation. -/
theorem vacantLabelStrip_preserves_and_clears {axis : Axis} {strip gap : Int}
    {rect result : Rect} {moved : List LabelRelocation}
    (h : vacantLabelStrip axis strip gap rect moved = .ok result) :
    strip ≤ axis.start result ∧
    axis.other.start result = axis.other.start rect ∧
    result.w = rect.w ∧ result.h = rect.h ∧
    ∀ previous ∈ moved, meetsInterior result previous.after = false := by
  unfold vacantLabelStrip at h
  split at h
  · cases h
  · rename_i nonnegative
    have resultSpec := vacantStrip_spec (by omega) h
    cases axis <;>
      simpa only [Axis.start, Axis.other, Axis.withStart] using resultSpec

structure GridPoint where
  cross : Int
  rank : Int
  deriving BEq, Repr

def Axis.grid (axis : Axis) (p : Point) : GridPoint :=
  ⟨axis.point p, axis.other.point p⟩

def Axis.at (axis : Axis) (p : GridPoint) : Point :=
  match axis with
  | .x => ⟨p.cross, p.rank⟩
  | .y => ⟨p.rank, p.cross⟩

structure Obstacle where
  cross0 : Int
  cross1 : Int
  rank0 : Int
  rank1 : Int

def obstacleOf (axis : Axis) (r : Rect) : Obstacle :=
  ⟨axis.start r, axis.start r + axis.length r,
    axis.other.start r, axis.other.start r + axis.other.length r⟩

/-- Cell text occupies closed glyph coordinates, so its routing reservation extends one cell
on every side. These are wide grid coordinates, not narrowed scene coordinates. -/
def textObstacle (axis : Axis) (rect : Rect) : Obstacle :=
  let obstacle := obstacleOf axis rect
  ⟨obstacle.cross0 - 1, obstacle.cross1 + 1, obstacle.rank0 - 1, obstacle.rank1 + 1⟩

theorem textObstacle_contains_closed {axis : Axis} {rect : Rect} {point : GridPoint}
    (hcross : axis.start rect ≤ point.cross ∧
      point.cross ≤ axis.start rect + axis.length rect)
    (hrank : axis.other.start rect ≤ point.rank ∧
      point.rank ≤ axis.other.start rect + axis.other.length rect) :
    (textObstacle axis rect).cross0 < point.cross ∧
    point.cross < (textObstacle axis rect).cross1 ∧
    (textObstacle axis rect).rank0 < point.rank ∧
    point.rank < (textObstacle axis rect).rank1 := by
  simp only [textObstacle, obstacleOf]
  omega

def textObstacles (axis : Axis) (s : Scene) : List Obstacle :=
  if s.options.profile == .cell then
    s.items.flatMap fun group => group.items.filterMap fun item =>
      match item with
      | .text text =>
        if 0 < text.rect.w ∧ 0 < text.rect.h then some (textObstacle axis text.rect) else none
      | _ => none
  else []

def Obstacle.hits (o : Obstacle) (a b : GridPoint) : Bool :=
  (a.rank == b.rank && decide (o.rank0 < a.rank ∧ a.rank < o.rank1 ∧
    min a.cross b.cross < o.cross1 ∧ o.cross0 < max a.cross b.cross)) ||
  (a.cross == b.cross && decide (o.cross0 < a.cross ∧ a.cross < o.cross1 ∧
    min a.rank b.rank < o.rank1 ∧ o.rank0 < max a.rank b.rank))

-- The top and left glyph boundaries used to be legal open-interior route lines.
#guard (textObstacle .x ⟨3, 4, 5, 1⟩).hits ⟨0, 4⟩ ⟨10, 4⟩
#guard (textObstacle .x ⟨3, 4, 5, 1⟩).hits ⟨3, 0⟩ ⟨3, 8⟩

structure RouteGrid where
  cross : Array Int
  rank : Array Int
  obstacles : List Obstacle

def sortedCoordinates (xs : List Int) : Array Int :=
  ((xs.mergeSort (fun a b => decide (a ≤ b))).eraseDups).toArray

def routeGrid (obs : List Obstacle) (inflate : Int) (entry exit : GridPoint) : RouteGrid :=
  ⟨sortedCoordinates ([entry.cross, exit.cross] ++ obs.flatMap (fun o =>
      [o.cross0 - inflate, o.cross1 + inflate])),
    sortedCoordinates ([entry.rank, exit.rank] ++ obs.flatMap (fun o =>
      [o.rank0 - inflate, o.rank1 + inflate])), obs⟩

def RouteGrid.vertex (g : RouteGrid) (p : GridPoint) : Nat :=
  (g.cross.toList.takeWhile (fun v => decide (v < p.cross))).length * g.rank.size +
    (g.rank.toList.takeWhile (fun v => decide (v < p.rank))).length

def RouteGrid.point (g : RouteGrid) (v : Nat) : GridPoint :=
  ⟨g.cross[v / g.rank.size]?.getD 0, g.rank[v % g.rank.size]?.getD 0⟩

def RouteGrid.neighbour (g : RouteGrid) (v move : Nat) : Option Nat := do
  let i := v / g.rank.size
  let j := v % g.rank.size
  let (i, j) ← match move with
    | 0 => some (i + 1, j)
    | 1 => if i = 0 then none else some (i - 1, j)
    | 2 => some (i, j + 1)
    | _ => if j = 0 then none else some (i, j - 1)
  if decide (i < g.cross.size ∧ j < g.rank.size) then some (i * g.rank.size + j) else none

def RouteGrid.free (g : RouteGrid) (a b : GridPoint) : Bool :=
  !(g.obstacles.any (fun o => o.hits a b))

structure SearchNode where
  state : Nat
  cost : Int
  path : List Nat

structure RouteSearch where
  queue : List SearchNode
  best : Option SearchNode

def turnCost (bend : Int) (a b : Nat) : Int := if a = b then 0 else bend

def heuristic (g : RouteGrid) (goal v : Nat) : Int :=
  let p := g.point v
  let q := g.point goal
  (p.cross - q.cross).natAbs + (p.rank - q.rank).natAbs

def queueLe (g : RouteGrid) (goal : Nat) (a b : SearchNode) : Bool :=
  let pa := a.cost + heuristic g goal (a.state / 4)
  let pb := b.cost + heuristic g goal (b.state / 4)
  decide (pa < pb ∨ (pa = pb ∧ a.state ≤ b.state))

def relaxNode (g : RouteGrid) (bend : Int) (remaining : List Nat) (node : SearchNode)
    (queue : List SearchNode) (move : Nat) : List SearchNode :=
  if move = (node.state % 4 ^^^ 1) then queue
  else match g.neighbour (node.state / 4) move with
  | none => queue
  | some v =>
    let state := v * 4 + move
    let a := g.point (node.state / 4)
    let b := g.point v
    let cost := node.cost + (b.cross - a.cross).natAbs + (b.rank - a.rank).natAbs +
      turnCost bend (node.state % 4) move
    if !remaining.contains state || !g.free a b then queue
    else if queue.any (fun old => old.state == state && decide (old.cost ≤ cost)) then queue
    else { state := state, cost := cost, path := v :: node.path } ::
      queue.filter (fun old => old.state != state)

/-- Each expansion removes one directional grid state from `remaining`. Its length is the
structural search bound; there is no configurable cutoff or fuel-exhaustion result. -/
def searchGrid (g : RouteGrid) (goal endMove : Nat) (bend : Int)
    (remaining : List Nat) (search : RouteSearch) : Option SearchNode :=
  match (search.queue.mergeSort (queueLe g goal)) with
  | [] => search.best
  | node :: queue =>
    if search.best.any (fun best =>
        decide (node.cost + heuristic g goal (node.state / 4) ≥ best.cost)) then search.best
    else if h : node.state ∈ remaining then
      let rest := remaining.erase node.state
      let total := node.cost + turnCost bend (node.state % 4) endMove
      let best := if node.state / 4 == goal &&
          search.best.all (fun best => decide (total < best.cost))
        then some { node with cost := total } else search.best
      let next := [0, 1, 2, 3].foldl (relaxNode g bend rest node) queue
      searchGrid g goal endMove bend rest ⟨next, best⟩
    else search.best
termination_by remaining.length
decreasing_by
  simpa only [List.length_erase_of_mem h] using Nat.sub_lt (List.length_pos_of_mem h) (by decide : 0 < 1)

structure RouteEnds where
  source : Point
  target : Point
  entry : GridPoint
  exit : GridPoint
  startMove : Nat
  endMove : Nat

def outward (axis : Axis) (r : Rect) (rank : Int) : Int :=
  if 2 * rank ≥ 2 * axis.other.start r + axis.other.length r then 1 else -1

def shiftedPoint (axis : Axis) (delta : Int) (p : Point) : Except LayoutError Point := do
  pure (axis.withPoint p (← Measure.checkedI32 (axis.point p + delta)))

def routeEnds (axis : Axis) (sp : Spacing) (pin : Pin) (fromBox toBox : Box)
    (original : List Point) : Except LayoutError RouteEnds := do
  let source ← shiftedPoint axis (pin.boxDelta fromBox.id) (original.headD ⟨0, 0⟩)
  let target ← shiftedPoint axis (pin.boxDelta toBox.id) (original.getLast?.getD ⟨0, 0⟩)
  let s := axis.grid source
  let t := axis.grid target
  let leave := outward axis fromBox.rect s.rank
  let enter := outward axis toBox.rect t.rank
  pure ⟨source, target, ⟨s.cross, s.rank + leave * sp.slot⟩,
    ⟨t.cross, t.rank + enter * sp.slot⟩, if leave < 0 then 3 else 2,
    if enter < 0 then 2 else 3⟩

def simplifyPoints (points : List Point) : List Point :=
  (points.foldl (fun acc p =>
    if acc.head? == some p then acc
    else
      let rec trim : List Point → List Point
        | b :: a :: rest =>
          if (a.x == b.x && b.x == p.x) || (a.y == b.y && b.y == p.y)
          then trim (a :: rest) else b :: a :: rest
        | xs => xs
      p :: trim acc) []).reverse

def routePolyline (axis : Axis) (g : RouteGrid) (ends : RouteEnds)
    (path : List Nat) : Except LayoutError (List Point) := do
  let middle ← path.reverse.mapM fun v => do
    let p := g.point v
    pure (axis.at ⟨← Measure.checkedI32 p.cross, ← Measure.checkedI32 p.rank⟩)
  pure (simplifyPoints ([ends.source] ++ middle ++ [ends.target]))

def clearPolyline (g : RouteGrid) (axis : Axis) (points : List Point) : Bool :=
  (points.zip points.tail).all (fun (a, b) => g.free (axis.grid a) (axis.grid b))

def findRoute (axis : Axis) (ends : RouteEnds) (obs boxes : List Obstacle) (bend : Int) :
    List Int → Except LayoutError (List Point)
  | [] => .error .domain
  | inflate :: rest => do
    let g := routeGrid obs inflate ends.entry ends.exit
    let start := g.vertex ends.entry
    let goal := g.vertex ends.exit
    let found := searchGrid g goal ends.endMove bend
      (List.range (g.cross.size * g.rank.size * 4))
      ⟨[⟨start * 4 + ends.startMove, 0, [start]⟩], none⟩
    match found with
    | none => findRoute axis ends obs boxes bend rest
    | some node =>
      let points ← routePolyline axis g ends node.path
      let boxGrid := { g with obstacles := boxes }
      if clearPolyline boxGrid axis points then pure points
      else findRoute axis ends obs boxes bend rest

def replaceRouteItem (old points : List Point) : Primitive → Primitive
  | .polyline _ corner paint => .polyline points corner paint
  | .markerRef name pt axis =>
    if some pt = old.head? then .markerRef name (points.headD pt) axis
    else if some pt = old.getLast? then .markerRef name (points.getLast?.getD pt) axis
    else .markerRef name pt axis
  | item => item

def rerouteBands (axis : Axis) (sp : Spacing) (bend : Int) (bands : List Band)
    (pin : Pin) (original : List Route) (s : Scene) : Except LayoutError Scene := do
  let routes ← (s.routes.zip original).mapM fun (r, old) => do
    let band := fun id => bands.findIdx? (fun b => b.id == id || b.members.contains id)
    match band r.fromId, band r.toId, s.boxes.find? (·.id == r.fromId),
        s.boxes.find? (·.id == r.toId) with
    | some fi, some ti, some fb, some tb =>
      if fi == ti || old.points.length < 2 then pure r
      else
        let ends ← routeEnds axis sp pin fb tb old.points
        let boxes := (s.boxes.filter (fun b => b.exclusive && b.id != r.fromId &&
          b.id != r.toId)).map (fun b => obstacleOf axis b.rect)
        let obs := boxes ++ textObstacles axis s
        pure { r with points := ← findRoute axis ends obs boxes bend [sp.slot, 0] }
    | _, _, _, _ => pure r
  let items := s.items.map fun g =>
    match s.routes.find? (·.id == g.owner), routes.find? (·.id == g.owner) with
    | some old, some r =>
      if g.role == .edge then { g with items := g.items.map (replaceRouteItem old.points r.points) }
      else g
    | _, _ => g
  pure { s with routes := routes, items := items }

/-- Pin the top-level lanes of a laid-out scene to their cross-axis bands. A scene with no lane
is returned unchanged. -/
def pinBands (boxes : List ModelBox) (o : Options) (s : Scene) : Except LayoutError Scene := do
  let lanes := lanesOf boxes
  if lanes.isEmpty then pure s
  else
    let sp ← spacingOf o.profile
    let axis := Axis.ofDirection o.direction
    let bands := layBands boxes s axis sp lanes
    let pinned ← applyPin (buildPin axis bands s) bands s
    let routed ← rerouteBands axis sp (LayoutConst.rank_gap.get o.profile) bands
      (buildPin axis bands s) s.routes pinned
    let origin ← restoreOrigin axis routed
    let strip ← Measure.checkedI32 (highest axis origin + sp.slot)
    let relocated ← relocateLabels axis strip sp.slot origin
    growCanvas axis s.canvas relocated

/-- Consecutive bands: each starts where the previous one ends, the first at the given start. -/
def Tiled : Int → List Band → Prop
  | _, [] => True
  | start, b :: bs => b.start = start ∧ Tiled (start + b.thickness) bs

theorem foldl_min_le (rest : List Int) (v : Int) : rest.foldl min v ≤ v := by
  induction rest generalizing v with
  | nil => exact Int.le_refl v
  | cons a rest ih => exact Int.le_trans (ih (min v a)) (by omega)

theorem le_foldl_max (rest : List Int) (v : Int) : v ≤ rest.foldl max v := by
  induction rest generalizing v with
  | nil => exact Int.le_refl v
  | cons a rest ih => exact Int.le_trans (by omega) (ih (max v a))

theorem bounds_le {vs : List Int} {lo hi : Int} (h : bounds vs = some (lo, hi)) : lo ≤ hi := by
  cases vs with
  | nil => simp [bounds] at h
  | cons v rest =>
    simp only [bounds, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Int.le_trans (foldl_min_le rest v) (le_foldl_max rest v)

/-- A lane is never thinner than its title band and two clearances. -/
theorem laneBand_thickness_nonneg (boxes : List ModelBox) (s : Scene) (axis : Axis)
    (sp : Spacing) (lane : String) (start : Int) (ht : 0 ≤ sp.title) (hc : 0 ≤ sp.clear) :
    0 ≤ (laneBand boxes s axis sp lane start).thickness := by
  unfold laneBand
  cases hb : bounds (contentValues boxes s axis lane
      ((boxes.filter fun b => inLane boxes b.id lane).map (·.id))) with
  | none => simp only [hb, Option.getD_none]; omega
  | some p =>
    have := bounds_le (lo := p.1) (hi := p.2) (by simpa using hb)
    simp only [hb, Option.getD_some]
    omega

theorem layLanes_length (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing)
    (lanes : List String) (start : Int) :
    (layLanes boxes s axis sp lanes start).length = lanes.length := by
  induction lanes generalizing start with
  | nil => rfl
  | cons lane rest ih => simp [layLanes, ih]

theorem layLanes_tiled (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing)
    (lanes : List String) (start : Int) : Tiled start (layLanes boxes s axis sp lanes start) := by
  induction lanes generalizing start with
  | nil => trivial
  | cons lane rest ih => exact ⟨rfl, ih _⟩

theorem tiled_snoc {bs : List Band} {x : Band} {start : Int} (h : Tiled start bs)
    (hx : x.start = start + (bs.map (·.thickness)).sum) : Tiled start (bs ++ [x]) := by
  induction bs generalizing start with
  | nil => exact ⟨by simpa using hx, trivial⟩
  | cons b rest ih =>
    refine ⟨h.1, ih h.2 ?_⟩
    rw [hx]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem looseBand_start (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing)
    (loose : List String) (start : Int) :
    (looseBand boxes s axis sp loose start).start = start := by
  unfold looseBand
  split <;> rfl

/-- Lane bands, and the band of the root nodes after them, tile the cross axis from the least
lane start with no gap, in lane order. -/
theorem layBands_tiled (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing)
    (lanes : List String) :
    Tiled (firstLaneStart s lanes axis) (layBands boxes s axis sp lanes) := by
  unfold layBands
  by_cases hl : (looseNodes boxes).isEmpty = true
  · simp only [hl, ↓reduceIte]
    exact layLanes_tiled boxes s axis sp lanes _
  · simp only [hl, ↓reduceIte, Bool.false_eq_true]
    exact tiled_snoc (layLanes_tiled boxes s axis sp lanes _) (looseBand_start _ _ _ _ _ _)

theorem pinBands_no_lanes {boxes : List ModelBox} {o : Options} {s : Scene}
    (h : lanesOf boxes = []) : pinBands boxes o s = .ok s := by
  simp [pinBands, h]
  rfl

theorem relocateLabels_boxes {axis : Axis} {strip gap : Int} {s result : Scene}
    (h : relocateLabels axis strip gap s = .ok result) : result.boxes = s.boxes := by
  unfold relocateLabels at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    rfl

theorem relocateLabels_routes {axis : Axis} {strip gap : Int} {s result : Scene}
    (h : relocateLabels axis strip gap s = .ok result) : result.routes = s.routes := by
  unfold relocateLabels at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    rfl

theorem relocateLabels_canvas {axis : Axis} {strip gap : Int} {s result : Scene}
    (h : relocateLabels axis strip gap s = .ok result) : result.canvas = s.canvas := by
  unfold relocateLabels at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    rfl

theorem Move.apply_inI32 {m : Move} {v w : Int} (h : m.apply v = .ok w) : InI32 w := by
  unfold Move.apply Measure.checkedI32 at h
  split at h
  · cases h
    assumption
  · cases h

/-- The canvas never shrinks along the cross axis and encloses the geometry. -/
theorem growCanvas_covers {axis : Axis} {canvas : Size} {s s' : Scene}
    (h : growCanvas axis canvas s = .ok s') :
    axis.extent canvas ≤ axis.extent s'.canvas ∧ highest axis s ≤ axis.extent s'.canvas := by
  unfold growCanvas at h
  cases hc : Measure.checkedI32 (highest axis s) with
  | error e => simp [hc, Functor.map, Except.map] at h
  | ok grown =>
    have hg : grown = highest axis s := by
      unfold Measure.checkedI32 at hc
      split at hc
      · cases hc; rfl
      · cases hc
    simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    subst hg
    cases axis <;> simp [Axis.extent, Axis.withExtent] <;> omega

theorem checkedI32_ok {v w : Int} (h : Measure.checkedI32 v = .ok w) : w = v := by
  unfold Measure.checkedI32 at h
  split at h
  · cases h; rfl
  · cases h

/-- Frame replacement stretches the lane's own box over exactly its band. -/
theorem replaceFrame_places_lane {axis : Axis} {band : Band} {s s' : Scene}
    (h : replaceFrame axis band s = .ok s') (hb : ∃ b ∈ s.boxes, b.id = band.id) :
    ∃ b ∈ s'.boxes, b.id = band.id ∧ axis.start b.rect = band.start ∧
      axis.length b.rect = band.thickness := by
  unfold replaceFrame at h
  cases hf : s.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    obtain ⟨b, hbm, hid⟩ := hb
    have hnone := List.findIdx?_eq_none_iff.mp hf b hbm
    simp [hid] at hnone
  | some index =>
    obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    rw [hf] at h
    cases hs : Measure.checkedI32 band.start with
    | error e => simp [hs, bind, Except.bind] at h
    | ok start =>
      cases ht : Measure.checkedI32 band.thickness with
      | error e => simp [hs, ht, bind, Except.bind] at h
      | ok thickness =>
        have hs' := checkedI32_ok hs
        have ht' := checkedI32_ok ht
        simp only [hs, ht, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        subst hs'
        subst ht'
        refine ⟨_, List.getElem_mem (l := List.mapIdx _ s.boxes) (n := index) (by simpa using hi), ?_⟩
        simp only [List.getElem_mapIdx]
        refine ⟨by simpa using hp, ?_, ?_⟩ <;> cases axis <;> simp [placeRect, Axis.start,
          Axis.length, Axis.withStart, Axis.withLength]

/-- Pinning never shrinks the canvas along the cross axis. -/
theorem pinBands_canvas_grows {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hl : (lanesOf boxes).isEmpty = false) (h : pinBands boxes o s = .ok r) :
    (Axis.ofDirection o.direction).extent s.canvas ≤
      (Axis.ofDirection o.direction).extent r.canvas := by
  unfold pinBands at h
  simp only [hl, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · exact (growCanvas_covers h).1

end LaneBands
end Layered
end Elegant

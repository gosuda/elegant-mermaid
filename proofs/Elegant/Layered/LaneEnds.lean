import Elegant.Layered.LaneBands

set_option autoImplicit false

/-! Final lane-end attachment for the swimlane kind. `pinBands` mirrors the engines up to
canvas growth; `pinLanes` adds the final attachment. After the canvas grows, every route end
whose endpoint box is a lane frame and whose cross coordinate equals the old frame side is
slid along the cross axis to the matching new side, the route is simplified, and its
edge-group polyline and end markers are retargeted. -/

namespace Elegant
namespace Layered
namespace LaneBands

structure LaneFrame where
  id : String
  near : Int
  length : Int
  deriving Repr

def laneFrames (axis : Axis) (bands : List Band) (s : Scene) : List LaneFrame :=
  bands.filterMap fun b => (s.boxes.find? (·.id == b.id)).map fun box =>
    ⟨b.id, axis.start box.rect + b.shift - b.start, axis.length box.rect⟩

def attachEnd (axis : Axis) (frames : List LaneFrame) (boxes : List Box) (id : String)
    (p : Point) : Except LayoutError (Option Point) :=
  match frames.find? (·.id == id), boxes.find? (·.id == id) with
  | some f, some b =>
    let start := axis.start b.rect
    let lo := start + f.near
    if axis.point p = lo + f.length then do
      pure (some (axis.withPoint p (← Measure.checkedI32 (start + axis.length b.rect))))
    else if axis.point p = lo then pure (some (axis.withPoint p start))
    else pure none
  | _, _ => pure none

def attachRoute (axis : Axis) (frames : List LaneFrame) (boxes : List Box) (r : Route) :
    Except LayoutError Route :=
  match r.points.head?, r.points.getLast? with
  | some first, some last => do
    let head ← attachEnd axis frames boxes r.fromId first
    let tail ← attachEnd axis frames boxes r.toId last
    if head.isNone && tail.isNone then pure r
    else pure { r with points := simplifyPoints (head.toList ++ r.points ++ tail.toList) }
  | _, _ => pure r

def attachItem (old points : List Point) : Primitive → Primitive
  | .polyline _ corner paint => .polyline points corner paint
  | .markerRef name pt ax =>
    if some pt = old.head? then
      let a := points.headD pt
      .markerRef name a (PipelineImpl.markerAxis (points.getD 1 a) a)
    else if some pt = old.getLast? then
      let b := points.getLast?.getD pt
      .markerRef name b (PipelineImpl.markerAxis (points.getD (points.length - 2) b) b)
    else .markerRef name pt ax
  | item => item

def attachLaneEnds (axis : Axis) (frames : List LaneFrame) (s : Scene) :
    Except LayoutError Scene := do
  let routes ← s.routes.mapM (attachRoute axis frames s.boxes)
  let items := s.items.map fun g =>
    if g.role == .edge then
      match s.routes.find? (·.id == g.owner), routes.find? (·.id == g.owner) with
      | some old, some r =>
        if old.points = r.points then g else { g with items := g.items.map (attachItem old.points r.points) }
      | _, _ => g
    else g
  pure { s with routes := routes, items := items }

def pinLanes (boxes : List ModelBox) (o : Options) (s : Scene) : Except LayoutError Scene := do
  let pinned ← pinBands boxes o s
  let lanes := lanesOf boxes
  if lanes.isEmpty then pure pinned
  else
    let sp ← spacingOf o.profile
    let axis := Axis.ofDirection o.direction
    attachLaneEnds axis (laneFrames axis (layBands boxes s axis sp lanes) s) pinned

theorem pinLanes_no_lanes {boxes : List ModelBox} {o : Options} {s : Scene}
    (h : lanesOf boxes = []) : pinLanes boxes o s = .ok s := by
  have hp : pinBands boxes o s = .ok s := pinBands_no_lanes h
  unfold pinLanes
  simp only [hp, bind, Except.bind, h, List.isEmpty_nil, ↓reduceIte, pure, Except.pure]

end LaneBands
end Layered
end Elegant

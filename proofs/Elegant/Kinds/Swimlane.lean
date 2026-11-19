import Elegant.Kinds.Common
import Elegant.Layered.LaneEnds

set_option autoImplicit false

/-! Swimlane model adapter. The diagram is the flowchart language with one change: every
top-level subgraph is a lane cluster. The layered family lays the whole model out with the
flowchart sizes, labelled edges asking for the minimum length the dump gives; the lane-band pass
(`Layered.LaneBands.pinLanes`) then pins each lane to its cross-axis band, as the Go swimlane
layout does, before the one cell projection of the adapter. -/

namespace Elegant
namespace Kinds
namespace Swimlane

open Common

def input (m : Model) : Layered.Input :=
  { kind := m.kind
    boxes := m.boxes
    routes := m.routes
    texts := m.boxes.map (boxText m)
    edges := m.routes.map fun r => edgeOptions (max r.minLength 1) r
    labels := m.labels }

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match Layered.layoutFamily (input m) m.options with
  | .error e => .error e
  | .ok result =>
    match Layered.LaneBands.pinLanes m.boxes m.options result.scene with
    | .error e => .error (.geometry e)
    | .ok scene =>
      .ok { result with scene := scene.projectCellAttachments (routeMarkers m) }

/-- The dump of a swimlane layout is the dump of the attached pinned family scene: the
adapter's cell projection only changes the display list. -/
theorem layout_dump {m : Model} {r : Layered.FamilyResult} (h : layout m = .ok r) :
    ∃ base : Layered.FamilyResult, ∃ pinned : Scene,
      Layered.layoutFamily (input m) m.options = .ok base ∧
      Layered.LaneBands.pinLanes m.boxes m.options base.scene = .ok pinned ∧
      r.scene.layoutDump = pinned.layoutDump := by
  unfold layout at h
  cases hf : Layered.layoutFamily (input m) m.options with
  | error e => simp [hf] at h
  | ok base =>
    cases hp : Layered.LaneBands.pinLanes m.boxes m.options base.scene with
    | error e => simp [hf, hp] at h
    | ok pinned =>
      simp only [hf, hp] at h
      cases h
      exact ⟨base, pinned, rfl, hp, Scene.projectCellAttachments_layoutDump _ _⟩

/-- A diagram with no top-level lane is the plain layered layout. -/
theorem layout_no_lanes {m : Model} (h : Layered.LaneBands.lanesOf m.boxes = []) :
    layout m = (Layered.layoutFamily (input m) m.options).map fun result =>
      { result with scene := result.scene.projectCellAttachments (routeMarkers m) } := by
  unfold layout
  cases hf : Layered.layoutFamily (input m) m.options with
  | error e => rfl
  | ok base => simp [Layered.LaneBands.pinLanes_no_lanes h, Except.map]

end Swimlane
end Kinds
end Elegant

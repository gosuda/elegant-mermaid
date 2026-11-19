import Elegant.Kinds.Common
import Elegant.Layered.LaneEnds
import Elegant.Layered.LayeredAdmission

set_option autoImplicit false

/-! Swimlane model adapter. The diagram is the flowchart language with one change: every
top-level subgraph is a lane cluster. The layered family lays the whole model out with the
flowchart sizes, labelled edges asking for the minimum length the dump gives; the lane-band pass
(`Layered.LaneBands.pinLanes`) then pins each lane to its cross-axis band, as the Go swimlane
layout does, before the one cell projection of the adapter.

Admission guards (parity-neutral on real inputs; both answer
`.error (.geometry .domain)`): `nestedInLaneB` rejects a model whose nested boxes do
not all sit in some lane (`NestedInLane`, proved in `SwimlaneValidSeams`);
`Layered.admit` rejects an input with an empty box id, a box id equal to a route id,
a non-exclusive fixed-size box, or a nonpositive fixed size (`layeredAdmissibleB`).

`layout_nested` / `layout_admissible` recover both guard facts from a successful layout;
`layout_dump` exposes the executed family run and pin; `layout_no_lanes` is the plain
layered layout when there are no lanes and both guards pass. -/

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

/-- Executable lane admission: every nested box sits in some lane. This is the
`Bool` mirror of `Layered.LaneBands.NestedInLane` (see `nestedInLaneB_spec` in
`SwimlaneValidSeams`); a top-level box needs no lane. -/
def nestedInLaneB (boxes : List ModelBox) : Bool :=
  boxes.all fun b => b.parent == "" ||
    (Layered.LaneBands.lanesOf boxes).any fun lane =>
      Layered.LaneBands.inLane boxes b.id lane

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match nestedInLaneB m.boxes with
  | true =>
    match Layered.admit (input m) (Layered.layoutFamily (input m) m.options) with
    | .error e => .error e
    | .ok base =>
      match Layered.LaneBands.pinLanes m.boxes m.options base.scene with
      | .error e => .error (.geometry e)
      | .ok scene =>
        .ok { base with scene := scene.projectCellAttachments (routeMarkers m) }
  | false => .error (.geometry .domain)

/-- A successful layout passed lane admission. -/
theorem layout_nested {m : Model} {r : Layered.FamilyResult}
    (h : layout m = .ok r) : nestedInLaneB m.boxes = true := by
  unfold layout at h
  cases hb : nestedInLaneB m.boxes with
  | true => rfl
  | false => simp [hb] at h

/-- A successful layout passed the layered admission guard. -/
theorem layout_admissible {m : Model} {r : Layered.FamilyResult}
    (h : layout m = .ok r) : Layered.layeredAdmissibleB (input m) = true := by
  have hn := layout_nested h
  unfold layout at h
  simp only [hn] at h
  cases ha : Layered.admit (input m) (Layered.layoutFamily (input m) m.options) with
  | error e => simp [ha] at h
  | ok base => exact (Layered.admit_ok ha).1

/-- The dump of a swimlane layout is the dump of the attached pinned family scene: the
adapter's cell projection only changes the display list. -/
theorem layout_dump {m : Model} {r : Layered.FamilyResult} (h : layout m = .ok r) :
    ∃ base : Layered.FamilyResult, ∃ pinned : Scene,
      Layered.layoutFamily (input m) m.options = .ok base ∧
      Layered.LaneBands.pinLanes m.boxes m.options base.scene = .ok pinned ∧
      r.scene.layoutDump = pinned.layoutDump := by
  have hn := layout_nested h
  unfold layout at h
  simp only [hn] at h
  cases ha : Layered.admit (input m) (Layered.layoutFamily (input m) m.options) with
  | error e => simp [ha] at h
  | ok base =>
    simp only [ha] at h
    have hfam : Layered.layoutFamily (input m) m.options = .ok base :=
      (Layered.admit_ok ha).2
    cases hp : Layered.LaneBands.pinLanes m.boxes m.options base.scene with
    | error e => simp [hp] at h
    | ok pinned =>
      simp only [hp] at h
      cases h
      exact ⟨base, pinned, hfam, hp, Scene.projectCellAttachments_layoutDump _ _⟩

/-- A diagram with no top-level lane is the plain layered layout, once both
admission guards pass. -/
theorem layout_no_lanes {m : Model} (h : Layered.LaneBands.lanesOf m.boxes = [])
    (hn : nestedInLaneB m.boxes = true)
    (ha : Layered.layeredAdmissibleB (input m) = true) :
    layout m = (Layered.layoutFamily (input m) m.options).map fun result =>
      { result with scene := result.scene.projectCellAttachments (routeMarkers m) } := by
  have hadm : Layered.admit (input m) (Layered.layoutFamily (input m) m.options) =
      Layered.layoutFamily (input m) m.options := by
    unfold Layered.admit
    simp [ha]
  unfold layout
  simp only [hn, hadm]
  cases hf : Layered.layoutFamily (input m) m.options with
  | error e => rfl
  | ok base => simp [Layered.LaneBands.pinLanes_no_lanes h, Except.map]

end Swimlane
end Kinds
end Elegant

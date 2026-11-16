import Elegant.Kinds.Common
import Elegant.GridSimplify

set_option autoImplicit false

/-! Block model adapter. The grid family reads the model-stage dump directly (boxes, routes, labels
and the shape tokens of grid-67), so the adapter only projects the cell display list onto the
painted borders, as Go's `layout.Layout` does for every kind under the cell profile, and wraps the
scene as a family result. The block family has no iteration cap, so it never reports one. -/

namespace Elegant
namespace Kinds
namespace Block

open Common

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match _root_.Elegant.Grid.layout m with
  | .error e => .error (.geometry e)
  | .ok scene =>
    .ok { scene := scene.projectCellAttachments (routeMarkers m), budgetExhausted := false }

theorem layout_spec {m : Model} {r : Layered.FamilyResult} (h : layout m = .ok r) :
    ∃ s, _root_.Elegant.Grid.layout m = .ok s ∧
      r.scene.layoutDump = s.layoutDump ∧ r.budgetExhausted = false := by
  unfold layout at h
  cases hs : _root_.Elegant.Grid.layout m with
  | error e => simp [hs] at h
  | ok s =>
    simp only [hs, Except.ok.injEq] at h
    subst h
    exact ⟨s, rfl, Scene.projectCellAttachments_layoutDump _ _, rfl⟩

theorem layout_orthogonal {m : Model} {r : Layered.FamilyResult}
    (h : layout m = .ok r) : Validator.C4 r.scene.layoutDump := by
  obtain ⟨s, hs, hdump, _⟩ := layout_spec h
  rw [hdump]
  exact _root_.Elegant.Grid.layout_orthogonal hs

theorem layout_canvas {m : Model} {r : Layered.FamilyResult}
    (h : layout m = .ok r) : Validator.C1 r.scene.layoutDump := by
  obtain ⟨s, hs, hdump, _⟩ := layout_spec h
  rw [hdump]
  exact _root_.Elegant.Grid.layout_canvas hs

theorem layout_siblings {m : Model} {r : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok r) : Validator.C2 r.scene.layoutDump := by
  obtain ⟨s, hs, hdump, _⟩ := layout_spec h
  rw [hdump]
  exact _root_.Elegant.Grid.layout_siblings hwf hs

theorem layout_parent {m : Model} {r : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok r) : Validator.C3 r.scene.layoutDump := by
  obtain ⟨s, hs, hdump, _⟩ := layout_spec h
  rw [hdump]
  exact _root_.Elegant.Grid.layout_parent hwf hs

theorem layout_ports {m : Model} {r : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok r) : Validator.C5 r.scene.layoutDump := by
  obtain ⟨s, hs, hdump, _⟩ := layout_spec h
  rw [hdump]
  exact _root_.Elegant.Grid.layout_ports hwf hs

theorem layout_route_clearance {m : Model} {r : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok r) : Validator.C6 r.scene.layoutDump := by
  obtain ⟨s, hs, hdump, _⟩ := layout_spec h
  rw [hdump]
  exact _root_.Elegant.Grid.layout_route_clearance hwf hs

theorem layout_label_clearance {m : Model} {r : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok r) : Validator.C7 r.scene.layoutDump := by
  obtain ⟨s, hs, hdump, _⟩ := layout_spec h
  rw [hdump]
  exact _root_.Elegant.Grid.layout_label_clearance hwf hs

theorem layout_frame_clearance {m : Model} {r : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok r) : Validator.C8 r.scene.layoutDump := by
  obtain ⟨s, hs, hdump, _⟩ := layout_spec h
  rw [hdump]
  exact _root_.Elegant.Grid.layout_frame_clearance hwf hs

theorem block_valid {m : Model} {r : Layered.FamilyResult}
    (hwf : WellFormed m) (_hlimits : WithinLimits m) (h : layout m = .ok r) :
    HardConstraints r.scene.layoutDump :=
  ⟨layout_canvas h, layout_siblings hwf h, layout_parent hwf h,
    layout_orthogonal h, layout_ports hwf h, layout_route_clearance hwf h,
    layout_label_clearance hwf h, layout_frame_clearance hwf h⟩

end Block
end Kinds
end Elegant

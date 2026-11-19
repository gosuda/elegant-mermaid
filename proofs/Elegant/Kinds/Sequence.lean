import Elegant.Kinds.Common
import Elegant.SequenceValid

set_option autoImplicit false

/-! Sequence model adapter. The family reads the model-stage dump directly (boxes, routes, labels
and the event stream in `regions`), so the adapter only projects the cell display list onto the
painted borders, as Go's `layout.Layout` does for every kind under the cell profile, and wraps the
scene as a family result. The sequence family has no iteration cap, so it never reports one. -/

namespace Elegant
namespace Kinds
namespace Sequence

open Common

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match _root_.Elegant.Sequence.layout m with
  | .error e => .error (.geometry e)
  | .ok scene =>
    .ok { scene := scene.projectCellAttachments (routeMarkers m), budgetExhausted := false }

theorem layout_spec {m : Model} {r : Layered.FamilyResult} (h : layout m = .ok r) :
    ∃ s, _root_.Elegant.Sequence.layout m = .ok s ∧
      r.scene.layoutDump = s.layoutDump ∧ r.budgetExhausted = false := by
  unfold layout at h
  cases hs : _root_.Elegant.Sequence.layout m with
  | error e => simp [hs] at h
  | ok s =>
    simp only [hs, Except.ok.injEq] at h
    subst h
    exact ⟨s, rfl, Scene.projectCellAttachments_layoutDump _ _, rfl⟩

theorem layout_valid {m : Model} {r : Layered.FamilyResult} (hwf : WellFormed m)
    (hlim : WithinLimits m) (h : layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  obtain ⟨s, hs, hd, _⟩ := layout_spec h
  rw [hd]
  exact _root_.Elegant.Sequence.sequence_valid hwf hlim hs

end Sequence
end Kinds
end Elegant

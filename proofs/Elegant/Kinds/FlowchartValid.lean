import Elegant.Layered.FamilyAssembly
import Elegant.Kinds.Flowchart
import Elegant.Layered.InputFixedFit
import Elegant.Layered.BoxRouteIdsDisjoint
import ElegantGeometry.Validator

set_option autoImplicit false

/-! Flowchart validity from the layered family seams.

The adapter feeds the model boxes and routes verbatim to `Layered.layoutFamily`,
then only rewrites the display list: cell attachment projection and icon drawing.
Both rewrites preserve the layout dump, so a successful layout of a model with
nonempty box ids satisfies the hard constraints. -/

namespace Elegant
namespace Kinds

/-- The adapter's scene has the family's dump; only the display list differs. -/
theorem flowchart_layout_spec {m : Model} {r : Layered.FamilyResult}
    (h : Flowchart.layout m = .ok r) :
    ∃ res, Layered.layoutFamily (Flowchart.input m) m.options = .ok res ∧
      r.scene.layoutDump = res.scene.layoutDump := by
  unfold Flowchart.layout at h
  cases hf : Layered.layoutFamily (Flowchart.input m) m.options with
  | error e => simp [hf, bind, Except.bind] at h
  | ok res =>
    simp only [hf, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨res, rfl,
      (Flowchart.placeIcons_layoutDump _ _).trans
        (Scene.projectCellAttachments_layoutDump _ _)⟩

/-- Flowchart validity from the family seams: the adapter projects cell attachments
and draws icons, both display-only, so a successful layout of a model with nonempty
box ids satisfies the hard constraints. -/
theorem flowchart_valid_of_seams (S : Layered.PipelineImpl.LayeredSeams)
    {m : Model} {r : Layered.FamilyResult}
    (hids : ∀ b ∈ m.boxes, b.id ≠ "")
    (hdisj : Layered.PipelineImpl.BoxRouteIdsDisjoint (Flowchart.input m))
    (h : Flowchart.layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  obtain ⟨res, hf, hd⟩ := flowchart_layout_spec h
  rw [hd]
  exact Layered.PipelineImpl.layoutFamily_valid_of_seams S hids
    (Layered.PipelineImpl.inputFixedFit_of_nil (inp := Flowchart.input m) rfl)
    hdisj hf

end Kinds
end Elegant

import Elegant.Layered.FamilyAssembly
import Elegant.Kinds.Flowchart
import Elegant.Layered.LayeredAdmission
import Elegant.Layered.InputFixedFit
import Elegant.Layered.BoxRouteIdsDisjoint
import ElegantGeometry.Validator

set_option autoImplicit false
/-! Flowchart validity from the layered family seams.

The adapter feeds the model boxes and routes verbatim to `Layered.layoutFamily` under the
shared `Layered.admit` guard (empty box id, box id equal to a route id, non-exclusive
fixed-size box, or nonpositive fixed size answers `.error (.geometry .domain)`), then only
rewrites the display list: cell attachment projection and icon drawing. Both rewrites
preserve the layout dump. `flowchart_layout_spec` derives the guard (`layeredAdmissibleB`)
and the successful family run from `Flowchart.layout m = .ok r`; `flowchart_valid_of_seams`
derives nonempty box ids and route-id disjointness from the guard via
`layeredAdmissibleB_spec`, takes fixed-size room from `inputFixedFit_of_nil` (the adapter
builds no fixed sizes), and passes all three to `layoutFamily_valid_of_seams`. -/

namespace Elegant
namespace Kinds

/-- The adapter's scene has the family's dump; the guard and the family run behind a
successful layout. -/
theorem flowchart_layout_spec {m : Model} {r : Layered.FamilyResult}
    (h : Flowchart.layout m = .ok r) :
    ∃ res, Layered.layeredAdmissibleB (Flowchart.input m) = true ∧
      Layered.layoutFamily (Flowchart.input m) m.options = .ok res ∧
      r.scene.layoutDump = res.scene.layoutDump := by
  unfold Flowchart.layout at h
  cases ha : Layered.admit (Flowchart.input m)
      (Layered.layoutFamily (Flowchart.input m) m.options) with
  | error e => simp [ha, bind, Except.bind] at h
  | ok fam =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨hadm, hfam⟩ := Layered.admit_ok ha
    subst h
    exact ⟨fam, hadm, hfam,
      (Flowchart.placeIcons_layoutDump _ _).trans
        (Scene.projectCellAttachments_layoutDump _ _)⟩

/-- Flowchart validity from the family seams: the adapter projects cell attachments
and draws icons, both display-only, so a successful guarded layout satisfies the hard
constraints. The guard supplies nonempty box ids and route-id disjointness; fixed-size
room holds because the adapter builds no fixed sizes. -/
theorem flowchart_valid_of_seams (S : Layered.PipelineImpl.LayeredSeams)
    {m : Model} {r : Layered.FamilyResult}
    (h : Flowchart.layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  obtain ⟨res, hadm, hf, hd⟩ := flowchart_layout_spec h
  rw [hd]
  obtain ⟨hids, hdisj, _, _⟩ := Layered.layeredAdmissibleB_spec hadm m.options
  exact Layered.PipelineImpl.layoutFamily_valid_of_seams S hids
    (Layered.PipelineImpl.inputFixedFit_of_nil (inp := Flowchart.input m) rfl)
    hdisj hf
end Kinds
end Elegant

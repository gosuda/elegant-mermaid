import Elegant.Kinds.State
import Elegant.Kinds.UsecaseValidExact
import Elegant.Layered.ExactPipeline
import Elegant.Layered.FamilyAssemblyB
import Elegant.Layered.RegionReduction
import ElegantGeometry.Validator

set_option autoImplicit false

/-! State family validity through the exact pipeline.

When a state model has no concurrency regions and no side notes,
`Layered.state_reduces_exact` runs the region-and-note family entry
`Layered.layoutFamilyRN` as the exact family entry `Layered.layoutFamilyX`.
The exact entry is valid from the `Usecase.ExactSeams` record via
`Usecase.exactBaseSeams` and `layoutFamilyB_valid_of_seams`; the state theorem
below instantiates that bridge at the state exact ids
`((sizes m).map (·.1))` and concludes `Validator.check ... = true`, the form
`State.familyCheck` needs. -/

namespace Elegant
namespace Kinds
namespace State

/-- Family validity for any `layoutFamilyX exactIds` run from the exact seams:
`exactBaseSeams` builds the base seams for `layoutX exactIds`, and the
base-parametric family theorem assembles the hard constraints. This is the
general content reused from `usecase_family_valid_of_exactSeams`, restated over
an arbitrary exact-id list instead of the usecase actor ids. -/
theorem layoutFamilyX_valid_of_exactSeams {exactIds : List String}
    {inp : Layered.Input} {o : Options} {res : Layered.FamilyResult}
    (R : Usecase.ExactSeams exactIds)
    (hids : ∀ b ∈ inp.boxes, b.id ≠ "")
    (hfix : Layered.PipelineImpl.InputFixedFit inp o)
    (hdisj : Layered.PipelineImpl.BoxRouteIdsDisjoint inp)
    (h : Layered.layoutFamilyX exactIds inp o = .ok res) :
    HardConstraints res.scene.layoutDump := by
  simp only [Layered.layoutFamilyX] at h
  exact Layered.PipelineImpl.layoutFamilyB_valid_of_seams
    (Usecase.exactBaseSeams exactIds R) hids hfix hdisj h

/-- State family validity from the exact seams: for a model whose family run
reduces by `state_reduces_exact` (no regions, no notes), the executed
region-and-note run satisfies the validator check. The hypotheses are the
reduction premises (`hfam`/`hreg`/`hnotes`), the exact seam record `R` at the
state exact ids, and the model premises. -/
theorem state_family_valid_of_exactSeams {m : Model} {res : Layered.FamilyResult}
    (R : Usecase.ExactSeams ((sizes m).map (fun p => p.1)))
    (hids : ∀ b ∈ m.boxes, b.id ≠ "")
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (hfix : Layered.PipelineImpl.InputFixedFit (input m (sizes m)) m.options)
    (hdisj : Layered.PipelineImpl.BoxRouteIdsDisjoint (input m (sizes m)))
    (hfam : Layered.layoutFamilyRN ((sizes m).map (fun p => p.1)) m.regionSets
      (input m (sizes m)) m.options = .ok res)
    (hreg : Layered.RegionImpl.graphRegions (input m (sizes m)) m.regionSets
      = .ok [])
    (hnotes : Layered.PipelineImpl.attachmentsOf (input m (sizes m)).boxes = []) :
    Validator.check res.scene.layoutDump = true := by
  have _ := hwf
  have _ := hlim
  have hx : Layered.layoutFamilyX ((sizes m).map (fun p => p.1))
      (input m (sizes m)) m.options = .ok res :=
    Layered.state_reduces_exact _ _ _ _ _ hfam hreg hnotes
  have hboxes : (input m (sizes m)).boxes = m.boxes := rfl
  have hids' : ∀ b ∈ (input m (sizes m)).boxes, b.id ≠ "" := by
    rw [hboxes]
    exact hids
  have hc := layoutFamilyX_valid_of_exactSeams R hids' hfix hdisj hx
  exact (Validator.check_iff _).mpr hc

end State
end Kinds
end Elegant

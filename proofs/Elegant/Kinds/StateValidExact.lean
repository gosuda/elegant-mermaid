import Elegant.Kinds.State
import Elegant.Kinds.UsecaseValidExact
import Elegant.Layered.ExactPipeline
import Elegant.Layered.FamilyAssemblyB
import Elegant.Layered.LayeredAdmission
import Elegant.Layered.RegionReduction
import ElegantGeometry.Validator

set_option autoImplicit false

/-! State family validity through the exact pipeline.

When a state model has no concurrency regions and no side notes,
`Layered.state_reduces_exact` runs the region-and-note family entry
`Layered.layoutFamilyRN` as the exact family entry `Layered.layoutFamilyX`.
`Usecase.exactBaseSeams` and `layoutFamilyB_valid_of_seams` prove validity
for the exact family. The State theorem instantiates this result at the
pseudo-state ids and turns the hard constraints into a validator check.
`Layered.layeredAdmissibleB_spec` derives the id, fit, and disjointness premises
from the admission guard, which adapter callers recover via `admit_ok`. -/

namespace Elegant
namespace Kinds
namespace State

/-- Any admitted `layoutFamilyX` run satisfies the hard constraints. -/
theorem layoutFamilyX_valid {exactIds : List String}
    {inp : Layered.Input} {o : Options} {res : Layered.FamilyResult}
    (hadm : Layered.layeredAdmissibleB inp = true)
    (h : Layered.layoutFamilyX exactIds inp o = .ok res) :
    HardConstraints res.scene.layoutDump := by
  simp only [Layered.layoutFamilyX] at h
  obtain ⟨hids, hdisj, hfix, hpos⟩ := Layered.layeredAdmissibleB_spec hadm o
  exact Layered.PipelineImpl.layoutFamilyB_valid_of_seams
    (Usecase.exactBaseSeams exactIds) hids hfix hpos hdisj h

/-- When the region-and-note run reduces to the exact family (no regions and
no side notes), its layout dump passes the validator. -/
theorem state_family_valid_no_regions_no_notes {m : Model} {res : Layered.FamilyResult}
    (hadm : Layered.layeredAdmissibleB (input m (sizes m)) = true)
    (hwf : WellFormed m) (hlim : WithinLimits m)
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
  have hc := layoutFamilyX_valid hadm hx
  exact (Validator.check_iff _).mpr hc

end State
end Kinds
end Elegant

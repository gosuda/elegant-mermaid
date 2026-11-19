import Elegant.Kinds.State
import Elegant.Kinds.StateValid
import Elegant.Layered.LayeredAdmission
import Elegant.Layered.RegionNotesFamilyValid
import Elegant.Layered.RegionPipeline
import ElegantGeometry.Validator
set_option autoImplicit false

/-! State validity from the region-and-note seams.

The exact theorem `state_valid_of_exactSeams` needs no region sets and no side
notes; `state_valid_of_regionNotesSeams` is its counterpart at the general
`Layered.layoutFamilyRN` run: the seams record instantiates at the model's
region sets resolved by `graphRegions`, and the generic family theorem
`layoutFamilyRN_valid_of_seams` discharges the transfer premise of
`state_valid_of_family`, which transports `HardConstraints` along the
adapter's display-only steps. The id, disjointness, and fit premises are
derived from the adapter's admission guard (`layout_spec` plus
`Layered.layeredAdmissibleB_spec`), not assumed. -/

namespace Elegant
namespace Kinds
namespace State

/-- State validity from the region-and-note seams: for a model whose region
sets resolve to `idSets` by `graphRegions`, a successful adapter run satisfies
the hard constraints when the region-and-note seams hold. The premises mirror
`state_valid_of_exactSeams` (side premises, well-formedness, limits, and the
run success), replacing the exact-seam record by the region-and-note seams and
dropping the no-regions/no-notes reduction hypotheses; the id, disjointness,
and fit premises come from the admission guard. -/
theorem state_valid_of_regionNotesSeams {m : Model} {r : Layered.FamilyResult}
    {idSets : List (String × List String)}
    (S : Layered.PipelineImpl.RegionNotesSeams ((sizes m).map (·.1)) idSets)
    (hgraph : Layered.RegionImpl.graphRegions (input m (sizes m)) m.regionSets
      = .ok idSets)
    (_hwf : WellFormed m) (_hlim : WithinLimits m)
    (h : layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  apply state_valid_of_family h
  intro res hf
  obtain ⟨_, hadm, _, _⟩ := layout_spec h
  obtain ⟨hids, hdisj, hfix, _⟩ := Layered.layeredAdmissibleB_spec hadm m.options
  exact Layered.PipelineImpl.layoutFamilyRN_valid_of_seams S hgraph hids hfix hdisj hf

end State
end Kinds
end Elegant

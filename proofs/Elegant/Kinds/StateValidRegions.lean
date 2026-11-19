import Elegant.Kinds.State
import Elegant.Kinds.StateValid
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
adapter's display-only steps. -/

namespace Elegant
namespace Kinds
namespace State

/-- State validity from the region-and-note seams: for a model whose region
sets resolve to `idSets` by `graphRegions`, a successful adapter run satisfies
the hard constraints when the region-and-note seams hold. The premises mirror
`state_valid_of_exactSeams` (side premises, well-formedness, limits, id
nonemptiness, and the run success), replacing the exact-seam record by the
region-and-note seams and dropping the no-regions/no-notes reduction
hypotheses. -/
theorem state_valid_of_regionNotesSeams {m : Model} {r : Layered.FamilyResult}
    {idSets : List (String × List String)}
    (S : Layered.PipelineImpl.RegionNotesSeams ((sizes m).map (·.1)) idSets)
    (hgraph : Layered.RegionImpl.graphRegions (input m (sizes m)) m.regionSets
      = .ok idSets)
    (hids : ∀ b ∈ m.boxes, b.id ≠ "")
    (_hwf : WellFormed m) (_hlim : WithinLimits m)
    (hfix : Layered.PipelineImpl.InputFixedFit (input m (sizes m)) m.options)
    (hdisj : Layered.PipelineImpl.BoxRouteIdsDisjoint (input m (sizes m)))
    (h : layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  apply state_valid_of_family h
  intro res hf
  exact Layered.PipelineImpl.layoutFamilyRN_valid_of_seams S hgraph
    (by
      have hboxes : (input m (sizes m)).boxes = m.boxes := rfl
      rw [hboxes]
      exact hids) hfix hdisj hf

end State
end Kinds
end Elegant

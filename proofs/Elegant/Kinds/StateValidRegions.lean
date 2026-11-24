import Elegant.Kinds.State
import Elegant.Kinds.StateValid
import Elegant.Layered.LayeredAdmission
import Elegant.Layered.RegionNotesFamilyValid
import Elegant.Layered.RegionPipeline
import ElegantGeometry.Validator
set_option autoImplicit false

/-! State validity from the region-and-note seams.

The exact theorem `state_valid_no_regions_no_notes` needs no region sets and
no side notes; `state_valid_of_regionNotesSeams` covers the general
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
the hard constraints when the region-and-note seams hold. The id, disjointness,
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
  obtain ⟨hids, hdisj, hfix, hpos⟩ := Layered.layeredAdmissibleB_spec hadm m.options
  exact Layered.PipelineImpl.layoutFamilyRN_valid_of_seams S hgraph hids hfix hpos hdisj hf

private def endpointCycle (profile : Profile) : Model :=
  { kind := "state"
    profile := profile
    options := ({ profile := profile } : Options)
    boxes :=
      ([{ id := "G1", role := .group, exclusive := false },
        { id := "A", role := .group, parent := "G1", exclusive := false },
        { id := "B", role := .group, parent := "G1", exclusive := false },
        { id := "G2", role := .group, exclusive := false },
        { id := "C", role := .group, parent := "G2", exclusive := false },
        { id := "D", role := .group, parent := "G2", exclusive := false },
        { id := "a1", parent := "A", exclusive := false },
        { id := "b1", parent := "B", exclusive := false },
        { id := "c1", parent := "C", exclusive := false },
        { id := "d1", parent := "D", exclusive := false }] : List ModelBox)
    routes :=
      ([{ id := "e0", fromId := "G1", toId := "G2" },
        { id := "e1", fromId := "G2", toId := "G1" }] : List ModelRoute)
    regionSets :=
      ([{ parent := 0, regions := [1, 2] },
        { parent := 3, regions := [4, 5] }] : List ModelRegionSet) }

private def endpointCycleC5 (profile : Profile) : Bool :=
  match layout (endpointCycle profile) with
  | .ok result => Validator.c5 result.scene.layoutDump
  | .error _ => false

#guard modelWellFormed (endpointCycle .cell)
#guard decide (WithinLimits (endpointCycle .cell))
#guard endpointCycleC5 .cell
#guard modelWellFormed (endpointCycle .vector)
#guard decide (WithinLimits (endpointCycle .vector))
#guard endpointCycleC5 .vector

end State
end Kinds
end Elegant

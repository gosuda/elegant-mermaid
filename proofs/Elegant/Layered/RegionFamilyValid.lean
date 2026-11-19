import Elegant.Layered.RegionSeams

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Region family validity from the region seams: the executed `layoutFamilyR`
run over the resolved id sets satisfies the hard constraints. `hgraph` ties
the `RegionSeams` index to the `graphRegions` resolution of the model sets, so
`h` rewrites to a `layoutFamilyB` run at the reindexing base that
`regionBaseSeams` speaks about; the generic `layoutFamilyB_valid_of_seams`
lift supplies the rest. -/
theorem layoutFamilyR_valid_of_seams {exactIds : List String}
    {sets : List ModelRegionSet} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (R : RegionSeams exactIds idSets)
    (hgraph : RegionImpl.graphRegions inp sets = .ok idSets)
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "")
    (hfix : InputFixedFit inp o) (hdisj : BoxRouteIdsDisjoint inp)
    (h : Elegant.Layered.layoutFamilyR exactIds sets inp o = .ok res) :
    HardConstraints res.scene.layoutDump := by
  have hB : layoutFamilyB
      (fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o')
      inp o = .ok res := by
    have h2 := h
    simp only [Elegant.Layered.layoutFamilyR, hgraph] at h2
    exact h2
  exact layoutFamilyB_valid_of_seams (regionBaseSeams R) hids hfix hdisj hB

end PipelineImpl
end Layered
end Elegant

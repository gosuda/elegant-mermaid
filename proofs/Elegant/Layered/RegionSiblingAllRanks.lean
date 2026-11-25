import Elegant.Layered.RegionSiblingSameLayer
import Elegant.Layered.RegionDifferentLayerClearance

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

theorem componentRunR_region_siblings_disjoint {P : Params} {exactIds : List String}
    {s : RegionSpec} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {labels : List MeasuredLabel} {graph0 graph cg' : Graph}
    {comp : List Nat} {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hgraph : exactGraph P exactIds inp o labels graph0 = .ok graph)
    (hrun : componentRunR P (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) graph comp candidate) labels orderOptions = .ok (cg', run))
    {u v keyU keyV : Nat} {nu nv : Node} {bu bv : ModelBox}
    (hne : u ≠ v)
    (hpartU : comp[u]? = some keyU) (hpartV : comp[v]? = some keyV)
    (hnu : graph.nodes[keyU]? = some nu) (hnv : graph.nodes[keyV]? = some nv)
    (hboxU : inp.boxes[keyU]? = some bu) (hboxV : inp.boxes[keyV]? = some bv)
    (hplainU : nu.border = 0) (hplainV : nv.border = 0) (hparent : bu.parent = bv.parent) :
    Disjoint (frameRect P cg' run u) (frameRect P cg' run v) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  have hnodes : cg'.nodes = (componentCandidateR (some s) graph comp candidate).nodes := by
    rcases stages.hRank with ⟨_, _, _, _, he, _⟩ | ⟨_, _, hrank⟩
    · rw [he]
    · exact rankEquivalentR_nodes_eq hrank
  have hnu' : cg'.nodes[u]? = some nu := by
    rw [hnodes]
    exact component_node_lookupR hpartU hnu
  have hnv' : cg'.nodes[v]? = some nv := by
    rw [hnodes]
    exact component_node_lookupR hpartV hnv
  by_cases hrank : (rk run.proper.rank u).toNat = (rk run.proper.rank v).toNat
  · obtain ⟨hband, _⟩ := componentRunR_plain_rank_bands hrun
    obtain ⟨layerU, hindexU, hu, _⟩ := hband hnu' hplainU
    obtain ⟨layerV, hindexV, hv, _⟩ := hband hnv' hplainV
    rw [← hrank] at hindexV
    have heq : layerU = layerV := Option.some.inj (hindexU.symm.trans hindexV)
    have hvU : v ∈ layerU := heq.symm ▸ hv
    have hlayer : layerU ∈ run.layers := List.mem_iff_getElem?.mpr ⟨_, hindexU⟩
    exact componentRunR_region_same_layer_siblings_disjoint h0 hgraph hrun hlayer
      hu hvU hne hpartU hpartV hnu hnv hboxU hboxV hplainU hplainV hparent
  · exact componentRunR_positions_disjointR_different_rank hrun hnu' hnv' hplainU hplainV hrank

end Elegant.Layered.PipelineImpl

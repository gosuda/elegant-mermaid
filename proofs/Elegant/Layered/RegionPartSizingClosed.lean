import Elegant.Layered.RegionBaseExecutedValidity
import Elegant.Layered.RegionFixedBoxDominance
import Elegant.Layered.RegionLabelPlacementProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

theorem componentRunR_forward_anchor_size {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {k : Nat} {edge : Edge} {first : MeasuredLabel}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    (hk : cg'.edges[k]? = some edge) (hne : edge.tail ≠ edge.head)
    (hfirst : (routeLabels labels edge.decl).head? = some first) :
    ∃ index nd,
      labelAnchorIndex run.proper k
        (rk run.proper.rank edge.tail +
          Int.fdiv (rk run.proper.rank edge.head - rk run.proper.rank edge.tail) 2) =
            some index ∧
      run.proper.nodes[index]? = some nd ∧
      (stackSize cg'.slot (routeLabels labels edge.decl)).width + first.gutter ≤ nd.node.w ∧
      (stackSize cg'.slot (routeLabels labels edge.decl)).height ≤ nd.node.h := by
  obtain ⟨_, _, _, p0, labeled, pCoord, _, _, _, _, placed, q0, _, _, hs⟩ :=
    componentRunR_stages hrun
  obtain ⟨halign₀, hwf⟩ := normalize_node_rank_alignment hs.hNorm
  obtain ⟨hrank, hkeys⟩ := addLabelNodes_anchor_keys hs.hLabels
  have hlen : labeled.nodes.length = p0.nodes.length := by
    simpa only [List.length_map] using congrArg List.length hkeys
  have halign : labeled.nodes.length = labeled.rank.length := by rw [hlen, hrank, halign₀]
  have hbounds := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hk)
  have htail : edge.tail < labeled.rank.length := by
    rw [← halign, hlen]
    exact Nat.lt_of_lt_of_le hbounds.1 (normalize_nodes_length_le hs.hNorm)
  have hhead : edge.head < labeled.rank.length := by
    rw [← halign, hlen]
    exact Nat.lt_of_lt_of_le hbounds.2.1 (normalize_nodes_length_le hs.hNorm)
  obtain ⟨index, selected, hi, hselected, hw, hh⟩ :=
    componentLabels_selected_size hk hne hfirst hs.hLabels
  have hkey := labelAnchorIndex_node_edge hi hselected
  have hplain := addLabelNodes_edgeAnchorsPlain (normalize_edgeAnchorsPlain hs.hNorm) hs.hLabels
  have hb : selected.node.border = 0 :=
    hplain selected (List.mem_of_getElem? hselected) (by simp [hkey])
  obtain ⟨coord, hcoord, hbcoord, hwcoord, hhcoord⟩ :=
    regionCoordinatePlainDims P exact spec hselected hb
  rw [hs.hCoord] at hcoord
  obtain ⟨out, hout, hbout, hwout, hhout, hkeysPlaced, hrankPlaced⟩ :
      ∃ out, placed.nodes[index]? = some out ∧ out.node.border = 0 ∧
        out.node.w = coord.node.w ∧ coord.node.h ≤ out.node.h ∧
        placed.nodes.map ProperNode.edge = pCoord.nodes.map ProperNode.edge ∧
        placed.rank = pCoord.rank := by
    rcases hs.hPlaced with ⟨_, _, _, _, heq⟩ | ⟨_, _, _, _, hcross⟩
    · rw [heq]
      exact ⟨coord, hcoord, hbcoord, rfl, Int.le_refl _, rfl, rfl⟩
    · obtain ⟨n, hn, hb', hw', hh'⟩ := regionCrossPlainDims hcross hcoord
      obtain ⟨hk', hr', _, _⟩ := crossCoordsR_label_metadata hcross
      exact ⟨n, hn, hb'.trans hbcoord, hw', hh', hk', hr'⟩
  have hlookup : run.proper.nodes[index]? = some out := by
    rw [← hs.hDrop, OrderImpl.dropSynthetic_nodes]
    exact proxyWidths_plain_node hs.hProxy hout hbout
  have hprefix := coordinateGraphR_label_prefix P exact spec labeled
  rw [hs.hCoord] at hprefix
  have hCoordIdx := labelAnchorIndex_prefix halign hprefix.1 hprefix.2 hi
  obtain ⟨extra, hr⟩ := hprefix.2
  have hkeysFinal : run.proper.nodes.map ProperNode.edge = pCoord.nodes.map ProperNode.edge := by
    rw [← hs.hDrop, OrderImpl.dropSynthetic_nodes, proxyWidths_edge_keys hs.hProxy, hkeysPlaced]
  have hrankFinal : run.proper.rank = pCoord.rank := by
    rw [← hs.hDrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hs.hProxy).2.1, hrankPlaced]
  have htailFinal : rk run.proper.rank edge.tail = rk labeled.rank edge.tail := by
    rw [hrankFinal, hr, NormalizeImpl.rk_append_left htail]
  have hheadFinal : rk run.proper.rank edge.head = rk labeled.rank edge.head := by
    rw [hrankFinal, hr, NormalizeImpl.rk_append_left hhead]
  refine ⟨index, out, ?_, hlookup, ?_, ?_⟩
  · rw [htailFinal, hheadFinal]
    unfold labelAnchorIndex at hCoordIdx ⊢
    rwa [hkeysFinal, hrankFinal]
  · rw [hwout, ← hw]
    exact hwcoord
  · rw [← hh, hhcoord]
    exact hhout

theorem SceneExecutionR.envelopeFits {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate : Nat} {spec : Option RegionSpec}
    {cg : Graph} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunR execution.params (exactDecls exactIds inp) spec inp
      (componentCandidateR spec execution.graph comp candidate) execution.measured
      orderOptions = .ok (cg, run)) :
    EnvelopeFits execution.params cg run execution.measured := by
  intro k edge env hk henv
  by_cases hloop : edge.tail = edge.head
  · exact execution.nonForwardEnvelopeFits hrun hk henv (.inl hloop)
  by_cases hrev : edge.reversed = true
  · exact execution.nonForwardEnvelopeFits hrun hk henv (.inr hrev)
  have hfalse := Bool.eq_false_of_ne_true hrev
  have hforward := henv
  unfold labelEnvelope at hforward
  obtain ⟨first, hfirst, hforward⟩ := Option.bind_eq_some_iff.mp hforward
  have hb : (edge.tail == edge.head) = false := by simp [hloop]
  simp only [hb, hfalse, ↓reduceIte, Bool.false_eq_true] at hforward
  obtain ⟨found, hfound, hforward⟩ := Option.bind_eq_some_iff.mp hforward
  obtain ⟨index, nd, hi, hnode, hw, hh⟩ := componentRunR_forward_anchor_size hrun hk hloop hfirst
  rw [labelAnchorIndex_eq] at hi
  have hindex : found.2 = index := by
    simpa only [hfound, Option.map_some, Option.some.injEq] using hi
  have hrect : env = Labels.textRectAt run.proper run.xs run.ys found.2 first.gutter :=
    (Option.some.inj hforward).symm
  rw [stackSize_width_eq] at hw
  rw [stackSize_height_eq] at hh
  have hreserved :
      Labels.stackWidth ((routeLabels execution.measured edge.decl).map fun l =>
        (l.width, l.height)) ≤ env.w ∧
      Labels.stackHeight cg.slot ((routeLabels execution.measured edge.decl).map fun l =>
        (l.width, l.height)) ≤ env.h := by
    rw [hrect, hindex]
    have hbound :
        Labels.stackWidth ((routeLabels execution.measured edge.decl).map fun l =>
          (l.width, l.height)) ≤ nd.node.w - first.gutter ∧
        Labels.stackHeight cg.slot ((routeLabels execution.measured edge.decl).map fun l =>
          (l.width, l.height)) ≤ nd.node.h := ⟨by omega, hh⟩
    simpa [Labels.textRectAt, Labels.rectAt, Labels.labelRect,
      RouteImpl.nodeW, RouteImpl.nodeH, hnode] using hbound
  exact labelEnvelope_nonloop_fits hk hloop henv execution.measured_nonnegR
    (R_partSizingR_chosenFacts execution hrun).2.2 hreserved.1 hreserved.2

theorem R_partSizingRResidual_holds (exactIds : List String)
    (idSets : List (String × List String)) : R_PartSizingRResidual exactIds idSets := by
  intro inp o res execution q _hq cg run spec index hrun
  exact ⟨componentRunR_original_nodes_covered hrun, execution.envelopeFits hrun⟩

end Elegant.Layered.PipelineImpl

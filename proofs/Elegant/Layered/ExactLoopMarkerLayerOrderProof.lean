import Elegant.Layered.ExactGroupMarkerOrderProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Opposite side markers of a looping group top share the path of their unique
source anchor. In their common rank, the executed order puts the left marker first. -/
theorem xleg_loopMarkerLayerOrderX_holds :
    ∀ (exactIds : List String), XLEG_LoopMarkerLayerOrderX exactIds := by
  intro exactIds inp o res execution comp candidate run orderOptions cg hcomp hcg hrun
  subst cg
  intro _t nt _ht _hloop _htop mL mR nL nR hl hr hbl hbr hol hor hrank _hrankTop
  obtain ⟨_, labeled, _, hcoordinate, hkeys, hready, hrecords, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  have hwf : OrderImpl.BordersWellFormed run.coordinateProper := by
    rw [← hcoordinate]
    unfold coordinateGraphX
    exact materializeDummyPaths_bordersWellFormed (clearProxyExtents_bordersWellFormed
      (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))
  have hsourceL := X_side_original hready (hcoordinate.symm ▸ hl) (Or.inl hbl)
  have hsourceR := X_side_original hready (hcoordinate.symm ▸ hr) (Or.inr hbr)
  obtain ⟨topL, htopL, _, _, hpathL⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? hsourceL) (Or.inl hbl)
  obtain ⟨topR, htopR, _, _, hpathR⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? hsourceR) (Or.inr hbr)
  obtain ⟨hzipL, hbL⟩ := List.mem_filter.mp htopL
  obtain ⟨hzipR, hbR⟩ := List.mem_filter.mp htopR
  have hrecordL := List.mem_zipIdx_iff_getElem?.mp hzipL
  have hrecordR := List.mem_zipIdx_iff_getElem?.mp hzipR
  have howner : topL.1.node.clusterPath.getLast? = topR.1.node.clusterPath.getLast? := by
    rw [← hpathL, ← hpathR, hol, hor]
  have htop := X_titled_group_owner_unique execution.graph0_eq execution.graph_eq hcomp
    hkeys hrecords hrecordL hrecordR (by simpa using hbL) (by simpa using hbR) howner
  rw [htop] at hrecordL
  have hpre : nL.node.clusterPath <+: nR.node.clusterPath := by
    rw [hpathL, hpathR, Option.some.inj (hrecordL.symm.trans hrecordR)]
    exact List.prefix_rfl
  have hreal : ∀ {i : Nat} {node : ProperNode}, run.coordinateProper.nodes[i]? = some node →
      (node.node.border = -1 ∨ node.node.border = 1) → node.dummy = false := by
    intro i node hlookup hside
    cases hd : node.dummy with
    | false => rfl
    | true =>
      have hz := hwf.2.2 i node hlookup hd
      rcases hside with hside | hside <;> omega
  have hne : mL ≠ mR := by
    intro h
    rw [h] at hl
    rw [Option.some.inj (hl.symm.trans hr)] at hbl
    omega
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, hord, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨hlen, hmemL⟩ := ExecutedBorderOrder.node_layer _ _ _ hord hl
  have hmemR := (ExecutedBorderOrder.node_layer _ _ _ hord hr).2
  rw [← hrank] at hmemR
  rw [hlayers] at hlen hmemL hmemR
  have hlayer := layer_getD_mem (run := run) hlen
  obtain ⟨jL, hjL⟩ := List.mem_iff_getElem?.mp hmemL
  obtain ⟨jR, hjR⟩ := List.mem_iff_getElem?.mp hmemR
  have horder : OrderImpl.order run.coordinateProper orderOptions = .ok run.layers := by
    simp [OrderImpl.order, hord, hlayers]
  have hindices := (OrderImpl.order_border_ends _ _ _ horder hwf _ hlayer
    jL jR mL mR nL nR hjL hjR hl hr hne (hreal hl (Or.inl hbl))
    (hreal hr (Or.inr hbr)) hpre).1 hbl
  exact ⟨_, jL, jR, hlayer, hjL, hjR, hindices⟩

end Elegant.Layered.PipelineImpl

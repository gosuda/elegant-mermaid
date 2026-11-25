import Elegant.Layered.ExactNonforwardHullClosedProof
import Elegant.Layered.ExactSideMarkerFactsProof
import Elegant.Layered.ForeignSideChainShapeProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem rightMarker_source {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t m : Nat} {group : Node} {marker : ProperNode}
    (hgroup : (componentCandidate execution.graph comp candidate).nodes[t]? = some group)
    (hgroupBorder : group.border = -2)
    (hmarker : run.coordinateProper.nodes[m]? = some marker) (hb : marker.node.border = 1)
    (hlast : marker.node.clusterPath.getLast? = some group.decl) :
    marker.node.clusterPath = group.clusterPath ∧ marker.node.w = execution.params.clusterBorderW := by
  obtain ⟨_, labeled, _, hc, hkeys, hready, hrecords, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  have hsource := X_side_original hready (hc.symm ▸ hmarker) (Or.inr hb)
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? hsource) (Or.inr hb)
  obtain ⟨hzip, hpred⟩ := List.mem_filter.mp htop
  have htopRecord := List.mem_zipIdx_iff_getElem?.mp hzip
  have hrequested := X_titled_marker_record (P := execution.params) (exact := exactDecls exactIds inp)
    (hrecords t group hgroup) (Or.inl hgroupBorder)
  have hrequestedBorder : (titleF ⟨group, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hgroupBorder
  obtain ⟨_, _, hgroupPath⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq hgroup hgroupBorder
  have hrequestedLast : (titleF ⟨group, false, none, false⟩).node.clusterPath.getLast? =
      some group.decl := by
    rw [(titleF_keys _).2.2.1, hgroupPath]
    simp
  have hsameOwner : top.1.node.clusterPath.getLast? =
      (titleF ⟨group, false, none, false⟩).node.clusterPath.getLast? := by
    rw [← hpath, hlast, hrequestedLast]
  have hidx := X_titled_group_owner_unique execution.graph0_eq execution.graph_eq hcomp
    hkeys hrecords htopRecord hrequested (beq_iff_eq.mp hpred) hrequestedBorder hsameOwner
  rw [hidx] at htopRecord
  refine ⟨?_, shape_side_width _ _ hready hsource (Or.inr hb)⟩
  rw [hpath, Option.some.inj (htopRecord.symm.trans hrequested)]
  exact (titleF_keys _).2.2.1

private theorem rightMarker_placed {P : Params} {exact : List Nat} {cg : Graph}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {run : Run}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {m : Nat} {marker : ProperNode} (hm : run.coordinateProper.nodes[m]? = some marker)
    (hb : marker.node.border = 1) :
    run.proper.nodes[m]? = some marker ∧ run.xs.getD m 0 = run.coordinateXs.getD m 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  have hnproxy : ¬(marker.node.border = -2 ∨ marker.node.border = 2) := by rw [hb]; decide
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 m marker hm hnproxy
  exact ⟨by rw [← hdrop, OrderImpl.dropSynthetic_nodes]; exact hnode,
    by simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]⟩

set_option maxHeartbeats 1000000 in
/-- The ancestor's right marker brackets the owner's right marker in the same rank.
The ordered gap includes the applicable loop extent before the ancestor's frame edge. -/
theorem exactNonforwardHull_group_ancestor_right
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t pos : Nat} {owner group : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hgroup : (componentCandidate execution.graph comp candidate).nodes[pos]? = some group)
    (hownerBorder : owner.border = -2) (hgroupBorder : group.border = -2)
    (hne : t ≠ pos) (hanc : group.decl ∈ owner.clusterPath)
    (hloop : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges, e.tail = t ∧ e.head = t) :
    let cg := componentCandidate execution.graph comp candidate
    let footprint := loopFootprintExt cg run execution.measured t
    let ancestor := frameRect execution.params cg run pos
    footprint.x + footprint.w < ancestor.x + ancestor.w := by
  let cg := componentCandidate execution.graph comp candidate
  let footprint := loopFootprintExt cg run execution.measured t
  let ancestor := frameRect execution.params cg run pos
  change footprint.x + footprint.w < ancestor.x + ancestor.w
  have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (exactGraph_shape (measuredGraph_shape execution.graph0_eq) execution.graph_eq) candidate
  have hdeclNe : group.decl ≠ owner.decl := by
    intro h
    have hp := (X_group_path_iff_decl execution.graph0_eq execution.graph_eq
      howner hgroup hownerBorder hgroupBorder).mpr h.symm
    exact hne (hshape.1 t pos owner group howner hgroup hownerBorder hgroupBorder hp)
  obtain ⟨ownerBox, hownerBox, hownerPath⟩ :=
    X_cg_group_box execution.graph0_eq execution.graph_eq howner hownerBorder
  obtain ⟨groupBox, hgroupBox, hgroupPath⟩ :=
    X_cg_group_box execution.graph0_eq execution.graph_eq hgroup hgroupBorder
  have hpathMem : group.decl ∈ Compound.path inp.boxes ownerBox := by
    rw [hownerPath, List.mem_append] at hanc
    exact hanc.resolve_right fun h => hdeclNe (List.mem_singleton.mp h)
  have hprefix : group.clusterPath <+: owner.clusterPath := by
    rw [hgroupPath, hownerPath]
    exact (Compound.path_ancestor_prefix (inputModel inp o) hwf hgroupBox hownerBox hpathMem).trans
      (List.prefix_append _ _)
  have hmarkers := XLEG_groupMarkerOrderX_of_leaves exactIds
    (xleg_loopMarkerCoreX_holds exactIds) (xleg_loopMarkerLayerOrderX_holds exactIds)
    (xleg_loopMarkerSpanX_holds exactIds)
    inp o res execution hwf hfp comp candidate run orderOptions cg hcomp rfl hrun
  obtain ⟨_, mR, _, right, _, hmR, _, hbR, _, hlastR, hext, _, hshare, _, hcross, hnonneg, _⟩ :=
    hmarkers.2 t owner howner hloop hownerBorder
  obtain ⟨hpR, hxR⟩ := rightMarker_placed hrun hmR hbR
  have hpathR := (rightMarker_source execution hcomp hrun howner hownerBorder hmR hbR hlastR).1
  have hcontains : right.node.clusterPath.contains group.decl = true := by
    rw [hpathR]
    exact List.contains_iff_mem.mpr (by rw [hownerPath]; exact List.mem_append_left _ hpathMem)
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    unfold boxLines at h
    simpa only [List.length_zipIdx] using Sequence.mapM_ok_length _ _ _ h
  let rank := (rk run.proper.rank mR).toNat
  obtain ⟨_, mA, _, enclosing, _, _, _, _, hmA, hbA, hlastA, hRankA⟩ :=
    XN_bracketMarkersAtRank_holds exactIds execution.graph0_eq execution.graph_eq hlines hwf hfp
      hcomp hrun rank hpR hcontains (Nat.le_refl _) hpR hcontains (Nat.le_refl _)
  obtain ⟨hpA, hxA⟩ := rightMarker_placed hrun hmA hbA
  obtain ⟨hpathA, hwidthA⟩ := rightMarker_source execution hcomp hrun hgroup hgroupBorder hmA hbA hlastA
  have hsameRank : OrderImpl.lay run.coordinateProper mA = OrderImpl.lay run.coordinateProper mR := by
    simp only [OrderImpl.lay, hRankA, Int.toNat_natCast, rank, X_proper_rank_eq_local hrun mR]
  obtain ⟨_, labeled, _, hc, _, hready, _, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  have hbwf : OrderImpl.BordersWellFormed run.coordinateProper := by
    rw [← hc]
    unfold coordinateGraphX
    exact materializeDummyPaths_bordersWellFormed (clearProxyExtents_bordersWellFormed
      (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))
  have hreal {i : Nat} {nd : ProperNode} (hi : run.coordinateProper.nodes[i]? = some nd)
      (hb : nd.node.border = 1) : nd.dummy = false := by
    cases hd : nd.dummy with
    | false => rfl
    | true =>
      have hz := hbwf.2.2 i nd hi hd
      omega
  have hmarkerNe : mA ≠ mR := by
    intro h
    rw [h] at hmA
    have hsame := Option.some.inj (hmA.symm.trans hmR)
    rw [hsame] at hlastA
    exact hdeclNe (Option.some.inj (hlastA.symm.trans hlastR))
  obtain ⟨_, _, _, _, _, _, _, ⟨_, horder, hlayers⟩, _, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hLen, hMemR⟩ := ExecutedBorderOrder.node_layer _ _ _ horder hmR
  have hMemA := (ExecutedBorderOrder.node_layer _ _ _ horder hmA).2
  rw [hsameRank] at hMemA
  rw [hlayers] at hLen hMemR hMemA
  have hlayer := layer_getD_mem (run := run) hLen
  obtain ⟨jR, hjR⟩ := List.mem_iff_getElem?.mp hMemR
  obtain ⟨jA, hjA⟩ := List.mem_iff_getElem?.mp hMemA
  have ho : OrderImpl.order run.coordinateProper orderOptions = .ok run.layers := by
    simp [OrderImpl.order, horder, hlayers]
  have hbefore := (OrderImpl.order_border_ends _ _ _ ho hbwf _ hlayer
    jA jR mA mR enclosing right hjA hjR hmA hmR hmarkerNe
    (hreal hmA hbA) (hreal hmR hbR) (by rw [hpathA, hpathR]; exact hprefix)).2 hbA
  have hgap := xleg_rightMarker_later_gap hrun hmR hbR hmA hlayer hjR hjA hbefore
  have hreserve : footprint.w ≤ (right.node.loopExtent : Int) := by
    let sizes := loopSizes cg.edges execution.measured t cg.slot
    have hwidth : footprint.w = (if run.exact.contains t then Loops.exactExtent cg.slot sizes
        else Loops.extent cg.slot sizes) := by
      change (if run.exact.contains t then Loops.exactExtent else Loops.extent) cg.slot sizes = _
      cases run.exact.contains t <;> rfl
    rw [hwidth]
    exact hext
  have frameRight {i : Nat} {nd : Node} (hi : cg.nodes[i]? = some nd) (hb : nd.border = -2) :
      (frameRect execution.params cg run i).x + (frameRect execution.params cg run i).w =
        (boundsOf (groupBorderRects cg run nd.decl) []).right := by
    rw [frameRect_group_span (cg := cg) hi hb]
    dsimp only
    rw [Int.add_comm, Int.sub_add_cancel]
  have hframeX : footprint.x = RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR := by
    have hmem := groupBorderRects_mem_of_record (cg := cg) hpR (Or.inr hbR) hlastR
    have hge := (boundsOf_rect_mem hmem).2
    rw [rectAt_eq] at hge
    dsimp only at hge
    have hle := boundsOf_right_le_of_all hnonneg (rects := groupBorderRects cg run owner.decl)
      (fun rect hrect => by
        obtain ⟨v, nd, hv, hb, hl, rfl⟩ := groupBorderRects_inv hrect
        rw [rectAt_eq]
        dsimp only
        rcases hb with hb | hb
        · rw [((hshare hv hl).1 hb).2]
          exact hcross
        · rw [((hshare hv hl).2 hb).2] <;> exact Int.le_refl _)
    change (frameRect execution.params cg run t).x + (frameRect execution.params cg run t).w = _
    exact (frameRight howner hownerBorder).trans (Int.le_antisymm hle hge)
  have hmemA := groupBorderRects_mem_of_record (cg := cg) hpA (Or.inr hbA) hlastA
  have hcover := (boundsOf_rect_mem hmemA).2
  rw [rectAt_eq] at hcover
  dsimp only at hcover
  have hbound : RouteImpl.leftOf run.proper run.xs mA + RouteImpl.nodeW run.proper mA ≤
      ancestor.x + ancestor.w := by
    change _ ≤ (frameRect execution.params cg run pos).x + (frameRect execution.params cg run pos).w
    rw [frameRight hgroup hgroupBorder]
    exact hcover
  have hW : 1 ≤ enclosing.node.w := by
    rw [hwidthA]
    exact checkedParams_clusterBorderW_ge_one execution.checked
  have hAncestorReserve : 0 ≤ (enclosing.node.loopExtent : Int) := Int.natCast_nonneg _
  apply Int.lt_of_lt_of_le _ hbound
  rw [hframeX]
  simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, hpR, hpA, hxR, hxA,
    Int.fdiv_eq_ediv_of_nonneg _ (by decide : 0 ≤ (2 : Int)),
    Int.add_mul_ediv_left _ _ (by decide : (2 : Int) ≠ 0)] at hgap ⊢
  omega

/-- A looping group's extended reservation is strictly inside each distinct ancestor frame. -/
theorem exactNonforwardHull_group_ancestor_strict
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t pos : Nat} {owner group : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hgroup : (componentCandidate execution.graph comp candidate).nodes[pos]? = some group)
    (hownerBorder : owner.border = -2) (hgroupBorder : group.border = -2)
    (hne : t ≠ pos) (hanc : group.decl ∈ owner.clusterPath)
    (hloop : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges, e.tail = t ∧ e.head = t) :
    let cg := componentCandidate execution.graph comp candidate
    (frameRect execution.params cg run pos).StrictInside (loopFootprintExt cg run execution.measured t) :=
  (exactNonforwardHull_group_ancestor_iff_right execution hwf hfp hcomp hrun
    howner hgroup hownerBorder hgroupBorder hne hanc hloop).mpr
    (exactNonforwardHull_group_ancestor_right execution hwf hfp hcomp hrun
      howner hgroup hownerBorder hgroupBorder hne hanc hloop)

end Elegant.Layered.PipelineImpl

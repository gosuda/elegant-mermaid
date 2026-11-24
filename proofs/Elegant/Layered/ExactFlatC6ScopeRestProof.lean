import Elegant.Layered.ExactFlatC6LoopSepNonSelfProof
import Elegant.Layered.ExactGroupLoopFixedLeafGapProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem scopeRest_nonproxy_record {P : Params} {exact : List Nat} {cg : Graph}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {run : Run}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {nd : ProperNode} (hcoord : run.coordinateProper.nodes[i]? = some nd)
    (hborder : ¬ (nd.node.border = -2 ∨ nd.node.border = 2)) :
    run.proper.nodes[i]? = some nd ∧ run.xs.getD i 0 = run.coordinateXs.getD i 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 i nd hcoord hborder
  rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  exact ⟨hnode, by simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]⟩

private theorem scopeRest_layer {P : Params} {exact : List Nat} {cg : Graph}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {run : Run}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {b : Nat} (hb : b < run.proper.nodes.length) :
    ∃ layer, run.layers[(rk run.proper.rank b).toNat]? = some layer ∧ b ∈ layer := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlanes, _, _⟩ := componentRunX_spec hrun
  have hcover := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hlanes).1).2.2.2.1
  obtain ⟨layer, hlayer, hmember, _⟩ := hcover b hb
  exact ⟨layer, hlayer, hmember⟩

set_option maxHeartbeats 800000 in
private theorem scopeRest_plainLoop {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat}
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {k : Nat} {e : Edge}
    (hedge : (componentCandidate execution.graph comp candidate).edges[k]? = some e)
    {owner : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[e.tail]? = some owner)
    (hplain : owner.border = 0) {b : Nat} {target : ProperNode}
    (hcoord : run.coordinateProper.nodes[b]? = some target)
    (hnp : ¬ (target.node.border = -2 ∨ target.node.border = 2)) (hne : e.tail ≠ b) :
    Disjoint (loopFootprint (componentCandidate execution.graph comp candidate)
        run execution.measured e.tail) (RouteImpl.boxRect run.proper run.xs run.ys b) := by
  let cg := componentCandidate execution.graph comp candidate
  let foot := loopFootprint cg run execution.measured e.tail
  let box := RouteImpl.boxRect run.proper run.xs run.ys b
  change Disjoint foot box
  have ht := componentRunX_original_nodes_covered hrun e.tail (List.getElem?_eq_some_iff.mp howner).1
  have htarget := (scopeRest_nonproxy_record hrun hcoord hnp).1
  have hb := (List.getElem?_eq_some_iff.mp htarget).1
  have hborder : (cg.nodes.getD e.tail default).border = 0 := by
    simp only [cg, List.getD_eq_getElem?_getD, howner, Option.getD_some, hplain]
  have hframe := plain_frame_eq_boxRect default cg run e.tail ht (by omega)
  have hfootX : foot.x = RouteImpl.leftOf run.proper run.xs e.tail +
      RouteImpl.nodeW run.proper e.tail := by
    change (frameRect default cg run e.tail).x + (frameRect default cg run e.tail).w = _
    rw [hframe] <;> rfl
  have hfootY : foot.y = run.ys.getD e.tail 0 := by
    change (frameRect default cg run e.tail).y = _
    rw [hframe] <;> rfl
  have hfootH : foot.h = RouteImpl.nodeH run.proper e.tail := by
    change (frameRect default cg run e.tail).h = _
    rw [hframe] <;> rfl
  let rt := (rk run.proper.rank e.tail).toNat
  let rb := (rk run.proper.rank b).toNat
  obtain ⟨lt, hlt, _, htopT, hbottomT⟩ := componentRunX_node_rank_band hrun ht
  obtain ⟨lb, hlb, _, htopB, hbottomB⟩ := componentRunX_node_rank_band hrun hb
  have hbands := (X_ReserveBands_holds exactIds hrun).2
  rcases Nat.lt_trichotomy rt rb with hbefore | heq | hafter
  · have hgap := hbands rt rb lt lb hbefore hlt hlb
    apply rect_disjoint_of_y
    left
    change foot.y + foot.h ≤ run.ys.getD b 0
    rw [hfootY, hfootH]
    exact Int.le_trans hbottomT (Int.le_trans hgap htopB)
  · have hsame := hlb
    change run.layers[rb]? = some lb at hsame
    rw [← heq, hlt] at hsame
    have hsameLayer : lt = lb := Option.some.inj hsame
    obtain ⟨_, hlayerT, hmemT⟩ := scopeRest_layer hrun ht
    obtain ⟨_, hlayerB, hmemB⟩ := scopeRest_layer hrun hb
    have heqT := Option.some.inj (hlayerT.symm.trans hlt)
    have heqB := Option.some.inj (hlayerB.symm.trans hlb)
    rw [heqT] at hmemT
    rw [heqB, ← hsameLayer] at hmemB
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmemT
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmemB
    have hmem := List.mem_of_getElem? hlt
    rcases Nat.lt_trichotomy i j with hij | hij | hji
    · have hmiss := XLEM_plainRightGap_of_nonproxy exactIds inp o res execution
        comp candidate run orderOptions cg k e b hcomp rfl hrun hedge hborder
        target htarget hnp hmem hi hj hij
      exact Elegant.Layered.not_meetsInterior_of_contained X_loopFootprint_in_ext hmiss
    · subst j
      exact (hne (Option.some.inj (hi.symm.trans hj))).elim
    · obtain ⟨_, _, _, _, hnorm, hlabels, hcoordinate, _⟩ := componentRunX_spec hrun
      have hsource := addLabelNodes_untouched_node hlabels (normalize_node_record hnorm howner) rfl
      obtain ⟨actual, hactual, _, hbActual, _, _⟩ :=
        coordinateGraphX_plain_anchor_dims (exact := exactDecls exactIds inp)
          execution.params hsource hplain
      rw [hcoordinate] at hactual
      have hnpActual : ¬ (actual.node.border = -2 ∨ actual.node.border = 2) := by
        rw [hbActual]
        decide
      have hordered := XB_orderedIntervals_holds exactIds execution.graph0_eq execution.graph_eq
        hcomp hrun hmem hji hj hi hcoord hactual hnp hnpActual
      have hownerRecord := (scopeRest_nonproxy_record hrun hactual hnpActual).1
      have hw : 0 ≤ RouteImpl.nodeW run.proper e.tail := by
        simpa only [RouteImpl.nodeW, hownerRecord] using
          (componentRunX_dims_nonneg hrun e.tail actual hownerRecord).1
      apply rect_disjoint_of_x
      right
      change RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b ≤ foot.x
      rw [hfootX]
      omega
  · have hgap := hbands rb rt lb lt hafter hlb hlt
    apply rect_disjoint_of_y
    right
    change run.ys.getD b 0 + RouteImpl.nodeH run.proper b ≤ foot.y
    rw [hfootY]
    exact Int.le_trans hbottomB (Int.le_trans hgap htopT)

set_option maxHeartbeats 1200000 in
theorem scopeRest_groupLoop {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat}
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {k : Nat} {e : Edge}
    (hedge : (componentCandidate execution.graph comp candidate).edges[k]? = some e)
    (hself : e.tail = e.head) {owner : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[e.tail]? = some owner)
    (hgroup : owner.border = -2) {b : Nat} {target : ProperNode}
    (hcoord : run.coordinateProper.nodes[b]? = some target)
    (hnp : ¬ (target.node.border = -2 ∨ target.node.border = 2)) :
    Disjoint (loopFootprint (componentCandidate execution.graph comp candidate)
        run execution.measured e.tail) (RouteImpl.boxRect run.proper run.xs run.ys b) := by
  let cg := componentCandidate execution.graph comp candidate
  let frame := frameRect default cg run e.tail
  let foot := loopFootprint cg run execution.measured e.tail
  let box := RouteImpl.boxRect run.proper run.xs run.ys b
  change Disjoint foot box
  intro hmeet
  have hy : max frame.y (run.ys.getD b 0) <
      min (frame.y + frame.h) (run.ys.getD b 0 + RouteImpl.nodeH run.proper b) := hmeet.2
  obtain ⟨htarget, hxTarget⟩ := scopeRest_nonproxy_record hrun hcoord hnp
  have hnonempty := XB_memberNonempty_holds exactIds execution.graph0_eq execution.graph_eq
    hcomp hrun howner hgroup
  obtain ⟨⟨lo, loNode, hlo, hloPath, hloRank⟩, ⟨hi, hiNode, hhi, hhiPath, hhiRank⟩⟩ :=
    componentRunX_group_member_rank_bracket hrun howner hgroup htarget hnonempty hy
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    unfold boxLines at h
    simpa only [List.length_zipIdx] using Sequence.mapM_ok_length _ _ _ h
  obtain ⟨_, m, _, marker, _, _, _, _, hm, hbM, hlastM, hrankM⟩ :=
    XN_bracketMarkersAtRank_holds exactIds execution.graph0_eq execution.graph_eq hlines hwf hframed
      hcomp hrun (rk run.proper.rank b).toNat hlo hloPath hloRank hhi hhiPath hhiRank
  have hnpM : ¬ (marker.node.border = -2 ∨ marker.node.border = 2) := by rw [hbM]; decide
  obtain ⟨hpM, hxM⟩ := scopeRest_nonproxy_record hrun hm hnpM
  have hmarkers := XLEG_groupMarkerOrderX_of_leaves exactIds
    (xleg_loopMarkerCoreX_holds exactIds) (xleg_loopMarkerLayerOrderX_holds exactIds)
    (xleg_loopMarkerSpanX_holds exactIds)
    inp o res execution hwf hframed comp candidate run orderOptions cg hcomp rfl hrun
  have hloops : ∃ loop ∈ cg.edges, loop.tail = e.tail ∧ loop.head = e.tail :=
    ⟨e, List.mem_of_getElem? hedge, rfl, hself.symm⟩
  obtain ⟨_, right, _, ndR, _, hcR, _, hbR, _, hlastR, _, _, hshare, _, hcross, hnonneg, _⟩ :=
    hmarkers.2 e.tail owner howner hloops hgroup
  have hnpR : ¬ (ndR.node.border = -2 ∨ ndR.node.border = 2) := by rw [hbR]; decide
  have hpR := (scopeRest_nonproxy_record hrun hcR hnpR).1
  have hr := groupBorderRects_mem_of_record (cg := cg) hpR (Or.inr hbR) hlastR
  have hright := (boundsOf_rect_mem hr).2
  rw [rectAt_eq] at hright
  have hleft := boundsOf_right_le_of_all (rects := groupBorderRects cg run owner.decl) hnonneg
    (fun rect hrect => by
      obtain ⟨q, nd, hq, hside, hlast, heq⟩ := groupBorderRects_inv hrect
      rw [heq, rectAt_eq]
      dsimp only
      rcases hside with hs | hs
      · rw [((hshare hq hlast).1 hs).2]
        exact hcross
      · rw [((hshare hq hlast).2 hs).2] <;> exact Int.le_refl _)
  have hfootX : foot.x = RouteImpl.leftOf run.proper run.xs m +
      RouteImpl.nodeW run.proper m := by
    have hsame := ((hshare hpM hlastM).2 hbM).2
    calc
      foot.x = frame.x + frame.w := rfl
      _ = (boundsOf (groupBorderRects cg run owner.decl) []).right := by
        change (frameRect default cg run e.tail).x + (frameRect default cg run e.tail).w = _
        rw [frameRect_group_span howner hgroup]
        dsimp only
        rw [Int.add_comm, Int.sub_add_cancel]
      _ = _ := (Int.le_antisymm hleft hright).trans hsame.symm
  obtain ⟨layer, hlayer, hbMem⟩ := scopeRest_layer hrun (List.getElem?_eq_some_iff.mp htarget).1
  obtain ⟨layerM, hlayerM, hmMem⟩ := scopeRest_layer hrun (List.getElem?_eq_some_iff.mp hpM).1
  rw [X_proper_rank_eq_local hrun m, hrankM, Int.toNat_natCast, hlayer] at hlayerM
  have hsameLayer : layer = layerM := Option.some.inj hlayerM
  rw [← hsameLayer] at hmMem
  obtain ⟨i, hiM⟩ := List.mem_iff_getElem?.mp hmMem
  obtain ⟨j, hjB⟩ := List.mem_iff_getElem?.mp hbMem
  refine rect_disjoint_of_x (a := foot) (b := box) ?_ hmeet
  rcases Nat.lt_trichotomy i j with hij | hij | hji
  · left
    have hgap := xleg_rightMarker_later_gap hrun hm hbM hcoord
      (List.mem_of_getElem? hlayer) hiM hjB hij
    have hwidth : foot.w = (if run.exact.contains e.tail then
        Loops.exactExtent cg.slot (loopSizes cg.edges execution.measured e.tail cg.slot)
      else Loops.extent cg.slot (loopSizes cg.edges execution.measured e.tail cg.slot)) := by
      change (if run.exact.contains e.tail then Loops.exactExtent else Loops.extent) cg.slot
        (loopSizes cg.edges execution.measured e.tail cg.slot) = _
      cases run.exact.contains e.tail <;> rfl
    have hreserve : foot.w ≤ (marker.node.loopExtent : Int) := by
      rw [hwidth]
      exact xleg_rightMarker_extent_ge execution hcomp hrun howner hgroup hm hbM hlastM
    change foot.x + foot.w ≤ RouteImpl.leftOf run.proper run.xs b
    rw [hfootX]
    simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, hpM, htarget, hxM, hxTarget,
      Int.fdiv_eq_ediv_of_nonneg _ (by decide : 0 ≤ (2 : Int))] at hgap ⊢
    omega
  · right
    subst j
    have heq : b = m := Option.some.inj (hjB.symm.trans hiM)
    change RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b ≤ foot.x
    rw [heq, hfootX] <;> exact Int.le_refl _
  · right
    have hordered := XB_orderedIntervals_holds exactIds execution.graph0_eq execution.graph_eq
      hcomp hrun (List.mem_of_getElem? hlayer) hji hjB hiM hcoord hm hnp hnpM
    have hw : 0 ≤ RouteImpl.nodeW run.proper m := by
      simpa only [RouteImpl.nodeW, hpM] using (componentRunX_dims_nonneg hrun m marker hpM).1
    change RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b ≤ foot.x
    rw [hfootX]
    omega

/-- Exact component reservations separate plain target frames at every proper index, including
synthetic titles, side markers and edge-label dummies. No declaration-scope test is needed. -/
theorem x6_loopSep_nonSelf_scopeRest_holds :
    ∀ exactIds, X6_LoopSep_NonSelf_ScopeRest exactIds := by
  intro exactIds inp o res execution hwf hframed comp candidate run v b k e
    hcomp hbdr hrun hne hedge htail hhead hb _hnonexclusive
  let cg := componentCandidate execution.graph comp candidate
  let order := candidateOrder candidate
  change (cg.nodes.getD b default).border = 0 at hbdr
  change cg.edges[k]? = some e at hedge
  change LoopFootprintSeparation cg run execution.measured v b
  have hself := htail.trans hhead.symm
  rw [← htail] at hne ⊢
  unfold LoopFootprintSeparation
  rw [plain_frame_eq_boxRect default cg run b hb (by omega)]
  obtain ⟨nd, hnd⟩ : ∃ nd, run.proper.nodes[b]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hb⟩
  by_cases hproxy : nd.node.border = -2 ∨ nd.node.border = 2
  · have hmiss := XLEM_plainRightProxyMiss_holds exactIds inp o res execution
      comp candidate run order cg e b hcomp rfl hrun nd hnd hproxy
    exact Elegant.Layered.not_meetsInterior_of_contained X_loopFootprint_in_ext hmiss
  obtain ⟨target, hcoord, hborder, _⟩ := XLEM_proper_coord hrun hnd
  have hnp : ¬ (target.node.border = -2 ∨ target.node.border = 2) := by rwa [hborder]
  have hbounds := candidate_edge_endpoints_bounded_general execution.graph comp candidate
    hcomp (sceneExecutionX_edges_bounded execution) (List.mem_of_getElem? hedge)
  obtain ⟨owner, howner⟩ : ∃ owner, cg.nodes[e.tail]? = some owner :=
    ⟨_, List.getElem?_eq_getElem hbounds.1⟩
  rcases (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq howner).1 with
    hplain | hgroup | hbottom
  · exact scopeRest_plainLoop execution hcomp hrun hedge howner hplain hcoord hnp hne
  · exact scopeRest_groupLoop execution hwf hframed hcomp hrun hedge hself howner hgroup hcoord hnp
  · exact (exactBottomNoLoopX execution comp candidate run order hcomp cg rfl hrun
      e.tail owner howner hbottom ⟨e, List.mem_of_getElem? hedge, rfl, hself.symm⟩).elim

end Elegant.Layered.PipelineImpl

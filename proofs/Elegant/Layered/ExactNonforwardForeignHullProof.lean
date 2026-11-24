import Elegant.Layered.ExactBorderChainBProof
import Elegant.Layered.ExactForeignRankPairAnchorsProof
import Elegant.Layered.ExactNonforwardHullClosedProof
import Elegant.Layered.ExactLoopEnvelopeRightProof
import Elegant.Layered.ExactPlainNodePathProof
import Elegant.Layered.ForeignSideChainShapeProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem foreign_lines_length {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  unfold boxLines at h
  simpa only [List.length_zipIdx] using Sequence.mapM_ok_length _ _ _ h

private theorem foreign_nonproxy {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {nd : ProperNode} (hnd : run.coordinateProper.nodes[i]? = some nd)
    (hb : ¬ (nd.node.border = -2 ∨ nd.node.border = 2)) :
    run.proper.nodes[i]? = some nd ∧ run.xs.getD i 0 = run.coordinateXs.getD i 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hrecord, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 i nd hnd hb
  rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  exact ⟨hrecord, by simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]⟩

private theorem foreign_layer_position {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {i r : Nat} {nd : ProperNode} (hnd : run.coordinateProper.nodes[i]? = some nd)
    (hrank : rk run.coordinateProper.rank i = (r : Int)) :
    run.layers.getD r [] ∈ run.layers ∧ ∃ j : Nat, (run.layers.getD r [])[j]? = some i := by
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, hord, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨hlen, hmem⟩ := ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord hord hnd
  simp only [OrderImpl.lay, hrank, Int.toNat_natCast, hlayers] at hlen hmem
  exact ⟨layer_getD_mem (run := run) (k := r) hlen, List.mem_iff_getElem?.mp hmem⟩

private theorem foreign_member_hulls_before {P : Params} {exactIds : List String}
    {inp : Input} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {d e : Nat} (hne : groupMemberRects cg run e ≠ [])
    (hordered : ∀ i j : Nat, i < run.proper.nodes.length → j < run.proper.nodes.length →
      (run.proper.nodes.getD i default).node.clusterPath.contains d = true →
      (run.proper.nodes.getD j default).node.clusterPath.contains e = true →
      rk run.proper.rank i < rk run.proper.rank j) :
    (boundsOf (groupMemberRects cg run d) []).bottom ≤
      (boundsOf (groupMemberRects cg run e) []).minY := by
  have htop := XB_topNonneg_holds exactIds hrun
  have hbands := (X_ReserveBands_holds exactIds hrun).2
  have hnonneg : 0 ≤ (boundsOf (groupMemberRects cg run e) []).minY := by
    apply boundsOf_minY_ge_of_all hne
    intro rect hrect
    obtain ⟨j, nd, hj, _, rfl⟩ := groupMemberRects_inv hrect
    obtain ⟨_, _, _, hlo, _⟩ := componentRunX_node_rank_band hrun (List.getElem?_eq_some_iff.mp hj).1
    change 0 ≤ run.ys.getD j 0
    exact Int.le_trans (htop _) hlo
  refine boundsOf_bottom_le_of_all hnonneg ?_
  intro first hfirst
  refine boundsOf_minY_ge_of_all hne ?_
  intro second hsecond
  obtain ⟨i, ni, hi, hdi, rfl⟩ := groupMemberRects_inv hfirst
  obtain ⟨j, nj, hj, hej, rfl⟩ := groupMemberRects_inv hsecond
  have hi' := (List.getElem?_eq_some_iff.mp hi).1
  have hj' := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨li, hli, hri, _, hbot⟩ := componentRunX_node_rank_band hrun hi'
  obtain ⟨lj, hlj, hrj, hupper, _⟩ := componentRunX_node_rank_band hrun hj'
  have hlt := hordered i j hi' hj'
    (by simpa only [List.getD_eq_getElem?_getD, hi, Option.getD_some] using hdi)
    (by simpa only [List.getD_eq_getElem?_getD, hj, Option.getD_some] using hej)
  have hgap := hbands _ _ li lj (by omega) hli hlj
  change run.ys.getD i 0 + RouteImpl.nodeH run.proper i ≤ run.ys.getD j 0
  omega

private theorem foreign_frame_x_of_markers {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {pos mL mR : Nat} {group : Node} {nL nR : ProperNode}
    (hg : (componentCandidate execution.graph comp candidate).nodes[pos]? = some group)
    (hgroup : group.border = -2)
    (hL : run.proper.nodes[mL]? = some nL) (hbL : nL.node.border = -1)
    (hlastL : nL.node.clusterPath.getLast? = some group.decl)
    (hR : run.proper.nodes[mR]? = some nR) (hbR : nR.node.border = 1)
    (hlastR : nR.node.clusterPath.getLast? = some group.decl)
    (hrank : rk run.proper.rank mL = rk run.proper.rank mR) :
    let rect := frameRect execution.params (componentCandidate execution.graph comp candidate) run pos
    rect.x = RouteImpl.leftOf run.proper run.xs mL ∧
      rect.x + rect.w = RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR := by
  let cg := componentCandidate execution.graph comp candidate
  let rects := groupBorderRects cg run group.decl
  have hspan {i j : Nat} {first second : ProperNode}
      (hi : run.proper.nodes[i]? = some first)
      (hbi : first.node.border = -1 ∨ first.node.border = 1)
      (hli : first.node.clusterPath.getLast? = some group.decl)
      (hj : run.proper.nodes[j]? = some second)
      (hbj : second.node.border = -1 ∨ second.node.border = 1)
      (hlj : second.node.clusterPath.getLast? = some group.decl) :=
    XN_sideMarkerSpanAligned_of_chain exactIds
      (X_foreignBorderChainXAligned_framed exactIds) execution.graph0_eq execution.graph_eq
      (foreign_lines_length execution) hwf hfp hcomp hrun
      (decl := group.decl) (m := i) (m' := j) (marker := first) (marker' := second)
      hi hbi hli hj hbj hlj
  have hpair := hspan hL (Or.inl hbL) hlastL hR (Or.inr hbR) hlastR
  have hcross := hpair.2.2 ⟨hbL, hbR, hrank⟩
  have hrightNonneg := (hspan hR (Or.inr hbR) hlastR hR (Or.inr hbR) hlastR).2.1
  have hmL : Labels.rectAt run.proper run.xs run.ys mL ∈ rects :=
    groupBorderRects_mem_of_record (cg := cg) hL (Or.inl hbL) hlastL
  have hmR : Labels.rectAt run.proper run.xs run.ys mR ∈ rects :=
    groupBorderRects_mem_of_record (cg := cg) hR (Or.inr hbR) hlastR
  have hall : ∀ r ∈ rects, RouteImpl.leftOf run.proper run.xs mL ≤ r.x ∧
      r.x + r.w ≤ RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR := by
    intro r hm
    obtain ⟨i, nd, hi, hb, hlast, rfl⟩ := groupBorderRects_inv (cg := cg) hm
    change RouteImpl.leftOf run.proper run.xs mL ≤ RouteImpl.leftOf run.proper run.xs i ∧
      RouteImpl.leftOf run.proper run.xs i + RouteImpl.nodeW run.proper i ≤
        RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR
    rcases hb with hb | hb
    · have he := (hspan hi (Or.inl hb) hlast hL (Or.inl hbL) hlastL).1 (hb.trans hbL.symm)
      exact ⟨by rw [he.1] <;> exact Int.le_refl _, by rw [he.2]; exact hcross.2⟩
    · have he := (hspan hi (Or.inr hb) hlast hR (Or.inr hbR) hlastR).1 (hb.trans hbR.symm)
      exact ⟨by rw [he.1]; exact hcross.1, by rw [he.2] <;> exact Int.le_refl _⟩
  have hlo := boundsOf_minX_ge_of_all (List.ne_nil_of_mem hmL) (fun r hr => (hall r hr).1)
  have hhi := boundsOf_right_le_of_all hrightNonneg (fun r hr => (hall r hr).2)
  have hlow := (boundsOf_rect_mem hmL).1
  have hhigh := (boundsOf_rect_mem hmR).2
  change (boundsOf rects []).minX ≤ RouteImpl.leftOf run.proper run.xs mL at hlow
  change RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR ≤
    (boundsOf rects []).right at hhigh
  dsimp only
  rw [frameRect_group_span (cg := cg) hg hgroup]
  change (boundsOf rects []).minX = _ ∧
    (boundsOf rects []).minX + ((boundsOf rects []).right - (boundsOf rects []).minX) = _
  refine ⟨Int.le_antisymm hlow hlo, ?_⟩
  rw [Int.add_comm, Int.sub_add_cancel]
  exact Int.le_antisymm hhi hhigh

private theorem foreign_reserved_gap {run : Run} {i j : Nat} {a b : ProperNode} {extent : Int}
    (ha : run.proper.nodes[i]? = some a) (hb : run.proper.nodes[j]? = some b)
    (hxi : run.xs.getD i 0 = run.coordinateXs.getD i 0)
    (hxj : run.xs.getD j 0 = run.coordinateXs.getD j 0)
    (hext : extent ≤ (a.node.loopExtent : Int))
    (hgap : Int.fdiv (a.node.w + 2 * (a.node.loopExtent : Int)) 2 +
      Int.fdiv (b.node.w + 2 * (b.node.loopExtent : Int)) 2 + 1 ≤
      run.coordinateXs.getD j 0 - run.coordinateXs.getD i 0) :
    RouteImpl.leftOf run.proper run.xs i + RouteImpl.nodeW run.proper i + extent ≤
      RouteImpl.leftOf run.proper run.xs j := by
  have hbext : 0 ≤ (b.node.loopExtent : Int) := Int.natCast_nonneg _
  simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, ha, hb, hxi, hxj,
    Int.fdiv_eq_ediv_of_nonneg _ (by decide : 0 ≤ (2 : Int))] at hgap ⊢
  omega

set_option maxHeartbeats 1200000 in
/-- A looping group's reservation misses a mutually unrelated group on the
executed candidate. Disjoint ranks suffice vertically. In a shared rank, the
side-marker order chooses which horizontal bound uses the loop extent. -/
theorem exactNonforwardForeignHull_group_disjoint
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t pos : Nat} {owner group : Node}
    (hloop : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges, e.tail = t ∧ e.head = t)
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hownerBorder : owner.border = -2)
    (hgroup : (componentCandidate execution.graph comp candidate).nodes[pos]? = some group)
    (hgroupBorder : group.border = -2)
    (hforeign : group.decl ∉ owner.clusterPath) (hreverse : owner.decl ∉ group.clusterPath) :
    Disjoint (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos)
      (loopFootprintExt (componentCandidate execution.graph comp candidate) run execution.measured t) := by
  let cg := componentCandidate execution.graph comp candidate
  let foot := loopFootprintExt cg run execution.measured t
  let frame := frameRect execution.params cg run pos
  let own := frameRect execution.params cg run t
  change Disjoint frame foot
  have hx : foot.x = own.x + own.w := rfl
  have hy : foot.y = own.y := rfl
  have hh : foot.h = own.h :=
    exactNonforwardHull_group_height execution hcomp hrun howner hownerBorder hloop
  obtain ⟨_, _, hpath⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq howner hownerBorder
  have hne : owner.decl ≠ group.decl := by
    intro he
    exact hforeign (by rw [← he, hpath]; simp)
  obtain ⟨loT, hiT, loG, hiG, htLe, hgLe, htSpan, hgSpan, htSides, hgSides⟩ :=
    XB_foreignClusterRankSpans_holds exactIds (XB_foreignRankPairAnchors_holds exactIds)
      execution.graph0_eq execution.graph_eq (foreign_lines_length execution) hwf hfp
      hcomp hrun howner hgroup hownerBorder hgroupBorder hne
  have hmT := XB_memberNonempty_holds exactIds execution.graph0_eq execution.graph_eq
    hcomp hrun howner hownerBorder
  have hmG := XB_memberNonempty_holds exactIds execution.graph0_eq execution.graph_eq
    hcomp hrun hgroup hgroupBorder
  by_cases htBefore : hiT < loG
  · have hgap := foreign_member_hulls_before hrun hmG (d := owner.decl) (by
      intro i j hi hj hci hcj
      have h1 := htSpan i hi hci
      have h2 := hgSpan j hj hcj
      omega)
    refine rect_disjoint_of_y (Or.inr ?_)
    rw [hy, hh]
    change (frameRect execution.params cg run t).y + (frameRect execution.params cg run t).h ≤
      (frameRect execution.params cg run pos).y
    rw [frameRect_group_span howner hownerBorder, frameRect_group_span hgroup hgroupBorder]
    dsimp only
    omega
  by_cases hgBefore : hiG < loT
  · have hgap := foreign_member_hulls_before hrun hmT (d := group.decl) (by
      intro i j hi hj hci hcj
      have h1 := hgSpan i hi hci
      have h2 := htSpan j hj hcj
      omega)
    refine rect_disjoint_of_y (Or.inl ?_)
    rw [hy]
    change (frameRect execution.params cg run pos).y + (frameRect execution.params cg run pos).h ≤
      (frameRect execution.params cg run t).y
    rw [frameRect_group_span howner hownerBorder, frameRect_group_span hgroup hgroupBorder]
    dsimp only
    omega
  let r := (max loT loG).toNat
  have hr : (r : Int) = max loT loG := by
    have hl : 0 ≤ loT := by
      obtain ⟨a, _, nd, _, ha, hb, _, hra, _⟩ := htSides loT (Int.le_refl _) htLe
      have hpa := (foreign_nonproxy hrun ha (by rw [hb]; decide)).1
      obtain ⟨_, _, hnonneg, _, _⟩ :=
        componentRunX_node_rank_band hrun (List.getElem?_eq_some_iff.mp hpa).1
      rw [X_proper_rank_eq_local hrun a, hra] at hnonneg
      exact hnonneg
    exact Int.toNat_of_nonneg (by omega)
  obtain ⟨tL, tR, ntL, ntR, htL, hbtL, hltL, hrtL, htR, hbtR, hltR, hrtR⟩ :=
    htSides (r : Int) (by omega) (by omega)
  obtain ⟨gL, gR, ngL, ngR, hgL, hbgL, hlgL, hrgL, hgR, hbgR, hlgR, hrgR⟩ :=
    hgSides (r : Int) (by omega) (by omega)
  have hntL : ¬ (ntL.node.border = -2 ∨ ntL.node.border = 2) := by rw [hbtL]; decide
  have hntR : ¬ (ntR.node.border = -2 ∨ ntR.node.border = 2) := by rw [hbtR]; decide
  have hngL : ¬ (ngL.node.border = -2 ∨ ngL.node.border = 2) := by rw [hbgL]; decide
  have hngR : ¬ (ngR.node.border = -2 ∨ ngR.node.border = 2) := by rw [hbgR]; decide
  obtain ⟨hptL, _⟩ := foreign_nonproxy hrun htL hntL
  obtain ⟨hptR, hxtR⟩ := foreign_nonproxy hrun htR hntR
  obtain ⟨hpgL, hxgL⟩ := foreign_nonproxy hrun hgL hngL
  obtain ⟨hpgR, _⟩ := foreign_nonproxy hrun hgR hngR
  have htPair : rk run.proper.rank tL = rk run.proper.rank tR := by
    rw [X_proper_rank_eq_local hrun tL, X_proper_rank_eq_local hrun tR, hrtL, hrtR]
  have hgPair : rk run.proper.rank gL = rk run.proper.rank gR := by
    rw [X_proper_rank_eq_local hrun gL, X_proper_rank_eq_local hrun gR, hrgL, hrgR]
  obtain ⟨_, hownRight⟩ := foreign_frame_x_of_markers execution hwf hfp hcomp hrun
    howner hownerBorder hptL hbtL hltL hptR hbtR hltR htPair
  obtain ⟨hgroupLeft, hgroupRight⟩ := foreign_frame_x_of_markers execution hwf hfp hcomp hrun
    hgroup hgroupBorder hpgL hbgL hlgL hpgR hbgR hlgR hgPair
  obtain ⟨hlayer, itR, hitR⟩ := foreign_layer_position hrun (r := r) htR hrtR
  obtain ⟨_, igL, higL⟩ := foreign_layer_position hrun (r := r) hgL hrgL
  obtain ⟨_, igR, higR⟩ := foreign_layer_position hrun (r := r) hgR hrgR
  have hpathG : group.clusterPath.contains owner.decl = false :=
    Bool.eq_false_iff.mpr (fun h => hreverse (List.contains_iff_mem.mp h))
  have hpathT : owner.clusterPath.contains group.decl = false :=
    Bool.eq_false_iff.mpr (fun h => hforeign (List.contains_iff_mem.mp h))
  rcases XB_foreignBorderLayerOrder_holds exactIds execution.graph0_eq execution.graph_eq
    hcomp hrun howner hgroup hownerBorder hgroupBorder hne hpathG hpathT hlayer with hleft | hright
  · have hgap := xleg_rightMarker_later_gap hrun htR hbtR hgL hlayer hitR higL
      (hleft _ _ _ _ _ _ hitR higL htR hgL (Or.inr hbtR) hltR (Or.inl hbgL) hlgL)
    have hext := xleg_rightMarker_extent_ge execution hcomp hrun howner hownerBorder
      htR hbtR hltR
    have hw : foot.w ≤ (ntR.node.loopExtent : Int) := by
      let sizes := loopSizes cg.edges execution.measured t cg.slot
      calc
        foot.w = (if run.exact.contains t then Loops.exactExtent cg.slot sizes
            else Loops.extent cg.slot sizes) := by
          change (if run.exact.contains t then Loops.exactExtent else Loops.extent) cg.slot sizes = _
          cases run.exact.contains t <;> rfl
        _ ≤ _ := hext
    have h := foreign_reserved_gap hptR hpgL hxtR hxgL hw hgap
    exact rect_disjoint_of_x (Or.inr (by rw [hx, hownRight, hgroupLeft]; exact h))
  · have h := XB_orderedIntervals_holds exactIds execution.graph0_eq execution.graph_eq
      hcomp hrun hlayer
      (hright _ _ _ _ _ _ hitR higR htR hgR (Or.inr hbtR) hltR (Or.inr hbgR) hlgR)
      higR hitR hgR htR hngR hntR
    have hw : 0 ≤ RouteImpl.nodeW run.proper tR := by
      simpa only [RouteImpl.nodeW, hptR] using (componentRunX_dims_nonneg hrun tR ntR hptR).1
    refine rect_disjoint_of_x (Or.inl ?_)
    rw [hx, hownRight, hgroupRight]
    omega

/-- A plain owner's footprint is bracketed by member ranks whenever it can
overlap the foreign frame vertically. The later-rank bound uses the extended
reservation, even when the exact owner's own frame has zero height. -/
theorem exactNonforwardForeignHull_plain_rank_split
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t pos : Nat} {owner group : Node}
    (hloop : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges, e.tail = t ∧ e.head = t)
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hplain : owner.border = 0)
    (hgroup : (componentCandidate execution.graph comp candidate).nodes[pos]? = some group)
    (hgroupBorder : group.border = -2) :
    let cg := componentCandidate execution.graph comp candidate
    let foot := loopFootprintExt cg run execution.measured t
    let frame := frameRect execution.params cg run pos
    frame.y + frame.h ≤ foot.y ∨ foot.y + foot.h ≤ frame.y ∨
      ((∃ a nd, run.proper.nodes[a]? = some nd ∧ nd.node.clusterPath.contains group.decl = true ∧
        (rk run.proper.rank a).toNat ≤ (rk run.proper.rank t).toNat) ∧
      (∃ b nd, run.proper.nodes[b]? = some nd ∧ nd.node.clusterPath.contains group.decl = true ∧
        (rk run.proper.rank t).toNat ≤ (rk run.proper.rank b).toNat)) := by
  let cg := componentCandidate execution.graph comp candidate
  let foot := loopFootprintExt cg run execution.measured t
  let frame := frameRect execution.params cg run pos
  let r := (rk run.proper.rank t).toNat
  have hb : (cg.nodes.getD t default).border ≠ -2 := by
    simp only [cg, List.getD_eq_getElem?_getD, howner, Option.getD_some, hplain]
    decide
  obtain ⟨edge, hedge, ht, hh⟩ := hloop
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hedge
  have hself := ht.trans hh.symm
  have hfoot := XLEM_footBelow_holds exactIds (XLEM_plainReserve_holds exactIds)
    inp o res execution comp candidate run orderOptions cg k edge hcomp rfl hrun hk hself
    (by rwa [ht])
  rw [ht, ← X_proper_rank_eq_local hrun t] at hfoot
  obtain ⟨layer, hlayer, htop, hbottom⟩ := hfoot
  have hbnds := (X_ReserveBands_holds exactIds hrun).2
  by_cases hlow : ∃ a nd, run.proper.nodes[a]? = some nd ∧
      nd.node.clusterPath.contains group.decl = true ∧ (rk run.proper.rank a).toNat ≤ r
  · by_cases hhigh : ∃ b nd, run.proper.nodes[b]? = some nd ∧
        nd.node.clusterPath.contains group.decl = true ∧ r ≤ (rk run.proper.rank b).toNat
    · exact Or.inr (Or.inr ⟨hlow, hhigh⟩)
    · have hnonneg := Int.le_trans (XB_topNonneg_holds exactIds hrun r) htop
      have hgap : (boundsOf (groupMemberRects cg run group.decl) []).bottom ≤ foot.y :=
        boundsOf_bottom_le_of_all hnonneg (fun rect hrect => by
          obtain ⟨i, nd, hi, hmem, rfl⟩ := groupMemberRects_inv hrect
          have hlt : (rk run.proper.rank i).toNat < r := by
            exact Nat.lt_of_not_ge fun hge => hhigh ⟨i, nd, hi, hmem, hge⟩
          obtain ⟨li, hli, _, _, hrectBot⟩ := componentRunX_node_rank_band hrun
            (List.getElem?_eq_some_iff.mp hi).1
          change run.ys.getD i 0 + RouteImpl.nodeH run.proper i ≤ foot.y
          exact Int.le_trans hrectBot (Int.le_trans (hbnds _ _ li layer hlt hli hlayer) htop))
      refine Or.inl ?_
      change (frameRect execution.params cg run pos).y +
        (frameRect execution.params cg run pos).h ≤ foot.y
      rw [frameRect_group_span (cg := cg) hgroup hgroupBorder]
      dsimp only
      rw [Int.add_comm, Int.sub_add_cancel]
      exact hgap
  · have hne := XB_memberNonempty_holds exactIds execution.graph0_eq execution.graph_eq
      hcomp hrun hgroup hgroupBorder
    have hgap := boundsOf_minY_ge_of_all hne
      (lo := foot.y + foot.h) (fun rect hrect => by
        obtain ⟨i, nd, hi, hmem, rfl⟩ := groupMemberRects_inv hrect
        have hlt : r < (rk run.proper.rank i).toNat := by
          exact Nat.lt_of_not_ge fun hge => hlow ⟨i, nd, hi, hmem, hge⟩
        obtain ⟨li, hli, _, hrectTop, _⟩ := componentRunX_node_rank_band hrun
          (List.getElem?_eq_some_iff.mp hi).1
        change foot.y + foot.h ≤ run.ys.getD i 0
        exact Int.le_trans (hbottom _ li hlt hli) hrectTop)
    exact Or.inr (Or.inl (by
      change foot.y + foot.h ≤ (frameRect execution.params cg run pos).y
      rw [frameRect_group_span hgroup hgroupBorder]
      exact hgap))

private theorem foreign_plain_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {t : Nat} {owner : Node} (howner : cg.nodes[t]? = some owner) (hplain : owner.border = 0) :
    ∃ nd, run.coordinateProper.nodes[t]? = some nd ∧ nd.node.border = 0 ∧
      nd.node.clusterPath = owner.clusterPath := by
  obtain ⟨_, _, labeled, _, hnorm, hlab, hcoord, _, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  have hs := addLabelNodes_untouched_node hlab (normalize_node_record hnorm howner) rfl
  let sized := sizeProperPortsX P exact labeled
  obtain ⟨nd, hn, hd, hb, hp⟩ : ∃ nd, sized.nodes[t]? = some nd ∧
    nd.dummy = false ∧ nd.node.border = 0 ∧ nd.node.clusterPath = owner.clusterPath := by
    dsimp only [sized, sizeProperPortsX]
    simp only [List.getElem?_map, List.getElem?_zipIdx, hs, Option.map_some]
    split <;> exact ⟨_, rfl, rfl, hplain, rfl⟩
  have ht : (titleReservations sized).nodes[t]? = some nd := by
    rw [titleReservations_nodes, List.getElem?_append_left (by
      simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hn).1)]
    simp [List.getElem?_map, hn, titleF, hb]
  obtain ⟨_, hnodes, _⟩ := addClusterBorders_extra (titleReservations sized) P.clusterBorderW
  have hborder : (OrderImpl.addClusterBorders (titleReservations sized) P.clusterBorderW).nodes[t]? =
      some nd := by
    rw [hnodes, List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1]
    exact ht
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations sized) P.clusterBorderW)).nodes[t]? = some nd := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hborder, clearF, hb]
  refine ⟨nd, ?_, hb, hp⟩
  rw [← hcoord]
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx]
  change (clearProxyExtents (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes[t]? =
    some nd at hclear
  rw [hclear]
  simp only [Option.map_some, hd, Bool.false_eq_true, ↓reduceIte]

private theorem foreign_left_marker_positive
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {m : Nat} {nd : ProperNode} (hm : run.coordinateProper.nodes[m]? = some nd)
    (hb : nd.node.border = -1) : 0 < nd.node.w := by
  obtain ⟨_, labeled, _, hc, _, hready, _, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  rw [← hc] at hm
  have hw := shape_side_width (titleReservations (sizeProperPortsX execution.params
    (exactDecls exactIds inp) labeled)) execution.params.clusterBorderW hready
    (X_side_original hready hm (Or.inl hb)) (Or.inl hb)
  have hpos := checkedParams_clusterBorderW_ge_one execution.checked
  omega

private theorem foreign_plain_later_center_gap {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {a b : Nat} {na nb : ProperNode}
    (ha : run.coordinateProper.nodes[a]? = some na) (hplain : na.node.border = 0)
    (hb : run.coordinateProper.nodes[b]? = some nb)
    {layer : List Nat} (hlayer : layer ∈ run.layers) {i j : Nat}
    (hi : layer[i]? = some a) (hj : layer[j]? = some b) (hlt : i < j) :
    Int.fdiv (na.node.w + 2 * (na.node.loopExtent : Int)) 2 +
      Int.fdiv (nb.node.w + 2 * (nb.node.loopExtent : Int)) 2 + 1 ≤
      run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRunX_spec hrun
  obtain ⟨hgap, hpad, _, hs, _⟩ := CoordsImpl.crossCoordsClusterWith_spec hcross
  have hnextLen : i + 1 < layer.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    omega
  let next := layer[i + 1]
  have hnext : layer[i + 1]? = some next := List.getElem?_eq_getElem hnextLen
  have hnoTitle : CoordsImpl.ownTitleAnchor run.coordinateProper a next = false := by
    cases h : run.coordinateProper.nodes[next]? <;>
      simp [CoordsImpl.ownTitleAnchor, ha, hplain, h]
  have hfirst := CoordsImpl.cluster_balance_separated hcross layer hlayer i a next hi hnext
  have hmin := CoordsImpl.clusterGap_ge_min (ng := P.nodeGap) (cp := P.clusterPad) _ _ _ hnoTitle
  have hwa : CoordsImpl.nodeW run.coordinateProper a =
      na.node.w + 2 * (na.node.loopExtent : Int) := by simp only [CoordsImpl.nodeW, ha]
  have hwb : CoordsImpl.nodeW run.coordinateProper b =
      nb.node.w + 2 * (nb.node.loopExtent : Int) := by simp only [CoordsImpl.nodeW, hb]
  rw [← hwa, ← hwb]
  unfold CoordsImpl.clusterSep CoordsImpl.coordSep at hfirst
  by_cases heq : i + 1 = j
  · have he : next = b := Option.some.inj (hnext.symm.trans (heq ▸ hj))
    rw [he] at hfirst hmin
    omega
  · have htail := CoordsImpl.cluster_zero_pairs_separated hcross layer hlayer (i + 1) j next b
      (by omega) hnext hj
    have halfNonneg : 0 ≤ Int.fdiv (CoordsImpl.nodeW run.coordinateProper next) 2 :=
      Int.fdiv_nonneg (CoordsImpl.nodeW_nonneg hs next) (by decide)
    omega

set_option maxHeartbeats 1200000 in
/-- A plain loop's reservation misses a foreign group. Only the shared-rank
case with the plain owner to the left consumes its horizontal reservation. -/
theorem exactNonforwardForeignHull_plain_disjoint
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t pos : Nat} {owner group : Node}
    (hloop : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges, e.tail = t ∧ e.head = t)
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hplain : owner.border = 0)
    (hgroup : (componentCandidate execution.graph comp candidate).nodes[pos]? = some group)
    (hgroupBorder : group.border = -2) (hforeign : group.decl ∉ owner.clusterPath) :
    let cg := componentCandidate execution.graph comp candidate
    let foot := loopFootprintExt cg run execution.measured t
    Disjoint (frameRect execution.params cg run pos) foot := by
  let cg := componentCandidate execution.graph comp candidate
  let foot := loopFootprintExt cg run execution.measured t
  let frame := frameRect execution.params cg run pos
  change Disjoint frame foot
  rcases exactNonforwardForeignHull_plain_rank_split execution hwf hfp hcomp hrun hloop howner
    hplain hgroup hgroupBorder with hbefore | hafter | ⟨⟨lo, nlo, hlo, hclo, hrlo⟩,
      ⟨hi, nhi, hhi, hchi, hrhi⟩⟩
  · exact rect_disjoint_of_y (Or.inl hbefore)
  · exact rect_disjoint_of_y (Or.inr hafter)
  let r := (rk run.proper.rank t).toNat
  obtain ⟨mL, mR, nL, nR, hcL, hbL, hnL, hrL, hcR, hbR, hnR, hrR⟩ :=
    XN_bracketMarkersAtRank_holds exactIds execution.graph0_eq execution.graph_eq
      (foreign_lines_length execution) hwf hfp hcomp hrun r hlo hclo hrlo hhi hchi hrhi
  obtain ⟨actual, hcT, hbT, hpT⟩ := foreign_plain_record hrun howner hplain
  have hnpT : ¬ (actual.node.border = -2 ∨ actual.node.border = 2) := by rw [hbT]; decide
  have hnpL : ¬ (nL.node.border = -2 ∨ nL.node.border = 2) := by rw [hbL]; decide
  have hnpR : ¬ (nR.node.border = -2 ∨ nR.node.border = 2) := by rw [hbR]; decide
  obtain ⟨hpT', hxT⟩ := foreign_nonproxy hrun hcT hnpT
  obtain ⟨hpL, hxL⟩ := foreign_nonproxy hrun hcL hnpL
  obtain ⟨hpR, _⟩ := foreign_nonproxy hrun hcR hnpR
  obtain ⟨_, _, hnonnegT, _, _⟩ := componentRunX_node_rank_band hrun
    (List.getElem?_eq_some_iff.mp hpT').1
  have hrT : rk run.coordinateProper.rank t = (r : Int) := by
    rw [← X_proper_rank_eq_local hrun t]
    exact (Int.toNat_of_nonneg hnonnegT).symm
  have hrLT : rk run.proper.rank mL = rk run.proper.rank t := by
    rw [X_proper_rank_eq_local hrun mL, X_proper_rank_eq_local hrun t, hrL, hrT]
  have hrRT : rk run.proper.rank mR = rk run.proper.rank t := by
    rw [X_proper_rank_eq_local hrun mR, X_proper_rank_eq_local hrun t, hrR, hrT]
  obtain ⟨hframeLeft, hframeRight⟩ := foreign_frame_x_of_markers execution hwf hfp hcomp hrun
    hgroup hgroupBorder hpL hbL hnL hpR hbR hnR (hrLT.trans hrRT.symm)
  have hscope : actual.node.clusterPath.contains group.decl = false := by
    rw [hpT]
    exact Bool.eq_false_iff.mpr (fun h => hforeign (List.contains_iff_mem.mp h))
  have hbOwner : (cg.nodes.getD t default).border = 0 := by
    simp only [cg, List.getD_eq_getElem?_getD, howner, Option.getD_some, hplain]
  have hfootX : foot.x = RouteImpl.leftOf run.proper run.xs t +
      RouteImpl.nodeW run.proper t := by
    change (frameRect execution.params cg run t).x +
      (frameRect execution.params cg run t).w = _
    rw [plain_frame_eq_boxRect execution.params cg run t
      (List.getElem?_eq_some_iff.mp hpT').1 (by rw [hbOwner]; decide)] <;> rfl
  rcases XN_plainClearOfSideMarker_of_path exactIds (XN_plainNodePathResidual_holds exactIds)
    execution.graph0_eq execution.graph_eq hcomp hrun hpT' hbT hscope hpL hbL hnL hpR hbR hnR
    hrLT hrRT with hownerLeft | hgroupLeft
  · obtain ⟨hlayer, i, hi⟩ := foreign_layer_position hrun (r := r) hcT hrT
    obtain ⟨_, j, hj⟩ := foreign_layer_position hrun (r := r) hcL hrL
    have horder : i < j := by
      rcases Nat.lt_trichotomy i j with h | h | h
      · exact h
      · subst j
        have htm : t = mL := Option.some.inj (hi.symm.trans hj)
        subst mL
        have he := Option.some.inj (hcT.symm.trans hcL)
        rw [he, hbL] at hbT
        omega
      · have hord := XB_orderedIntervals_holds exactIds execution.graph0_eq execution.graph_eq
          hcomp hrun hlayer h hj hi hcL hcT hnpL hnpT
        have hwL := foreign_left_marker_positive execution hcomp hrun hcL hbL
        have hwT := (componentRunX_dims_nonneg hrun t actual hpT').1
        simp only [RouteImpl.nodeW, hpT', hpL] at hord hownerLeft
        omega
    have hlocal : t < comp.length := by
      simpa only [componentCandidate_nodes, componentGraph, List.length_map] using
        (List.getElem?_eq_some_iff.mp howner).1
    have hext := XLEMR_cg_node_extent execution hcomp rfl hrun hlocal howner hbOwner hcT
    have hreserve : foot.w ≤ (actual.node.loopExtent : Int) := by
      let sizes := loopSizes cg.edges execution.measured t cg.slot
      calc
        foot.w = (if run.exact.contains t then Loops.exactExtent cg.slot sizes
            else Loops.extent cg.slot sizes) := by
          change (if run.exact.contains t then Loops.exactExtent else Loops.extent) cg.slot sizes = _
          cases run.exact.contains t <;> rfl
        _ ≤ _ := hext
    have hgap := foreign_plain_later_center_gap hrun hcT hbT hcL hlayer hi hj horder
    have h := foreign_reserved_gap hpT' hpL hxT hxL hreserve hgap
    exact rect_disjoint_of_x (Or.inr (by rw [hfootX, hframeLeft]; exact h))
  · have hw := (componentRunX_dims_nonneg hrun t actual hpT').1
    have hw' : 0 ≤ RouteImpl.nodeW run.proper t := by
      simpa only [RouteImpl.nodeW, hpT'] using hw
    refine rect_disjoint_of_x (Or.inl ?_)
    rw [hframeRight, hfootX]
    omega

/-- The mutually foreign case of `XNonfwd_NonAncHullW`, for any successful
candidate run of the admitted input, independently of portfolio selection. -/
theorem exactNonforwardForeignHull_disjointW
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {t pos : Nat} {owner group : Node}
    (hloop : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges, e.tail = t ∧ e.head = t)
    (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hgroup : (componentCandidate execution.graph comp candidate).nodes[pos]? = some group)
    (hgroupBorder : group.border = -2)
    (hforeign : group.decl ∉ owner.clusterPath) (hreverse : owner.decl ∉ group.clusterPath) :
    Disjoint (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos)
      (loopFootprintExt (componentCandidate execution.graph comp candidate) run execution.measured t) := by
  rcases (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq howner).1 with
    hplain | htop | hbottom
  · exact exactNonforwardForeignHull_plain_disjoint execution hwf hfp hcomp hrun
      hloop howner hplain hgroup hgroupBorder hforeign
  · exact exactNonforwardForeignHull_group_disjoint execution hwf hfp hcomp hrun
      hloop howner htop hgroup hgroupBorder hforeign hreverse
  · exact (exactBottomNoLoopX execution comp candidate run orderOptions hcomp _ rfl
      hrun t owner howner hbottom hloop).elim

end Elegant.Layered.PipelineImpl

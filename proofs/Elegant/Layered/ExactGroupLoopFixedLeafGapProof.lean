import Elegant.Layered.ExactFlatForeignLoopProof
import Elegant.Layered.ExactGroupMarkerOrderProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem nonproxy_record {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hnd : run.coordinateProper.nodes[v]? = some nd)
    (hborder : ¬(nd.node.border = -2 ∨ nd.node.border = 2)) :
    run.proper.nodes[v]? = some nd ∧ run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hproper, hxs⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v nd hnd hborder
  rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  exact ⟨hproper, by simp only [List.getD_eq_getElem?_getD, hxs, Option.getD_some]⟩

private theorem candidate_slot (g : Graph) (comp : List Nat) (candidate : Nat) :
    (componentCandidate g comp candidate).slot = g.slot := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl

private theorem loop_band_nonneg (slot : Int) (sizes : List LoopLabel) (hslot : 0 ≤ slot) :
    0 ≤ Loops.band slot sizes := by
  have fold_nonneg (xs : List LoopLabel) (h : Int) (hh : 0 ≤ h) :
      0 ≤ xs.foldl (fun acc l => max acc l.height) h := by
    induction xs generalizing h with
    | nil => exact hh
    | cons _ _ ih => exact ih _ (Int.le_trans hh (Int.le_max_left _ _))
  exact fold_nonneg sizes (2 * slot) (by omega)

private theorem loop_width_pos (slot : Int) (sizes : List LoopLabel) (selected : Bool)
    (hslot : 0 < slot) (hne : sizes ≠ []) (hw : ∀ l ∈ sizes, 0 ≤ l.width) :
    0 < (if selected then Loops.exactExtent else Loops.extent) slot sizes := by
  cases sizes with
  | nil => exact False.elim (hne rfl)
  | cons first rest =>
    cases selected with
    | false =>
      have h := Loops.outer_label_extent slot (first :: rest) (by omega) hw first (by simp)
      have hm := Int.mul_pos hslot (show 0 < ((first :: rest).length : Int) + 1 by omega)
      have hw0 := hw first (by simp)
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    | true =>
      have fold_nonneg (xs : List LoopLabel) (w : Int) (hh : 0 ≤ w) :
          0 ≤ xs.foldl (fun acc l => max acc l.width) w := by
        induction xs generalizing w with
        | nil => exact hh
        | cons _ _ ih => exact ih _ (Int.le_trans hh (Int.le_max_left _ _))
      have hh := fold_nonneg (first :: rest) 0 (by omega)
      have hm := Int.mul_pos hslot (show 0 < 2 * ((first :: rest).length : Int) + 1 by omega)
      change 0 < slot * (2 * ((first :: rest).length : Int) + 1) +
        (first :: rest).foldl (fun acc l => max acc l.width) 0
      omega

set_option maxHeartbeats 800000 in
theorem required_height_le_group_top {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate t : Nat}
    {owner : Node} (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hgroup : owner.border = -2) (hextent : 0 < owner.loopExtent) :
    Loops.requiredHeight (componentCandidate execution.graph comp candidate).slot
      (loopSizes (componentCandidate execution.graph comp candidate).edges execution.measured t
        (componentCandidate execution.graph comp candidate).slot) ≤ owner.h := by
  obtain ⟨u, hu, hgraphOwner⟩ := componentCandidate_nonplain_source howner (by omega)
  have hu0 : u < execution.graph0.nodes.length := by
    rw [← exactGraph_length execution.graph_eq]
    exact (List.getElem?_eq_some_iff.mp hgraphOwner).1
  obtain ⟨base, hbase⟩ : ∃ n, execution.graph0.nodes[u]? = some n :=
    ⟨_, List.getElem?_eq_getElem hu0⟩
  obtain ⟨out, hout, hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hbase
  have houtEq : out = owner := Option.some.inj (hout.symm.trans hgraphOwner)
  have hbaseGroup : base.border = -2 := hborder.symm.trans (by rw [houtEq, hgroup])
  obtain ⟨hdecl, box, hbox, hrole, _⟩ := measuredGraph_group_origin execution.graph0_eq hbase hbaseGroup
  let boxes := inp.boxes.map fun b =>
    if inp.fixedSizes.any (fun f => f.1 == b.id) then { b with role := .node } else b
  have heffective : boxes[u]? = some box := by simpa only [boxes, hdecl] using hbox
  have huBoxes := (List.getElem?_eq_some_iff.mp heffective).1
  obtain ⟨source, hsource, hdemote⟩ := Option.map_eq_some_iff.mp
    (show (inp.boxes[u]?).map (fun b =>
      if inp.fixedSizes.any (fun f => f.1 == b.id) then { b with role := .node } else b) = some box by
      simpa only [boxes, List.getElem?_map] using heffective)
  have hfixed : inp.fixedSizes.any (fun f => f.1 == source.id) = false := by
    cases hf : inp.fixedSizes.any (fun f => f.1 == source.id) with
    | false => rfl
    | true =>
      simp only [hf, ↓reduceIte] at hdemote
      have hr := congrArg ModelBox.role hdemote
      rw [hrole] at hr
      cases hr
  have hfind : inp.fixedSizes.find? (fun f => f.1 == source.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hfixed)
  have hg := execution.graph_eq
  unfold exactGraph at hg
  obtain ⟨updated, hupdated, hg⟩ := bind_ok hg
  obtain ⟨nd, hstep, hnd⟩ := (mapM_getElem? _ _ _ hupdated).2 u base hbase
  have nodes_eq : execution.graph.nodes = updated :=
    congrArg Graph.nodes (Except.ok.inj hg).symm
  rw [nodes_eq] at hgraphOwner
  have nd_eq : nd = owner := Option.some.inj (hnd.symm.trans hgraphOwner)
  have hsame : base = owner := by
    cases he : exactIds.contains source.id with
    | false =>
      have h : (Except.ok base : Except LayoutError Node) = .ok nd := by
        simpa only [hdecl, hsource, he, hfixed, Bool.and_false, Bool.not_false,
          Bool.true_and, ↓reduceIte, pure, Except.pure] using hstep
      exact (Except.ok.inj h).trans nd_eq
    | true =>
      simp only [hdecl, hsource, he, hfixed, hfind, Bool.and_false, Bool.not_true,
        throw, throwThe, MonadExceptOf.throw] at hstep
      cases hstep
  obtain ⟨metric, labels, raw, hm, hl, _, hrawSlot, hprep, hreserve⟩ :=
    measuredGraph_loop_reservation_before_prepare execution.graph0_eq
  have hm' := Except.ok.inj (hm.symm.trans execution.metric_eq)
  subst metric
  have hl' := Except.ok.inj (hl.symm.trans execution.measured_eq)
  subst labels
  obtain ⟨nodes, _, titles, hprep', hlen, _⟩ := measuredGraph_prepared_source execution.graph0_eq
  let titleSizes := execution.lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * execution.params.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  change execution.graph0 = Compound.prepare boxes execution.params.clusterPad titleSizes raw at hprep
  have hrawlen : raw.nodes.length = execution.lines.length := by
    have h1 := congrArg (fun (g : Graph) => g.nodes.length) hprep
    have h2 := congrArg (fun (g : Graph) => g.nodes.length) hprep'
    change execution.graph0.nodes.length =
      (Compound.markNodes boxes execution.params.clusterPad titleSizes raw.nodes).length at h1
    change execution.graph0.nodes.length =
      (Compound.markNodes boxes execution.params.clusterPad titles nodes).length at h2
    rw [Compound.markNodes_length] at h1 h2
    exact (Nat.add_right_cancel (h1.symm.trans h2)).trans hlen
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    unfold boxLines at h
    simpa only [List.length_zipIdx] using Sequence.mapM_ok_length _ _ _ h
  have huRaw : u < raw.nodes.length := by
    rw [hrawlen, hlines]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hmark := Compound.prepare_group_title_record boxes execution.params.clusterPad titleSizes
    raw huRaw heffective hrole
  rw [← hprep, hbase] at hmark
  have hmarkEq := Option.some.inj hmark
  have hkeep := congrArg Node.loopExtent hmarkEq
  change base.loopExtent = raw.nodes[u].loopExtent at hkeep
  have hnonzero : ¬ ((raw.nodes[u].loopExtent == 0) = true) := by
    intro hz
    have hz' := beq_iff_eq.mp hz
    rw [← hkeep, hsame] at hz'
    exact Nat.lt_irrefl 0 (hz' ▸ hextent)
  have hheight := congrArg Node.h hmarkEq
  change base.h = (if raw.nodes[u].loopExtent == 0 then
    (titleSizes.getD u (0, 0)).2 + execution.params.clusterPad else
    max ((titleSizes.getD u (0, 0)).2 + execution.params.clusterPad) raw.nodes[u].h) at hheight
  rw [ite_eq_right hnonzero] at hheight
  have hslot0 : execution.graph0.slot = execution.params.slot := by
    rw [hprep]
    exact hrawSlot
  have hslotX : execution.graph.slot = execution.graph0.slot := by
    rw [← Except.ok.inj hg]
  have ht := (List.getElem?_eq_some_iff.mp hu).1
  have hkey := (List.getElem?_eq_some_iff.mp hu).2
  rw [candidate_slot, hslotX,
    componentCandidate_loopSizes_preserved execution.graph comp (components_nodup _ _ hcomp)
      candidate t ht execution.measured execution.graph0.slot,
    hkey, exactGraph_edges execution.graph_eq, hslot0]
  have hrawSizes := prepare_loopSizes_preserved boxes execution.params.clusterPad titleSizes
    raw u huBoxes execution.measured execution.params.slot
  rw [← hprep] at hrawSizes
  rw [hrawSizes, ← hsame, hheight]
  exact Int.le_trans (hreserve u _ (List.getElem?_eq_getElem huRaw)) (Int.le_max_right _ _)

theorem group_title_record {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {t : Nat} {owner : Node} (howner : cg.nodes[t]? = some owner) (hgroup : owner.border = -2) :
    ∃ (v : Nat), run.proper.nodes[v]? = some (copyF (⟨owner, false, none, false⟩, t)) := by
  obtain ⟨_, _, labeled, _, hnorm, hlabeled, hcoord, _⟩ := componentRunX_spec hrun
  let nd : ProperNode := ⟨owner, false, none, false⟩
  have hlabel : labeled.nodes[t]? = some nd :=
    addLabelNodes_untouched_node hlabeled (normalize_node_record hnorm howner) rfl
  let sized := sizeProperPortsX P exact labeled
  have hsize : sized.nodes[t]? = some nd := by
    have hb : (nd.node.border != 0) = true := by
      change (owner.border != 0) = true
      rw [hgroup]
      decide
    change (sizeProperPortsX P exact labeled).nodes[t]? = some nd
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hlabel, Option.map_some]
    simp [hb]
  have hin : (nd, t) ∈ titleNodes sized := by
    unfold titleNodes
    apply List.mem_filter.mpr
    exact ⟨List.mem_zipIdx_iff_getElem?.mpr hsize, by simp [nd, hgroup]⟩
  let titled := titleReservations sized
  have htitle : copyF (nd, t) ∈ titled.nodes := by
    change copyF (nd, t) ∈ (titleReservations sized).nodes
    rw [titleReservations_nodes]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hin, rfl⟩)
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra titled P.clusterBorderW
  have hborderMem : copyF (nd, t) ∈ (OrderImpl.addClusterBorders titled P.clusterBorderW).nodes := by
    rw [hborder]
    exact List.mem_append_left extra htitle
  obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hborderMem
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes[v]? =
      some (copyF (nd, t)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hv]
    simp [clearF, copyF]
  obtain ⟨actual, hactual, _⟩ := materialize_exists _ hclear
  obtain ⟨before, hbefore, _, _, _, hsame⟩ := materialize_lookup _ hactual
  have hb := Option.some.inj (hbefore.symm.trans hclear)
  subst before
  have heq : actual = copyF (nd, t) := hsame rfl
  subst actual
  have hcp : run.coordinateProper.nodes[v]? = some (copyF (nd, t)) := by
    rw [← hcoord]
    exact hactual
  exact ⟨v, (nonproxy_record hrun hcp (by simp [copyF])).1⟩

/-- A target band overlapping a group's member hull has group members on both
sides of that rank, allowing either witness to be in the target rank itself. -/
theorem componentRunX_group_member_rank_bracket {exactIds : List String} {inp : Input}
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {t v : Nat} {owner : Node} (howner : cg.nodes[t]? = some owner) (hgroup : owner.border = -2)
    {target : ProperNode} (htarget : run.proper.nodes[v]? = some target)
    (hne : groupMemberRects cg run owner.decl ≠ [])
    (hoverlap : max (frameRect P cg run t).y (run.ys.getD v 0) <
      min ((frameRect P cg run t).y + (frameRect P cg run t).h)
        (run.ys.getD v 0 + RouteImpl.nodeH run.proper v)) :
    (∃ low nd, run.proper.nodes[low]? = some nd ∧ nd.node.clusterPath.contains owner.decl = true ∧
      (rk run.proper.rank low).toNat ≤ (rk run.proper.rank v).toNat) ∧
    (∃ high nd, run.proper.nodes[high]? = some nd ∧ nd.node.clusterPath.contains owner.decl = true ∧
      (rk run.proper.rank v).toNat ≤ (rk run.proper.rank high).toNat) := by
  let r := (rk run.proper.rank v).toNat
  obtain ⟨ly, hly, _, htop, hbot⟩ :=
    componentRunX_node_rank_band hrun (List.getElem?_eq_some_iff.mp htarget).1
  have hdisj := (X_ReserveBands_holds exactIds hrun).2
  rw [frameRect_group_span howner hgroup] at hoverlap
  dsimp only at hoverlap
  constructor
  · apply Classical.byContradiction
    intro hlow
    have habove := boundsOf_minY_ge_of_all hne (lo := run.ys.getD v 0 + RouteImpl.nodeH run.proper v)
      (fun rect hrect => by
        obtain ⟨q, nd, hq, hmember, heq⟩ := groupMemberRects_inv hrect
        have hnot : ¬ (rk run.proper.rank q).toNat ≤ r :=
          fun hh => hlow ⟨q, nd, hq, hmember, hh⟩
        have hlt : r < (rk run.proper.rank q).toNat := by omega
        obtain ⟨lq, hlq, _, htopq, _⟩ :=
          componentRunX_node_rank_band hrun (List.getElem?_eq_some_iff.mp hq).1
        have hgap := hdisj r _ ly lq hlt hly hlq
        rw [heq, rectAt_eq]
        change run.ys.getD v 0 + RouteImpl.nodeH run.proper v ≤ run.ys.getD q 0
        exact Int.le_trans hbot (Int.le_trans hgap htopq))
    omega
  · apply Classical.byContradiction
    intro hhigh
    have hyn := Int.le_trans (XB_topNonneg_holds exactIds hrun r) htop
    have hbelow := boundsOf_bottom_le_of_all hyn (rects := groupMemberRects cg run owner.decl)
      (fun rect hrect => by
        obtain ⟨q, nd, hq, hmember, heq⟩ := groupMemberRects_inv hrect
        have hnot : ¬ r ≤ (rk run.proper.rank q).toNat :=
          fun hh => hhigh ⟨q, nd, hq, hmember, hh⟩
        have hlt : (rk run.proper.rank q).toNat < r := by omega
        obtain ⟨lq, hlq, _, _, hbotq⟩ :=
          componentRunX_node_rank_band hrun (List.getElem?_eq_some_iff.mp hq).1
        have hgap := hdisj _ r lq ly hlt hlq hly
        rw [heq, rectAt_eq]
        change run.ys.getD q 0 + RouteImpl.nodeH run.proper q ≤ run.ys.getD v 0
        exact Int.le_trans hbotq (Int.le_trans hgap htop))
    omega

private theorem right_marker_hull {P : Params} {cg : Graph} {run : Run} {t mL mR : Nat}
    {owner : Node} (howner : cg.nodes[t]? = some owner) (hgroup : owner.border = -2)
    {ndR : ProperNode} (hproperR : run.proper.nodes[mR]? = some ndR)
    (hbR : ndR.node.border = 1) (hlastR : ndR.node.clusterPath.getLast? = some owner.decl)
    (hshare : ∀ {q : Nat} {nd : ProperNode}, run.proper.nodes[q]? = some nd →
      nd.node.clusterPath.getLast? = some owner.decl →
      ((nd.node.border = -1 →
        RouteImpl.leftOf run.proper run.xs q = RouteImpl.leftOf run.proper run.xs mL ∧
        RouteImpl.leftOf run.proper run.xs q + RouteImpl.nodeW run.proper q =
          RouteImpl.leftOf run.proper run.xs mL + RouteImpl.nodeW run.proper mL) ∧
      (nd.node.border = 1 →
        RouteImpl.leftOf run.proper run.xs q = RouteImpl.leftOf run.proper run.xs mR ∧
        RouteImpl.leftOf run.proper run.xs q + RouteImpl.nodeW run.proper q =
          RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR)))
    (hcross : RouteImpl.leftOf run.proper run.xs mL + RouteImpl.nodeW run.proper mL ≤
      RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR)
    (hnonneg : 0 ≤ RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR) :
    (frameRect P cg run t).x + (frameRect P cg run t).w =
      RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR := by
  have hm : Labels.rectAt run.proper run.xs run.ys mR ∈ groupBorderRects cg run owner.decl :=
    groupBorderRects_mem_of_record hproperR (Or.inr hbR) hlastR
  have hge := (boundsOf_rect_mem hm).2
  rw [rectAt_eq] at hge
  dsimp only at hge
  have hle := boundsOf_right_le_of_all hnonneg (rects := groupBorderRects cg run owner.decl)
    (fun rect hrect => by
      obtain ⟨v, nd, hv, hb, hl, he⟩ := groupBorderRects_inv hrect
      rw [he, rectAt_eq]
      dsimp only
      rcases hb with hb | hb
      · rw [((hshare hv hl).1 hb).2]
        exact hcross
      · rw [((hshare hv hl).2 hb).2] <;> exact Int.le_refl _)
  rw [frameRect_group_span howner hgroup]
  dsimp only
  omega

set_option maxHeartbeats 1200000 in
/-- On an executed, well-formed framed run, a vertically overlapping plain
frame is outside a looping group's horizontal reservation. The layout does
not need to know whether the plain frame came from a fixed leaf. -/
theorem componentRunX_groupLoop_footprint_horizontal_gap {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat}
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph comp candidate).edges[i]? = some edge)
    (hself : edge.tail = edge.head) {owner target : Node} {v : Nat}
    (howner : (componentCandidate execution.graph comp candidate).nodes[edge.tail]? = some owner)
    (hgroup : owner.border = -2)
    (htarget : (componentCandidate execution.graph comp candidate).nodes[v]? = some target)
    (hplain : target.border = 0) :
    let cg := componentCandidate execution.graph comp candidate
    let foot := loopFootprintExt cg run execution.measured edge.tail
    let frame := frameRect execution.params cg run v
    max foot.y frame.y < min (foot.y + foot.h) (frame.y + frame.h) →
    foot.x + foot.w ≤ frame.x ∨ frame.x + frame.w ≤ foot.x := by
  let cg := componentCandidate execution.graph comp candidate
  let sizes := loopSizes cg.edges execution.measured edge.tail cg.slot
  let group := frameRect execution.params cg run edge.tail
  let frame := frameRect execution.params cg run v
  let foot := loopFootprintExt cg run execution.measured edge.tail
  change (max foot.y frame.y < min (foot.y + foot.h) (frame.y + frame.h)) →
    foot.x + foot.w ≤ frame.x ∨ frame.x + frame.w ≤ foot.x
  intro hy
  have hloops : ∃ e ∈ cg.edges, e.tail = edge.tail ∧ e.head = edge.tail :=
    ⟨edge, List.mem_of_getElem? hedge, rfl, hself.symm⟩
  have hmarkers := XLEG_groupMarkerOrderX_of_leaves exactIds
    (xleg_loopMarkerCoreX_holds exactIds) (xleg_loopMarkerLayerOrderX_holds exactIds)
    (xleg_loopMarkerSpanX_holds exactIds)
    inp o res execution hwf hfp comp candidate run orderOptions cg hcomp rfl hrun
  obtain ⟨mL, mR, _, ndR, _, hmR, _, hbR, _, hlastR, hextR, _, hshare, _, hcross, hnonneg, _⟩ :=
    hmarkers.2 edge.tail owner howner hloops hgroup
  have hnpR : ¬(ndR.node.border = -2 ∨ ndR.node.border = 2) := by rw [hbR]; decide
  have hproperR := (nonproxy_record hrun hmR hnpR).1
  have hhull := right_marker_hull (P := execution.params) howner hgroup hproperR hbR hlastR
    hshare hcross hnonneg
  have hslot : 0 < cg.slot := by
    have hp : 1 ≤ execution.params.slot := (checkedParams_valid execution.checked).2.2.1
    have hg := execution.graph_eq
    unfold exactGraph at hg
    obtain ⟨_, _, hg⟩ := bind_ok hg
    have hs : execution.graph.slot = execution.graph0.slot := by
      rw [← Except.ok.inj hg]
    obtain ⟨_, _, _, hprep, _, _⟩ := measuredGraph_prepared_source execution.graph0_eq
    have hs0 := congrArg Graph.slot hprep
    change execution.graph0.slot = execution.params.slot at hs0
    change 0 < (componentCandidate execution.graph comp candidate).slot
    rw [candidate_slot, hs, hs0]
    omega
  have hsizes : sizes ≠ [] := by
    intro h
    have hem : edge ∈ loopEdges cg.edges edge.tail := by
      unfold loopEdges
      apply List.mem_filter.mpr
      exact ⟨List.mem_of_getElem? hedge, by simp [hself]⟩
    have hm : stackSize cg.slot (routeLabels execution.measured edge.decl) ∈ sizes := by
      unfold sizes loopSizes
      exact List.mem_map.mpr ⟨edge, hem, rfl⟩
    rw [h] at hm
    cases hm
  have hw : ∀ l ∈ sizes, 0 ≤ l.width := by
    intro l hl
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hl
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hfootW : 0 < foot.w := loop_width_pos cg.slot sizes (run.exact.contains edge.tail) hslot hsizes hw
  have hfootWidth : foot.w =
      (if run.exact.contains edge.tail then Loops.exactExtent cg.slot sizes
       else Loops.extent cg.slot sizes) := by
    change (if run.exact.contains edge.tail then Loops.exactExtent else Loops.extent) cg.slot sizes = _
    cases run.exact.contains edge.tail <;> rfl
  have hextCopy := xleg_rightMarker_copies_extent execution.graph0_eq execution.graph_eq
    hcomp hrun howner hgroup hmR hbR hlastR
  have hownerExtent : 0 < owner.loopExtent := by
    have hwidth : foot.w ≤ (owner.loopExtent : Int) := by
      rw [hfootWidth, ← hextCopy]
      exact hextR
    omega
  have hheight := required_height_le_group_top execution hcomp howner hgroup hownerExtent
  change Loops.requiredHeight cg.slot sizes ≤ owner.h at hheight
  obtain ⟨title, htitle⟩ := group_title_record hrun howner hgroup
  obtain ⟨_, _, hpath⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq howner hgroup
  have htitlePath : (copyF (⟨owner, false, none, false⟩, edge.tail)).node.clusterPath.contains
      owner.decl = true := by
    change owner.clusterPath.contains owner.decl = true
    simp [hpath]
  have hmem : Labels.rectAt run.proper run.xs run.ys title ∈ groupMemberRects cg run owner.decl :=
    fbs_groupMemberRects_mem htitle htitlePath
  have hgroupH : owner.h ≤ group.h := by
    have hh := boundsOf_height_ge_member hmem
    rw [rectAt_eq] at hh
    change RouteImpl.nodeH run.proper title ≤ _ at hh
    simp only [RouteImpl.nodeH, htitle, copyF] at hh
    change owner.h ≤ (frameRect execution.params cg run edge.tail).h
    rw [frameRect_group_span howner hgroup]
    exact hh
  have hb := loop_band_nonneg cg.slot sizes (by omega)
  have hprod := Int.mul_nonneg (show 0 ≤ (sizes.length : Int) by omega) hb
  have hfit : (sizes.length : Int) * Loops.band cg.slot sizes ≤ group.h := by
    unfold Loops.requiredHeight at hheight
    rw [Int.mul_assoc] at hheight
    omega
  have hfootY : foot.y = group.y := rfl
  have hfootH : foot.h = group.h := by
    change max group.h ((sizes.length : Int) * Loops.band cg.slot sizes) = group.h
    exact Int.max_eq_left hfit
  have hget : cg.nodes.getD v default = target := by
    change (componentCandidate execution.graph comp candidate).nodes.getD v default = target
    rw [List.getD_eq_getElem?_getD, htarget, Option.getD_some]
  obtain ⟨_, _, labeled, _, hnorm, hlab, hcoord, _, _, _, _, hlanes, _, _⟩ := componentRunX_spec hrun
  have hlabeled := addLabelNodes_untouched_node hlab (normalize_node_record hnorm htarget) rfl
  obtain ⟨actual, hactual, _, hbV, _, _⟩ :=
    coordinateGraphX_plain_anchor_dims (exact := exactDecls exactIds inp)
      execution.params hlabeled hplain
  rw [hcoord] at hactual
  have hnpV : ¬(actual.node.border = -2 ∨ actual.node.border = 2) := by rw [hbV]; decide
  obtain ⟨hpV, hxV⟩ := nonproxy_record hrun hactual hnpV
  have hframe : frame = ⟨RouteImpl.leftOf run.proper run.xs v, run.ys.getD v 0,
      actual.node.w, actual.node.h⟩ := by
    change frameRect execution.params cg run v = _
    unfold frameRect
    simp only [hget, hplain, show ((0 : Int) != -2) = true from rfl, ↓reduceIte]
    exact nodeRect_of_record hpV
  have hnH : RouteImpl.nodeH run.proper v = actual.node.h := by simp only [RouteImpl.nodeH, hpV]
  rw [hfootY, hfootH, hframe, ← hnH] at hy
  have hne : groupMemberRects cg run owner.decl ≠ [] := by
    intro h
    rw [h] at hmem
    cases hmem
  obtain ⟨⟨low, lowNd, hlow, hcLow, hrLow⟩, ⟨high, highNd, hhigh, hcHigh, hrHigh⟩⟩ :=
    componentRunX_group_member_rank_bracket hrun howner hgroup hpV hne hy
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    unfold boxLines at h
    simpa only [List.length_zipIdx] using Sequence.mapM_ok_length _ _ _ h
  obtain ⟨_, right, _, nd, _, _, _, _, hcR, hbRight, hlastRight, hrightRank⟩ :=
    XN_bracketMarkersAtRank_holds exactIds execution.graph0_eq execution.graph_eq hlines hwf hfp
      hcomp hrun (rk run.proper.rank v).toNat hlow hcLow hrLow hhigh hcHigh hrHigh
  have hnp : ¬(nd.node.border = -2 ∨ nd.node.border = 2) := by rw [hbRight]; decide
  obtain ⟨hpRight, hxRight⟩ := nonproxy_record hrun hcR hnp
  have hcover := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hlanes).1).2.2.2.1
  obtain ⟨layer, hlayer, hmemV, _⟩ := hcover v (List.getElem?_eq_some_iff.mp hpV).1
  obtain ⟨layerR, hlayerR, hmemR, _⟩ := hcover right (List.getElem?_eq_some_iff.mp hpRight).1
  rw [X_proper_rank_eq_local hrun right, hrightRank, Int.toNat_natCast, hlayer] at hlayerR
  have heqLayers : layer = layerR := Option.some.inj hlayerR
  subst layerR
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmemR
  obtain ⟨iv, hiv⟩ := List.mem_iff_getElem?.mp hmemV
  have hRight := ((hshare hpRight hlastRight).2 hbRight).2
  have hfootX : foot.x = RouteImpl.leftOf run.proper run.xs right + RouteImpl.nodeW run.proper right := by
    calc
      foot.x = group.x + group.w := rfl
      _ = _ := hhull.trans hRight.symm
  rcases Nat.lt_trichotomy j iv with hbefore | heq | hafter
  · left
    have hgap := xleg_rightMarker_later_gap hrun hcR hbRight hactual
      (List.mem_of_getElem? hlayer) hj hiv hbefore
    have hext : foot.w ≤ (nd.node.loopExtent : Int) := by
      rw [hfootWidth]
      exact xleg_rightMarker_extent_ge execution hcomp hrun howner hgroup hcR hbRight hlastRight
    rw [hfootX, hframe]
    simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW, hpRight, hpV, hxRight, hxV,
      Int.fdiv_eq_ediv_of_nonneg _ (by decide : 0 ≤ (2 : Int))] at hgap ⊢
    omega
  · subst iv
    have hv : right = v := Option.some.inj (hj.symm.trans hiv)
    subst right
    have hnd := Option.some.inj (hcR.symm.trans hactual)
    rw [hnd, hbV] at hbRight
    omega
  · right
    have hordered := XB_orderedIntervals_holds exactIds execution.graph0_eq execution.graph_eq
      hcomp hrun (List.mem_of_getElem? hlayer) hafter hiv hj hactual hcR hnpV hnp
    have hwidth := (componentRunX_dims_nonneg hrun) right nd hpRight |>.1
    rw [hfootX, hframe]
    simp only [RouteImpl.nodeW, hpRight, hpV] at hordered ⊢
    omega

/-- Discharge the fixed-leaf seam using the stronger plain-frame gap. -/
theorem exactGroupLoopFixedLeafGap_holds (exactIds : List String) : ExactGroupLoopFixedLeafGap exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run hrun i edge hedge hself
    owner v key target source entry howner hgroup _hkey _hsource _hfixed _hleaf htarget hplain
    _houtside _hrank
  dsimp only
  intro _hwidth hoverlap
  exact componentRunX_groupLoop_footprint_horizontal_gap execution hwf hfp hcomp hrun
    hedge hself howner hgroup htarget hplain hoverlap

/-- A self-loop in a successful exact layout misses the rendered frame of any fixed leaf
    when the input is well formed and its parents are framed. -/
theorem layoutX_selfLoop_fixedLeaf_frame_miss
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutX exactIds inp o = .ok res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {boxId : String} {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun row => row.1 == boxId) = some entry)
    (hleaf : ExactFixedLeaf inp boxId)
    {frame : Box} (hframe : res.scene.boxes.find? (fun box => box.id == boxId) = some frame)
    {route : Route} (hroute : route ∈ res.scene.routes) (hself : route.fromId = route.toId) :
    ¬ Polyline.hitsRect route.points frame.rect :=
  layoutX_selfLoop_fixedLeaf_frame_miss_of_group_gap h hwf hfp
    (exactGroupLoopFixedLeafGap_holds exactIds) hfixed hleaf hframe hroute hself

end Elegant.Layered.PipelineImpl

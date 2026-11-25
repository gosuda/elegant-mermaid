import Elegant.Layered.ExactForeignBorderSpansProof
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ComponentRunGen
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.SizingFacts
import Elegant.Layered.Coords
import Elegant.Layered.CgShape
import Elegant.Layered.Labels
import Elegant.Layered.Normalize
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Order
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.Pipeline

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open CoordsImpl

/-! # Exact border-span run facts

Proves the three single-fact residuals of `XB_foreignBorderSpansSeparated_holds`
(`ExactForeignBorderSpansProof.lean`):

* `XB_orderedIntervals_holds`: replay of `componentRun_nonproxy_ordered_intervals`
  over `componentRunX_spec`, via the shared `X_cg_run_bundle` and prefixed copies
  of the `ExactFlatC2`/`ExactC8aSpansProof` private helpers.
* `XB_topNonneg_holds`: replay of `fbs_run_top_nonneg`: pre-reserve tops are
  nonnegative and `reserveExactRanks` only adds nonnegative prefix shifts.
* `XB_memberNonempty_holds`: replay of `fbs_group_node_member` over the exact
  bundle and marker record, with the group-box origin transported across
  `exactGraph` by `X_cg_group_box`.
-/

/-! ## Reserved-top nonnegativity helpers -/

/-- Prefix sums of a nonnegative list stay nonnegative. -/
private theorem XBbs_prefix_mem_nonneg (es : List Int) (s : Int) (out : List Int)
    (hs : 0 ≤ s) (ho : ∀ x ∈ out, 0 ≤ x) (hnn : ∀ e ∈ es, 0 ≤ e) :
    ∀ x ∈ (es.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (s, out)).2, 0 ≤ x := by
  induction es generalizing s out with
  | nil => simpa using ho
  | cons e es ih =>
    simp only [List.foldl_cons]
    exact ih (s + e) (out ++ [s]) (by have he := hnn e List.mem_cons_self; omega)
      (by
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with hx | hx
        · exact ho x hx
        · simp only [List.mem_singleton] at hx
          rw [hx]
          exact hs)
      (fun a ha => hnn a (List.mem_cons_of_mem _ ha))

/-- A shift-vector entry read with `getD` is nonnegative. -/
private theorem XBbs_prefix_getD_nonneg (extra : List Int) (hnn : ∀ e ∈ extra, 0 ≤ e)
    (r : Nat)
    (hr : r < ((extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).length) :
    0 ≤ ((extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).getD r 0 := by
  have hmem := List.mem_of_getElem? (List.getElem?_eq_getElem hr)
  have hnn2 := XBbs_prefix_mem_nonneg extra 0 [] (Int.le_refl 0) (by simp) hnn _ hmem
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  exact hnn2

/-- Every reserved rank top of an executed exact run is nonnegative. -/
theorem XB_topNonneg_holds (exactIds : List String) : XB_TopNonneg exactIds := by
  intro P inp cg run labels orderOptions hrun k
  have hrunGen : componentRunGen P (sizeProperPortsX P (exactDecls exactIds inp))
      (reserveExactRanks cg (exactDecls exactIds inp) labels)
      (cg.nodes.zipIdx.filterMap fun q => if (exactDecls exactIds inp).contains q.1.decl then some q.2 else none)
      cg labels orderOptions = .ok run := by
    rw [← componentRunX_eq_gen]
    exact hrun
  obtain ⟨_ranks, _p0, _labeled, _q0, _ypre, top_pre, ys_pre, _hn, _hl, _hcoord, _hord, _hcross,
    _hproxy, _hdrop, _hrouteWL, _hrouting, hry, _hyspre, hres, _hcy, _hroutes, _hexact⟩ :=
    componentRunGen_spec hrunGen
  obtain ⟨extra, shifts, _hlen, hnn, hpref, _hlenS, htop, _hys⟩ :=
    (runHooksShift_exact P exactIds inp cg labels).shifts
      run.coordinateProper run.layers ys_pre top_pre run.ys run.top hres
  have hpre : ∀ k, 0 ≤ top_pre.getD k 0 := by
    obtain ⟨hg, hslot, _hlen2, hsnn, _hsz, htopEq, _hy⟩ := CoordsImpl.rankCoordsWith_spec hry
    have hheights : ∀ x ∈ run.layers.map (CoordsImpl.layerHeight run.coordinateProper),
        0 ≤ x := by
      intro x hx
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hx
      exact CoordsImpl.layerHeight_nonneg _ _
    have hsteps : ∀ x ∈ CoordsImpl.rankSteps P.rankGap P.slot run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots)), 0 ≤ x :=
      CoordsImpl.rankSteps_nonneg (by omega) (by omega) _ _ _ hsnn
    intro k
    rw [htopEq, List.getD_eq_getElem?_getD]
    cases hk : (CoordsImpl.topsFrom 0 1 0
        (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
        (CoordsImpl.rankSteps P.rankGap P.slot run.coordinateProper run.layers
          (run.routing.gaps.map (·.slots))))[k]? with
    | none => exact Int.le_refl 0
    | some t =>
      exact CoordsImpl.topsFrom_ge 0 1 (Int.le_refl 0) (by decide) _ _ _ hheights hsteps t
        (List.mem_of_getElem? hk)
  have hshiftsNN : ∀ r : Nat, 0 ≤ shifts.getD r 0 := by
    intro r
    rw [hpref]
    by_cases hr : r < ((extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).length
    · exact XBbs_prefix_getD_nonneg extra hnn r hr
    · cases hkk : ((extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2)[r]? with
      | none =>
        rw [List.getD_eq_getElem?_getD, hkk]
        exact Int.le_refl 0
      | some t =>
        exfalso
        have hlt := (List.getElem?_eq_some_iff.mp hkk).1
        omega
  have htopLen : run.top.length = top_pre.length := by
    unfold reserveExactRanks at hres
    obtain ⟨topNew, htopM, h1⟩ := bind_ok hres
    obtain ⟨_ysNew, _hysM, h2⟩ := bind_ok h1
    have hpair := Except.ok.inj h2
    have htopNew_eq : topNew = run.top := congrArg Prod.snd hpair
    obtain ⟨hlenM, _⟩ := mapM_getElem? _ _ _ htopM
    rw [htopNew_eq, List.length_zipIdx] at hlenM
    exact hlenM
  by_cases hk : k < top_pre.length
  · rw [htop k hk]
    have h1 := hpre k
    have h2 := hshiftsNN k
    omega
  · have hk' : ¬ k < run.top.length := by omega
    cases hkk : run.top[k]? with
    | none =>
      rw [List.getD_eq_getElem?_getD, hkk]
      exact Int.le_refl 0
    | some t =>
      exfalso
      have hlt := (List.getElem?_eq_some_iff.mp hkk).1
      omega

/-! ## Ordered-intervals helpers (prefixed copies) -/

/-- Exact bordered-graph node classification. -/
private theorem XBbs_coordinateGraph0_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.clusterPath = m.node.clusterPath ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = q.1.node.clusterPath) := by
  rw [clearProxyExtents_nodes] at h
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  rw [hx] at h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hl, rfl⟩ := h
  have hlen : (sizeProperPortsX P exact p).nodes.length = p.nodes.length :=
    sizeProperPortsX_length P exact p
  obtain ⟨c1, c2, c3, c4⟩ := clearF_keys m
  by_cases hv1 : v < (titleReservations (sizeProperPortsX P exact p)).nodes.length
  · rw [List.getElem?_append_left hv1] at hl
    rw [titleReservations_nodes] at hl hv1
    by_cases hv2 : v < (sizeProperPortsX P exact p).nodes.length
    · rw [List.getElem?_append_left (by simpa using hv2)] at hl
      left
      cases hs : (sizeProperPortsX P exact p).nodes[v]? with
      | none => simp [List.getElem?_map, hs] at hl
      | some s =>
        simp only [List.getElem?_map, hs, Option.map_some, Option.some.injEq] at hl
        subst hl
        have hk := sizeProperPortsX_key P exact p v
        rw [hs] at hk
        cases hp : p.nodes[v]? with
        | none => simp [hp] at hk
        | some mp =>
          simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨hd, hb, hpth⟩ := hk
          obtain ⟨t1, t2, t3, t4⟩ := titleF_keys s
          refine ⟨mp, rfl, ?_, ?_, ?_, ?_⟩
          · rw [c1, t1, hd]
          · rw [c2, t2, hb]
          · rw [c3, t3, hpth]
          · intro hbd
            rw [c4]
            exact t4 (by rw [← t2, ← c2]; exact hbd)
    · right; right
      rw [List.getElem?_append_right (by simpa [hlen] using hv2)] at hl
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hl
      obtain ⟨q, hq, rfl⟩ := hl
      refine ⟨v - (sizeProperPortsX P exact p).nodes.length, q, ?_, by omega, ?_, ?_, ?_⟩
      · simpa [hlen] using hq
      · rw [c1]; rfl
      · rw [c2]; rfl
      · rw [c3]; rfl
  · rw [List.getElem?_append_right (by omega)] at hl
    right; left
    obtain ⟨e1, e2⟩ := hall m (List.mem_of_getElem? hl)
    refine ⟨(clearF_keys m).1.trans e1, ?_⟩
    rw [(clearF_keys m).2.1]
    exact e2

/-- Exact coordinate-graph node classification. -/
private theorem XBbs_coordinateGraph_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphX P exact p).nodes[v]? = some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      (m.dummy = false → nd.node.clusterPath = m.node.clusterPath) ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      (q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath)) := by
  unfold coordinateGraphX at h
  obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup _ h
  rcases XBbs_coordinateGraph0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
    ⟨i, q, hq, hv, h1, h2, h3⟩
  · refine Or.inl ⟨m, hm, hd.trans h1, hb.trans h2, fun hf => ?_, fun hbd => ?_⟩
    · have : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd this]
      exact h3
    · rw [hh]
      exact h4 (by rw [← hb]; exact hbd)
  · exact Or.inr (Or.inl ⟨by rw [hd]; exact h1, by rw [hb]; exact h2⟩)
  · refine Or.inr (Or.inr ⟨i, q, hq, hv, hd.trans h1, hb.trans h2, fun hf => ?_⟩)
    have : m1.dummy = false := by rw [h1]; exact hf
    rw [hnd this]
    exact h3

/-- Exact coordinate titles are unique per cluster path. -/
private theorem XBbs_pc_title_unique {cg : Graph} {P : Params} {exact : List Nat}
    {labeled : Proper} (hK : NodeKeys cg labeled)
    (hS : CgShape cg) {a b : Nat} {na nb : ProperNode}
    (ha : (coordinateGraphX P exact labeled).nodes[a]? = some na)
    (hb : (coordinateGraphX P exact labeled).nodes[b]? = some nb)
    (h1 : na.node.border = 3) (h2 : nb.node.border = 3)
    (hp : na.node.clusterPath = nb.node.clusterPath) : a = b := by
  have key : ∀ {v : Nat} {nd : ProperNode},
      (coordinateGraphX P exact labeled).nodes[v]? = some nd →
      nd.node.border = 3 →
      ∃ (i : Nat) (q : ProperNode × Nat),
        (titleNodes (sizeProperPortsX P exact labeled))[i]? = some q ∧
        v = labeled.nodes.length + i ∧ nd.node.clusterPath = q.1.node.clusterPath := by
    intro v nd h hb3
    rcases XBbs_coordinateGraph_lookup P exact labeled h with ⟨m, hm, _, h1, _, _⟩ | ⟨_, h1⟩ |
      ⟨i, q, hq, hv, hqd, _, h4⟩
    · rcases hK v m hm with ⟨n, hn, _, hb, _⟩ | ⟨_, hb, _⟩
      · exact absurd (by rw [← hb, ← h1]; exact hb3) (hS.2 n (List.mem_of_getElem? hn))
      · rw [hb] at h1; omega
    · omega
    · obtain ⟨hs, hbq⟩ := titleNodes_spec hq
      have hk := sizeProperPortsX_key P exact labeled q.2
      rw [hs] at hk
      cases hp : labeled.nodes[q.2]? with
      | none => simp [hp] at hk
      | some mp =>
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hk1, hk2, _⟩ := hk
        rcases hK q.2 mp hp with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
        · exact ⟨i, q, hq, hv, h4 (by rw [hk1]; exact hmd)⟩
        · rw [hk2] at hbq
          rw [hb'] at hbq
          exact absurd hbq (by decide)
  obtain ⟨i, qi, hqi, hvi, hpi⟩ := key ha h1
  obtain ⟨j, qj, hqj, hvj, hpj⟩ := key hb h2
  obtain ⟨hsi, hbi⟩ := titleNodes_spec hqi
  obtain ⟨hsj, hbj⟩ := titleNodes_spec hqj
  have kI := sizeProperPortsX_key P exact labeled qi.2
  have kJ := sizeProperPortsX_key P exact labeled qj.2
  rw [hsi] at kI
  rw [hsj] at kJ
  cases hli : labeled.nodes[qi.2]? with
  | none => simp [hli] at kI
  | some mi =>
    cases hlj : labeled.nodes[qj.2]? with
    | none => simp [hlj] at kJ
    | some mj =>
      simp only [hli, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kI
      simp only [hlj, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kJ
      have hidx : qi.2 = qj.2 :=
        labeled_topUnique hK hS hli hlj (by rw [← kI.2.1]; exact hbi)
          (by rw [← kJ.2.1]; exact hbj)
          (by rw [← kI.2.2, ← kJ.2.2, ← hpi, ← hpj]; exact hp)
      have hij : i = j :=
        nodup_map_inj_aux (·.2) (titleNodes_snd_nodup _) hqi hqj hidx
      rw [hvi, hvj, hij]

/-- Exact proper nodes transfer unchanged for non-proxy borders. -/
private theorem XBbs_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

set_option maxHeartbeats 2000000 in
/-- On a layer of an executed exact run, a node left of another ends before
the other starts. -/
theorem XB_orderedIntervals_holds (exactIds : List String) :
    XB_OrderedIntervals exactIds := by
  intro P inp o lines measured graph0 graph h0 h comp hcomp candidate run labels
    orderOptions hrun layer hlayer i j a b first second hij ha hb hfirst hsecond
    hfirstBorder hsecondBorder
  obtain ⟨rr, labeled, hrr, hc, hk, _, hrecords, hranks, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
    (exactGraph_shape (measuredGraph_shape h0) h) candidate
  have huniq : ∀ (u v : Nat) (left right : ProperNode),
      run.coordinateProper.nodes[u]? = some left →
      run.coordinateProper.nodes[v]? = some right →
      left.node.border = 3 → right.node.border = 3 →
      left.node.clusterPath = right.node.clusterPath → u = v := by
    intro u v left right hleft hright hleftBorder hrightBorder hpath
    apply XBbs_pc_title_unique hk hshape
      (by rw [hc]; exact hleft)
      (by rw [hc]; exact hright) hleftBorder hrightBorder hpath
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRunX_spec hrun
  have hsep := cluster_all_pairs_separated hcross huniq layer hlayer i j a b
    first second hij ha hb hfirst hsecond
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨hng, hcp, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨hfinalFirst, hxa⟩ := XBbs_nonproxy_record hrun hfirst hfirstBorder
  obtain ⟨hfinalSecond, hxb⟩ := XBbs_nonproxy_record hrun hsecond hsecondBorder
  have hwa : RouteImpl.nodeW run.proper a =
      RouteImpl.nodeW run.coordinateProper a := by
    simp only [RouteImpl.nodeW, hfinalFirst, hfirst]
  have hwb : RouteImpl.nodeW run.proper b =
      RouteImpl.nodeW run.coordinateProper b := by
    simp only [RouteImpl.nodeW, hfinalSecond, hsecond]
  have hga : RouteImpl.nodeW run.coordinateProper a ≤
      CoordsImpl.nodeW run.coordinateProper a := CoordsImpl.nodeW_ge_width _ _
  have hgb : RouteImpl.nodeW run.coordinateProper b ≤
      CoordsImpl.nodeW run.coordinateProper b := CoordsImpl.nodeW_ge_width _ _
  have e : ∀ width : Int, Int.fdiv width 2 = width / 2 :=
    fun width => Int.fdiv_eq_ediv_of_nonneg width (by decide)
  unfold CoordsImpl.coordSep at hsep
  simp only [e] at hsep
  simp only [RouteImpl.leftOf, RouteImpl.xAt, hxa, hxb, hwa, hwb, e]
  omega

/-! ## Member-nonempty helpers -/

/-- Exact proxy span record over `componentRunX`. -/
private theorem XBbs_proxy_interval {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner : Nat) (span : FramePorts.Span),
      node.node.clusterPath.getLast? = some owner ∧
      proxySpan run.coordinateProper run.coordinateXs owner index = .ok span ∧
      run.proper.nodes[index]? =
        some { node with node := { node.node with w := span.hi - span.lo } } ∧
      0 ≤ span.hi - span.lo ∧
      RouteImpl.leftOf run.proper run.xs index = span.lo ∧
      RouteImpl.leftOf run.proper run.xs index + RouteImpl.nodeW run.proper index = span.hi := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = q0.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨owner, span, ownerEq, hspan, outputNode, widthNonnegative, left, right⟩ :=
    proxyWidths_proxy_interval hproxy hnode hborder
  refine ⟨owner, span, ownerEq, hspan, ?_, widthNonnegative, ?_, ?_⟩
  · simpa only [nodesEq] using outputNode
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using left
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using right

/-- Every group-declaration node of an executed exact component contributes a
nonempty member hull. -/
theorem XB_memberNonempty_holds (exactIds : List String) :
    XB_MemberNonempty exactIds := by
  intro P inp o lines measured graph0 graph h0 h comp hcomp candidate run labels
    orderOptions hrun u uNode hu hgroup
  obtain ⟨_, labeled, _, _, hc, _, _, hrecords, _, _, _⟩ :=
    X_group_bottom_source h0 h hcomp hrun hu hgroup
  have hlab : labeled.nodes[u]? = some ⟨uNode, false, none, false⟩ :=
    hrecords u uNode hu
  have hcoordU : run.coordinateProper.nodes[u]? =
      some (clearF (titleF ⟨uNode, false, none, false⟩)) := by
    rw [← hc]
    exact X_coordinateGraph_marker_record hlab (Or.inl hgroup) rfl
  have hb2 : (clearF (titleF ⟨uNode, false, none, false⟩)).node.border = -2 :=
    (clearF_keys _).2.1.trans ((titleF_keys _).2.1.trans hgroup)
  obtain ⟨_owner, _span, _, _, hrecU, _, _, _⟩ :=
    XBbs_proxy_interval hrun hcoordU (Or.inl hb2)
  have hkeys : (clearF (titleF ⟨uNode, false, none, false⟩)).node.clusterPath =
      uNode.clusterPath := by
    rw [(clearF_keys _).2.2.1, (titleF_keys _).2.2.1]
  have hpathU : (run.proper.nodes.getD u default).node.clusterPath =
      uNode.clusterPath := by
    rw [List.getD_eq_getElem?_getD, hrecU]
    exact hkeys
  obtain ⟨_, _, hpath'⟩ := X_cg_group_box h0 h hu hgroup
  have hcontains : (run.proper.nodes.getD u default).node.clusterPath.contains
      uNode.decl = true := by
    rw [hpathU, hpath']
    simp
  obtain ⟨na, hna, hcn⟩ := fbs_contains_bridge' hcontains
  exact List.ne_nil_of_mem (fbs_groupMemberRects_mem hna hcn)

end PipelineImpl
end Layered
end Elegant

import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ComponentRunGen
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ExactFlatC2
import Elegant.Layered.ExactFlatC5Rank
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact twin of the non-group foreign-span seam

`XN_ForeignNonGroupSpansClear` is the exact twin of `ForeignNonGroupSpansClear`
(`ForeignSpansFacts.lean`): a non-group node of a foreign component part is
clear of a group frame's spans, for a run of `componentRunX` (fixed decls
`exactDecls exactIds inp`) rather than `componentRun`.

Replay of `ForeignNonGroupSpansProof.lean` over the exact run. Shared
run-generic facts (`frameRect_group_span`, the border/member rect lemmas, the
`boundsOf` hull lemmas, the `Disjoint` helpers, `proxyWidths_rel`,
`X_ReserveBands_holds`, `componentRunX_node_band`) are reused directly.
The exact-specific bridges are proved here: the record source
(`XN_run_record_source`), reserved-top nonnegativity (`XN_top_nonneg`),
the plain anchor record (`XN_componentRun_original_plain_record`), and the
bottom-marker case (`XN_bottomMarker_frame_disjoint`).

Seam facts the plain theorem takes as premises stay premises in exact form
(`XN_BracketMarkersAtRank`, `XN_PlainClearOfSideMarker`,
`XN_SideMarkerSpanAligned`).

Probe evidence (`proofs/wip/Probe/ExactNonGroupSpansTProbe.lean`): a fixed
foreign node next to a group frame stays disjoint at scene level for the
baseline, a huge fixed size (`800x600`, `50000x10`), and a zero fixed size;
a negative fixed size is rejected by `layoutX` with `.domain`. No falsifying
witness was found, so the replay proceeds. -/

/-- Residual (rank assignment and border-marker creation phase), exact form:
copy of `BracketMarkersAtRank` over `componentRunX`. -/
def XN_BracketMarkersAtRank (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel} {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl : Nat} (r : Nat) {low high : Nat} {lowNd highNd : ProperNode},
      run.proper.nodes[low]? = some lowNd →
      lowNd.node.clusterPath.contains decl = true →
      (rk run.proper.rank low).toNat ≤ r →
      run.proper.nodes[high]? = some highNd →
      highNd.node.clusterPath.contains decl = true →
      r ≤ (rk run.proper.rank high).toNat →
      ∃ (mL mR : Nat) (nL nR : ProperNode),
        run.coordinateProper.nodes[mL]? = some nL ∧
        nL.node.border = -1 ∧
        nL.node.clusterPath.getLast? = some decl ∧
        rk run.coordinateProper.rank mL = (r : Int) ∧
        run.coordinateProper.nodes[mR]? = some nR ∧
        nR.node.border = 1 ∧
        nR.node.clusterPath.getLast? = some decl ∧
        rk run.coordinateProper.rank mR = (r : Int)

/-- Residual (order phase), exact form: copy of `PlainClearOfSideMarker` over
`componentRunX`. -/
def XN_PlainClearOfSideMarker (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel} {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl v mL mR : Nat} {plain nL nR : ProperNode},
      run.proper.nodes[v]? = some plain →
      plain.node.border = 0 →
      plain.node.clusterPath.contains decl = false →
      run.proper.nodes[mL]? = some nL →
      nL.node.border = -1 →
      nL.node.clusterPath.getLast? = some decl →
      run.proper.nodes[mR]? = some nR →
      nR.node.border = 1 →
      nR.node.clusterPath.getLast? = some decl →
      rk run.proper.rank mL = rk run.proper.rank v →
      rk run.proper.rank mR = rk run.proper.rank v →
      RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤
          RouteImpl.leftOf run.proper run.xs mL ∨
        RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR ≤
          RouteImpl.leftOf run.proper run.xs v

/-- Residual (alignment phase), exact form: copy of `SideMarkerSpanAligned`
over `componentRunX`. -/
def XN_SideMarkerSpanAligned (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel} {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl m m' : Nat} {marker marker' : ProperNode},
      run.proper.nodes[m]? = some marker →
      (marker.node.border = -1 ∨ marker.node.border = 1) →
      marker.node.clusterPath.getLast? = some decl →
      run.proper.nodes[m']? = some marker' →
      (marker'.node.border = -1 ∨ marker'.node.border = 1) →
      marker'.node.clusterPath.getLast? = some decl →
      (marker.node.border = marker'.node.border →
        RouteImpl.leftOf run.proper run.xs m =
          RouteImpl.leftOf run.proper run.xs m' ∧
        RouteImpl.leftOf run.proper run.xs m + RouteImpl.nodeW run.proper m =
          RouteImpl.leftOf run.proper run.xs m' + RouteImpl.nodeW run.proper m') ∧
      0 ≤ RouteImpl.leftOf run.proper run.xs m + RouteImpl.nodeW run.proper m ∧
      ((marker.node.border = -1 ∧ marker'.node.border = 1 ∧
        rk run.proper.rank m = rk run.proper.rank m') →
        RouteImpl.leftOf run.proper run.xs m ≤
          RouteImpl.leftOf run.proper run.xs m' ∧
        RouteImpl.leftOf run.proper run.xs m + RouteImpl.nodeW run.proper m ≤
          RouteImpl.leftOf run.proper run.xs m' + RouteImpl.nodeW run.proper m')

/-- Exact twin of `ForeignNonGroupSpansClear`: the executed foreign-span
clause against a non-group witness, for one exact run. -/
def XN_ForeignNonGroupSpansClear (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel} {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border ≠ -2 →
    uNode.decl ≠ wNode.decl →
    wNode.clusterPath.contains uNode.decl = false →
    uNode.clusterPath.contains wNode.decl = false →
    Disjoint (frameRect P (componentCandidate graph comp candidate) run u)
      (frameRect P (componentCandidate graph comp candidate) run w)

/-! ## Exact record source -/

/-- Every exact run node's record agrees with a coordinate-phase record on
border and height (replay of `run_record_source` over `componentRunX_spec`;
`proxyWidths` is shared). -/
private theorem XN_run_record_source {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {q : Nat} {nd : ProperNode} (hq : run.proper.nodes[q]? = some nd) :
    ∃ cw : ProperNode, run.coordinateProper.nodes[q]? = some cw ∧
      cw.node.border = nd.node.border ∧ cw.node.h = nd.node.h := by
  obtain ⟨_ranks, _p0, _labeled, q0, _hn, _hlabeled, _hc, _ordp, _cross,
    hproxy, hdrop, _hrouteWL, _hrouting, _hroutes⟩ := componentRunX_spec hrun
  obtain ⟨_edges, _rank, hlen, _xlen, hrecords, _nonproxy⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hq0 : q0.nodes[q]? = some nd := by rw [← hnodes]; exact hq
  have hqLen : q < run.coordinateProper.nodes.length := by
    have hq0len : q < q0.nodes.length := (List.getElem?_eq_some_iff.mp hq0).1
    rw [← hlen]
    exact hq0len
  have hsource : run.coordinateProper.nodes[q]? =
      some (run.coordinateProper.nodes[q]'hqLen) :=
    List.getElem?_eq_getElem hqLen
  obtain ⟨final, hfinal, _dummy, hborder, hheight⟩ := hrecords q _ hsource
  have heq : final = nd := Option.some.inj (hfinal.symm.trans hq0)
  refine ⟨_, hsource, ?_, ?_⟩
  · exact hborder.symm.trans (congrArg (fun n => n.node.border) heq)
  · exact hheight.symm.trans (congrArg (fun n => n.node.h) heq)

/-! ## Exact reserved-top nonnegativity -/

/-- Prefix sums of a nonnegative list stay nonnegative (copy of the
`X_extra_fold`/`X_prefix_length` content for the shift vector). -/
private theorem XN_prefix_mem_nonneg (es : List Int) (s : Int) (out : List Int)
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
private theorem XN_prefix_getD_nonneg (extra : List Int) (hnn : ∀ e ∈ extra, 0 ≤ e)
    (r : Nat)
    (hr : r < ((extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).length) :
    0 ≤ ((extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).getD r 0 := by
  have hmem := List.mem_of_getElem? (List.getElem?_eq_getElem hr)
  have hnn2 := XN_prefix_mem_nonneg extra 0 [] (Int.le_refl 0) (by simp) hnn _ hmem
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  exact hnn2

/-- The exact reserved `run.top` stays nonnegative: pre-reserve tops are
nonnegative (`rankCoordsWith_spec`, as in `fbs_run_top_nonneg`) and
`reserveExactRanks` only adds nonnegative prefix-sum shifts. -/
private theorem XN_top_nonneg (exactIds : List String) {P : Params} {inp : Input} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run) :
    ∀ k : Nat, 0 ≤ run.top.getD k 0 := by
  have hrunGen : componentRunGen P (sizeProperPortsX P (exactDecls exactIds inp))
      (reserveExactRanks cg (exactDecls exactIds inp) labels)
      (cg.nodes.zipIdx.filterMap fun q => if (exactDecls exactIds inp).contains q.1.decl then some q.2 else none)
      cg labels orderOptions = .ok run := by
    rw [← componentRunX_eq_gen]
    exact hrun
  obtain ⟨_ranks, _p0, _labeled, _q0, _y_pre, top_pre, ys_pre, _hn, _hl, _hcoord, _hord, _hcross,
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
    · exact XN_prefix_getD_nonneg extra hnn r hr
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
  intro k
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

/-! ## Exact plain anchor record -/

/-- Exact coordinate anchor for a plain node (copy of
`X_coordinateGraphX_plain_anchor_dims` with the key fields threaded through
`sizeProperPortsX_key`, `titleF_keys`, `clearF_keys`, and the
non-dummy materialization identity). -/
private theorem XN_coordinateGraphX_plain_anchor (P : Params) (exact : List Nat) (p : Proper)
    {i : Nat} {nd : ProperNode} (hp : p.nodes[i]? = some nd) (hb : nd.node.border = 0)
    (hd : nd.dummy = false) :
    ∃ out, (coordinateGraphX P exact p).nodes[i]? = some out ∧
      out.edge = nd.edge ∧ out.node.border = 0 ∧
      nd.node.w ≤ out.node.w ∧ out.node.h = nd.node.h ∧
      out.node.clusterPath = nd.node.clusterPath ∧ out.dummy = false := by
  obtain ⟨sized, hs, he, hb', hw, hh⟩ :
      ∃ sized, (sizeProperPortsX P exact p).nodes[i]? = some sized ∧
        sized.edge = nd.edge ∧ sized.node.border = 0 ∧
        nd.node.w ≤ sized.node.w ∧ sized.node.h = nd.node.h := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
    split
    · exact ⟨nd, rfl, rfl, hb, Int.le_refl _, rfl⟩
    · refine ⟨_, rfl, rfl, hb, ?_, rfl⟩
      exact Int.le_max_left _ _
  have hkey := sizeProperPortsX_key P exact p i
  rw [hs, hp] at hkey
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
  obtain ⟨hdd, _hbb, hpp⟩ := hkey
  have hsd : sized.dummy = false := hdd.trans hd
  have hsp : sized.node.clusterPath = nd.node.clusterPath := hpp
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have htitle : (titleReservations (sizeProperPortsX P exact p)).nodes[i]? = some sized := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp [List.getElem?_map, hs, titleF, hb']
  obtain ⟨_extra, hextension, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]? = some sized := by
    rw [hextension,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hcleared : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[i]? =
        some (clearF sized) := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hplaced, clearF, hb']
  have hcd : (clearF sized).dummy = false := (clearF_keys sized).1.trans hsd
  have hcb : (clearF sized).node.border = 0 := (clearF_keys sized).2.1.trans hb'
  have hcp : (clearF sized).node.clusterPath = nd.node.clusterPath :=
    (clearF_keys sized).2.2.1.trans hsp
  have hch : (clearF sized).node.h = nd.node.h := (clearF_keys sized).2.2.2.trans hh
  have hce : (clearF sized).edge = sized.edge := by
    unfold clearF
    by_cases hc : (sized.node.border == -2 || sized.node.border == 2) = true
    · simp [hc]
    · simp [hc]
  have hcw : (clearF sized).node.w = sized.node.w := by
    unfold clearF
    by_cases hc : (sized.node.border == -2 || sized.node.border == 2) = true
    · simp [hc]
    · simp [hc]
  have hmat : (coordinateGraphX P exact p).nodes[i]? = some (clearF sized) := by
    unfold coordinateGraphX materializeDummyPaths
    simp only [List.getElem?_map, List.getElem?_zipIdx, hcleared, Option.map_some,
      hcd, Bool.false_eq_true, reduceIte]
  refine ⟨clearF sized, hmat, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hce.trans he
  · exact hcb
  · rw [hcw]
    exact hw
  · exact hch
  · exact hcp
  · exact hcd

/-- Proxy materialization keeps the exact coordinate anchor (copy of
`X_componentRun_plain_node_dims` from `ExactFitClosure`). -/
private theorem XN_componentRun_plain_node {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {nd : ProperNode}
    (hnode : run.coordinateProper.nodes[i]? = some nd)
    (hborder : nd.node.border = 0) :
    run.proper.nodes[i]? = some nd := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hprojected := proxyWidths_plain_node hproxy hnode hborder
  rw [← hdrop]
  exact hprojected

/-- Exact original plain record: a border-`0` component node keeps its record
through the exact run (replay of `componentRun_original_plain_record`;
widths may grow, so only border and path are stated). -/
private theorem XN_componentRun_original_plain_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      run.proper.nodes[index]? = some actual ∧
      actual.dummy = false ∧ actual.node.border = 0 ∧
      actual.node.clusterPath = node.clusterPath := by
  obtain ⟨_ranks, _p0, labeled, _q0, hn, hl, hcoord, _hord, _hcross, _hproxy, _hdrop,
    _hrouteWL, _hrouting, _hroutes⟩ := componentRunX_spec hrun
  have hp := normalize_node_record hn hnode
  have hlabRec : labeled.nodes[index]? = some (⟨node, false, none, false⟩ : ProperNode) :=
    addLabelNodes_untouched_node hl hp rfl
  obtain ⟨actual, hactual, _hedge, hplainA, _hw, _hh, hpath, hfalse⟩ :=
    XN_coordinateGraphX_plain_anchor P exact labeled hlabRec hplain rfl
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hcoord]
    exact hactual
  exact ⟨actual, hcoordinate, XN_componentRun_plain_node hrun hcoordinate hplainA,
    hfalse, hplainA, hpath⟩

/-! ## The exact bottom-marker case -/

/-- A bottom marker of the exact measured graph keeps height `0` through the
executed exact pipeline, so its placed frame rectangle is disjoint from every
rectangle (replay of `bottomMarker_frame_disjoint` over `componentRunX_spec`
and `X_coordinateGraph_marker_record`). -/
private theorem XN_bottomMarker_frame_disjoint {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {w : Nat} {wNode : Node} (hw : cg.nodes[w]? = some wNode)
    (hbottom : wNode.border = 2) (u : Nat) :
    Disjoint (frameRect P cg run u) (frameRect P cg run w) := by
  obtain ⟨_ranks, _p0, labeled, q0, hn, hl, hcoord, _hord, _hcross, hproxy, hdrop,
    _hrouteWL, _hrouting, _hroutes⟩ := componentRunX_spec hrun
  obtain ⟨_edges, _rank, _nlen, _xlen, hrecords, _nonproxy⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hlabRec : labeled.nodes[w]? = some (⟨wNode, false, none, false⟩ : ProperNode) :=
    addLabelNodes_untouched_node hl (normalize_node_record hn hw) rfl
  have hdummyW : (⟨wNode, false, none, false⟩ : ProperNode).dummy = false := rfl
  have hcpRec : (coordinateGraphX P exact labeled).nodes[w]? =
      some (clearF (titleF (⟨wNode, false, none, false⟩ : ProperNode))) :=
    X_coordinateGraph_marker_record hlabRec (Or.inr hbottom) hdummyW
  have hcpBorder : (clearF (titleF (⟨wNode, false, none, false⟩ : ProperNode))).node.border
      = wNode.border :=
    (clearF_keys _).2.1.trans (titleF_keys _).2.1
  have hcpFlat : (clearF (titleF (⟨wNode, false, none, false⟩ : ProperNode))).node.h = 0 := by
    have ht := (titleF_keys (⟨wNode, false, none, false⟩ : ProperNode)).2.2.2 (Or.inr hbottom)
    have hc := (clearF_keys (titleF (⟨wNode, false, none, false⟩ : ProperNode))).2.2.2
    rw [hc]
    exact ht
  have hrunCpRec : run.coordinateProper.nodes[w]? =
      some (clearF (titleF (⟨wNode, false, none, false⟩ : ProperNode))) := by
    rw [← hcoord]
    exact hcpRec
  obtain ⟨final, hfinal, _dummy, _border, hfinalH⟩ := hrecords w _ hrunCpRec
  have hpropW' : run.proper.nodes[w]? = some final := by rw [hnodes]; exact hfinal
  have hgetW : cg.nodes.getD w default = wNode := by
    rw [List.getD_eq_getElem?_getD, hw]
    rfl
  have hframeW : frameRect P cg run w = nodeRect cg run w := by
    unfold frameRect
    simp only []
    rw [hgetW, hbottom]
    rfl
  rw [hframeW, nodeRect_of_record hpropW']
  refine disjoint_of_height_zero_right ?_
  rw [hfinalH]
  exact hcpFlat

/-! ## The exact plain-witness case -/

/-- An exact plain witness separates from the group's frame on `y` whenever
its rank is outside the member rank range, and on `x` through the
border-marker pair span whenever inside; the marker facts are the three
`XN_` residuals. Replay of `plain_frame_disjoint`: rank bands come from
`componentRunX_node_band` and `X_ReserveBands_holds`, top nonnegativity from
`XN_top_nonneg`. -/
private theorem XN_plain_frame_disjoint (exactIds : List String)
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel} {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (hg : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (horder : XN_PlainClearOfSideMarker exactIds)
    (halign : XN_SideMarkerSpanAligned exactIds)
    {u w : Nat} {uNode wNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hw : (componentCandidate graph comp candidate).nodes[w]? = some wNode)
    (hgroupU : uNode.border = -2) (hplain : wNode.border = 0)
    (hpathW : wNode.clusterPath.contains uNode.decl = false) :
    Disjoint (frameRect P (componentCandidate graph comp candidate) run u)
      (frameRect P (componentCandidate graph comp candidate) run w) := by
  obtain ⟨actual, _coord, hpropW, _dummy, hbW0, hpathWeq⟩ :=
    XN_componentRun_original_plain_record hrun hw hplain
  have hgetW : (componentCandidate graph comp candidate).nodes.getD w default = wNode := by
    rw [List.getD_eq_getElem?_getD, hw]
    rfl
  have hframeW : frameRect P (componentCandidate graph comp candidate) run w =
      nodeRect (componentCandidate graph comp candidate) run w := by
    unfold frameRect
    simp only []
    rw [hgetW, hplain]
    rfl
  obtain ⟨_ranks, _p0, _labeled, q0, _hn, _hlabeled, _hc, _ordp, _cross,
    hproxy, hdrop, hrouteWL, _hrouting, _hroutes⟩ :=
    componentRunX_spec hrun
  obtain ⟨_edges, hrankEq, _nlen, _xlen, _records, hnp⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  obtain ⟨_len, _sz, _members, hcov, _edges2⟩ :=
    RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hrouteWL).1
  have htopNN : ∀ r : Nat, (0 : Int) ≤ run.top.getD r 0 := XN_top_nonneg exactIds hrun
  have hXbands := X_ReserveBands_holds exactIds hrun
  have hwP : w < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hpropW).1
  obtain ⟨lW, hlyW, hwTopBand, hwBotBand⟩ :=
    componentRunX_node_band hrun hpropW (XN_run_record_source hrun hpropW)
  have hcovw := hcov w hwP
  obtain ⟨-, -, -, hwNN⟩ := hcovw
  have hrkWNN : 0 ≤ rk run.coordinateProper.rank w := by rw [← hranks]; exact hwNN
  have hysWNN : (0 : Int) ≤ run.ys.getD w 0 :=
    Int.le_trans (htopNN _) hwTopBand
  by_cases hLow : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      nd.node.clusterPath.contains uNode.decl = true ∧
      (rk run.coordinateProper.rank q).toNat ≤ (rk run.coordinateProper.rank w).toNat
  · by_cases hHigh : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      nd.node.clusterPath.contains uNode.decl = true ∧
      (rk run.coordinateProper.rank w).toNat ≤ (rk run.coordinateProper.rank q).toNat
    · obtain ⟨low, lowNd, hlowRec, hlowCon, hlowLe⟩ := hLow
      obtain ⟨high, highNd, hhighRec, hhighCon, hhighGe⟩ := hHigh
      rw [← hranks] at hlowLe hhighGe
      obtain ⟨mL, mR, nL, nR, hcpmL, hborderL, hlastL, hrankL,
        hcpmR, hborderR, hlastR, hrankR⟩ :=
        hbracket h0 hg hlines hwf hfp hcomp hrun (rk run.proper.rank w).toNat
          hlowRec hlowCon hlowLe hhighRec hhighCon hhighGe
      have hnotProxyL : ¬(nL.node.border = -2 ∨ nL.node.border = 2) := by
        rw [hborderL]; omega
      have hnotProxyR : ¬(nR.node.border = -2 ∨ nR.node.border = 2) := by
        rw [hborderR]; omega
      obtain ⟨hnpRecL, -⟩ := hnp mL nL hcpmL hnotProxyL
      obtain ⟨hnpRecR, -⟩ := hnp mR nR hcpmR hnotProxyR
      have hmarkRunL : run.proper.nodes[mL]? = some nL := by
        rw [hnodes]; exact hnpRecL
      have hmarkRunR : run.proper.nodes[mR]? = some nR := by
        rw [hnodes]; exact hnpRecR
      have hrankmWL : rk run.proper.rank mL = rk run.proper.rank w := by
        rw [hranks, hrankL, hranks]
        exact Int.toNat_of_nonneg hrkWNN
      have hrankmWR : rk run.proper.rank mR = rk run.proper.rank w := by
        rw [hranks, hrankR, hranks]
        exact Int.toNat_of_nonneg hrkWNN
      have hrankLR : rk run.proper.rank mL = rk run.proper.rank mR := by
        rw [hrankmWL, hrankmWR]
      have hnotMem : actual.node.clusterPath.contains uNode.decl = false := by
        rw [hpathWeq]
        exact hpathW
      obtain hsep :=
        horder h0 hg hcomp hrun hpropW hbW0 hnotMem
          hmarkRunL hborderL hlastL hmarkRunR hborderR hlastR hrankmWL hrankmWR
      have hmemRectL : Labels.rectAt run.proper run.xs run.ys mL ∈
          groupBorderRects (componentCandidate graph comp candidate) run uNode.decl :=
        groupBorderRects_mem_of_record hmarkRunL (Or.inl hborderL) hlastL
      have hneRects : groupBorderRects (componentCandidate graph comp candidate) run uNode.decl ≠ [] := by
        intro hnil
        rw [hnil] at hmemRectL
        simp at hmemRectL
      have hborderLOr : nL.node.border = -1 ∨ nL.node.border = 1 :=
        Or.inl hborderL
      have hborderROr : nR.node.border = -1 ∨ nR.node.border = 1 :=
        Or.inr hborderR
      have hcross :=
        (halign h0 hg hcomp hrun hmarkRunL hborderLOr hlastL
          hmarkRunR hborderROr hlastR).2.2 ⟨hborderL, hborderR, hrankLR⟩
      have hall : ∀ r ∈ groupBorderRects (componentCandidate graph comp candidate) run uNode.decl,
          RouteImpl.leftOf run.proper run.xs mL ≤ r.x ∧
            r.x + r.w ≤ RouteImpl.leftOf run.proper run.xs mR +
              RouteImpl.nodeW run.proper mR := by
        intro r hr
        obtain ⟨q, nd, hq, hbq, hlastq, hrq⟩ := groupBorderRects_inv hr
        rcases hbq with hbqL | hbqR
        · obtain ⟨heq1, heq2⟩ :=
            (halign h0 hg hcomp hrun hmarkRunL hborderLOr hlastL
              hq (Or.inl hbqL) hlastq).1 (by rw [hborderL, hbqL])
          rw [hrq, rectAt_eq]
          dsimp only
          rw [heq1, ← heq2]
          exact ⟨Int.le_refl _, hcross.2⟩
        · obtain ⟨heq1, heq2⟩ :=
            (halign h0 hg hcomp hrun hmarkRunR hborderROr hlastR
              hq (Or.inr hbqR) hlastq).1 (by rw [hborderR, hbqR])
          rw [hrq, rectAt_eq]
          dsimp only
          refine ⟨?_, ?_⟩
          · rw [← heq1]; exact hcross.1
          · omega
      have hnonnegR :=
        (halign h0 hg hcomp hrun hmarkRunR hborderROr hlastR
          hmarkRunR hborderROr hlastR).2.1
      have hminX := boundsOf_minX_ge_of_all hneRects (fun r hr => (hall r hr).1)
      have hright := boundsOf_right_le_of_all hnonnegR
        (fun r hr => (hall r hr).2)
      have hcontain := boundsOf_rect_mem hmemRectL
      rw [rectAt_eq] at hcontain
      rw [frameRect_group_span hu hgroupU, hframeW, nodeRect_of_record hpropW]
      unfold Disjoint Rect.meetsInterior
      simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW,
        hpropW, hmarkRunL, hmarkRunR,
        Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)]
        at hsep hcontain hminX hright ⊢
      omega
    · have hAllAbove : ∀ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd →
          nd.node.clusterPath.contains uNode.decl = true →
          (rk run.coordinateProper.rank q).toNat < (rk run.coordinateProper.rank w).toNat := by
        intro q nd hrec hcon
        refine Classical.byContradiction (fun hcontra => ?_)
        exact hHigh ⟨q, nd, hrec, hcon, by omega⟩
      have hmem : ∀ r ∈ groupMemberRects (componentCandidate graph comp candidate) run uNode.decl,
          r.y + r.h ≤ run.ys.getD w 0 := by
        intro r hr
        obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
        obtain ⟨l, hly, hqTop, hqBot⟩ :=
          componentRunX_node_band hrun hq (XN_run_record_source hrun hq)
        have hband := hXbands.2
          (rk run.coordinateProper.rank q).toNat (rk run.coordinateProper.rank w).toNat
          l lW (hAllAbove q nd hq hcon) hly hlyW
        simp only [RouteImpl.nodeH, hq] at hqBot
        rw [hrq, rectAt_eq]
        simp only [RouteImpl.yAt, RouteImpl.nodeH, hq]
        omega
      have hbot := boundsOf_bottom_le_of_all hysWNN hmem
      rw [frameRect_group_span hu hgroupU, hframeW, nodeRect_of_record hpropW]
      refine rect_disjoint_of_y (Or.inl ?_)
      have hkey : (boundsOf (groupMemberRects (componentCandidate graph comp candidate) run uNode.decl) []).minY +
          ((boundsOf (groupMemberRects (componentCandidate graph comp candidate) run uNode.decl) []).bottom -
            (boundsOf (groupMemberRects (componentCandidate graph comp candidate) run uNode.decl) []).minY) ≤
          run.ys.getD w 0 := by omega
      exact hkey
  · by_cases hHigh : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      nd.node.clusterPath.contains uNode.decl = true ∧
      (rk run.coordinateProper.rank w).toNat ≤ (rk run.coordinateProper.rank q).toNat
    · by_cases hmemNil : groupMemberRects (componentCandidate graph comp candidate) run uNode.decl = []
      · rw [frameRect_group_span hu hgroupU, hmemNil]
        refine disjoint_of_height_zero_left ?_
        show (boundsOf [] []).bottom - (boundsOf [] []).minY = 0
        rfl
      · have hmem : ∀ r ∈ groupMemberRects (componentCandidate graph comp candidate) run uNode.decl,
          run.ys.getD w 0 + RouteImpl.nodeH run.proper w ≤ r.y := by
          intro r hr
          obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
          obtain ⟨l, hly, hqTop, hqBot⟩ :=
            componentRunX_node_band hrun hq (XN_run_record_source hrun hq)
          have hAllBelow : (rk run.coordinateProper.rank w).toNat <
              (rk run.coordinateProper.rank q).toNat := by
            refine Classical.byContradiction (fun hcontra => ?_)
            exact hLow ⟨q, nd, hq, hcon, by omega⟩
          have hband := hXbands.2
            (rk run.coordinateProper.rank w).toNat (rk run.coordinateProper.rank q).toNat
            lW l hAllBelow hlyW hly
          simp only [RouteImpl.nodeH, hq] at hqBot
          simp only [RouteImpl.nodeH, hpropW] at hwBotBand
          rw [hrq, rectAt_eq]
          dsimp only
          simp only [RouteImpl.yAt, RouteImpl.nodeH, hpropW]
          omega
        have htop := boundsOf_minY_ge_of_all hmemNil hmem
        simp only [RouteImpl.nodeH, hpropW] at htop
        rw [frameRect_group_span hu hgroupU, hframeW, nodeRect_of_record hpropW]
        refine rect_disjoint_of_y (Or.inr ?_)
        omega
    · have hmemNil : groupMemberRects (componentCandidate graph comp candidate) run uNode.decl = [] := by
        refine Classical.byContradiction (fun hne => ?_)
        cases hmem : groupMemberRects (componentCandidate graph comp candidate) run uNode.decl with
        | nil => exact hne hmem
        | cons r rest =>
          obtain ⟨q, nd, hq, hcon, _r⟩ :=
            groupMemberRects_inv (show r ∈ groupMemberRects (componentCandidate graph comp candidate) run uNode.decl by
              rw [hmem]; exact List.mem_cons_self)
          rcases (show (rk run.coordinateProper.rank q).toNat ≤
              (rk run.coordinateProper.rank w).toNat ∨
            (rk run.coordinateProper.rank w).toNat ≤
              (rk run.coordinateProper.rank q).toNat by omega) with hle | hle
          · exact hLow ⟨q, nd, hq, hcon, hle⟩
          · exact hHigh ⟨q, nd, hq, hcon, hle⟩
      rw [frameRect_group_span hu hgroupU, hmemNil]
      refine disjoint_of_height_zero_left ?_
      show (boundsOf [] []).bottom - (boundsOf [] []).minY = 0
      rfl

/-! ## The seam -/

/-- The exact non-group foreign-span seam: from the marker-existence,
marker-ordering and marker-alignment residuals, every non-group witness of an
executed exact run keeps its frame rectangle disjoint from an unrelated
group's frame. The bottom-marker case and both rank-band cases of plain
witnesses are proved outright; only the inside-the-bracket plain case consumes
the residuals. -/
theorem XN_foreignNonGroupSpansClear_holds
    (exactIds : List String)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (horder : XN_PlainClearOfSideMarker exactIds)
    (halign : XN_SideMarkerSpanAligned exactIds) :
    XN_ForeignNonGroupSpansClear exactIds := by
  intro P inp o lines measured graph0 graph h0 hg hlines hwf hfp comp hcomp candidate run labels orderOptions
    hrun u w uNode wNode hu hw hgroupU hwNgroup hne hpathW hpathU
  obtain ⟨hborders, _path⟩ := X_componentCandidate_marker_shape h0 hg hw
  rcases hborders with hwPlain | hgroupW | hwBottom
  · exact XN_plain_frame_disjoint exactIds h0 hg hlines hwf hfp hcomp hrun hbracket horder halign hu hw hgroupU hwPlain hpathW
  · exact absurd hgroupW hwNgroup
  · exact XN_bottomMarker_frame_disjoint hrun hw hwBottom u

end PipelineImpl

end Layered

end Elegant

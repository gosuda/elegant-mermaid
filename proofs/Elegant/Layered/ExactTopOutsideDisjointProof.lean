import Elegant.Layered.ExactLoopRectTopSamePartProof
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ComponentRunGen
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ExactFlatC2
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact loop-rect top outsider disjointness (W form)

Proves `XLrr_TopOutsideDisjointW` (closed in
`ExactLoopRectTopSamePartProof.lean`) modulo the single narrower residual
`XLrr_TopOutsideDisjointInRangeW`: an executed exact run frame of a plain
node outside a group is disjoint from the group-top frame, where the only
open case is the in-range one (group members exist at ranks both below and
above the outsider, so the rank bands do not separate).

 Closed here: both rank-band cases (outsider strictly above or below every
 member rank) via `componentRunX_node_band` plus the closed
 `X_ReserveBands_holds` disjoint bands, the empty-hull height-zero cases, and
 the reduction splitting the target into band cases plus the in-range
 residual. The in-range case (same-rank marker bracket plus plain/marker
 ordering and alignment) stays open as the single residual; it is strictly
 narrower than the target (adds the two rank-witness hypotheses) and is a
 lemma on the way, owned by the side-marker lane.

 Probe evidence (`proofs/wip/Probe/ExactTopOutsideDisjointTProbe.lean`):
 14 pairs over 13 executed inputs, `disj=true` everywhere:
 `wit-zero-outsider` (zero-size outsider, in-range), `zero-member`
 (zero-size member, in-range), `nested` (two group tops vs one outsider),
 `self-loop-outsider`, `huge-outsider` (`50000x10`), `siblings` (four pairs,
 one all-below), `wide-member`, `zero-outsider` (zero-size outsider),
 `above-outsider`, `solo` (shallow source above a member chain); vacuous on
 `flat` (no groups), `empty-group` (separate components), `ill-formed`
 (rejected at prep). No falsifying witness was found.
-/

 /-- Per-execution in-range outsider case: the residual behind
 `XLrr_TopOutsideDisjointW`. Same statement plus member-rank witnesses on
 both sides of the outsider rank (the rank bands then fail to separate, so
 the marker-bracket argument is needed). Strictly narrower than the target;
 true on the probe above (13 of 14 pairs are in-range, all `disj=true`). -/
 def XLrr_TopOutsideDisjointInRangeW (exactIds : List String) : Prop :=
   ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecutionX exactIds inp o res)
     (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
     {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run →
    ∀ {v w : Nat} {node member : Node},
      (componentCandidate execution.graph comp candidate).nodes[v]? = some node →
      node.border = -2 →
      (componentCandidate execution.graph comp candidate).nodes[w]? = some member →
      member.border = 0 →
      ¬(member.clusterPath.contains node.decl = true) →
      (∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
        nd.node.clusterPath.contains node.decl = true ∧
        (rk run.coordinateProper.rank q).toNat ≤ (rk run.coordinateProper.rank w).toNat) →
      (∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
        nd.node.clusterPath.contains node.decl = true ∧
        (rk run.coordinateProper.rank w).toNat ≤ (rk run.coordinateProper.rank q).toNat) →
      Disjoint (frameRect execution.params (componentCandidate execution.graph comp candidate) run w)
        (frameRect execution.params (componentCandidate execution.graph comp candidate) run v)

/-- File-unique prefix for all private helpers in this module. -/
private theorem xtod_prefix_mem_nonneg (es : List Int) (s : Int) (out : List Int)
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
private theorem xtod_prefix_getD_nonneg (extra : List Int) (hnn : ∀ e ∈ extra, 0 ≤ e)
    (r : Nat)
    (hr : r < ((extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).length) :
    0 ≤ ((extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1])) (0, ([] : List Int))).2).getD r 0 := by
  have hmem := List.mem_of_getElem? (List.getElem?_eq_getElem hr)
  have hnn2 := xtod_prefix_mem_nonneg extra 0 [] (Int.le_refl 0) (by simp) hnn _ hmem
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  exact hnn2

/-- The exact reserved `run.top` stays nonnegative. -/
private theorem xtod_top_nonneg (exactIds : List String) {P : Params} {inp : Input} {cg : Graph}
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
    · exact xtod_prefix_getD_nonneg extra hnn r hr
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

/-- Every exact run node's record agrees with a coordinate-phase record on
border and height. -/
private theorem xtod_run_record_source {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
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

 /-- Exact coordinate anchor for a plain node. -/
 private theorem xtod_coordinateGraphX_plain_anchor (P : Params) (exact : List Nat) (p : Proper)
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

 /-- Proxy materialization keeps the exact coordinate anchor. -/
 private theorem xtod_componentRun_plain_node {P : Params} {exact : List Nat} {cg : Graph}
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
 through the exact run. -/
 private theorem xtod_componentRun_original_plain_record {P : Params} {exact : List Nat} {cg : Graph}
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
     xtod_coordinateGraphX_plain_anchor P exact labeled hlabRec hplain rfl
   have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
     rw [← hcoord]
     exact hactual
   exact ⟨actual, hcoordinate, xtod_componentRun_plain_node hrun hcoordinate hplainA,
     hfalse, hplainA, hpath⟩

 /-- Outsider disjointness from the in-range residual: the band cases close
 here, the in-range rank case is the residual. -/
 theorem XLrr_topOutsideDisjointW_holds (exactIds : List String)
     (hInRange : XLrr_TopOutsideDisjointInRangeW exactIds) :
     XLrr_TopOutsideDisjointW exactIds := by
   intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
   intro v w node member hnode hgroup hmember hplain hinside
   obtain ⟨_, _, hpropW, _, _, _⟩ :=
     xtod_componentRun_original_plain_record hrun hmember hplain
   have hgetW : (componentCandidate execution.graph comp candidate).nodes.getD w default = member := by
     rw [List.getD_eq_getElem?_getD, hmember]
     rfl
   have hframeW : frameRect execution.params (componentCandidate execution.graph comp candidate) run w =
       nodeRect (componentCandidate execution.graph comp candidate) run w := by
     unfold frameRect
     simp only []
     rw [hgetW, hplain]
     rfl
   obtain ⟨lW, hlyW, hwTopBand, hwBotBand⟩ :=
     componentRunX_node_band hrun hpropW (xtod_run_record_source hrun hpropW)
   have htopNN : ∀ k : Nat, 0 ≤ run.top.getD k 0 := xtod_top_nonneg exactIds hrun
   have hysWNN : (0 : Int) ≤ run.ys.getD w 0 :=
     Int.le_trans (htopNN _) hwTopBand
   have hbands := (X_ReserveBands_holds exactIds hrun).2
   by_cases hLow : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
       nd.node.clusterPath.contains node.decl = true ∧
       (rk run.coordinateProper.rank q).toNat ≤ (rk run.coordinateProper.rank w).toNat
   · by_cases hHigh : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
         nd.node.clusterPath.contains node.decl = true ∧
         (rk run.coordinateProper.rank w).toNat ≤ (rk run.coordinateProper.rank q).toNat
     · exact hInRange execution hwf hfp hcomp hrun hnode hgroup hmember hplain hinside hLow hHigh
     · have hAllAbove : ∀ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd →
           nd.node.clusterPath.contains node.decl = true →
           (rk run.coordinateProper.rank q).toNat < (rk run.coordinateProper.rank w).toNat := by
         intro q nd hrec hcon
         refine Classical.byContradiction (fun hcontra => ?_)
         exact hHigh ⟨q, nd, hrec, hcon, by omega⟩
       have hmem : ∀ r ∈ groupMemberRects (componentCandidate execution.graph comp candidate) run node.decl,
           r.y + r.h ≤ run.ys.getD w 0 := by
         intro r hr
         obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
         obtain ⟨l, hly, _, hqBot⟩ :=
           componentRunX_node_band hrun hq (xtod_run_record_source hrun hq)
         have hband := hbands
           (rk run.coordinateProper.rank q).toNat (rk run.coordinateProper.rank w).toNat
           l lW (hAllAbove q nd hq hcon) hly hlyW
         simp only [RouteImpl.nodeH, hq] at hqBot
         rw [hrq, rectAt_eq]
         simp only [RouteImpl.yAt, RouteImpl.nodeH, hq]
         omega
       have hbot := boundsOf_bottom_le_of_all hysWNN hmem
       rw [frameRect_group_span hnode hgroup, hframeW, nodeRect_of_record hpropW]
       refine rect_disjoint_of_y (Or.inr ?_)
       have hkey : (boundsOf (groupMemberRects (componentCandidate execution.graph comp candidate) run node.decl) []).minY +
           ((boundsOf (groupMemberRects (componentCandidate execution.graph comp candidate) run node.decl) []).bottom -
             (boundsOf (groupMemberRects (componentCandidate execution.graph comp candidate) run node.decl) []).minY) ≤
           run.ys.getD w 0 := by omega
       exact hkey
   · by_cases hmemNil : groupMemberRects (componentCandidate execution.graph comp candidate) run node.decl = []
     · rw [frameRect_group_span hnode hgroup, hmemNil]
       refine disjoint_of_height_zero_right ?_
       show (boundsOf [] []).bottom - (boundsOf [] []).minY = 0
       rfl
     · have hmem : ∀ r ∈ groupMemberRects (componentCandidate execution.graph comp candidate) run node.decl,
         run.ys.getD w 0 + RouteImpl.nodeH run.proper w ≤ r.y := by
         intro r hr
         obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
         obtain ⟨l, hly, hqTop, hqBot⟩ :=
           componentRunX_node_band hrun hq (xtod_run_record_source hrun hq)
         have hAllBelow : (rk run.coordinateProper.rank w).toNat <
             (rk run.coordinateProper.rank q).toNat := by
           refine Classical.byContradiction (fun hcontra => ?_)
           exact hLow ⟨q, nd, hq, hcon, by omega⟩
         have hband := hbands
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
       rw [frameRect_group_span hnode hgroup, hframeW, nodeRect_of_record hpropW]
       refine rect_disjoint_of_y (Or.inl ?_)
       omega

 end PipelineImpl
 end Layered
 end Elegant

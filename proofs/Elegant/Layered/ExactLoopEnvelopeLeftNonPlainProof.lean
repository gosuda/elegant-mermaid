import Elegant.Layered.ExactLoopEnvelopeSidesProof
import Elegant.Layered.ExactLoopEnvelopeLayerProof
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactBorderSpanRunFactsProof
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.LoopFootprintGeneralOrder
import Elegant.Layered.CoordGraph
import Elegant.Layered.SizingFacts
import Elegant.Layered.CgShape
import Elegant.Layered.Labels
import Elegant.Layered.SceneBounds
import Elegant.Layered.Loops

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! Left non-plain case of the exact loop-envelope same-rank miss.

Target: `XLEM_LeftNonPlain` (`ExactLoopEnvelopeSidesProof.lean`): the
extended footprint of a self-loop on a border-`0` owner misses an earlier
same-layer box `v` that is not an original plain node (group marker, dummy,
or title). Together with the proved `XLEM_leftMiss_holds` modem this closes
`XLEM_LeftMiss`.

Probe truth (`proofs/wip/Probe/ExactLeftNonPlainTProbe.lean`, vector
profile, both candidate orders): twelve executed inputs: `sibL`
(self-loop with earlier sibling), `zero` (zero-size fixed owner),
`empty-group` (degenerate group frame), `nested` (two-deep nesting),
`ill` (prep domain error, vacuous), `grploop` (group-owner control),
`exact-a` (exact-extent branch), `twogroups`/`twofree`/`twofree-exact`
(sibling groups, plain and exact branches), `samegroupfree`
(unrelated same-group sibling), `samegroupfree-exact` (prep domain
error, vacuous). No `disj = false` on any executed run. Every in-scope
same-layer earlier box was an original plain node (`samegroupfree`:
`t = 3 v = 2 gap = true disj = true` on both candidates); every
non-plain/appended earlier box was scope-skipped (a marker of a group
containing the owner), so the residual is vacuously true on all probes.

Proof: the owner keeps its plain record; `v` splits on its coordinate
border. Proxy `v` (`±2`) has proper height zero, so the y-overlap is
impossible. Non-proxy `v` is ordered against the owner by
`XB_orderedIntervals_holds`, and the footprint starts at the owner
frame's right edge, so the x-gap closes the miss. No extra premise is
needed: `XB_orderedIntervals_holds` and the run bundle are proved facts
applied to the executed run's own equations. -/

/-- Pure x-gap, symmetric: a box ending left of the footprint misses it. -/
private theorem XLEMLN_rect_miss_left {fp rb : Rect}
    (h : rb.x + rb.w ≤ fp.x) : ¬ fp.meetsInterior rb := by
  unfold Rect.meetsInterior
  omega

/-- Exact proper nodes transfer unchanged for non-proxy borders. -/
private theorem XLEMLN_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
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

/-- Exact original plain nodes keep their measured record. -/
private theorem XLEMLN_original_plain_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      run.proper.nodes[index]? = some actual ∧
      actual.node.border = 0 ∧
      node.w ≤ actual.node.w ∧ actual.node.h = node.h ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, p0, labeled, _, hn, hl, hc, _, _, _, _, _, _, _⟩ :=
    componentRunX_spec h
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨actual, hactual, _, hborder, hwidth, hheight⟩ :=
    coordinateGraphX_plain_anchor_dims P hsource hplain
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hc]
    exact hactual
  have hproper := (XLEMLN_nonproxy_record h hcoordinate (by rw [hborder]; decide)).1
  have hxs := (XLEMLN_nonproxy_record h hcoordinate (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hborder, hwidth, hheight, ?_⟩
  exact hxs

/-- Exact coordinate record from a proper record. -/
private theorem XLEMLN_proper_coord {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp) :
    ∃ nvc : ProperNode, run.coordinateProper.nodes[v]? = some nvc ∧
      nvc.node.border = nvp.node.border ∧ nvc.node.h = nvp.node.h := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hprox, hdrop, _, _, _⟩ := componentRunX_spec h
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  obtain ⟨_, _, hlen, _, hAll, _⟩ := proxyWidths_rel hprox
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes]; exact hlen
  have hvR : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hrec).1
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hcadr : run.coordinateProper.nodes[v]? = some run.coordinateProper.nodes[v] :=
    List.getElem?_eq_getElem hvC
  obtain ⟨nd', hnd', _, hb', hh'⟩ := hAll v _ hcadr
  have hnd2 : run.proper.nodes[v]? = some nd' := by rw [hnodes]; exact hnd'
  have hnde : nd' = nvp := Option.some.inj (hnd2.symm.trans hrec)
  rw [hnde] at hb' hh'
  exact ⟨run.coordinateProper.nodes[v], hcadr, hb'.symm, hh'.symm⟩

/-- Appended coordinate nodes are never proxy. -/
private theorem XLEMLN_appended_nonproxy {P : Params} {exact : List Nat} {labeled : Proper}
    {run : Run}
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    {v : Nat} {nvc : ProperNode}
    (hcoordV : run.coordinateProper.nodes[v]? = some nvc)
    (hlen : labeled.nodes.length ≤ v) :
    nvc.node.border ≠ -2 ∧ nvc.node.border ≠ 2 := by
  rw [← hc] at hcoordV
  obtain ⟨m1, hm1, _, hb1, _, _⟩ := materialize_lookup _ hcoordV
  rw [clearProxyExtents_nodes] at hm1
  obtain ⟨m2, hm2, hcm⟩ : ∃ m,
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW).nodes[v]? = some m ∧ clearF m = m1 :=
    Option.map_eq_some_iff.mp (by simpa [List.getElem?_map] using hm1)
  have hb2 : m2.node.border = m1.node.border := by
    have h := (clearF_keys m2).2.1
    rw [hcm] at h
    exact h.symm
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  rw [hx] at hm2
  by_cases hpre : v < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length
  · rw [List.getElem?_append_left hpre] at hm2
    rw [titleReservations_nodes] at hm2
    have hsz : (sizeProperPortsX P exact labeled).nodes.length = labeled.nodes.length := by
      unfold sizeProperPortsX
      simp
    by_cases ht : v < (sizeProperPortsX P exact labeled).nodes.length
    · rw [List.getElem?_append_left (by simpa using ht)] at hm2
      obtain ⟨m3, hm3, htm⟩ : ∃ m,
          (sizeProperPortsX P exact labeled).nodes[v]? = some m ∧ titleF m = m2 := by
        simp only [List.getElem?_map] at hm2
        cases hl : (sizeProperPortsX P exact labeled).nodes[v]? with
        | none => simp [hl] at hm2
        | some m =>
          simp only [hl, Option.map_some, Option.some.injEq] at hm2
          exact ⟨m, rfl, hm2⟩
      have hkey := sizeProperPortsX_key P exact labeled v
      rw [hm3] at hkey
      cases hl : labeled.nodes[v]? with
      | none => simp [hl] at hkey
      | some m4 =>
        have hlt : v < labeled.nodes.length := (List.getElem?_eq_some_iff.mp hl).1
        omega
    · have hge : (sizeProperPortsX P exact labeled).nodes.length ≤ v := Nat.le_of_not_lt ht
      have hlen : ((sizeProperPortsX P exact labeled).nodes.map titleF).length =
          (sizeProperPortsX P exact labeled).nodes.length := by simp
      have hle : ((sizeProperPortsX P exact labeled).nodes.map titleF).length ≤ v := by
        omega
      rw [List.getElem?_append_right hle, hlen] at hm2
      obtain ⟨q, _, hqeq⟩ : ∃ q, q ∈ titleNodes (sizeProperPortsX P exact labeled) ∧
          copyF q = m2 :=
        List.mem_map.mp (List.mem_of_getElem? hm2)
      have hb3 : m2.node.border = 3 := by rw [← hqeq]; rfl
      constructor <;> omega
  · have hge : (titleReservations (sizeProperPortsX P exact labeled)).nodes.length ≤ v :=
      Nat.le_of_not_lt hpre
    rw [List.getElem?_append_right hge] at hm2
    obtain ⟨_, hbE⟩ := hall m2 (List.mem_of_getElem? hm2)
    rcases hbE with hL | hR <;> constructor <;> omega

/-- A proxy coordinate index lies inside the labeled prefix. -/
private theorem XLEMLN_proxy_labeled_lt {P : Params} {exact : List Nat} {labeled : Proper}
    {run : Run}
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    {v : Nat} {nvc : ProperNode}
    (hcoordV : run.coordinateProper.nodes[v]? = some nvc)
    (hbVc : nvc.node.border = -2 ∨ nvc.node.border = 2) :
    v < labeled.nodes.length := by
  by_cases hgt : v < labeled.nodes.length
  · exact hgt
  · have hle : labeled.nodes.length ≤ v := Nat.le_of_not_lt hgt
    obtain ⟨hne1, hne2⟩ := XLEMLN_appended_nonproxy hc hcoordV hle
    rcases hbVc with h1 | h1 <;> omega

/-- Proxy proper nodes have height zero. -/
private theorem XLEMLN_proxy_proper_h_zero {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {labeled : Proper}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    (hkeys : NodeKeys cg labeled)
    {v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp)
    (hb : nvp.node.border = -2 ∨ nvp.node.border = 2) :
    RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨nvc, hcoordV, hbV, hhV⟩ := XLEMLN_proper_coord hrun hrec
  have hbVc : nvc.node.border = -2 ∨ nvc.node.border = 2 := by rw [hbV]; exact hb
  have hcoordV0 := hcoordV
  have hltL : v < labeled.nodes.length := XLEMLN_proxy_labeled_lt hc hcoordV hbVc
  have hlabeledV : labeled.nodes[v]? = some labeled.nodes[v] :=
    List.getElem?_eq_getElem hltL
  have hszLen : (sizeProperPortsX P exact labeled).nodes.length = labeled.nodes.length := by
    unfold sizeProperPortsX
    simp
  have hpre : v < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length := by
    rw [titleReservations_nodes, List.length_append, List.length_map, List.length_map]
    omega
  have hltS : v < (sizeProperPortsX P exact labeled).nodes.length := by omega
  have hcoordV' := hcoordV
  rw [← hc] at hcoordV'
  unfold coordinateGraphX at hcoordV'
  obtain ⟨m1, hm1, _, hb1, _, _⟩ := materialize_lookup _ hcoordV'
  rw [clearProxyExtents_nodes] at hm1
  obtain ⟨m2, hm2, hcm⟩ : ∃ m,
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW).nodes[v]? = some m ∧ clearF m = m1 :=
    Option.map_eq_some_iff.mp (by simpa [List.getElem?_map] using hm1)
  have hb2 : m2.node.border = m1.node.border := by
    have h := (clearF_keys m2).2.1
    rw [hcm] at h
    exact h.symm
  obtain ⟨extra, hx, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  rw [hx, List.getElem?_append_left hpre] at hm2
  rw [titleReservations_nodes, List.getElem?_append_left (by simpa [hszLen] using hltL)] at hm2
  obtain ⟨m3, hm3, htm⟩ : ∃ m,
      (sizeProperPortsX P exact labeled).nodes[v]? = some m ∧ titleF m = m2 :=
    Option.map_eq_some_iff.mp (by simpa [List.getElem?_map] using hm2)
  have hb3 : m3.node.border = m2.node.border := by
    have h := (titleF_keys m3).2.1
    rw [htm] at h
    exact h.symm
  have hkey := sizeProperPortsX_key P exact labeled v
  rw [hm3, hlabeledV] at hkey
  have hlnB : (labeled.nodes[v]).node.border = nvc.node.border := by
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
    obtain ⟨_, hb4, _⟩ := hkey
    omega
  have hlnB2 : (labeled.nodes[v]).node.border = -2 ∨ (labeled.nodes[v]).node.border = 2 := by
    rw [hlnB]; exact hbVc
  rcases hkeys v _ hlabeledV with ⟨_, _, hmd, _, _⟩ | ⟨_, hb0, _⟩
  · have hmark := X_coordinateGraph_marker_record (P := P) (exact := exact) hlabeledV hlnB2 hmd
    rw [hc] at hmark
    have hinj : clearF (titleF (labeled.nodes[v])) = nvc :=
      Option.some.inj (hmark.symm.trans hcoordV0)
    have hz : (clearF (titleF (labeled.nodes[v]))).node.h = 0 :=
      (clearF_keys _).2.2.2.trans ((titleF_keys _).2.2.2 hlnB2)
    have hnvc0 : nvc.node.h = 0 := hinj ▸ hz
    have hnvp : nvp.node.h = 0 := by omega
    have hH : RouteImpl.nodeH run.proper v = nvp.node.h := by simp [RouteImpl.nodeH, hrec]
    rw [hH]
    exact hnvp
  · omega

/-- A proxy box meets no footprint interior: its proper height is zero. -/
private theorem XLEMLN_proxy_miss {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {labeled : Proper}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (hc : coordinateGraphX P exact labeled = run.coordinateProper)
    (hkeys : NodeKeys cg labeled)
    {t v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp)
    (hb : nvp.node.border = -2 ∨ nvp.node.border = 2) :
    ¬ (loopFootprintExt cg run labels t).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  have hz : RouteImpl.nodeH run.proper v = 0 :=
    XLEMLN_proxy_proper_h_zero hrun hc hkeys hrec hb
  have hh : (RouteImpl.boxRect run.proper run.xs run.ys v).h = 0 := by
    simpa only [RouteImpl.boxRect] using hz
  intro hmeet
  obtain ⟨_, hy⟩ := hmeet
  omega

/-- Footprint origin from the owner frame equation. -/
private theorem XLEMLN_fp_of_frame {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {t : Nat}
    (hFr : frameRect default cg run t =
      RouteImpl.boxRect run.proper run.xs run.ys t) :
    (loopFootprintExt cg run labels t).x =
      (RouteImpl.boxRect run.proper run.xs run.ys t).x +
        (RouteImpl.boxRect run.proper run.xs run.ys t).w := by
  unfold loopFootprintExt
  simp only [hFr]

/-- Left non-plain case, proved: ordered intervals plus the footprint
origin close the miss for non-proxy `v`; proxies miss by zero height. -/
theorem XLEM_leftNonPlain_holds (exactIds : List String) :
    XLEM_LeftNonPlain exactIds := by
  intro inp o res execution comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope0 hscope1 hB0 hOrig layer hlayer pu pv hpu hpv hlt
  subst hcg
  have hbd := sceneExecutionX_edges_bounded execution
  have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp candidate
    hcomp hbd (List.mem_of_getElem? hk)
  have hltCG : e.tail < (componentCandidate execution.graph comp candidate).nodes.length :=
    hbnd.1
  obtain ⟨nt, hnt⟩ : ∃ nt,
      (componentCandidate execution.graph comp candidate).nodes[e.tail]? = some nt :=
    ⟨_, List.getElem?_eq_getElem hltCG⟩
  have hnb : nt.border = 0 := by
    have hget : (componentCandidate execution.graph comp candidate).nodes.getD e.tail
        default = nt := by
      rw [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
    rw [← hget]
    exact hB0
  have hcovered := componentRunX_original_nodes_covered hrun
  have htP : e.tail < run.proper.nodes.length := hcovered e.tail hltCG
  have hne2 : ((componentCandidate execution.graph comp candidate).nodes.getD e.tail
      default).border ≠ -2 := by
    have hget : (componentCandidate execution.graph comp candidate).nodes.getD e.tail
        default = nt := by
      rw [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
    rw [hget]
    omega
  have hFrBox := plain_frame_eq_boxRect default _ run e.tail htP hne2
  obtain ⟨actualT, hcoordT, hpropT, hb0T, _, _, _⟩ :=
    XLEMLN_original_plain_record hrun hnt hnb
  obtain ⟨ndV, hrecV⟩ : ∃ nd, run.proper.nodes[v]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hv⟩
  obtain ⟨actualV, hcoordV, hbV, _hhV⟩ := XLEMLN_proper_coord hrun hrecV
  by_cases hpx : actualV.node.border = -2 ∨ actualV.node.border = 2
  · obtain ⟨_, labeled, _, hc, hkeys, _, _, _, _⟩ :=
      X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
    exact XLEMLN_proxy_miss hrun hc hkeys hrecV (by rw [← hbV]; exact hpx)
  · obtain ⟨hproperV, _hxsV⟩ := XLEMLN_nonproxy_record hrun hcoordV hpx
    have hnpT : ¬(actualT.node.border = -2 ∨ actualT.node.border = 2) := by
      rw [hb0T]; decide
    have hord := XB_orderedIntervals_holds exactIds execution.graph0_eq execution.graph_eq
      hcomp hrun hlayer hlt hpv hpu hcoordV hcoordT hpx hnpT
    have hBwEq : (RouteImpl.boxRect run.proper run.xs run.ys e.tail).w =
        actualT.node.w := by
      simp only [RouteImpl.boxRect, RouteImpl.nodeW, hpropT]
    have hdims := componentRunX_dims_nonneg hrun
    have hBW : (0 : Int) ≤ (RouteImpl.boxRect run.proper run.xs run.ys e.tail).w := by
      rw [hBwEq]
      exact (hdims e.tail actualT hpropT).1
    have hfp := XLEMLN_fp_of_frame (labels := execution.measured) hFrBox
    have eV : (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w =
        RouteImpl.leftOf run.proper run.xs v +
          RouteImpl.nodeW run.proper v := rfl
    have eT : (RouteImpl.boxRect run.proper run.xs run.ys e.tail).x =
        RouteImpl.leftOf run.proper run.xs e.tail := rfl
    have hgap : (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤
        (loopFootprintExt (componentCandidate execution.graph comp candidate) run
          execution.measured e.tail).x := by
      omega
    exact XLEMLN_rect_miss_left hgap

end PipelineImpl
end Layered
end Elegant

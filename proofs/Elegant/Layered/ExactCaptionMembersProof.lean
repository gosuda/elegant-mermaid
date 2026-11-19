import Elegant.Layered.ExactCaptionRunClearProof
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.BracketInsideRankFacts
import Elegant.Layered.CgShape
import Elegant.Layered.CoordGraph
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ExecutedFrameClearanceFacts

set_option autoImplicit false

open Elegant
open Elegant.Layered

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact run-level caption members (`XC_SameDeclMarkerX`, `XC_MemberDescX`, `XC_PlainMemberX`)

Proves the three member-case residuals of `XF_captionRunClearX_holds` by
replaying the plain proofs over `componentRunX`:

* `captionSameDeclMarkerDisjoint_executed` (`CaptionSameDeclMarkerProof`):
  the same-declaration trichotomy travels across `exactGraph`
  (`X_componentCandidate_marker_shape`); the border-`0` impossibility is pure
  declaration-index reasoning transported by `XCM_node_key_rev`; the bottom
  marker uses `X_componentRun_cg_bottom_find` + `X_group_top_lt_bottom` with
  the same band lemmas through `componentRunX_spec`. Exact replacement per
  the `ExactCaptionRunClearProof` header table: same band lemmas via
  `componentRunX_spec`.
* `captionPlainMemberClear_proved` (`CaptionLocalClearProof.lean:480`): the
  member rank lower bound replays through `X_cg_run_bundle` +
  `ranked_compound_member_interval`; bands come from `X_ReserveBands_holds`.
  Exact replacement per the header table: pre-reserve plus reserved bands
  and sibling disjointness.
* `captionMemberDescDisjoint_executed` (`CaptionDescDisjointProof`): the
  descendant rank chain and child-top facts need input well-formedness, so
  they stay as the narrow rank residuals `XC_DescChainX` / `XC_ChildTopX`
  below; the band assembly replays as in the other two cases. Exact
  replacement per the header table: same band lemmas plus `ExactPartBounded`
  title/record facts.

The transported caption bottom bound (`captionInTopBand_executed`) needs the
exact title-copy machinery, so it stays as the narrow single-inequality
residual `XC_CapBandX`. All three narrow residuals are single geometric
facts, strictly narrower than their goals, and true on the probe
(`proofs/wip/Probe/ExactCaptionMembersTProbe.lean`: flat, nested, sane
fixed, wider-than-slot fixed, taller-than-band fixed inputs).
-/

/-- `XCM_` copy of the private `X_exactGraph_node_key_rev`
(`ExactFlatC5Rank.lean:112`): exact-to-measured key transfer. -/
private theorem XCM_node_key_rev {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g g' : Graph}
    (h : exactGraph P exactIds inp o measured g = .ok g')
    {v : Nat} {nd' : Node} (hv : g'.nodes[v]? = some nd') :
    ∃ nd, g.nodes[v]? = some nd ∧ nd'.border = nd.border ∧
      nd'.clusterPath = nd.clusterPath ∧ nd'.decl = nd.decl := by
  have hlen : g'.nodes.length = g.nodes.length := exactGraph_length h
  have hvlt : v < g.nodes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hv).1
    omega
  have hmem : g.nodes[v]? = some g.nodes[v] := List.getElem?_eq_getElem hvlt
  obtain ⟨nd'', hnd'', hb, hc, hd⟩ := exactGraph_node_key h hmem
  have heq : nd'' = nd' := Option.some.inj (hnd''.symm.trans hv)
  subst heq
  exact ⟨g.nodes[v], hmem, hb, hc, hd⟩

/-- `XCM_` copy of `X_coordinateGraph_anchor_prefix`
(`ExactFlatC5Rank.lean:2435`). -/
private theorem XCM_coordinateGraph_anchor_prefix (P : Params) (exact : List Nat)
    (p : Proper) :
    ∃ extra, (coordinateGraphX P exact p).rank = p.rank ++ extra := by
  obtain ⟨extraRanks, hr⟩ := addClusterBorders_rank_prefix
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  obtain ⟨tail, htitle⟩ : ∃ tail, (titleReservations (sizeProperPortsX P exact p)).rank =
      p.rank ++ tail := by
    unfold titleReservations sizeProperPortsX
    exact ⟨_, rfl⟩
  refine ⟨tail ++ extraRanks, ?_⟩
  change (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).rank = _
  rw [hr, htitle, List.append_assoc]

/-- `XCM_` copy of `X_coordinateGraph_rank_record`
(`ExactFlatC5Rank.lean:2447`). -/
private theorem XCM_coordinateGraph_rank_record {P : Params} {exact : List Nat}
    {source : Proper} {index : Nat} {rank : Int}
    (h : source.rank[index]? = some rank) :
    (coordinateGraphX P exact source).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := XCM_coordinateGraph_anchor_prefix P exact source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- `XCM_` copy of `X_prepared_coordinate_original_rk`
(`ExactFlatC5Rank.lean:2495`). -/
private theorem XCM_prepared {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {source : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      source.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (coordinateGraphX P exact source).rank index = rk rr.ranks index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have hcoordinateLookup := XCM_coordinateGraph_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  simp only [rk, List.getD_eq_getElem?_getD, hcoordinateLookup, hrrLookup, Option.getD_some]

/-- `XCM_` copy of `XN_run_record_source`
(`ExactForeignNonGroupSpansProof.lean:166`). -/
private theorem XCM_run_record {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
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

/-- `XCM_` copy of `X_nonproxy_record` (`ExactFlatC2.lean:96`). -/
private theorem XCM_nonproxy {P : Params} {exact : List Nat}
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

/-- `XCM_` copy of `X_plain_node_path_source`
(`ExactFlatC7ExclusiveKey.lean:276`): measured-graph plain node source. -/
private theorem XCM_plain_path {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box := by
  obtain ⟨nodes, _edges, _titles, hprepared, _hnodeLength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hlines := execution.lines_eq
  unfold boxLines at hlines
  have hlineLength : execution.lines.length = inp.boxes.length := by
    simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlines).1
  have hpreparedNode := hnode
  rw [hprepared] at hpreparedNode
  have hi : index < nodes.length := by
    by_cases hi : index < nodes.length
    · exact hi
    · have hb := Compound.prepare_bottom_of_index _ _ _ _ index (by dsimp only; omega)
        hpreparedNode
      omega
  have hibox : index < inp.boxes.length := by omega
  let box := inp.boxes[index]'hibox
  have hbox : inp.boxes[index]? = some box := List.getElem?_eq_getElem hibox
  obtain ⟨_, hchangedBox, hpathMap⟩ := fixedSizes_path_index inp hbox
  obtain ⟨hdecl, hpath⟩ :=
    prepare_plain_path_origin _ _ _ _ hmetadata hpreparedNode hplain hchangedBox
  exact ⟨box, hbox, hdecl, hpath.trans hpathMap⟩

/-- Exact bottom-marker uniqueness transported from the measured graph
(copy of `measuredGraph_bottom_pair_eq` across `XCM_node_key_rev`). -/
private theorem XCM_bottom_pair_eq {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {e f : Node × Nat} (he : e ∈ graph.nodes.zipIdx) (hf : f ∈ graph.nodes.zipIdx)
    (hbe : e.1.border = 2) (hbf : f.1.border = 2) (hde : e.1.decl = f.1.decl) :
    e = f := by
  have helook : graph.nodes[e.2]? = some e.1 := List.mem_zipIdx_iff_getElem?.mp he
  have hflook : graph.nodes[f.2]? = some f.1 := List.mem_zipIdx_iff_getElem?.mp hf
  obtain ⟨e0, he0look, he0bord, _, he0decl⟩ := XCM_node_key_rev h helook
  obtain ⟨f0, hf0look, hf0bord, _, hf0decl⟩ := XCM_node_key_rev h hflook
  have hbe0 : e0.border = 2 := by rw [← he0bord]; exact hbe
  have hbf0 : f0.border = 2 := by rw [← hf0bord]; exact hbf
  have hde0 : e0.decl = f0.decl := by rw [← he0decl, ← hf0decl]; exact hde
  have he0mem : (e0, e.2) ∈ graph0.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr he0look
  have hf0mem : (f0, f.2) ∈ graph0.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hf0look
  have hpair := measuredGraph_bottom_pair_eq h0 he0mem hf0mem hbe0 hbf0 hde0
  have hidx : e.2 = f.2 := (Prod.mk.inj hpair).2
  rw [hidx] at helook
  have hnode : e.1 = f.1 := Option.some.inj (helook.symm.trans hflook)
  exact Prod.ext hnode hidx

/-- `XCM_` copy of `componentRun_proxy_interval`
(`ExecutedFrameClearanceFacts.lean`) over `componentRunX_spec`. -/
private theorem XCM_proxy_interval {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
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

/-- `XCM_` copy of `desc_bottom_coordinate`
(`CaptionDescDisjointProof.lean:334`). -/
private theorem XCM_bottom_coordinate {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hgroup : nd.border = 2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = 2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
  obtain ⟨_, labeled, _, hc, _, _, hrecords, _, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hrecords v nd hnode
  have hmarker := X_coordinateGraph_marker_record (P := P) (exact := exact) hrec
    (Or.inr hgroup) rfl
  rw [hc] at hmarker
  have hb : (clearF (titleF ⟨nd, false, none, false⟩)).node.border = 2 := by
    have h1 := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [h1, (titleF_keys _).2.1]
    exact hgroup
  have hd : (clearF (titleF ⟨nd, false, none, false⟩)).dummy = false :=
    (clearF_keys _).1.trans (titleF_keys _).1
  have hp : (clearF (titleF ⟨nd, false, none, false⟩)).node.clusterPath = nd.clusterPath :=
    (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
  have hh : (clearF (titleF ⟨nd, false, none, false⟩)).node.h = 0 :=
    (clearF_keys _).2.2.2.trans
      ((titleF_keys ⟨nd, false, none, false⟩).2.2.2 (Or.inr hgroup))
  exact ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, hb, hd, hp, hh⟩

/-- `XCM_` copy of `desc_bottom_proper`
(`CaptionDescDisjointProof.lean:362`). -/
private theorem XCM_bottom_proper {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = 2) (hcoordH : coord.node.h = 0) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath ∧
      RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨owner, span, _, _, hproper, _, _⟩ :=
    XCM_proxy_interval hrun hcoord (Or.inr hb)
  have hh : RouteImpl.nodeH run.proper v = 0 := by
    simp only [RouteImpl.nodeH, hproper]
    exact hcoordH
  exact ⟨_, hproper, rfl, hh⟩

/-- `XCM_` bottom-marker path fact via `X_cg_bottom_box`
(copy of `desc_bottom_path`). -/
private theorem XCM_bottom_path {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hborder : nd.border = 2) :
    nd.clusterPath.getLast? = some nd.decl ∧ nd.clusterPath.contains nd.decl = true := by
  obtain ⟨box, hbox, hpath⟩ := X_cg_bottom_box h0 h hnode hborder
  exact ⟨by rw [hpath]; simp, by rw [hpath]; simp⟩

/-- `XCM_` copies of `desc_foldl_minY_le` + `desc_minY_of_all_le` (pure geometry). -/
private theorem XCM_foldl_minY_le (rects : List Rect) (b : Bounds) (lo : Int)
    (hb : lo ≤ b.minY) (hall : ∀ r ∈ rects, lo ≤ r.y) :
    lo ≤ ((rects.foldl fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).minY := by
  induction rects generalizing b with
  | nil => simpa using hb
  | cons first rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · show lo ≤ min b.minY first.y
      have h1 := hb
      have h2 := hall first (by simp)
      omega
    · intro r hr
      exact hall r (List.mem_cons_of_mem _ hr)

private theorem XCM_minY_of_all_le (rects : List Rect) (lo : Int)
    (hall : ∀ r ∈ rects, lo ≤ r.y) (hne : rects ≠ []) :
    lo ≤ (boundsOf rects []).minY := by
  cases rects with
  | nil => exact absurd rfl hne
  | cons first rest =>
    unfold boundsOf
    dsimp only
    exact XCM_foldl_minY_le (first :: rest) _ lo (hall first (by simp)) hall

/-- `XCM_` exact group side-marker lookup (copy of
`SceneExecution.component_group_final_side` across the `X_` sources). -/
private theorem XCM_group_final_side {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ (sideIndex : Nat) (side : ProperNode),
      run.proper.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      side.node.clusterPath.getLast? = some node.decl := by
  obtain ⟨_, labeled, _, _, hc, _, _, hrecords, _, _, _⟩ :=
    X_group_bottom_source h0 h hcomp hrun hnode hgroup
  let proxy := clearF (titleF ⟨node, false, none, false⟩)
  have hproxy : run.coordinateProper.nodes[index]? = some proxy := by
    rw [← hc]
    exact X_coordinateGraph_marker_record (hrecords index node hnode) (Or.inl hgroup) rfl
  have hproxyBorder : proxy.node.border = -2 :=
    (clearF_keys _).2.1.trans ((titleF_keys _).2.1.trans hgroup)
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, _⟩ :=
    X_proxy_side_source hrun hproxy (Or.inl hproxyBorder)
  obtain ⟨_, _, hpath⟩ := X_cg_group_box h0 h hnode hgroup
  have hproxyLast : proxy.node.clusterPath.getLast? = some node.decl := by
    change (clearF (titleF ⟨node, false, none, false⟩)).node.clusterPath.getLast? = _
    rw [(clearF_keys _).2.2.1, (titleF_keys _).2.2.1]
    simp [hpath]
  have hsideProper : run.proper.nodes[sideIndex]? = some side :=
    (XCM_nonproxy hrun hside (by intro hc; rcases hsideBorder with h | h <;> rcases hc with h2 | h2 <;> omega)).1
  exact ⟨sideIndex, side, hsideProper, hsideBorder,
    hsideOwner.trans (howner.symm.trans hproxyLast)⟩

/-- Narrow shared residual: the transported caption bottom lies in its top
rank band. Single inequality; strictly narrower than any run-level
disjointness. -/
def XC_CapBandX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ (i : Nat) (stored0 : Rect) (tNode : Node),
      (i, stored0) ∈ componentTitles execution.params
        (componentCandidate execution.graph comp candidate) run →
      (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode →
      tNode.border = -2 →
      (transportCaption execution.params o execution.lines comp i stored0).y +
        (transportCaption execution.params o execution.lines comp i stored0).h ≤
        run.top.getD (rk run.coordinateProper.rank i).toNat 0 +
          CoordsImpl.layerHeight run.coordinateProper
            (run.layers.getD (rk run.coordinateProper.rank i).toNat [])

/-- Narrow descendant-rank residual: nested group tops strictly increase in
rank. Bundles the scope-prefix and chain steps into one rank fact over the
executed run. -/
def XC_DescChainX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {a b : Nat} {na nb : Node},
      (componentCandidate execution.graph comp candidate).nodes[a]? = some na →
      na.border = -2 →
      (componentCandidate execution.graph comp candidate).nodes[b]? = some nb →
      nb.border = -2 →
      na.decl ≠ nb.decl →
      nb.clusterPath.contains na.decl = true →
      ∃ rr : RankImpl.RankResult,
        rankWithBudget (Compound.rankingGraph
          (componentCandidate execution.graph comp candidate)) = .ok rr ∧
        rk rr.ranks a + 1 ≤ rk rr.ranks b

/-- Narrow child-top residual: the executed child-top rank bound over exact
runs (`ChildTopRankLe`). One rank fact; covers both the descendant-frame
hull argument and the bottom-marker top closure. -/
def XC_ChildTopX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {c : Nat} {nd : Node},
      (componentCandidate execution.graph comp candidate).nodes[c]? = some nd →
      nd.border = -2 →
      ChildTopRankLe (componentCandidate execution.graph comp candidate) run c

 /-- Same-declaration marker case over exact runs: replay of
 `captionSameDeclMarkerDisjoint_executed`. The trichotomy travels across
 `exactGraph`; the border-`0` impossibility is declaration-index reasoning
 transported by `XCM_node_key_rev`; the bottom marker uses the exact bottom
 bundle and the reserved-band gap. -/
 theorem XC_sameDeclMarkerX_holds (exactIds : List String)
     (hcap : XC_CapBandX exactIds) : XC_SameDeclMarkerX exactIds := by
   intro inp o res execution comp hcomp candidate run orderOptions hrun
   intro i stored0 tNode hmem hnode hborder pos fNode g0 hfn hsame hne hframe
   have hshape := (X_componentCandidate_marker_shape execution.graph0_eq
     execution.graph_eq hfn).1
   rcases hshape with hbor0 | hborNe | hbor2
   · obtain ⟨origT, _, hsrcT⟩ := componentCandidate_nonplain_source hnode (by omega)
     obtain ⟨t0, ht0look, htbord, _, ht0decl⟩ := XCM_node_key_rev execution.graph_eq hsrcT
     have htbordT : t0.border = -2 := by rw [← htbord]; exact hborder
     obtain ⟨hdeclT, _⟩ := measuredGraph_group_origin execution.graph0_eq ht0look htbordT
     have hfn2 : (comp.map fun v => execution.graph.nodes.getD v default)[pos]? =
         some fNode := by
       simpa [componentCandidate_nodes, componentGraph] using hfn
     rw [List.getElem?_map] at hfn2
     obtain ⟨origP, hcompP, hgetP⟩ := Option.map_eq_some_iff.mp hfn2
     have hltP : origP < execution.graph.nodes.length := by
       have hmemP : origP ∈ comp := List.mem_of_getElem? hcompP
       have hcomp' := hcomp
       simp only [components] at hcomp'
       obtain ⟨r, _, rfl⟩ := List.mem_map.mp hcomp'
       exact List.mem_range.mp (List.mem_filter.mp hmemP).1
     have hsrcP : execution.graph.nodes[origP]? = some fNode := by
       obtain ⟨n, hn⟩ : ∃ n, execution.graph.nodes[origP]? = some n :=
         ⟨_, List.getElem?_eq_some_iff.mpr ⟨hltP, rfl⟩⟩
       have hget : execution.graph.nodes.getD origP default = n := by
         simp [List.getD_eq_getElem?_getD, hn]
       rw [hget] at hgetP
       rw [hgetP] at hn
       exact hn
     obtain ⟨f0, hf0look, hf0bord, _, hf0decl⟩ := XCM_node_key_rev execution.graph_eq hsrcP
     have hf0bord0 : f0.border = 0 := by rw [← hf0bord]; exact hbor0
     obtain ⟨_, _, hdeclP, _⟩ := XCM_plain_path execution hf0look hf0bord0
     have hTP : origT = origP :=
       hdeclT.symm.trans (ht0decl.symm.trans (hsame.trans (hf0decl.trans hdeclP)))
     have hcontra : tNode = fNode := by
       have h1 : execution.graph.nodes[origT]? = some tNode := hsrcT
       rw [hTP] at h1
       exact Option.some.inj (h1.symm.trans hsrcP)
     have hb := congrArg Node.border hcontra
     rw [hborder, hbor0] at hb
     omega
   · exact (hne hborNe).elim
   · have hlines : execution.lines.length = inp.boxes.length := by
       have h := (mapM_getElem? _ _ _ execution.lines_eq).1
       simpa only [List.length_zipIdx] using h
     obtain ⟨bottom, hbottom⟩ :=
       X_componentRun_cg_bottom_find execution.graph0_eq execution.graph_eq hlines
         hcomp hnode hborder
     have hbordB : bottom.1.border = 2 := by
       have hcond := List.find?_some hbottom
       simp only [Bool.and_eq_true, beq_iff_eq] at hcond
       exact hcond.1
     have hdeclB : bottom.1.decl = tNode.decl := by
       have hcond := List.find?_some hbottom
       simp only [Bool.and_eq_true, beq_iff_eq] at hcond
       exact hcond.2
     have hnodeB : (componentCandidate execution.graph comp candidate).nodes[bottom.2]? =
         some bottom.1 :=
       List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hbottom)
     obtain ⟨origP, hcompP, hsrcP⟩ := componentCandidate_nonplain_source hfn (by omega)
     obtain ⟨origB, hcompB, hsrcB⟩ := componentCandidate_nonplain_source hnodeB (by omega)
     have hmemP : (fNode, origP) ∈ execution.graph.nodes.zipIdx :=
       List.mem_zipIdx_iff_getElem?.mpr hsrcP
     have hmemB : (bottom.1, origB) ∈ execution.graph.nodes.zipIdx :=
       List.mem_zipIdx_iff_getElem?.mpr hsrcB
     have hde : fNode.decl = bottom.1.decl := (hdeclB.trans hsame).symm
     have hpair :=
       XCM_bottom_pair_eq execution.graph0_eq execution.graph_eq hmemP hmemB hbor2 hbordB hde
     have horig : origP = origB := congrArg Prod.snd hpair
     have hpos : pos = bottom.2 := by
       have hnd := components_nodup execution.graph comp hcomp
       have hmapnd : (comp.map id).Nodup := by simpa using hnd
       have hcompB' : comp[bottom.2]? = some origP := by rw [horig]; exact hcompB
       exact nodup_map_inj_aux id hmapnd hcompP hcompB' rfl
     subst hpos
     have hindexLt : i < (componentCandidate execution.graph comp candidate).nodes.length :=
       (List.getElem?_eq_some_iff.mp hnode).1
     have hbotLt : bottom.2 < (componentCandidate execution.graph comp candidate).nodes.length :=
       (List.getElem?_eq_some_iff.mp hnodeB).1
     obtain ⟨rrB, _, hrrB, hcB, _, _, hranksB, hlt⟩ :=
       X_group_top_lt_bottom execution.graph0_eq execution.graph_eq hcomp hrun
     have htopLtBot := hlt i tNode bottom hnode hborder hbottom
     have eTop : rk run.coordinateProper.rank i = rk rrB.ranks i := by
       have h2x := XCM_prepared (P := execution.params) (exact := exactDecls exactIds inp)
         hrrB hranksB hindexLt
       rw [hcB] at h2x
       exact h2x
     have eBottom : rk run.coordinateProper.rank bottom.2 = rk rrB.ranks bottom.2 := by
       have h2x := XCM_prepared (P := execution.params) (exact := exactDecls exactIds inp)
         hrrB hranksB hbotLt
       rw [hcB] at h2x
       exact h2x
     have rEqT := X_proper_rank_eq_local hrun i
     have rEqB := X_proper_rank_eq_local hrun bottom.2
     obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, _⟩ := componentRunX_spec hrun
     have hindexLen : i < run.proper.nodes.length :=
       componentRunX_original_nodes_covered hrun i hindexLt
     have hbotLen : bottom.2 < run.proper.nodes.length :=
       componentRunX_original_nodes_covered hrun bottom.2 hbotLt
     have hcov :=
       (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
     obtain ⟨ltT, hlyT, hmemT, hnnT⟩ := hcov i hindexLen
     obtain ⟨ltB, hlyB, hmemB, hnnB⟩ := hcov bottom.2 hbotLen
     rw [rEqT] at hlyT hnnT
     rw [rEqB] at hlyB hnnB
     have hltTB : (rk run.coordinateProper.rank i).toNat <
         (rk run.coordinateProper.rank bottom.2).toNat := by
       have h1 := eTop
       have h2y := eBottom
       have h3 : rk rrB.ranks i + 1 ≤ rk rrB.ranks bottom.2 := htopLtBot
       have h4 := hnnT
       have h5 := hnnB
       omega
     have hRB := (X_ReserveBands_holds exactIds) hrun
     have hbandTB := hRB.2 _ _ _ _ hltTB hlyT hlyB
     have hcoordLenB : bottom.2 < run.coordinateProper.nodes.length := by
       obtain ⟨_, _, _, q0B, _, _, _, _, _, hproxyB, hdropB, _, _, _⟩ :=
         componentRunX_spec hrun
       obtain ⟨_, _, hqlenB, _, _, _⟩ := proxyWidths_rel hproxyB
       have hnodesB : run.proper.nodes = q0B.nodes := by rw [← hdropB]; rfl
       have h1 : bottom.2 < q0B.nodes.length := by rw [← hnodesB]; exact hbotLen
       omega
     have hrkBnn : 0 ≤ rk run.coordinateProper.rank bottom.2 := hnnB
     have hrkB : rk run.coordinateProper.rank bottom.2 =
         ((rk run.coordinateProper.rank bottom.2).toNat : Int) := by
       have h := Int.toNat_of_nonneg hrkBnn
       exact h.symm
     have hbandLo := hRB.1 _ _ _ hlyB hmemB hcoordLenB hrkB
     have hcap0 := hcap execution hcomp hrun i stored0 tNode hmem hnode hborder
     have hltTget : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = ltT := by
       simp only [List.getD_eq_getElem?_getD, hlyT, Option.getD_some]
     have hposGet : (componentCandidate execution.graph comp candidate).nodes.getD
         bottom.2 default = fNode := by
       simp only [List.getD_eq_getElem?_getD, hfn, Option.getD_some]
     have hfr : frameRect execution.params (componentCandidate execution.graph comp candidate)
         run bottom.2 =
         nodeRect (componentCandidate execution.graph comp candidate) run bottom.2 := by
       unfold frameRect
       simp only []
       rw [hposGet, hbor2]
       rfl
     have hgy : (nodeRect (componentCandidate execution.graph comp candidate) run
         bottom.2).y = run.ys.getD bottom.2 0 := rfl
     rw [← hframe, hfr]
     unfold Disjoint
     intro hcon
     obtain ⟨-, hy⟩ := hcon
     rw [hltTget] at hcap0
     omega

 /-- Plain-member case over exact runs: replay of
 `captionPlainMemberClear_proved`. The member rank lower bound replays through
 the exact rank bundle; bands come from `X_ReserveBands_holds`. -/
 theorem XC_plainMemberX_holds (exactIds : List String)
     (hcap : XC_CapBandX exactIds) : XC_PlainMemberX exactIds := by
   intro inp o res execution comp hcomp candidate run orderOptions hrun
   intro i stored0 tNode hmem hnode hborder pos fNode g0 hfn hne hplain hpath hframe
   have hlines : execution.lines.length = inp.boxes.length := by
     have h := (mapM_getElem? _ _ _ execution.lines_eq).1
     simpa only [List.length_zipIdx] using h
   obtain ⟨rr, _, hrr, hc, _, _, hrecords, hranks, _⟩ :=
     X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
   obtain ⟨bottom, hbottom⟩ :=
     X_componentRun_cg_bottom_find execution.graph0_eq execution.graph_eq hlines
       hcomp hnode hborder
   have hinterv := ranked_compound_member_interval hrr
     (List.mk_mem_zipIdx_iff_getElem?.mpr hnode) hborder hbottom
     (List.mk_mem_zipIdx_iff_getElem?.mpr hfn) hplain hpath
   have hindexLt : i < (componentCandidate execution.graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp hnode).1
   have hmemberLt : pos < (componentCandidate execution.graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp hfn).1
   have eTop : rk run.coordinateProper.rank i = rk rr.ranks i := by
     have h2 := XCM_prepared (P := execution.params) (exact := exactDecls exactIds inp)
       hrr hranks hindexLt
     rw [hc] at h2
     exact h2
   have eMember : rk run.coordinateProper.rank pos = rk rr.ranks pos := by
     have h2 := XCM_prepared (P := execution.params) (exact := exactDecls exactIds inp)
       hrr hranks hmemberLt
     rw [hc] at h2
     exact h2
   have rEqT := X_proper_rank_eq_local hrun i
   have rEqM := X_proper_rank_eq_local hrun pos
   obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, _⟩ := componentRunX_spec hrun
   have hindexLen : i < run.proper.nodes.length :=
     componentRunX_original_nodes_covered hrun i hindexLt
   have hmemberLen : pos < run.proper.nodes.length :=
     componentRunX_original_nodes_covered hrun pos hmemberLt
   have hcov :=
     (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
   obtain ⟨ltT, hlyT, hmemT, hnnT⟩ := hcov i hindexLen
   obtain ⟨ltM, hlyM, hmemM, hnnM⟩ := hcov pos hmemberLen
   rw [rEqT] at hlyT hnnT
   rw [rEqM] at hlyM hnnM
   have hltTM : (rk run.coordinateProper.rank i).toNat <
       (rk run.coordinateProper.rank pos).toNat := by
     have h1 := eTop
     have h2 := eMember
     have h3 : rk rr.ranks i + 1 ≤ rk rr.ranks pos := hinterv.1
     have h4 := hnnT
     have h5 := hnnM
     omega
   have hRB := (X_ReserveBands_holds exactIds) hrun
   have hbandTM := hRB.2 _ _ _ _ hltTM hlyT hlyM
   have hcoordLenM : pos < run.coordinateProper.nodes.length := by
     obtain ⟨_, _, _, q0M, _, _, _, _, _, hproxyM, hdropM, _, _, _⟩ :=
       componentRunX_spec hrun
     obtain ⟨_, _, hqlenM, _, _, _⟩ := proxyWidths_rel hproxyM
     have hnodesM : run.proper.nodes = q0M.nodes := by rw [← hdropM]; rfl
     have h1 : pos < q0M.nodes.length := by rw [← hnodesM]; exact hmemberLen
     omega
   have hrkMnn : 0 ≤ rk run.coordinateProper.rank pos := hnnM
   have hrkM : rk run.coordinateProper.rank pos =
       ((rk run.coordinateProper.rank pos).toNat : Int) := by
     have h := Int.toNat_of_nonneg hrkMnn
     exact h.symm
   have hMemBandLo := hRB.1 _ _ _ hlyM hmemM hcoordLenM hrkM
   have hcap0 := hcap execution hcomp hrun i stored0 tNode hmem hnode hborder
   have hltTget : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = ltT := by
     simp only [List.getD_eq_getElem?_getD, hlyT, Option.getD_some]
   have hmemberGet : (componentCandidate execution.graph comp candidate).nodes.getD pos
       default = fNode := by
     simp only [List.getD_eq_getElem?_getD, hfn, Option.getD_some]
   have hfr : frameRect execution.params (componentCandidate execution.graph comp candidate)
       run pos =
       nodeRect (componentCandidate execution.graph comp candidate) run pos := by
     unfold frameRect
     simp only []
     rw [hmemberGet, hplain]
     rfl
   have hgy : (nodeRect (componentCandidate execution.graph comp candidate) run pos).y =
       run.ys.getD pos 0 := rfl
   rw [← hframe, hfr]
   unfold Disjoint
   intro hcon
   obtain ⟨-, hy⟩ := hcon
   rw [hltTget] at hcap0
   omega

 /-- Descendant case over exact runs: replay of
 `captionMemberDescDisjoint_executed`. The rank chain and child-top bound
 stay as the narrow residuals `XC_DescChainX` / `XC_ChildTopX`; the band
 assembly replays through `componentRunX_spec` and `X_ReserveBands_holds`. -/
 theorem XC_memberDescX_holds (exactIds : List String)
     (hcap : XC_CapBandX exactIds) (hchain : XC_DescChainX exactIds)
     (hchild : XC_ChildTopX exactIds) : XC_MemberDescX exactIds := by
   intro inp o res execution comp hcomp candidate run orderOptions hrun
   intro i stored0 tNode hmem hnode hborder pos fNode g0 hfn hne hpath hnonplain hframe
   have hlines : execution.lines.length = inp.boxes.length := by
     have h := (mapM_getElem? _ _ _ execution.lines_eq).1
     simpa only [List.length_zipIdx] using h
   have hindexLt : i < (componentCandidate execution.graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp hnode).1
   have hposLt : pos < (componentCandidate execution.graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp hfn).1
   obtain ⟨rr, _, hrr, hc, _, _, _, hranks, _⟩ :=
     X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
   have eTop : rk run.coordinateProper.rank i = rk rr.ranks i := by
     have h2 := XCM_prepared (P := execution.params) (exact := exactDecls exactIds inp)
       hrr hranks hindexLt
     rw [hc] at h2
     exact h2
   have rEqT := X_proper_rank_eq_local hrun i
   have rEqM := X_proper_rank_eq_local hrun pos
   obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, _⟩ := componentRunX_spec hrun
   have hindexLen : i < run.proper.nodes.length :=
     componentRunX_original_nodes_covered hrun i hindexLt
   have hposLen : pos < run.proper.nodes.length :=
     componentRunX_original_nodes_covered hrun pos hposLt
   have hcov :=
     (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
   obtain ⟨ltT, hlyT, _, hnnT⟩ := hcov i hindexLen
   rw [rEqT] at hlyT hnnT
   have hcap0 := hcap execution hcomp hrun i stored0 tNode hmem hnode hborder
   have hltTget : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = ltT := by
     simp only [List.getD_eq_getElem?_getD, hlyT, Option.getD_some]
   rw [hltTget] at hcap0
   have hmemberGet : (componentCandidate execution.graph comp candidate).nodes.getD pos
       default = fNode := by
     simp only [List.getD_eq_getElem?_getD, hfn, Option.getD_some]
   have hRB := (X_ReserveBands_holds exactIds) hrun
   obtain ⟨ltM, hlyM, _, hnnM⟩ := hcov pos hposLen
   have hnnM0 : 0 ≤ rk run.proper.rank pos := hnnM
   rw [rEqM] at hlyM hnnM
   by_cases hfb : fNode.border = -2
   · obtain ⟨rrC, hrrC, hchainLe⟩ :=
       hchain execution hcomp hrun hnode hborder hfn hfb hne hpath
     have hrrEq : rrC = rr := Except.ok.inj (hrrC.symm.trans hrr)
     rw [hrrEq] at hchainLe
     have ePos : rk run.coordinateProper.rank pos = rk rr.ranks pos := by
       have h2 := XCM_prepared (P := execution.params) (exact := exactDecls exactIds inp)
         hrr hranks hposLt
       rw [hc] at h2
       exact h2
     have hltTM : (rk run.coordinateProper.rank i).toNat <
         (rk run.coordinateProper.rank pos).toNat := by
       have h1 := eTop
       have h2 := ePos
       have h3 : rk rr.ranks i + 1 ≤ rk rr.ranks pos := hchainLe
       have h4 := hnnT
       have h5 := hnnM
       omega
     have hbandTM := hRB.2 _ _ _ _ hltTM hlyT hlyM
     have htopLe := hchild execution hcomp hrun hfn hfb
     unfold ChildTopRankLe at htopLe
     rw [hmemberGet] at htopLe
     obtain ⟨sideIndex, side, hside, _, howner⟩ :=
       XCM_group_final_side execution.graph0_eq execution.graph_eq hcomp hrun hfn hfb
     let descRects := run.proper.nodes.zipIdx.filterMap fun q =>
       if q.1.node.clusterPath.contains fNode.decl then
         some (Labels.rectAt run.proper run.xs run.ys q.2)
       else none
     have hsideMem : Labels.rectAt run.proper run.xs run.ys sideIndex ∈ descRects := by
       apply List.mem_filterMap.mpr
       refine ⟨(side, sideIndex), List.mem_zipIdx_iff_getElem?.mpr hside, ?_⟩
       have hmemSide : fNode.decl ∈ side.node.clusterPath := List.mem_of_getLast? howner
       simp [hmemSide]
     have hneDesc : descRects ≠ [] := by
       intro hempty
       rw [hempty] at hsideMem
       exact List.not_mem_nil hsideMem
     have hmin : run.top.getD (rk run.coordinateProper.rank pos).toNat 0 ≤
         (boundsOf descRects []).minY := by
       refine XCM_minY_of_all_le _ _ ?_ hneDesc
       intro r hr
       obtain ⟨entry, hentry, heq⟩ := List.mem_filterMap.mp hr
       split at heq
       · rename_i hcontains
         have hrectEq := Option.some.inj heq
         rw [← hrectEq]
         have hle : rk run.proper.rank pos ≤ rk run.proper.rank entry.2 :=
           htopLe entry hentry hcontains
         have hqLen : entry.2 < run.proper.nodes.length :=
           (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hentry)).1
         have hqCoordLen : entry.2 < run.coordinateProper.nodes.length := by
           obtain ⟨_, _, _, q0E, _, _, _, _, _, hproxyE, hdropE, _, _, _⟩ :=
             componentRunX_spec hrun
           obtain ⟨_, _, hqlenE, _, _, _⟩ := proxyWidths_rel hproxyE
           have hnodesE : run.proper.nodes = q0E.nodes := by rw [← hdropE]; rfl
           have h1 : entry.2 < q0E.nodes.length := by rw [← hnodesE]; exact hqLen
           omega
         have rEqE := X_proper_rank_eq_local hrun entry.2
         have hleC : rk run.coordinateProper.rank pos ≤
             rk run.coordinateProper.rank entry.2 := by
           rw [← rEqM, ← rEqE]; exact hle
         obtain ⟨ltQ, hlyQ, hmemQ, hnnQ⟩ := hcov entry.2 hqLen
         rw [rEqE] at hlyQ
         have hnnQc : 0 ≤ rk run.coordinateProper.rank entry.2 := by
           rw [← rEqE]; exact hnnQ
         have hmonoQ : run.top.getD (rk run.coordinateProper.rank pos).toNat 0 ≤
             run.top.getD (rk run.coordinateProper.rank entry.2).toNat 0 := by
           by_cases heqR : (rk run.coordinateProper.rank pos).toNat =
               (rk run.coordinateProper.rank entry.2).toNat
           · rw [heqR]; exact Int.le_refl _
           · have hltQ : (rk run.coordinateProper.rank pos).toNat <
                 (rk run.coordinateProper.rank entry.2).toNat := by
               have h1 := hleC
               have h2 := hnnQc
               have h3 : 0 ≤ rk run.coordinateProper.rank pos := by
                 rw [← rEqM]; exact hnnM0
               omega
             have hle2 := hRB.2 _ _ _ _ hltQ hlyM hlyQ
             have hHnn : 0 ≤ CoordsImpl.layerHeight run.coordinateProper ltM :=
               CoordsImpl.layerHeight_nonneg _ _
             omega
         have hrkQ : rk run.coordinateProper.rank entry.2 =
             ((rk run.coordinateProper.rank entry.2).toNat : Int) := by
           have h := Int.toNat_of_nonneg hnnQc
           exact h.symm
         have hbandLoQ := hRB.1 _ _ _ hlyQ hmemQ hqCoordLen hrkQ
         have hYq : (Labels.rectAt run.proper run.xs run.ys entry.2).y =
             run.ys.getD entry.2 0 := rfl
         rw [hYq]
         have h1 := hmonoQ
         have h2 := hbandLoQ.1
         omega
       · cases heq
     have hframeY : g0.y = (boundsOf descRects []).minY := by
       rw [← hframe]
       simp only [descRects, frameRect, hmemberGet, hfb,
         show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
     rw [← hframeY] at hmin
     unfold Disjoint
     intro hcon
     obtain ⟨-, hy⟩ := hcon
     omega
   · have hb2 : fNode.border = 2 := by
       have hshapeB := (X_componentCandidate_marker_shape execution.graph0_eq
         execution.graph_eq hfn).1
       rcases hshapeB with h0 | hm2 | h2
       · exact absurd h0 hnonplain
       · exact absurd hm2 hfb
       · exact h2
     obtain ⟨t, ht⟩ := X_componentRun_cg_top_of_bottom execution.graph0_eq
       execution.graph_eq hlines hcomp hfn hb2
     have htPred := List.find?_some ht
     simp only [Bool.and_eq_true, beq_iff_eq] at htPred
     obtain ⟨htBorder, htPath⟩ := htPred
     have htMem : t ∈ (componentCandidate execution.graph comp candidate).nodes.zipIdx :=
       List.mem_of_find?_eq_some ht
     have htLookup : (componentCandidate execution.graph comp candidate).nodes[t.2]? =
         some t.1 := List.mem_zipIdx_iff_getElem?.mp htMem
     have hlastT : t.1.clusterPath.getLast? = some t.1.decl := by
       obtain ⟨_, _, hpathT⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq
         htLookup htBorder
       rw [hpathT]; simp
     have hlastF : fNode.clusterPath.getLast? = some fNode.decl :=
       (XCM_bottom_path execution.graph0_eq execution.graph_eq hfn hb2).1
     have htDecl : t.1.decl = fNode.decl := by
       have hget : t.1.clusterPath.getLast? = fNode.clusterPath.getLast? :=
         congrArg List.getLast? htPath
       rw [hlastT, hlastF] at hget
       exact Option.some.inj hget
     have hneT : tNode.decl ≠ t.1.decl := by
       rw [htDecl]
       exact hne
     have hcontainsT : t.1.clusterPath.contains tNode.decl = true := by
       rw [htPath]
       exact hpath
     have htLt : t.2 < (componentCandidate execution.graph comp candidate).nodes.length :=
       (List.getElem?_eq_some_iff.mp htLookup).1
     obtain ⟨rrT, hrrT, hchainTLe⟩ :=
       hchain execution hcomp hrun hnode hborder htLookup htBorder hneT hcontainsT
     have hrrTEq : rrT = rr := Except.ok.inj (hrrT.symm.trans hrr)
     rw [hrrTEq] at hchainTLe
     have etT : rk run.coordinateProper.rank t.2 = rk rr.ranks t.2 := by
       have h2 := XCM_prepared (P := execution.params) (exact := exactDecls exactIds inp)
         hrr hranks htLt
       rw [hc] at h2
       exact h2
     have rEqN := X_proper_rank_eq_local hrun t.2
     have htLen : t.2 < run.proper.nodes.length :=
       componentRunX_original_nodes_covered hrun t.2 htLt
     obtain ⟨ltN, hlyN, _, hnnN⟩ := hcov t.2 htLen
     rw [rEqN] at hlyN hnnN
     have hltTN : (rk run.coordinateProper.rank i).toNat <
         (rk run.coordinateProper.rank t.2).toNat := by
       have h1 := eTop
       have h2 := etT
       have h3 : rk rr.ranks i + 1 ≤ rk rr.ranks t.2 := hchainTLe
       have h4 := hnnT
       have h5 := hnnN
       omega
     have hbandTN := hRB.2 _ _ _ _ hltTN hlyT hlyN
     obtain ⟨coord, hcoord, hcoordB, _, hcoordP, hcoordH⟩ :=
       XCM_bottom_coordinate execution.graph0_eq execution.graph_eq hcomp hrun hfn hb2
     obtain ⟨bprop, hbprop, hbpropP, _⟩ :=
       XCM_bottom_proper hrun hcoord hcoordB hcoordH
     have hbproperD : run.proper.nodes.getD pos default = bprop := by
       simp only [List.getD_eq_getElem?_getD, hbprop, Option.getD_some]
     have hcontainsP : (run.proper.nodes.getD pos default).node.clusterPath.contains
         t.1.decl = true := by
       rw [hbproperD, hbpropP, hcoordP, htDecl]
       exact (XCM_bottom_path execution.graph0_eq execution.graph_eq hfn hb2).2
     have htGet : (componentCandidate execution.graph comp candidate).nodes.getD t.2
         default = t.1 := by
       simp only [List.getD_eq_getElem?_getD, htLookup, Option.getD_some]
     have hcloseLe : rk run.proper.rank t.2 ≤ rk run.proper.rank pos := by
       have hq2 : (bprop, pos) ∈ run.proper.nodes.zipIdx :=
         List.mk_mem_zipIdx_iff_getElem?.mpr hbprop
       have hq3 : (run.proper.nodes.getD pos default, pos) ∈ run.proper.nodes.zipIdx := by
         rw [hbproperD]; exact hq2
       have hcont : (run.proper.nodes.getD pos default).node.clusterPath.contains
           t.1.decl = true := hcontainsP
       have hclose := hchild execution hcomp hrun htLookup htBorder
       unfold ChildTopRankLe at hclose
       rw [htGet] at hclose
       exact hclose _ hq3 hcont
     obtain ⟨lP0B, hlyP0B, _, hnnP0B⟩ := hcov t.2 htLen
     obtain ⟨lQ0B, hlyQ0B, hmemQ0B, hnnQ0B⟩ := hcov pos hposLen
     rw [rEqN] at hlyP0B hnnP0B
     rw [rEqM] at hlyQ0B hnnQ0B
     have hcloseLeC : rk run.coordinateProper.rank t.2 ≤
         rk run.coordinateProper.rank pos := by
       rw [← rEqN, ← rEqM]; exact hcloseLe
     have hmono : run.top.getD (rk run.coordinateProper.rank t.2).toNat 0 ≤
         run.top.getD (rk run.coordinateProper.rank pos).toNat 0 := by
       by_cases heqR : (rk run.coordinateProper.rank t.2).toNat =
           (rk run.coordinateProper.rank pos).toNat
       · rw [heqR]; exact Int.le_refl _
       · have hltQ : (rk run.coordinateProper.rank t.2).toNat <
             (rk run.coordinateProper.rank pos).toNat := by
           have h1 := hcloseLeC
           have h2 := hnnP0B
           have h3 := hnnQ0B
           omega
         have hle2 := hRB.2 _ _ _ _ hltQ hlyP0B hlyQ0B
         have hHnn : 0 ≤ CoordsImpl.layerHeight run.coordinateProper lP0B :=
           CoordsImpl.layerHeight_nonneg _ _
         omega
     have hcoordLenM : pos < run.coordinateProper.nodes.length := by
       obtain ⟨_, _, _, q0M, _, _, _, _, _, hproxyM, hdropM, _, _, _⟩ :=
         componentRunX_spec hrun
       obtain ⟨_, _, hqlenM, _, _, _⟩ := proxyWidths_rel hproxyM
       have hnodesM : run.proper.nodes = q0M.nodes := by rw [← hdropM]; rfl
       have h1 : pos < q0M.nodes.length := by rw [← hnodesM]; exact hposLen
       omega
     have hrkMnn : 0 ≤ rk run.coordinateProper.rank pos := hnnQ0B
     have hrkM : rk run.coordinateProper.rank pos =
         ((rk run.coordinateProper.rank pos).toNat : Int) := by
       have h := Int.toNat_of_nonneg hrkMnn
       exact h.symm
     have hbandLo := hRB.1 _ _ _ hlyQ0B hmemQ0B hcoordLenM hrkM
     have hb : (fNode.border != -2) = true := by
       simp only [bne_iff_ne]
       exact hfb
     have hfr : frameRect execution.params (componentCandidate execution.graph comp candidate)
         run pos =
         nodeRect (componentCandidate execution.graph comp candidate) run pos := by
       unfold frameRect
       simp only [hmemberGet, hb, ↓reduceIte]
     have hgy : (nodeRect (componentCandidate execution.graph comp candidate) run pos).y =
         run.ys.getD pos 0 := rfl
     have hbelow : (transportCaption execution.params o execution.lines comp i stored0).y +
         (transportCaption execution.params o execution.lines comp i stored0).h ≤
         run.ys.getD pos 0 := by
       have h1 := hcap0
       have h2 := hbandTN
       have h3 := hmono
       have h4 := hbandLo.1
       omega
     unfold Disjoint
     intro hcon
     obtain ⟨-, hy⟩ := hcon
     rw [← hframe, hfr, hgy] at hy
     omega

end PipelineImpl
end Layered
end Elegant

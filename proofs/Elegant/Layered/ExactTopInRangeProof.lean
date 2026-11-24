import Elegant.Layered.ExactTopOutsideDisjointProof
import Elegant.Layered.ExactForeignNonGroupSpansProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact loop-rect top in-range outsider case (W form)

Proves `XLrr_TopOutsideDisjointInRangeW` (the residual behind
`XLrr_topOutsideDisjointW_holds` in `ExactTopOutsideDisjointProof.lean`):
an executed exact run frame of a plain node outside a group is disjoint
from the group-top frame when member ranks witness both sides of the
outsider rank.

The outsider is x-separated from the group span at its rank: the bracket
residual supplies the left/right border-marker pair at the outsider rank
(the per-rank marker-pair content of the foreign cluster rank spans; the
group-vs-group interval form is closed separately by
`XB_foreignClusterRankSpans_holds`), the order residual puts the plain
frame clear of one marker, and the alignment residual confines the whole
group border hull between the markers. No vertical separation is needed:
the member-rank witnesses on both sides rule out the band cases, so only
the same-rank marker argument runs. The group-top frame is the hull of
its member frames (`frameRect_group_span`, `groupMemberRects_inv`).

Stays open: the three side-marker residuals `XN_BracketMarkersAtRank`,
`XN_PlainClearOfSideMarker`, `XN_SideMarkerSpanAligned` (exact twins of
the plain-pipeline bracket/order/alignment facts, owned by the
side-marker lane). Each is strictly narrower than the target (marker
existence, order, or alignment only; no disjointness conclusion), so this
is a proved reduction and not a restatement.

Probe evidence (`proofs/wip/Probe/ExactTopOutsideDisjointTProbe.lean`):
14 pairs over 13 executed inputs, `disj=true` everywhere, including the
in-range zero-size outsider/member, nested, self-loop, huge-outsider and
wide-member pairs. No falsifying witness was found.
-/

/-- File-unique prefix for all private helpers in this module. -/
private theorem xtir_coordinateGraphX_plain_anchor (P : Params) (exact : List Nat) (p : Proper)
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
private theorem xtir_componentRun_plain_node {P : Params} {exact : List Nat} {cg : Graph}
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
private theorem xtir_componentRun_original_plain_record {P : Params} {exact : List Nat} {cg : Graph}
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
    xtir_coordinateGraphX_plain_anchor P exact labeled hlabRec hplain rfl
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hcoord]
    exact hactual
  exact ⟨actual, hcoordinate, xtir_componentRun_plain_node hrun hcoordinate hplainA,
    hfalse, hplainA, hpath⟩

/-- The in-range outsider case from the side-marker residuals: the outsider
is x-separated from the group span at its rank. Proved reduction; the
three marker residuals stay open (see module header). -/
theorem xlrr_topOutsideDisjointInRangeW_holds (exactIds : List String)
    (hbracket : XN_BracketMarkersAtRank exactIds)
    (horder : XN_PlainClearOfSideMarker exactIds)
    (halign : XN_SideMarkerSpanAligned exactIds) :
    XLrr_TopOutsideDisjointInRangeW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  intro v w node member hnode hgroup hmember hplain hpathW hLow hHigh
  obtain ⟨actual, _hcoordW, hpropW, _hdummyW, hbW0, hpathWeq⟩ :=
    xtir_componentRun_original_plain_record hrun hmember hplain
  have hgetW : (componentCandidate execution.graph comp candidate).nodes.getD w default = member := by
    rw [List.getD_eq_getElem?_getD, hmember]
    rfl
  have hframeW : frameRect execution.params (componentCandidate execution.graph comp candidate) run w =
      nodeRect (componentCandidate execution.graph comp candidate) run w := by
    unfold frameRect
    simp only []
    rw [hgetW, hplain]
    rfl
  obtain ⟨_ranks, _p0, _labeled, q0, _hn, _hlabeled, _hc, _ordp, _cross,
    hproxy, hdrop, hrouteWL, _hrouting, _hroutes⟩ := componentRunX_spec hrun
  obtain ⟨_edges, hrankEq, _nlen, _xlen, _records, hnp⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have hl := execution.lines_eq
    unfold PipelineImpl.boxLines at hl
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
        (PipelineImpl.mapM_getElem? _ _ _ hl).1
      _ = inp.boxes.length := List.length_zipIdx
  have hwP : w < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hpropW).1
  obtain ⟨_len, _sz, _members, hcov, _edges2⟩ :=
    RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hrouteWL).1
  have hcovw := hcov w hwP
  obtain ⟨-, -, -, hwNN⟩ := hcovw
  have hrkWNN : 0 ≤ rk run.coordinateProper.rank w := by rw [← hranks]; exact hwNN
  obtain ⟨low, lowNd, hlowRec, hlowCon, hlowLe⟩ := hLow
  obtain ⟨high, highNd, hhighRec, hhighCon, hhighGe⟩ := hHigh
  rw [← hranks] at hlowLe hhighGe
  obtain ⟨mL, mR, nL, nR, hcpmL, hborderL, hlastL, hrankL,
    hcpmR, hborderR, hlastR, hrankR⟩ :=
    hbracket execution.graph0_eq execution.graph_eq hlinesLen hwf hfp hcomp hrun
      (rk run.proper.rank w).toNat hlowRec hlowCon hlowLe hhighRec hhighCon hhighGe
  have hnotProxyL : ¬(nL.node.border = -2 ∨ nL.node.border = 2) := by
    rw [hborderL]
    omega
  have hnotProxyR : ¬(nR.node.border = -2 ∨ nR.node.border = 2) := by
    rw [hborderR]
    omega
  obtain ⟨hnpRecL, -⟩ := hnp mL nL hcpmL hnotProxyL
  obtain ⟨hnpRecR, -⟩ := hnp mR nR hcpmR hnotProxyR
  have hmarkRunL : run.proper.nodes[mL]? = some nL := by rw [hnodes]; exact hnpRecL
  have hmarkRunR : run.proper.nodes[mR]? = some nR := by rw [hnodes]; exact hnpRecR
  have hrankmWL : rk run.proper.rank mL = rk run.proper.rank w := by
    rw [hranks, hrankL, hranks]
    exact Int.toNat_of_nonneg hrkWNN
  have hrankmWR : rk run.proper.rank mR = rk run.proper.rank w := by
    rw [hranks, hrankR, hranks]
    exact Int.toNat_of_nonneg hrkWNN
  have hrankLR : rk run.proper.rank mL = rk run.proper.rank mR := by
    rw [hrankmWL, hrankmWR]
  have hnotMem : actual.node.clusterPath.contains node.decl = false := by
    rw [hpathWeq]
    simpa using hpathW
  obtain hsep :=
    horder execution.graph0_eq execution.graph_eq hcomp hrun hpropW hbW0 hnotMem
      hmarkRunL hborderL hlastL hmarkRunR hborderR hlastR hrankmWL hrankmWR
  have hmemRectL : Labels.rectAt run.proper run.xs run.ys mL ∈
      groupBorderRects (componentCandidate execution.graph comp candidate) run node.decl :=
    groupBorderRects_mem_of_record hmarkRunL (Or.inl hborderL) hlastL
  have hneRects : groupBorderRects (componentCandidate execution.graph comp candidate) run node.decl ≠ [] := by
    intro hnil
    rw [hnil] at hmemRectL
    simp at hmemRectL
  have hborderLOr : nL.node.border = -1 ∨ nL.node.border = 1 :=
    Or.inl hborderL
  have hborderROr : nR.node.border = -1 ∨ nR.node.border = 1 :=
    Or.inr hborderR
  have hcross :=
    (halign execution.graph0_eq execution.graph_eq hlinesLen hwf hfp hcomp hrun
      hmarkRunL hborderLOr hlastL
      hmarkRunR hborderROr hlastR).2.2 ⟨hborderL, hborderR, hrankLR⟩
  have hall : ∀ r ∈ groupBorderRects (componentCandidate execution.graph comp candidate) run node.decl,
      RouteImpl.leftOf run.proper run.xs mL ≤ r.x ∧
        r.x + r.w ≤ RouteImpl.leftOf run.proper run.xs mR +
          RouteImpl.nodeW run.proper mR := by
    intro r hr
    obtain ⟨q, nd, hq, hbq, hlastq, hrq⟩ := groupBorderRects_inv hr
    rcases hbq with hbqL | hbqR
    · obtain ⟨heq1, heq2⟩ :=
        (halign execution.graph0_eq execution.graph_eq hlinesLen hwf hfp hcomp hrun
          hmarkRunL hborderLOr hlastL
          hq (Or.inl hbqL) hlastq).1 (by rw [hborderL, hbqL])
      rw [hrq, rectAt_eq]
      dsimp only
      rw [heq1, ← heq2]
      exact ⟨Int.le_refl _, hcross.2⟩
    · obtain ⟨heq1, heq2⟩ :=
        (halign execution.graph0_eq execution.graph_eq hlinesLen hwf hfp hcomp hrun
          hmarkRunR hborderROr hlastR
          hq (Or.inr hbqR) hlastq).1 (by rw [hborderR, hbqR])
      rw [hrq, rectAt_eq]
      dsimp only
      refine ⟨?_, ?_⟩
      · rw [← heq1]
        exact hcross.1
      · omega
  have hnonnegR :=
    (halign execution.graph0_eq execution.graph_eq hlinesLen hwf hfp hcomp hrun
      hmarkRunR hborderROr hlastR
      hmarkRunR hborderROr hlastR).2.1
  have hminX := boundsOf_minX_ge_of_all hneRects (fun r hr => (hall r hr).1)
  have hright := boundsOf_right_le_of_all hnonnegR
    (fun r hr => (hall r hr).2)
  have hcontain := boundsOf_rect_mem hmemRectL
  rw [rectAt_eq] at hcontain
  rw [frameRect_group_span hnode hgroup, hframeW, nodeRect_of_record hpropW]
  unfold Disjoint Rect.meetsInterior
  simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW,
    hpropW, hmarkRunL, hmarkRunR,
    Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)]
    at hsep hcontain hminX hright ⊢
  omega

end PipelineImpl
end Layered
end Elegant

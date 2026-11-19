import Elegant.Layered.RouteLabelForeignClearProof
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.CoordGraph

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Dummy-cell foreign clearance for an executed run

`RouteLabelDummyCellForeignClear` is the placement-level core of
`RouteLabelForeignClear`: every forward-edge mid-rank anchor dummy cell misses
every group frame whose declaration avoids the dummy's cluster path.

Proof route: the dummy is a non-group proper node (`border = 0`, proved from
`pc_plain` transported through `proxyWidths`), so the executed-run span
machinery for plain witnesses (`plain_frame_disjoint` in
`ForeignNonGroupSpansProof.lean`) ports directly, with the dummy's `rectAt`
in place of the plain witness's `nodeRect`. The group frame is the hull of its
side-marker spans over its member rank range (`frameRect_group_span`): a dummy
at rank `r` is either outside the group's member rank range (vertical
separation by rank bands, `rankAxis_bands_disjoint`) or at a rank where the
group carries side markers and the span clearance (`PlainClearOfSideMarker`
plus `SideMarkerSpanAligned`) gives horizontal separation. This covers both
the empty and nonempty cluster-path cases uniformly, so `StrictDummyFrame` is
not needed here. -/

theorem routeLabelDummyCellForeignClear_of_run {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hbracket : BracketMarkersAtRank) (hrank : ForeignClusterRankSpans)
    (hxalign : ForeignBorderChainXAligned) :
    RouteLabelDummyCellForeignClear execution.params
      (componentCandidate execution.graph comp candidate) run := by
  have _hrankUse : ForeignClusterRankSpans := hrank
  have hgraph := execution.graph_eq
  have hlines : execution.lines.length = inp.boxes.length :=
    boxLines_length execution.lines_eq
  have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hxalign
  have horder : PlainClearOfSideMarker := plainClearOfSideMarker'
  intro edge e _hedge _hne _hrev d nd hdummy hfindd gpos gn hu hgrp hout
  have hpropD : run.proper.nodes[d]? = some nd :=
    List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfindd)
  have hnotMem : nd.node.clusterPath.contains gn.decl = false := by
    rw [List.contains_eq_mem]
    simp only [hout, decide_false]
  have hdummyB : nd.node.border = 0 := by
    obtain ⟨_ranks, _p0, labeled, q0, hn, hl, hc, _ordp, _cross,
      hproxy, hdrop, _hroute, _hr2, _hry, _hys, _hroutes⟩ :=
      componentRun_spec hrun
    have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
    have hq0d : q0.nodes[d]? = some nd := by rw [← hnodes]; exact hpropD
    have hlen : q0.nodes.length = run.coordinateProper.nodes.length :=
      (proxyWidths_rel hproxy).2.2.1
    have hdC : d < run.coordinateProper.nodes.length := by
      have hd0 : d < q0.nodes.length := (List.getElem?_eq_some_iff.mp hq0d).1
      omega
    obtain ⟨cn, hcn⟩ : ∃ cn, run.coordinateProper.nodes[d]? = some cn :=
      ⟨_, List.getElem?_eq_getElem hdC⟩
    obtain ⟨nd', hnd', hddum, hbord, _hh⟩ :=
      (proxyWidths_rel hproxy).2.2.2.2.1 d cn hcn
    have hndEq : nd' = nd := Option.some.inj (hnd'.symm.trans hq0d)
    have hcnDum : cn.dummy = true := by rw [← hddum, hndEq]; exact hdummy
    have hK : NodeKeys (componentCandidate execution.graph comp candidate) labeled :=
      addLabelNodes_keys _ _ _ (normalize_keys hn) hl
    have hcnL : (coordinateGraph execution.params labeled).nodes[d]? = some cn := by
      rw [hc]; exact hcn
    have hb0 : cn.node.border = 0 := pc_plain hK hcnL hcnDum
    rw [hndEq] at hbord
    exact hbord.trans hb0
  obtain ⟨_ranks, _p0, _labeled, q0, _hn, _hlabeled, _hc, _ordp, _cross,
    hproxy, hdrop, hroute, _hr2, hry, _hys, _hroutes⟩ :=
    componentRun_spec hrun
  obtain ⟨_edges, hrankEq, _nlen, _xlen, _records, hnp⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  obtain ⟨_len, _sz, _members, hcov, _edges2⟩ :=
    RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨hgap, hslot, _len2, hslots, _sizes, htopEq, _hyEq⟩ :=
    CoordsImpl.rankCoordsWith_spec hry
  have htopNN : ∀ r : Nat, (0 : Int) ≤ run.top.getD r 0 := by
    intro r
    have hheights : ∀ h ∈ run.layers.map (CoordsImpl.layerHeight run.coordinateProper),
        0 ≤ h := by
      intro h hh
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hh
      exact CoordsImpl.layerHeight_nonneg _ _
    have hsteps : ∀ s ∈ CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
        run.coordinateProper
        run.layers (run.routing.gaps.map (fun x => x.slots)), 0 ≤ s :=
      CoordsImpl.rankSteps_nonneg (by omega) (by omega) _ _ _ hslots
    have hmono : ∀ e ∈ CoordsImpl.topsFrom (0 : Int) 1 0
        (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
        (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
          run.coordinateProper run.layers
          (run.routing.gaps.map (fun x => x.slots))), (0 : Int) ≤ e := fun e he =>
      CoordsImpl.topsFrom_ge 0 1 (by omega) (by omega) _ _ 0 hheights hsteps e he
    cases hget : run.top[r]? with
    | none => simp only [List.getD_eq_getElem?_getD, hget, Option.getD_none]; omega
    | some v =>
      simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some]
      have hmem : v ∈ run.top := List.mem_of_getElem? hget
      rw [htopEq] at hmem
      exact hmono v hmem
  have hdP : d < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hpropD).1
  obtain ⟨lD, hlyD, hdTopBand, hdBotBand⟩ := run_node_band hrun hpropD
  have hcovd := hcov d hdP
  obtain ⟨-, -, -, hdNN⟩ := hcovd
  have hrkDNN : 0 ≤ rk run.coordinateProper.rank d := by rw [← hranks]; exact hdNN
  have hysDNN : (0 : Int) ≤ run.ys.getD d 0 :=
    Int.le_trans (htopNN _) hdTopBand
  by_cases hLow : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      nd.node.clusterPath.contains gn.decl = true ∧
      (rk run.coordinateProper.rank q).toNat ≤ (rk run.coordinateProper.rank d).toNat
  · by_cases hHigh : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      nd.node.clusterPath.contains gn.decl = true ∧
      (rk run.coordinateProper.rank d).toNat ≤ (rk run.coordinateProper.rank q).toNat
    · -- the bracket case: marker pair at d's rank, aligned span, foreign clearance
      obtain ⟨low, lowNd, hlowRec, hlowCon, hlowLe⟩ := hLow
      obtain ⟨high, highNd, hhighRec, hhighCon, hhighGe⟩ := hHigh
      rw [← hranks] at hlowLe hhighGe
      obtain ⟨mL, mR, nL, nR, hcpmL, hborderL, hlastL, hrankL,
        hcpmR, hborderR, hlastR, hrankR⟩ :=
        hbracket hgraph hlines hwf hframed hcomp hrun (rk run.proper.rank d).toNat
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
      have hrankmDL : rk run.proper.rank mL = rk run.proper.rank d := by
        rw [hranks, hrankL, hranks]
        exact Int.toNat_of_nonneg hrkDNN
      have hrankmDR : rk run.proper.rank mR = rk run.proper.rank d := by
        rw [hranks, hrankR, hranks]
        exact Int.toNat_of_nonneg hrkDNN
      have hrankLR : rk run.proper.rank mL = rk run.proper.rank mR := by
        rw [hrankmDL, hrankmDR]
      obtain hsep :=
        horder hgraph hcomp hrun hpropD hdummyB hnotMem
          hmarkRunL hborderL hlastL hmarkRunR hborderR hlastR hrankmDL hrankmDR
      have hmemRectL : Labels.rectAt run.proper run.xs run.ys mL ∈
          groupBorderRects (componentCandidate execution.graph comp candidate) run gn.decl :=
        groupBorderRects_mem_of_record hmarkRunL (Or.inl hborderL) hlastL
      have hneRects : groupBorderRects (componentCandidate execution.graph comp candidate) run
          gn.decl ≠ [] := by
        intro hnil
        rw [hnil] at hmemRectL
        simp at hmemRectL
      have hborderLOr : nL.node.border = -1 ∨ nL.node.border = 1 :=
        Or.inl hborderL
      have hborderROr : nR.node.border = -1 ∨ nR.node.border = 1 :=
        Or.inr hborderR
      have hcross :=
        (halign hgraph hcomp hrun hmarkRunL hborderLOr hlastL
          hmarkRunR hborderROr hlastR).2.2 ⟨hborderL, hborderR, hrankLR⟩
      have hall : ∀ r ∈ groupBorderRects (componentCandidate execution.graph comp candidate) run
          gn.decl,
          RouteImpl.leftOf run.proper run.xs mL ≤ r.x ∧
            r.x + r.w ≤ RouteImpl.leftOf run.proper run.xs mR +
              RouteImpl.nodeW run.proper mR := by
        intro r hr
        obtain ⟨q, nd, hq, hbq, hlastq, hrq⟩ := groupBorderRects_inv hr
        rcases hbq with hbqL | hbqR
        · obtain ⟨heq1, heq2⟩ :=
            (halign hgraph hcomp hrun hmarkRunL hborderLOr hlastL
              hq (Or.inl hbqL) hlastq).1 (by rw [hborderL, hbqL])
          rw [hrq, rectAt_eq]
          dsimp only
          rw [heq1, ← heq2]
          exact ⟨Int.le_refl _, hcross.2⟩
        · obtain ⟨heq1, heq2⟩ :=
            (halign hgraph hcomp hrun hmarkRunR hborderROr hlastR
              hq (Or.inr hbqR) hlastq).1 (by rw [hborderR, hbqR])
          rw [hrq, rectAt_eq]
          dsimp only
          refine ⟨?_, ?_⟩
          · rw [← heq1]; exact hcross.1
          · omega
      have hnonnegR :=
        (halign hgraph hcomp hrun hmarkRunR hborderROr hlastR
          hmarkRunR hborderROr hlastR).2.1
      have hminX := boundsOf_minX_ge_of_all hneRects (fun r hr => (hall r hr).1)
      have hright := boundsOf_right_le_of_all hnonnegR
        (fun r hr => (hall r hr).2)
      have hcontain := boundsOf_rect_mem hmemRectL
      rw [rectAt_eq] at hcontain
      rw [frameRect_group_span hu hgrp, rectAt_eq]
      unfold Disjoint Rect.meetsInterior
      simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW,
        hpropD, hmarkRunL, hmarkRunR,
        Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)]
        at hsep hcontain hminX hright ⊢
      omega
    · -- every member rank is strictly above d's rank
      have hAllAbove : ∀ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd →
          nd.node.clusterPath.contains gn.decl = true →
          (rk run.coordinateProper.rank q).toNat < (rk run.coordinateProper.rank d).toNat := by
        intro q nd hrec hcon
        refine Classical.byContradiction (fun hcontra => ?_)
        exact hHigh ⟨q, nd, hrec, hcon, by omega⟩
      have hmem : ∀ r ∈ groupMemberRects (componentCandidate execution.graph comp candidate) run
          gn.decl,
          r.y + r.h ≤ run.ys.getD d 0 := by
        intro r hr
        obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
        obtain ⟨l, hly, hqTop, hqBot⟩ := run_node_band hrun hq
        have hband := CoordsImpl.rankAxis_bands_disjoint hry
          (rk run.coordinateProper.rank q).toNat (rk run.coordinateProper.rank d).toNat
          l lD (hAllAbove q nd hq hcon) hly hlyD
        simp only [RouteImpl.nodeH, hq] at hqBot
        rw [hrq, rectAt_eq]
        simp only [RouteImpl.yAt, RouteImpl.nodeH, hq]
        omega
      have hbot := boundsOf_bottom_le_of_all hysDNN hmem
      rw [frameRect_group_span hu hgrp, rectAt_eq]
      refine rect_disjoint_of_y (Or.inr ?_)
      have hkey : (boundsOf (groupMemberRects (componentCandidate execution.graph comp candidate) run
          gn.decl) []).minY +
          ((boundsOf (groupMemberRects (componentCandidate execution.graph comp candidate) run
            gn.decl) []).bottom -
            (boundsOf (groupMemberRects (componentCandidate execution.graph comp candidate) run
              gn.decl) []).minY) ≤
          run.ys.getD d 0 := by omega
      exact hkey
  · by_cases hHigh : ∃ (q : Nat) (nd : ProperNode), run.proper.nodes[q]? = some nd ∧
      nd.node.clusterPath.contains gn.decl = true ∧
      (rk run.coordinateProper.rank d).toNat ≤ (rk run.coordinateProper.rank q).toNat
    · -- every member rank is strictly below d's rank
      by_cases hmemNil : groupMemberRects (componentCandidate execution.graph comp candidate) run
          gn.decl = []
      · rw [frameRect_group_span hu hgrp, hmemNil]
        refine disjoint_of_height_zero_right ?_
        show (boundsOf [] []).bottom - (boundsOf [] []).minY = 0
        rfl
      · have hmem : ∀ r ∈ groupMemberRects (componentCandidate execution.graph comp candidate) run
          gn.decl,
          run.ys.getD d 0 + RouteImpl.nodeH run.proper d ≤ r.y := by
          intro r hr
          obtain ⟨q, nd, hq, hcon, hrq⟩ := groupMemberRects_inv hr
          obtain ⟨l, hly, hqTop, hqBot⟩ := run_node_band hrun hq
          have hAllBelow : (rk run.coordinateProper.rank d).toNat <
              (rk run.coordinateProper.rank q).toNat := by
            refine Classical.byContradiction (fun hcontra => ?_)
            exact hLow ⟨q, nd, hq, hcon, by omega⟩
          have hband := CoordsImpl.rankAxis_bands_disjoint hry
            (rk run.coordinateProper.rank d).toNat (rk run.coordinateProper.rank q).toNat
            lD l hAllBelow hlyD hly
          simp only [RouteImpl.nodeH, hq] at hqBot
          simp only [RouteImpl.nodeH, hpropD] at hdBotBand
          rw [hrq, rectAt_eq]
          dsimp only
          simp only [RouteImpl.yAt, RouteImpl.nodeH, hpropD]
          omega
        have htop := boundsOf_minY_ge_of_all hmemNil hmem
        rw [frameRect_group_span hu hgrp, rectAt_eq]
        refine rect_disjoint_of_y (Or.inl ?_)
        simp only [RouteImpl.yAt] at ⊢
        omega
    · -- no member at all: the frame is flat
      have hmemNil : groupMemberRects (componentCandidate execution.graph comp candidate) run
          gn.decl = [] := by
        refine Classical.byContradiction (fun hne => ?_)
        cases hmem : groupMemberRects (componentCandidate execution.graph comp candidate) run
            gn.decl with
        | nil => exact hne hmem
        | cons r rest =>
          obtain ⟨q, nd, hq, hcon, _r⟩ :=
            groupMemberRects_inv (show r ∈ groupMemberRects
              (componentCandidate execution.graph comp candidate) run gn.decl by
              rw [hmem]; exact List.mem_cons_self)
          rcases (show (rk run.coordinateProper.rank q).toNat ≤
              (rk run.coordinateProper.rank d).toNat ∨
            (rk run.coordinateProper.rank d).toNat ≤
              (rk run.coordinateProper.rank q).toNat by omega) with hle | hle
          · exact hLow ⟨q, nd, hq, hcon, hle⟩
          · exact hHigh ⟨q, nd, hq, hcon, hle⟩
      rw [frameRect_group_span hu hgrp, hmemNil]
      refine disjoint_of_height_zero_right ?_
      show (boundsOf [] []).bottom - (boundsOf [] []).minY = 0
      rfl

end Elegant.Layered.PipelineImpl

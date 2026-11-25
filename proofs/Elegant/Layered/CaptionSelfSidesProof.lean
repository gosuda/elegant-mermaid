import Elegant.Layered.CaptionLocalClearProof
import Elegant.Layered.CaptionWidthFacts
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.GroupFrameSizingFacts
import Elegant.Layered.PartCaptionRunClearProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! ## Executed self-sides strictness

Strict upgrade of `measured_component_caption_border_interval`: the
title-copy node (border 3) and the group side markers (border -1 / 1) on the
same rank are strictly separated by `cluster_all_pairs_separated` (the unit
gap comes from `crossCoordsClusterWith_spec`, the right side additionally
needs `1 ≤ clusterBorderW`). The title-copy x tracks the transported caption
x (`componentRun_group_title_interval_source` plus `captionTitles_at_inj`
and `actual_title_caption_fit` width), and the frame edges are the side-marker
containment hull (`frameRect_group_width_eq_horizontal_span` with
`boundsOf_minX_le_rect_x` / `rect_right_le_boundsOf_right`). -/

/-- Copied from the private
`PartCaptionRunClearProof.captionTitles_keys_nodup`: titles install at most
one rect per component index. -/
private theorem captionTitles_keys_nodup_copy (P : Params) (cg : Graph) (run : Run) :
    ((componentTitles P cg run).map Prod.fst).Nodup := by
  let emit : Node × Nat → Option (Nat × Rect) := fun top => do
    if top.1.border != -2 then none else do
      let title ← run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath)
      let frame := frameRect P cg run top.2
      pure (top.2, Rect.mk
        (run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2)
        (frame.y + P.clusterPad) top.1.w (top.1.h - P.clusterPad))
  have identity : ∀ top caption, emit top = some caption → caption.1 = top.2 := by
    intro top caption he
    unfold emit at he
    split at he
    · contradiction
    · cases hf : run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath) with
      | none => simp [hf] at he
      | some title =>
        simp [hf] at he
        subst caption
        rfl
  have hindices : (cg.nodes.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hp := List.pairwise_map.mp hindices
  change ((componentTitles P cg run).map Prod.fst).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  change (cg.nodes.zipIdx.filterMap emit).Pairwise (fun a b => a.1 ≠ b.1)
  apply List.Pairwise.filterMap emit _ hp
  intro a b hne ca hca cb hcb
  rw [identity a ca hca, identity b cb hcb]
  exact hne

/-- Executed self-sides strictness: the transported caption of an executed
group keeps a positive gap from the left and right edges of its own frame. -/
theorem captionSelfSidesStrict_executed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (_hwf : WellFormed (inputModel inp o))
    (_hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run) :
    CaptionSelfSidesStrict execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp := by
  intro i stored0 tNode hmem hnode hborder
  obtain ⟨v, _, htitle, _, hplacement, hwidthEq⟩ :=
    measured_component_caption_cross_axis_source execution.graph_eq hcomp hrun hnode hborder
  obtain ⟨ord, left, right, _, hlayers, hleft, hright, hbracket⟩ :=
    componentRun_group_title_bracket execution.graph_eq hcomp hrun hnode hborder htitle
      (by rfl) (by rfl)
  obtain ⟨li, ti, ri, hli, hti, hri, hlt, htr⟩ := hbracket.positions
  rw [hlayers] at hli hti hri
  have hlayer := hbracket.layer_mem
  rw [hlayers] at hlayer
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRun_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨_, hcoordinate, hkeys, _⟩ :=
    componentRun_coordinate_source_alignment hrun
  have hshape : CgShape (componentCandidate execution.graph comp candidate) :=
    componentCandidate_shape (components_nodup execution.graph comp hcomp)
      (measuredGraph_shape execution.graph_eq) candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact pc_title_unique hkeys hshape
      (by rw [hcoordinate]; exact ha) (by rw [hcoordinate]; exact hb) hba hbb hp
  have hleftSep := cluster_all_pairs_separated hcross hunique _ hlayer
    li ti left v _ _ hlt hli hti hleft htitle
    (by change (-1 : Int) ≠ -2; decide) (by change (-1 : Int) ≠ 2; decide)
    (by change (3 : Int) ≠ -2; decide) (by change (3 : Int) ≠ 2; decide)
  have hrightSep := cluster_all_pairs_separated hcross hunique _ hlayer
    ti ri v right _ _ htr hti hri htitle hright
    (by change (3 : Int) ≠ -2; decide) (by change (3 : Int) ≠ 2; decide)
    (by change (1 : Int) ≠ -2; decide) (by change (1 : Int) ≠ 2; decide)
  obtain ⟨hleftFinal, hleftX⟩ :=
    componentRun_border_record hrun hleft (Or.inl rfl)
  obtain ⟨hrightFinal, hrightX⟩ :=
    componentRun_border_record hrun hright (Or.inr rfl)
  have hwidth : 0 ≤ tNode.w := by
    simpa only [copyF] using (sizesNonneg_lookup hsizes v _ htitle).1
  have hsideWidth : 0 ≤ execution.params.clusterBorderW := by
    simpa only [OrderImpl.borderLeft] using
      (sizesNonneg_lookup hsizes left _ hleft).1
  have hgap : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by omega
  have hcbw : 1 ≤ execution.params.clusterBorderW :=
    checkedParams_clusterBorderW_ge_one execution.checked
  have htitleLeftStrict : (Labels.rectAt run.proper run.xs run.ys left).x <
      run.coordinateXs.getD v 0 - Int.fdiv tNode.w 2 := by
    simp only [coordSep, CoordsImpl.nodeW, hleft, htitle, copyF,
      OrderImpl.borderLeft, titleF, hborder] at hleftSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hleftFinal, hleftX, OrderImpl.borderLeft]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hleftSep ⊢
    omega
  have htitleRightStrict : run.coordinateXs.getD v 0 - Int.fdiv tNode.w 2 + tNode.w <
      (Labels.rectAt run.proper run.xs run.ys right).x +
        (Labels.rectAt run.proper run.xs run.ys right).w := by
    simp only [coordSep, CoordsImpl.nodeW, hright, htitle, copyF,
      OrderImpl.borderRight, titleF, hborder] at hrightSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hrightFinal, hrightX, OrderImpl.borderRight]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hrightSep ⊢
    omega
  obtain ⟨_, _, horiginal⟩ :=
    componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨_, _, _, _, hpath⟩ :=
    measuredGraph_group_origin execution.graph_eq horiginal hborder
  have howner : tNode.clusterPath.getLast? = some tNode.decl := by
    rw [hpath]
    simp
  let borders := run.proper.nodes.zipIdx.filterMap fun q =>
    if (q.1.node.border == -1 || q.1.node.border == 1) &&
        q.1.node.clusterPath.getLast? == some tNode.decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none
  have hleftMem : Labels.rectAt run.proper run.xs run.ys left ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, left), List.mk_mem_zipIdx_iff_getElem?.mpr hleftFinal, ?_⟩
    simp [OrderImpl.borderLeft, titleF, hborder, howner]
  have hrightMem : Labels.rectAt run.proper run.xs run.ys right ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, right), List.mk_mem_zipIdx_iff_getElem?.mpr hrightFinal, ?_⟩
    simp [OrderImpl.borderRight, titleF, hborder, howner]
  have hlo := boundsOf_minX_le_rect_x borders []
    (Labels.rectAt run.proper run.xs run.ys left) hleftMem
  have hhi := rect_right_le_boundsOf_right borders []
    (Labels.rectAt run.proper run.xs run.ys right) hrightMem
  have hframeX :
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).x =
        (boundsOf borders []).minX := by
    simp [frameRect, List.getD_eq_getElem?_getD, hnode, hborder, borders]
  have hframeW :
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).w =
        (boundsOf borders []).right - (boundsOf borders []).minX := by
    exact frameRect_group_width_eq_horizontal_span hnode hborder
  have hnodup := captionTitles_keys_nodup_copy execution.params
    (componentCandidate execution.graph comp candidate) run
  have huniq : stored0 = Rect.mk
      (run.coordinateXs.getD v 0 - Int.fdiv tNode.w 2)
      ((frameRect execution.params (componentCandidate execution.graph comp candidate) run i).y +
        execution.params.clusterPad) tNode.w (tNode.h - execution.params.clusterPad) :=
    captionTitles_at_inj hnodup hmem hplacement
  have hcapW : (transportCapSize execution.params o execution.lines comp i).1 = tNode.w := by
    cases hdir : o.direction <;> simp_all [transportCapSize, titleCaptionSize]
  have hcapX : (transportCaption execution.params o execution.lines comp i stored0).x =
      run.coordinateXs.getD v 0 - Int.fdiv tNode.w 2 := by
    have hx : (transportCaption execution.params o execution.lines comp i stored0).x =
      stored0.x := rfl
    rw [hx, huniq]
  have hcapW' : (transportCaption execution.params o execution.lines comp i stored0).w =
      tNode.w := by
    have hw : (transportCaption execution.params o execution.lines comp i stored0).w =
      (transportCapSize execution.params o execution.lines comp i).1 := rfl
    rw [hw, hcapW]
  constructor
  · rw [hcapX]
    omega
  · rw [hcapX, hcapW', hframeX, hframeW]
    omega

end Elegant.Layered.PipelineImpl

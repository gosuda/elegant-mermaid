import Elegant.Layered.LoopExtentReservationProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.SideMarkerTopInCandidateProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Group-top loop-extent reservation

For an executed plain run, the loop footprint of a looping group top ends
left of the placed frame of every recorded non-marker node positioned right
of the top's right marker in the same layer.

The reserved width belongs to the right marker: the marker copy inequality is
a hypothesis, the group frame spans exactly the marker span (markers of one
declaration share one placed span, and a same-rank left/right pair orders the
left span below the right span), and the marker-to-node gap covers the carried
extent through the executed coordinate separation.
-/

/-- Local copy of the private `ler_lines_len`. -/
private theorem lrt_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) : e.lines.length = inp.boxes.length := by
  have h := e.lines_eq
  simp only [boxLines] at h
  calc e.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- Local copy of the private `tsep_foot_eq`. -/
private theorem lrt_foot_eq {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v : Nat}
    (hexact : run.exact = []) :
    loopFootprint cg run labels v = ⟨(frameRect default cg run v).x + (frameRect default cg run v).w, (frameRect default cg run v).y, Loops.extent cg.slot (loopSizes cg.edges labels v cg.slot), (frameRect default cg run v).h⟩ := by
  unfold loopFootprint
  have hcon : run.exact.contains v = false := by simp [hexact]
  simp only [hcon, Bool.false_eq_true, ↓reduceIte]

/-- Same-rank pair pins the border hull right edge to the right marker.
Local copy of the private `tsep_hull_eq_of_pair`, with the alignment taken as
a hypothesis instead of through the chain seam. -/
private theorem lrt_hull_eq_of_pair
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat)
    (run : Run) (oo : OrderOptions) (v : Nat) (nodeV : Node)
    (hcomp : comp ∈ components e.graph)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvtop : nodeV.border = -2)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured oo = .ok run)
    (halign : SideMarkerSpanAligned)
    (mL mR : Nat) (nL nR : ProperNode)
    (hL : run.proper.nodes[mL]? = some nL) (hbL : nL.node.border = -1)
    (hlL : nL.node.clusterPath.getLast? = some nodeV.decl)
    (hR : run.proper.nodes[mR]? = some nR) (hbR : nR.node.border = 1)
    (hlR : nR.node.clusterPath.getLast? = some nodeV.decl)
    (hrank : rk run.proper.rank mL = rk run.proper.rank mR) :
    (Labels.rectAt run.proper run.xs run.ys mR).x +
      (Labels.rectAt run.proper run.xs run.ys mR).w =
      (frameRect default (componentCandidate e.graph comp candidate) run v).x +
        (frameRect default (componentCandidate e.graph comp candidate) run v).w := by
  have hframe := frameRect_group_span (P := default) (run := run) hnodeV hvtop
  have hall : ∀ r ∈ groupBorderRects (componentCandidate e.graph comp candidate)
      run nodeV.decl,
      r.x + r.w ≤ (Labels.rectAt run.proper run.xs run.ys mR).x +
        (Labels.rectAt run.proper run.xs run.ys mR).w := by
    intro r hr
    obtain ⟨q, nd, hq, hbq, hlastq, hrq⟩ := groupBorderRects_inv hr
    rcases hbq with hbqL | hbqR
    · obtain ⟨heq1, heq2⟩ := (halign e.graph_eq (lrt_lines_len e) hwf hfp
        hcomp hrun hq (Or.inl hbqL) hlastq hL (Or.inl hbL) hlL).1
        (by rw [hbL, hbqL])
      have hcross := (halign e.graph_eq (lrt_lines_len e) hwf hfp hcomp hrun
        hL (Or.inl hbL) hlL hR (Or.inr hbR) hlR).2.2 ⟨hbL, hbR, hrank⟩
      rw [hrq, rectAt_eq run.proper run.xs run.ys q,
        rectAt_eq run.proper run.xs run.ys mR]
      dsimp only
      omega
    · obtain ⟨heq1, heq2⟩ := (halign e.graph_eq (lrt_lines_len e) hwf hfp
        hcomp hrun hq (Or.inr hbqR) hlastq hR (Or.inr hbR) hlR).1
        (by rw [hbR, hbqR])
      rw [hrq, rectAt_eq run.proper run.xs run.ys q,
        rectAt_eq run.proper run.xs run.ys mR]
      dsimp only
      omega
  have hnonnegR := (halign e.graph_eq (lrt_lines_len e) hwf hfp hcomp hrun
    hR (Or.inr hbR) hlR hR (Or.inr hbR) hlR).2.1
  have hmemR : Labels.rectAt run.proper run.xs run.ys mR ∈
      groupBorderRects (componentCandidate e.graph comp candidate) run
        nodeV.decl :=
    groupBorderRects_mem_of_record hR (Or.inr hbR) hlR
  have hRw : (Labels.rectAt run.proper run.xs run.ys mR).x +
      (Labels.rectAt run.proper run.xs run.ys mR).w =
      RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR := by
    rw [rectAt_eq]
  have hzero : (0 : Int) ≤ (Labels.rectAt run.proper run.xs run.ys mR).x +
      (Labels.rectAt run.proper run.xs run.ys mR).w := by
    rw [hRw]
    exact hnonnegR
  have hright := boundsOf_right_le_of_all hzero hall
  have hge := (boundsOf_rect_mem hmemR).2
  have hframeRW : (frameRect default (componentCandidate e.graph comp candidate)
      run v).x +
      (frameRect default (componentCandidate e.graph comp candidate)
      run v).w =
      (boundsOf (groupBorderRects (componentCandidate e.graph comp candidate) run
        nodeV.decl) []).right := by
    rw [hframe]
    dsimp only
    omega
  omega

/-- A recorded non-marker index is never a group-top position of the
candidate graph: the labelled record at a `-2` candidate index carries
border `-2` through the coordinate phase, against the recorded border. -/
private theorem lrt_no_group_at_b {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured orderOptions = .ok run)
    {b : Nat} {actualB : ProperNode}
    (hcoordB : run.coordinateProper.nodes[b]? = some actualB)
    (hbne : ¬ (actualB.node.border = -2 ∨ actualB.node.border = 2)) :
    ((componentCandidate e.graph comp candidate).nodes.getD b default).border ≠ -2 := by
  intro hcon
  have hdef : (default : Node).border = 0 := rfl
  by_cases hsome : ∃ nodeB : Node,
      (componentCandidate e.graph comp candidate).nodes[b]? = some nodeB
  · obtain ⟨nodeB, hnodeB⟩ := hsome
    have hget : (componentCandidate e.graph comp candidate).nodes.getD b default =
        nodeB := by
      simp only [List.getD_eq_getElem?_getD, hnodeB, Option.getD_some]
    have hbB : nodeB.border = -2 := by rw [← hget]; exact hcon
    obtain ⟨rr, labeled, hrr, hc, hkeys, hready, hrecords, _⟩ :=
      componentRun_prepared_titled_source e.graph_eq hcomp hrun
    have hlab : labeled.nodes[b]? =
        some (⟨nodeB, false, none, false⟩ : ProperNode) :=
      hrecords b nodeB hnodeB
    have hcoord : (coordinateGraph e.params labeled).nodes[b]? =
        some (clearF (titleF (⟨nodeB, false, none, false⟩ : ProperNode))) :=
      coordinateGraph_marker_record hlab (Or.inl hbB) rfl
    rw [hc] at hcoord
    have hinj : clearF (titleF (⟨nodeB, false, none, false⟩ : ProperNode)) =
        actualB :=
      Option.some.inj (hcoord.symm.trans hcoordB)
    have hbdr : (clearF (titleF
        (⟨nodeB, false, none, false⟩ : ProperNode))).node.border = -2 :=
      (clearF_keys _).2.1.trans ((titleF_keys _).2.1.trans hbB)
    rw [hinj] at hbdr
    exact hbne (Or.inl hbdr)
  · have hnone : (componentCandidate e.graph comp candidate).nodes[b]? = none := by
      cases h : (componentCandidate e.graph comp candidate).nodes[b]? with
      | none => rfl
      | some nodeB => exact absurd ⟨nodeB, h⟩ hsome
    have hget : (componentCandidate e.graph comp candidate).nodes.getD b default =
        default := by
      simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    rw [hget, hdef] at hcon
    omega

/-- The frame left edge at a non-group position is the placed rect left edge. -/
private theorem lrt_frameB_x {P : Params} {cg : Graph} {run : Run}
    {b : Nat} {actualB : ProperNode}
    (hproperB : run.proper.nodes[b]? = some actualB)
    (hgetNe : (cg.nodes.getD b default).border ≠ -2) :
    (frameRect P cg run b).x = (Labels.rectAt run.proper run.xs run.ys b).x := by
  have hframe : frameRect P cg run b = nodeRect cg run b := by
    unfold frameRect
    simp only []
    exact ite_eq_left (by simpa using hgetNe)
  have hrect : nodeRect cg run b = Labels.rectAt run.proper run.xs run.ys b := by
    rw [nodeRect_of_record hproperB, rectAt_eq run.proper run.xs run.ys b]
    simp only [RouteImpl.yAt, RouteImpl.nodeW, RouteImpl.nodeH, hproperB]
  rw [hframe, hrect]

/-- Executed group-top reservation: the footprint of a looping group top ends
left of the frame of every same-layer node recorded right of its right
marker. The marker copy inequality, the marker-span alignment, and the
well-formedness hypotheses for the marker-pair acquisition are premises;
`frameRect` ignores its `Params` argument, so the `default` form below gives
every `P` form. -/
theorem loopResTopReservation_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured orderOptions = .ok run)
    {v mR b : Nat} {nodeV : Node} {nR actualB : ProperNode}
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvTop : nodeV.border = -2)
    (hcoordR : run.coordinateProper.nodes[mR]? = some nR)
    (hbR : nR.node.border = 1)
    (hlastR : nR.node.clusterPath.getLast? = some nodeV.decl)
    (hext : (nR.node.loopExtent : Int) ≥ Loops.extent
      (componentCandidate e.graph comp candidate).slot
      (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
        (componentCandidate e.graph comp candidate).slot))
    (halign : SideMarkerSpanAligned)
    (hcoordB : run.coordinateProper.nodes[b]? = some actualB)
    (hbne : ¬ (actualB.node.border = -2 ∨ actualB.node.border = 2))
    (hproperB : run.proper.nodes[b]? = some actualB)
    (hxsB : run.xs.getD b 0 = run.coordinateXs.getD b 0)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {j iv : Nat} (hj : layer[j]? = some mR) (hiv : layer[iv]? = some b)
    (hlt : j < iv) :
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).x +
      (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).w ≤
      (frameRect default (componentCandidate e.graph comp candidate) run b).x := by
  have hexact : run.exact = [] := componentRun_exact_nil hrun
  have hfoot := lrt_foot_eq (cg := componentCandidate e.graph comp candidate)
    (run := run) (labels := e.measured) (v := v) hexact
  obtain ⟨hproperR, hxsR⟩ := componentRun_border_record hrun hcoordR (Or.inr hbR)
  have hconR : nR.node.clusterPath.contains nodeV.decl = true :=
    List.contains_iff_mem.mpr (List.mem_of_getLast? hlastR)
  obtain ⟨mL, mR', nL, nR', hcoordL, hbL', hlastL', hrankL',
      hcoordR', hbR'', hlastR', hrankR'⟩ :=
    bracketMarkersAtRank' e.graph_eq (lrt_lines_len e) hwf hfp hcomp hrun
      (rk run.proper.rank mR).toNat hproperR hconR (Nat.le_refl _)
      hproperR hconR (Nat.le_refl _)
  obtain ⟨hpropL, _⟩ := componentRun_border_record hrun hcoordL (Or.inl hbL')
  obtain ⟨hpropR', _⟩ := componentRun_border_record hrun hcoordR' (Or.inr hbR'')
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hproxy
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  have hrankPair : rk run.proper.rank mL = rk run.proper.rank mR' := by
    have e1 : rk run.proper.rank mL = rk run.coordinateProper.rank mL := by
      rw [hranks]
    have e2 : rk run.proper.rank mR' = rk run.coordinateProper.rank mR' := by
      rw [hranks]
    rw [e1, e2, hrankL', hrankR']
  have hHullPair := lrt_hull_eq_of_pair e hwf hfp comp candidate run orderOptions v nodeV
    hcomp hnodeV hvTop hrun halign mL mR' nL nR' hpropL hbL' hlastL'
    hpropR' hbR'' hlastR' hrankPair
  have hSameR : (Labels.rectAt run.proper run.xs run.ys mR').x +
      (Labels.rectAt run.proper run.xs run.ys mR').w =
      (Labels.rectAt run.proper run.xs run.ys mR).x +
        (Labels.rectAt run.proper run.xs run.ys mR).w := by
    obtain ⟨_, heqR⟩ := (halign e.graph_eq (lrt_lines_len e) hwf hfp hcomp hrun
      hpropR' (Or.inr hbR'') hlastR' hproperR (Or.inr hbR) hlastR).1
      (by rw [hbR'', hbR])
    rw [rectAt_eq run.proper run.xs run.ys mR',
      rectAt_eq run.proper run.xs run.ys mR]
    dsimp only
    exact heqR
  have hHullEq : (frameRect default (componentCandidate e.graph comp candidate)
      run v).x +
      (frameRect default (componentCandidate e.graph comp candidate)
      run v).w =
      (Labels.rectAt run.proper run.xs run.ys mR).x +
        (Labels.rectAt run.proper run.xs run.ys mR).w :=
    hHullPair.symm.trans hSameR
  have hGb : ((componentCandidate e.graph comp candidate).nodes.getD b
      default).border ≠ -2 :=
    lrt_no_group_at_b e hcomp hrun hcoordB hbne
  have hframeB : (frameRect default (componentCandidate e.graph comp candidate)
      run b).x =
      (Labels.rectAt run.proper run.xs run.ys b).x :=
    lrt_frameB_x hproperB hGb
  obtain ⟨_, _, _, hcoordinate, hkeys, _, _, _⟩ :=
    componentRun_prepared_titled_source e.graph_eq hcomp hrun
  have hshape := componentCandidate_shape (components_nodup e.graph comp hcomp)
    (measuredGraph_shape e.graph_eq) candidate
  have huniq : ∀ (u w : Nat) (left right : ProperNode),
      run.coordinateProper.nodes[u]? = some left →
      run.coordinateProper.nodes[w]? = some right →
      left.node.border = 3 → right.node.border = 3 →
      left.node.clusterPath = right.node.clusterPath → u = w := by
    intro u w left right hleft hright hleftBorder hrightBorder hpath
    apply pc_title_unique hkeys hshape
      (by rw [hcoordinate]; exact hleft)
      (by rw [hcoordinate]; exact hright) hleftBorder hrightBorder hpath
  have hRne1 : nR.node.border ≠ -2 := by omega
  have hRne2 : nR.node.border ≠ 2 := by omega
  have hBne1 : actualB.node.border ≠ -2 := fun h => hbne (Or.inl h)
  have hBne2 : actualB.node.border ≠ 2 := fun h => hbne (Or.inr h)
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hsep := CoordsImpl.cluster_all_pairs_separated hcross huniq layer hlayer
    j iv mR b nR actualB hlt hj hiv hcoordR hcoordB hRne1 hRne2 hBne1 hBne2
  simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcoordR, hcoordB] at hsep
  obtain ⟨hng, hcp, _, hsizesNN, _⟩ :=
    CoordsImpl.crossCoordsClusterWith_spec hcross
  have hgap : 1 ≤ min e.params.nodeGap e.params.clusterPad := by omega
  have hWmNN : (0 : Int) ≤ nR.node.w :=
    (sizesNonneg_lookup hsizesNN mR nR hcoordR).1
  have hWbNN : (0 : Int) ≤ actualB.node.w :=
    (sizesNonneg_lookup hsizesNN b actualB hcoordB).1
  have hNWmNN : 0 ≤ nR.node.w + 2 * (nR.node.loopExtent : Int) := by omega
  have hMsum : (Labels.rectAt run.proper run.xs run.ys mR).x +
      (Labels.rectAt run.proper run.xs run.ys mR).w =
      run.xs.getD mR 0 - Int.fdiv nR.node.w 2 + nR.node.w := by
    simp only [rectAt_eq, RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW,
      hproperR]
  have hBx : (Labels.rectAt run.proper run.xs run.ys b).x =
      run.xs.getD b 0 - Int.fdiv actualB.node.w 2 := by
    simp only [rectAt_eq, RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW,
      hproperB]
  rw [hfoot]
  dsimp only
  rw [hHullEq, hframeB, hMsum, hBx, hxsR, hxsB]
  simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
  omega

/-- The `hright` premise of `loopFootprintTopSeparation_holds`, in its exact
binder form plus the two ambient scene hypotheses used at both application
sites: the two extra `b` binders of the residual follow from the plain-node
record (`hbne` from the `border = 0` record, the `xs` equation from the
original plain record). -/
theorem loopResTopReservation_hright (inp : Input) (o : Options)
    (res : FamilyResult)
    (e : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat)
    (run : Run) (oo : OrderOptions) (v b : Nat) (nodeV nodeB : Node)
    (actualB : ProperNode) (mR : Nat) (nR : ProperNode)
    (hcomp : comp ∈ components e.graph)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvTop : nodeV.border = -2)
    (hnodeB : (componentCandidate e.graph comp candidate).nodes[b]? = some nodeB)
    (hbB : nodeB.border = 0)
    (hbAB : actualB.node.border = 0)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured oo = .ok run)
    (hpropB : run.proper.nodes[b]? = some actualB)
    (hcoordB : run.coordinateProper.nodes[b]? = some actualB)
    (hcoordR : run.coordinateProper.nodes[mR]? = some nR)
    (hbR : nR.node.border = 1)
    (hlastR : nR.node.clusterPath.getLast? = some nodeV.decl)
    (halign : SideMarkerSpanAligned)
    (hext : (nR.node.loopExtent : Int) ≥ Loops.extent
      (componentCandidate e.graph comp candidate).slot
      (loopSizes (componentCandidate e.graph comp candidate).edges e.measured v
        (componentCandidate e.graph comp candidate).slot))
    (layer : List Nat) (hlayer : layer ∈ run.layers)
    (iv j : Nat) (hiv : layer[iv]? = some b) (hj : layer[j]? = some mR)
    (hlt : j < iv) :
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).x +
      (loopFootprint (componentCandidate e.graph comp candidate) run e.measured v).w ≤
      (frameRect default (componentCandidate e.graph comp candidate) run b).x := by
  have hbne : ¬ (actualB.node.border = -2 ∨ actualB.node.border = 2) := by
    rw [hbAB]
    decide
  obtain ⟨_, _, _, _, _, _, _, _, _, hxsB'⟩ :=
    componentRun_original_plain_record hrun hnodeB hbB
  exact loopResTopReservation_holds e hwf hfp hcomp hrun hnodeV hvTop hcoordR
    hbR hlastR hext halign hcoordB hbne hpropB hxsB' hlayer hj hiv hlt

end PipelineImpl
end Layered
end Elegant

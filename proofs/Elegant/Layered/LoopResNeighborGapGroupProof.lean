import Elegant.Layered.LoopResNeighborGapProof
import Elegant.Layered.LoopResTopReservationProof
import Elegant.Layered.LoopResMarkerCopyProof
import Elegant.Layered.LoopFootprintResidualProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.SideMarkerPathsProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Witness for the group-top neighbor gap: ordered right/left markers in a
shared layer for disjoint groups with `Fleft`. Strictly narrower than
`LoopResNeighborGapGroupTop` (marker indices and layer order, no footprint
inequality). -/
def LoopResNeighborGapGroupTopWitness (P : Params) (cg : Graph) (run : Run) : Prop :=
  ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt → nt.border = -2 →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    ∀ (pos : Nat) (np : Node), cg.nodes[pos]? = some np → np.border = -2 →
      pos ≠ t → nt.decl ≠ np.decl →
      np.decl ∉ nt.clusterPath → nt.decl ∉ np.clusterPath →
      (frameRect P cg run t).x + (frameRect P cg run t).w ≤
        (frameRect P cg run pos).x →
      ∃ (mRt mLp : Nat) (nRt nLp : ProperNode) (layer : List Nat)
        (j iv : Nat),
        run.coordinateProper.nodes[mRt]? = some nRt ∧
        nRt.node.border = 1 ∧ nRt.node.clusterPath.getLast? = some nt.decl ∧
        run.coordinateProper.nodes[mLp]? = some nLp ∧
        nLp.node.border = -1 ∧ nLp.node.clusterPath.getLast? = some np.decl ∧
        layer ∈ run.layers ∧ layer[j]? = some mRt ∧ layer[iv]? = some mLp ∧
        j < iv

/-- Bottom loop owners are vacuous on executed runs: a `border = 2`
candidate node owns no loop sizes (`LoopFootprintBottomEmpty_holds`),
contradicting the self-loop witness. -/
private theorem lngg_bottom_vacuous {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate e.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 2)
    (het : ∃ e_ ∈ (componentCandidate e.graph comp candidate).edges,
      e_.tail = t ∧ e_.head = t) : False := by
  have hvlen : t < (componentCandidate e.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnt).1
  have hget : (componentCandidate e.graph comp candidate).nodes.getD t default = nt := by
    simp only [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
  have hborder : ((componentCandidate e.graph comp candidate).nodes.getD t default).border
      = 2 := by rw [hget, htB]
  have hempty := LoopFootprintBottomEmpty_holds e comp candidate run orderOptions t
    hcomp hrun hvlen hborder
  obtain ⟨ed, hmem, htail, hhead⟩ := het
  have hmemF : ed ∈ loopEdges (componentCandidate e.graph comp candidate).edges t := by
    apply List.mem_filter.mpr
    refine ⟨hmem, ?_⟩
    simp only [htail, hhead, beq_self_eq_true, Bool.and_self]
  have hne : loopEdges (componentCandidate e.graph comp candidate).edges t ≠ [] :=
    List.ne_nil_of_mem hmemF
  have hneS : loopSizes (componentCandidate e.graph comp candidate).edges e.measured t
      (componentCandidate e.graph comp candidate).slot ≠ [] := by
    intro hnil
    have hmap : (loopEdges (componentCandidate e.graph comp candidate).edges t).map
        (fun e_ => stackSize (componentCandidate e.graph comp candidate).slot
          (routeLabels e.measured e_.decl)) = [] := hnil
    rw [List.map_eq_nil_iff] at hmap
    exact hne hmap
  exact hneS hempty
/-- Local copy of `lgr_no_group_at_b`: a recorded non-marker index is never a
group-top position of the candidate graph. -/
private theorem lngg_no_group_at_b {inp : Input} {o : Options} {res : FamilyResult}
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
/-- Local copy of the private `lines_len`. -/
private theorem lngg_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) : e.lines.length = inp.boxes.length := by
  have h := e.lines_eq
  simp only [boxLines] at h
  calc e.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx
/-- Bracket pair at a left marker's rank, with proper records and rank equality. -/
private theorem lngg_bracket_pair {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured orderOptions = .ok run)
    {decl mLp : Nat} {nLp : ProperNode}
    (hproperP : run.proper.nodes[mLp]? = some nLp)
    (hconP : nLp.node.clusterPath.contains decl = true) :
    ∃ (mL mR : Nat) (nL nR : ProperNode),
      run.coordinateProper.nodes[mL]? = some nL ∧ nL.node.border = -1 ∧
      nL.node.clusterPath.getLast? = some decl ∧
      run.proper.nodes[mL]? = some nL ∧
      run.coordinateProper.nodes[mR]? = some nR ∧ nR.node.border = 1 ∧
      nR.node.clusterPath.getLast? = some decl ∧
      run.proper.nodes[mR]? = some nR ∧
      rk run.proper.rank mL = rk run.proper.rank mR := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hproxy
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]; exact hrankEq
  obtain ⟨mL, mR, nL, nR, hcoordL, hbL, hlastL, hrankL, hcoordR, hbR, hlastR, hrankR⟩ :=
    bracketMarkersAtRank' e.graph_eq (lngg_lines_len e) hwf hfp hcomp hrun
      (rk run.proper.rank mLp).toNat hproperP hconP (Nat.le_refl _)
      hproperP hconP (Nat.le_refl _)
  obtain ⟨hpropL, _⟩ := componentRun_border_record hrun hcoordL (Or.inl hbL)
  obtain ⟨hpropR, _⟩ := componentRun_border_record hrun hcoordR (Or.inr hbR)
  have hrankPair : rk run.proper.rank mL = rk run.proper.rank mR := by
    have e1 : rk run.proper.rank mL = rk run.coordinateProper.rank mL := by
      rw [hranks]
    have e2 : rk run.proper.rank mR = rk run.coordinateProper.rank mR := by
      rw [hranks]
    rw [e1, e2, hrankL, hrankR]
  exact ⟨mL, mR, nL, nR, hcoordL, hbL, hlastL, hpropL, hcoordR, hbR, hlastR, hpropR, hrankPair⟩
/-- Local copy of `lgr_frameB_x`: the frame left edge at a non-group position
is the placed rect left edge. -/
private theorem lngg_frameB_x {P : Params} {cg : Graph} {run : Run}
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
/-- Hull equality from a left marker: the foreign hull left edge is the left
marker's placed left edge (same-border sharing plus same-rank left-right). -/
private theorem lngg_hull_eq_of_left {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured orderOptions = .ok run)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate e.graph comp candidate).nodes[pos]? = some np)
    (hgrp : np.border = -2)
    {mLp : Nat} {nLp : ProperNode}
    (hproperP : run.proper.nodes[mLp]? = some nLp)
    (hbP : nLp.node.border = -1)
    (hlastP : nLp.node.clusterPath.getLast? = some np.decl)
    (halign : SideMarkerSpanAligned)
    {mL mR : Nat} {nL nR : ProperNode}
    (hpropL : run.proper.nodes[mL]? = some nL)
    (hbL : nL.node.border = -1)
    (hlastL : nL.node.clusterPath.getLast? = some np.decl)
    (hpropR : run.proper.nodes[mR]? = some nR)
    (hbR : nR.node.border = 1)
    (hlastR : nR.node.clusterPath.getLast? = some np.decl)
    (hrankPair : rk run.proper.rank mL = rk run.proper.rank mR) :
    (frameRect default (componentCandidate e.graph comp candidate) run pos).x =
      (Labels.rectAt run.proper run.xs run.ys mLp).x := by
  have hullX : (frameRect default (componentCandidate e.graph comp candidate) run pos).x =
      (boundsOf (groupBorderRects (componentCandidate e.graph comp candidate) run np.decl) []).minX := by
    rw [frameRect_group_span hnp hgrp]
  have hmemP : Labels.rectAt run.proper run.xs run.ys mLp ∈
      groupBorderRects (componentCandidate e.graph comp candidate) run np.decl :=
    groupBorderRects_mem_of_record hproperP (Or.inl hbP) hlastP
  have hneB : groupBorderRects (componentCandidate e.graph comp candidate) run np.decl ≠ [] :=
    List.ne_nil_of_mem hmemP
  have hrectLx : (Labels.rectAt run.proper run.xs run.ys mLp).x =
      RouteImpl.leftOf run.proper run.xs mLp := by rw [rectAt_eq]
  have hall : ∀ r ∈ groupBorderRects (componentCandidate e.graph comp candidate) run np.decl,
      (Labels.rectAt run.proper run.xs run.ys mLp).x ≤ r.x := by
    intro r hr
    obtain ⟨q, nd, hrec, hbor, hlast, rfl⟩ := groupBorderRects_inv hr
    have eQ : (Labels.rectAt run.proper run.xs run.ys q).x =
        RouteImpl.leftOf run.proper run.xs q := by rw [rectAt_eq]
    rcases hbor with hsideL | hsideR
    · have hal := halign e.graph_eq (lngg_lines_len e) hwf hfp hcomp hrun
        hproperP (Or.inl hbP) hlastP hrec (Or.inl hsideL) hlast
      have heq := (hal.1 (by rw [hbP, hsideL])).1
      omega
    · have halR := halign e.graph_eq (lngg_lines_len e) hwf hfp hcomp hrun
        hpropR (Or.inr hbR) hlastR hrec (Or.inr hsideR) hlast
      have heqR := (halR.1 (by rw [hbR, hsideR])).1
      have halLR := halign e.graph_eq (lngg_lines_len e) hwf hfp hcomp hrun
        hpropL (Or.inl hbL) hlastL hpropR (Or.inr hbR) hlastR
      have hle := (halLR.2.2 ⟨hbL, hbR, hrankPair⟩).1
      have halLL := halign e.graph_eq (lngg_lines_len e) hwf hfp hcomp hrun
        hpropL (Or.inl hbL) hlastL hproperP (Or.inl hbP) hlastP
      have hRL : RouteImpl.leftOf run.proper run.xs mL =
          RouteImpl.leftOf run.proper run.xs mLp :=
        ((halLL.1 (by rw [hbL, hbP])).1)
      omega
  have hge : (Labels.rectAt run.proper run.xs run.ys mLp).x ≤
      (boundsOf (groupBorderRects (componentCandidate e.graph comp candidate) run np.decl) []).minX :=
    boundsOf_minX_ge_of_all hneB hall
  have hminLe := (boundsOf_rect_mem hmemP).1
  rw [hullX]; omega
/-- Top reservation bound for the group-top footprint at the foreign left marker. -/
private theorem lngg_top_bound {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate)
      e.measured orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate e.graph comp candidate).nodes[t]? = some nt)
    (htG : nt.border = -2)
    {mRt mLp : Nat} {nRt nLp : ProperNode}
    (hcoordT : run.coordinateProper.nodes[mRt]? = some nRt)
    (hbT : nRt.node.border = 1)
    (hlastT : nRt.node.clusterPath.getLast? = some nt.decl)
    (hcoordP : run.coordinateProper.nodes[mLp]? = some nLp)
    (hbP : nLp.node.border = -1)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {j iv : Nat} (hj : layer[j]? = some mRt) (hiv : layer[iv]? = some mLp)
    (hlt : j < iv) :
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured t).x +
      (loopFootprint (componentCandidate e.graph comp candidate) run e.measured t).w ≤
      (frameRect default (componentCandidate e.graph comp candidate) run mLp).x := by
  have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
  have hext := loopResMarkerCopy_holds e comp candidate orderOptions run hcomp hrun
    hnt htG hcoordT hbT hlastT
  obtain ⟨hproperP, hxsP⟩ :=
    componentRun_border_record hrun hcoordP (Or.inl hbP)
  have hbne : ¬ (nLp.node.border = -2 ∨ nLp.node.border = 2) := by
    rw [hbP]; decide
  exact loopResTopReservation_holds e hwf hfp hcomp hrun hnt htG hcoordT hbT
    hlastT hext halign hcoordP hbne hproperP hxsP hlayer hj hiv hlt

/-- The bottom-owner residual holds on executed runs (vacuous). -/
theorem loopResNeighborGapBottomOwner_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    LoopResNeighborGapBottomOwner execution.params
      (componentCandidate execution.graph comp candidate) run
      execution.measured := by
  intro t nt hnt htB het pos np hnp hgrpB hne hne2 hni1 hni2 hFL
  exact False.elim (lngg_bottom_vacuous execution hcomp hrun hnt htB het)

/-- Group-top neighbor gap from the ordered-marker witness: the top reservation
bounds the footprint by the foreign left marker, whose placed edge is the
foreign hull left edge. -/
theorem loopResNeighborGapGroupTop_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hord : LoopResNeighborGapGroupTopWitness execution.params
      (componentCandidate execution.graph comp candidate) run) :
    LoopResNeighborGapGroupTop execution.params
      (componentCandidate execution.graph comp candidate) run
      execution.measured := by
  intro t nt hnt htG het pos np hnp hgrp hne hne2 hni1 hni2 hFL
  obtain ⟨mRt, mLp, nRt, nLp, layer, j, iv,
      hcoordT, hbT, hlastT, hcoordP, hbP, hlastP,
      hlayer, hj, hiv, hlt⟩ :=
    hord t nt hnt htG het pos np hnp hgrp hne hne2 hni1 hni2 hFL
  have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
  obtain ⟨hproperP, _⟩ :=
    componentRun_border_record hrun hcoordP (Or.inl hbP)
  have hconP : nLp.node.clusterPath.contains np.decl = true :=
    List.contains_iff_mem.mpr (List.mem_of_getLast? hlastP)
  obtain ⟨mL, mR, nL, nR, _, hbL, hlastL, hpropL, _, hbR, hlastR, hpropR,
      hrankPair⟩ :=
    lngg_bracket_pair execution hwf hfp hcomp hrun hproperP hconP
  have hTop := lngg_top_bound execution hwf hfp hx hcomp hrun hnt htG
    hcoordT hbT hlastT hcoordP hbP hlayer hj hiv hlt
  have hbne : ¬ (nLp.node.border = -2 ∨ nLp.node.border = 2) := by
    rw [hbP]; decide
  have hGb := lngg_no_group_at_b execution hcomp hrun hcoordP hbne
  have hframeB := lngg_frameB_x (P := default) hproperP hGb
  have hHull := lngg_hull_eq_of_left execution hwf hfp hcomp hrun hnp hgrp
    hproperP hbP hlastP halign hpropL hbL hlastL hpropR hbR hlastR hrankPair
  have hsame : (frameRect default
      (componentCandidate execution.graph comp candidate) run pos).x =
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x := rfl
  omega

end PipelineImpl
end Layered
end Elegant

import Elegant.Layered.LoopExtentReservationProof
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Route
import Elegant.Layered.Order
import Elegant.Layered.CoordGraph
import Elegant.Layered.LoopRectRealQProof
import Elegant.Layered.StrictMemberFrameProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Loop-footprint neighbor gap for plain owners

Proves the foreign-hull `x`-gap residual for a plain looping owner
(`nt.border = 0`): whenever a foreign group hull starts right of the plain
owner's frame, the loop footprint ends left of that hull.

Truth (see `wip/Probe/LoopResNeighborGapTProbe.lean`): flat and nested inputs,
plain and group-top owners, same-rank and off-rank foreign hulls; no
`Fleft /\ ¬R3` instance on any executed run.

Route: when the foreign group's proper members span the owner's rank, the
closed `bracketMarkersAtRank'` supplies the left/right border markers in the
owner's layer; a layer-index trichotomy puts the owner before the left
marker (then `loopRes_sameLayer_holds` bounds the footprint by the marker's
rect, and `SideMarkerSpanAligned` identifies every left marker's `x` with
the hull's left edge) or at/after it (then ordered intervals
(`componentRun_nonproxy_ordered_intervals`) plus the positive marker width
contradict the frame-left hypothesis). The group-top owner and the
off-rank plain case stay as the named single-inequality residuals below. -/

/-- The foreign group's proper members span the owner's rank: witnesses
below and above the owner's proper rank whose cluster paths contain the
declaration. This is exactly the bracket premise at the owner's rank. -/
def LoopResNeighborSpanning (run : Run) (t decl : Nat) : Prop :=
  ∃ (low high : Nat) (lowNd highNd : ProperNode),
    run.proper.nodes[low]? = some lowNd ∧
    lowNd.node.clusterPath.contains decl = true ∧
    (rk run.proper.rank low).toNat ≤ (rk run.proper.rank t).toNat ∧
    run.proper.nodes[high]? = some highNd ∧
    highNd.node.clusterPath.contains decl = true ∧
    (rk run.proper.rank t).toNat ≤ (rk run.proper.rank high).toNat

/-- Residual: the plain-owner off-rank case. Same binders as the
foreign-hull `x`-gap goal with `nt.border = 0` and the group's proper
members not spanning the owner's rank. Probe: `LoopResNeighborGapTProbe` (15 off-rank `Fleft`
instances across the flat, wide-label, nested, and tower inputs, every one
`R3`-holding, zero violations). -/
def LoopResNeighborGapOffRank (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt → nt.border = 0 →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    ∀ (pos : Nat) (np : Node), cg.nodes[pos]? = some np → np.border = -2 →
      pos ≠ t → nt.decl ≠ np.decl →
      np.decl ∉ nt.clusterPath → nt.decl ∉ np.clusterPath →
      ¬ LoopResNeighborSpanning run t np.decl →
      (frameRect P cg run t).x + (frameRect P cg run t).w ≤
        (frameRect P cg run pos).x →
      (loopFootprint cg run labels t).x + (loopFootprint cg run labels t).w ≤
        (frameRect P cg run pos).x

/-- Residual: the group-top owner case of the foreign-hull `x`-gap goal
(loop on a group top, `nt.border = -2`). Needs `LoopResMarkerCopy` plus the
marker-layer reservation; both stay open in the shared core. Probe:
`LoopResNeighborGapTProbe` (`grpLoopSameRank`: 3 group-owner `Fleft`
instances, every one `R3`-holding, zero violations). -/
def LoopResNeighborGapGroupTop (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt → nt.border = -2 →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    ∀ (pos : Nat) (np : Node), cg.nodes[pos]? = some np → np.border = -2 →
      pos ≠ t → nt.decl ≠ np.decl →
      np.decl ∉ nt.clusterPath → nt.decl ∉ np.clusterPath →
      (frameRect P cg run t).x + (frameRect P cg run t).w ≤
        (frameRect P cg run pos).x →
      (loopFootprint cg run labels t).x + (loopFootprint cg run labels t).w ≤
        (frameRect P cg run pos).x

/-- Residual: the bottom-marker owner case of the foreign-hull `x`-gap goal
(`nt.border = -2` is impossible for loop owners by marker shape, and bottom
indices carry no self-loops by `bottomLoopEmpty_holds`). Probe:
`LoopResNeighborGapTProbe` (no bottom-marker self-loop on any sample, so
the implication is vacuous there). -/
def LoopResNeighborGapBottomOwner (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt → nt.border = 2 →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    ∀ (pos : Nat) (np : Node), cg.nodes[pos]? = some np → np.border = -2 →
      pos ≠ t → nt.decl ≠ np.decl →
      np.decl ∉ nt.clusterPath → nt.decl ∉ np.clusterPath →
      (frameRect P cg run t).x + (frameRect P cg run t).w ≤
        (frameRect P cg run pos).x →
      (loopFootprint cg run labels t).x + (loopFootprint cg run labels t).w ≤
        (frameRect P cg run pos).x

/-- Local copy of the private `lines_len_general`. -/
private theorem lng_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) : e.lines.length = inp.boxes.length := by
  have h := e.lines_eq
  simp only [boxLines] at h
  calc e.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

/-- Local copy of the private side-marker width lemma: every side marker
emitted by `addClusterBorders` carries the border width. -/
private theorem lng_side_width (source : Proper) (width : Int)
    (hready : OrderImpl.BorderConstructionReady source)
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders source width).nodes[index]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    node.node.w = width := by
  have hP : ∀ n ∈ (OrderImpl.addClusterBorders source width).nodes,
      n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width := by
    rw [OrderImpl.addClusterBorders_eq]
    apply OrderImpl.foldl_inv
      (fun cur : Proper => ∀ n ∈ cur.nodes,
        n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width)
    · intro n hn hs
      rcases hs with hs | hs
      · exact ((hready.1 n hn).1 hs).elim
      · exact ((hready.1 n hn).2 hs).elim
    · intro state hstate entry hentry
      unfold OrderImpl.borderStep
      split
      · exact hstate
      · apply OrderImpl.foldl_inv
          (fun cur : Proper => ∀ n ∈ cur.nodes,
            n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width)
        · exact hstate
        · intro st hst off _
          intro n hn hs
          have hn' : n ∈ st.nodes ++
              [OrderImpl.borderLeft entry width,
                OrderImpl.borderRight entry width] := hn
          rcases List.mem_append.mp hn' with hold | hnew
          · exact hst n hold hs
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
            rcases hnew with rfl | rfl <;> rfl
  exact hP node (List.mem_of_getElem? hnode) hside

/-- Plain owner with spanning witnesses: the `x`-gap holds. The
bracket at the owner's rank puts both side markers in the owner's layer;
before the left marker the same-layer reservation applies, at/after it
ordered intervals contradict the frame-left premise. -/
theorem loopResNeighborGap_plainSpan_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 0)
    (_het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrpB : np.border = -2)
    (_hne : pos ≠ t) (_hne2 : nt.decl ≠ np.decl)
    (_hni1 : np.decl ∉ nt.clusterPath) (_hni2 : nt.decl ∉ np.clusterPath)
    (hspan : LoopResNeighborSpanning run t np.decl)
    (hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).x +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x := by
  obtain ⟨low, high, lowNd, highNd, hlowRec, hlowCon, hlowLe,
    hhighRec, hhighCon, hhighLe⟩ := hspan
  have hlines : execution.lines.length = inp.boxes.length :=
    lng_lines_len execution
  obtain ⟨mL, mR, nL, nR, hcoordL, hborderL, hlastL, hrankL,
    hcoordR, hborderR, hlastR, hrankR⟩ :=
    bracketMarkersAtRank' execution.graph_eq hlines hwf hframed hcomp hrun
      (rk run.proper.rank t).toNat hlowRec hlowCon hlowLe
      hhighRec hhighCon hhighLe
  obtain ⟨_, _, _, _q0, _, _, _, _, _, hproxy, hdrop, hroute, _, _, _, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hproxy
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]; exact hrankEq
  obtain ⟨actualT, hcoordT, hproperT, _, hbT0, _, _, _, _, _⟩ :=
    componentRun_original_plain_record hrun hnt htB
  obtain ⟨hproperL, hxsL⟩ :=
    componentRun_border_record hrun hcoordL (Or.inl hborderL)
  obtain ⟨hproperR, _⟩ :=
    componentRun_border_record hrun hcoordR (Or.inr hborderR)
  have hneL : ¬ (nL.node.border = -2 ∨ nL.node.border = 2) := by
    rw [hborderL]; decide
  have hneT : ¬ (actualT.node.border = -2 ∨ actualT.node.border = 2) := by
    rw [hbT0]; decide
  have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
  have hgeom := (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, hwwT, _, hcov, _⟩ := RouteImpl.layersOk_spec hgeom
  have hwT : t < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hproperT).1
  obtain ⟨lT, hlyT, hmemT, hrkTNNproper⟩ := hcov t hwT
  have hrkTNN : 0 ≤ rk run.coordinateProper.rank t := by
    rw [← hranks]; exact hrkTNNproper
  have hrkL : rk run.proper.rank mL = rk run.proper.rank t := by
    rw [hranks, hrankL, hranks]; exact Int.toNat_of_nonneg hrkTNN
  have hrkR : rk run.proper.rank mR = rk run.proper.rank t := by
    rw [hranks, hrankR, hranks]; exact Int.toNat_of_nonneg hrkTNN
  have hwL : mL < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hproperL).1
  obtain ⟨lM, hlyM, hmemM, _⟩ := hcov mL hwL
  have hlyEq : lM = lT := by
    rw [hrkL] at hlyM
    exact Option.some.inj (hlyM.symm.trans hlyT)
  rw [hlyEq] at hmemM
  obtain ⟨iv, hiv⟩ := List.mem_iff_getElem?.mp hmemT
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmemM
  have hlayer : lT ∈ run.layers := by
    obtain ⟨hmemLT, hmemEq⟩ := List.getElem?_eq_some_iff.mp hlyT
    rw [← hmemEq]; exact List.getElem_mem hmemLT
  have hvtlen : t < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnt).1
  have hgetT : (componentCandidate execution.graph comp candidate).nodes.getD t default =
      nt := by
    rw [List.getD_eq_getElem?_getD, hnt]; rfl
  have hframeT : frameRect execution.params
      (componentCandidate execution.graph comp candidate) run t =
      nodeRect (componentCandidate execution.graph comp candidate) run t :=
    frameRect_of_border_zero hgetT htB
  have hnodeT : nodeRect (componentCandidate execution.graph comp candidate) run t =
      ⟨RouteImpl.leftOf run.proper run.xs t, RouteImpl.yAt run.ys t,
        actualT.node.w, actualT.node.h⟩ :=
    nodeRect_of_record hproperT
  have hframeTx : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run t).x =
      RouteImpl.leftOf run.proper run.xs t := by rw [hframeT, hnodeT]
  have hframeTw : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run t).w =
      actualT.node.w := by rw [hframeT, hnodeT]
  have hullX : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run pos).x =
      (boundsOf (groupBorderRects
        (componentCandidate execution.graph comp candidate) run np.decl) []).minX := by
    rw [frameRect_group_span hnp hgrpB]
  have hmemL : Labels.rectAt run.proper run.xs run.ys mL ∈
      groupBorderRects
        (componentCandidate execution.graph comp candidate) run np.decl :=
    groupBorderRects_mem_of_record hproperL (Or.inl hborderL) hlastL
  have hminLe := (boundsOf_rect_mem hmemL).1
  have hneB : groupBorderRects
      (componentCandidate execution.graph comp candidate) run np.decl ≠ [] :=
    List.ne_nil_of_mem hmemL
  have hrectLx : (Labels.rectAt run.proper run.xs run.ys mL).x =
      RouteImpl.leftOf run.proper run.xs mL := by rw [rectAt_eq]
  have hall : ∀ r ∈ groupBorderRects
      (componentCandidate execution.graph comp candidate) run np.decl,
      (Labels.rectAt run.proper run.xs run.ys mL).x ≤ r.x := by
    intro r hr
    obtain ⟨q, nd, hrec, hbor, hlast, rfl⟩ := groupBorderRects_inv hr
    have eQ : (Labels.rectAt run.proper run.xs run.ys q).x =
        RouteImpl.leftOf run.proper run.xs q := by rw [rectAt_eq]
    rcases hbor with hsideL | hsideR
    · have hal := halign execution.graph_eq hlines hwf hframed hcomp hrun
        hproperL (Or.inl hborderL) hlastL hrec (Or.inl hsideL) hlast
      have heq := (hal.1 (by rw [hborderL, hsideL])).1
      omega
    · have halR := halign execution.graph_eq hlines hwf hframed hcomp hrun
        hproperR (Or.inr hborderR) hlastR hrec (Or.inr hsideR) hlast
      have heqR := (halR.1 (by rw [hborderR, hsideR])).1
      have halLR := halign execution.graph_eq hlines hwf hframed hcomp hrun
        hproperL (Or.inl hborderL) hlastL
        hproperR (Or.inr hborderR) hlastR
      have hle := (halLR.2.2 ⟨hborderL, hborderR, hrkL.trans hrkR.symm⟩).1
      omega
  have hge : (Labels.rectAt run.proper run.xs run.ys mL).x ≤
      (boundsOf (groupBorderRects
        (componentCandidate execution.graph comp candidate) run np.decl) []).minX :=
    boundsOf_minX_ge_of_all hneB hall
  have hullEq : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run pos).x =
      (Labels.rectAt run.proper run.xs run.ys mL).x := by
    rw [hullX]; omega
  rcases Nat.lt_or_ge iv j with hlt | hgeIdx
  · have hcore := loopRes_sameLayer_holds execution comp candidate orderOptions run
      hcomp hrun hvtlen hnt htB hcoordT hcoordL hneL hproperL hxsL hlayer hiv hj hlt
    rw [hullEq]; exact hcore
  · rcases Nat.eq_or_lt_of_le hgeIdx with heq | hgt
    · have htm : t = mL := Option.some.inj (hiv.symm.trans (heq ▸ hj))
      subst htm
      have hcontra := Option.some.inj (hproperT.symm.trans hproperL)
      have hb := congrArg (fun nd : ProperNode => nd.node.border) hcontra
      rw [hbT0, hborderL] at hb
      omega
    · have hsep := componentRun_nonproxy_ordered_intervals execution.graph_eq hcomp
        hrun hlayer hgt hj hiv hcoordL hcoordT hneL hneT
      have hwMLw : nL.node.w = execution.params.clusterBorderW := by
        obtain ⟨labeled, hcoordEq, hreadyB⟩ :=
          componentRun_titled_border_ready execution.graph_eq hcomp hrun
        have hcoordML : (coordinateGraph execution.params labeled).nodes[mL]? =
            some nL := by
          rw [hcoordEq]; exact hcoordL
        have horigL := coordinateGraph_side_original hreadyB hcoordML
          (Or.inl hborderL)
        exact lng_side_width _ _ hreadyB horigL (Or.inl hborderL)
      have hnWmL : RouteImpl.nodeW run.proper mL =
          execution.params.clusterBorderW := by
        simp only [RouteImpl.nodeW, hproperL, hwMLw]
      have hgeW : 1 ≤ execution.params.clusterBorderW :=
        checkedParams_clusterBorderW_ge_one execution.checked
      have hnWt : RouteImpl.nodeW run.proper t = actualT.node.w := by
        simp only [RouteImpl.nodeW, hproperT]
      have hwtNN : 0 ≤ actualT.node.w := hnWt ▸ (hwwT t hwT).1
      omega

/-- Plain looping owner: the `x`-gap holds modulo the off-rank
residual. The spanning case is `loopResNeighborGap_plainSpan_holds`; the
off-rank case is the residual premise. -/
theorem loopResNeighborGap_plain_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hoff : LoopResNeighborGapOffRank execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 0)
    (het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrpB : np.border = -2)
    (hne : pos ≠ t) (hne2 : nt.decl ≠ np.decl)
    (hni1 : np.decl ∉ nt.clusterPath) (hni2 : nt.decl ∉ np.clusterPath)
    (hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).x +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x := by
  by_cases hspan : LoopResNeighborSpanning run t np.decl
  · exact loopResNeighborGap_plainSpan_holds hwf hframed hx execution hcomp hrun
      hnt htB het hnp hgrpB hne hne2 hni1 hni2 hspan hFL
  · exact hoff t nt hnt htB het pos np hnp hgrpB hne hne2 hni1 hni2 hspan hFL

/-- Full `x`-gap from the plain theorem and the two non-plain
residuals. Candidate loop owners have border `0`, `-2` or `2`
(`componentCandidate_marker_shape`); the plain case splits on spanning. -/
theorem loopResNeighborGap_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hoff : LoopResNeighborGapOffRank execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured)
    (hgrp : LoopResNeighborGapGroupTop execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured)
    (hbot : LoopResNeighborGapBottomOwner execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrpB : np.border = -2)
    (hne : pos ≠ t) (hne2 : nt.decl ≠ np.decl)
    (hni1 : np.decl ∉ nt.clusterPath) (hni2 : nt.decl ∉ np.clusterPath)
    (hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).x +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x := by
  have hshape := (componentCandidate_marker_shape execution.graph_eq hnt).1
  rcases hshape with ht0 | htG | htBot
  · exact loopResNeighborGap_plain_holds hwf hframed hx execution hcomp hrun hoff
      hnt ht0 het hnp hgrpB hne hne2 hni1 hni2 hFL
  · exact hgrp t nt hnt htG het pos np hnp hgrpB hne hne2 hni1 hni2 hFL
  · exact hbot t nt hnt htBot het pos np hnp hgrpB hne hne2 hni1 hni2 hFL

end PipelineImpl
end Layered
end Elegant

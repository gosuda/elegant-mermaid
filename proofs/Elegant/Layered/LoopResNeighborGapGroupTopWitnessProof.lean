import Elegant.Layered.LoopResNeighborGapGroupProof
import Elegant.Layered.LoopResNeighborGapProof
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.StrictMemberFrameProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Loop-residue neighbor-gap group-top witness (shared-rank replacement)

Truth: `LoopResNeighborGapGroupTopWitness` (arbitrary `P/cg/run`, two
disjoint groups with `Fleft` imply ordered markers in a shared layer) is
FALSE. Witness (`wip/Probe/LoopGapGroupTopWitnessTProbe5.lean`, input
`chain2`): flowchart boxes `[G1, a, G2, b, y1, y2]` with `a` in `G1`,
`b` in `G2`, routes `G1 -> G1`, `a -> y1`, `y1 -> y2`, `y2 -> b`, loop
label 34 wide chars on `G1 -> G1`; `framedParents = true`,
`WellFormed = true`. In candidate 0 the component candidate has `t = 0`
(`border = -2`, `decl = 0`, `path = [0]`, self-loop present) and
`pos = 2` (`border = -2`, `decl = 2`, `path = [2]`, unrelated paths),
frame-right `192... <= 28250` (`Fleft` holds) but no shared layer contains
a right marker of `t` before a left marker of `pos` (marker ranks
`[0,1,2]` vs `[6,7,8]`, disjoint; `witness = false`). The same input has
footprint-right `33530 <= 28250` false, so the full
`LoopResNeighborGapGroupTop` (`Fleft -> footprint <= hull`) is also FALSE
without a shared-rank premise. A witness-only counterexample (shared-layer
failure with `R3` holding) is `tower3` (`G1/G2/G3` chain, `t = G1`,
`pos = G3`, ranks `[0,1,2]` vs `[4,5,6]`, `witness = false`, `R3 = true`).

Replacement (proved below): the same witness with the extra premise that
the two groups share a proper rank (some `a/b` with `contains` and equal
`rk`), quantified over executed runs only. Strictly narrower than the
target (extra premise, executed runs only). True on the shared-rank probe
(`grpLoopSameRank`/`directStack`/`sidePush`: `sharedRank = true`,
`witness = true` on every candidate).
-/

/-- Shared-rank witness for the group-top neighbor gap: for an executed
run, a looping group top `t` and an unrelated group top `pos` with
`Fleft`, whenever some proper nodes of the two declarations share a rank,
there are a right marker of `t` and a left marker of `pos` in one layer
with the right marker before the left marker. Strictly narrower than
`LoopResNeighborGapGroupTopWitness` (executed runs only, extra
shared-rank premise). -/
def LoopResNeighborGapGroupTopWitnessShared {inp : Input} {o : Options} {res : FamilyResult} (execution : SceneExecution inp o res) {comp : List Nat} (_hcomp : comp ∈ components execution.graph) {candidate : Nat} {run : Run} {orderOptions : OrderOptions} (_hrun : componentRun execution.params (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run) : Prop :=
  ∀ (t : Nat) (nt : Node), (componentCandidate execution.graph comp candidate).nodes[t]? = some nt → nt.border = -2 → (∃ e ∈ (componentCandidate execution.graph comp candidate).edges, e.tail = t ∧ e.head = t) → ∀ (pos : Nat) (np : Node), (componentCandidate execution.graph comp candidate).nodes[pos]? = some np → np.border = -2 → pos ≠ t → nt.decl ≠ np.decl → np.decl ∉ nt.clusterPath → nt.decl ∉ np.clusterPath → (frameRect execution.params (componentCandidate execution.graph comp candidate) run t).x + (frameRect execution.params (componentCandidate execution.graph comp candidate) run t).w ≤ (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).x → (∃ (a b : Nat) (na nb : ProperNode), run.proper.nodes[a]? = some na ∧ na.node.clusterPath.contains nt.decl = true ∧ run.proper.nodes[b]? = some nb ∧ nb.node.clusterPath.contains np.decl = true ∧ rk run.proper.rank a = rk run.proper.rank b) → ∃ (mRt mLp : Nat) (nRt nLp : ProperNode) (layer : List Nat) (j iv : Nat), run.coordinateProper.nodes[mRt]? = some nRt ∧ nRt.node.border = 1 ∧ nRt.node.clusterPath.getLast? = some nt.decl ∧ run.coordinateProper.nodes[mLp]? = some nLp ∧ nLp.node.border = -1 ∧ nLp.node.clusterPath.getLast? = some np.decl ∧ layer ∈ run.layers ∧ layer[j]? = some mRt ∧ layer[iv]? = some mLp ∧ j < iv
private theorem lggt_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) : e.lines.length = inp.boxes.length := by
  have h := e.lines_eq
  simp only [boxLines] at h
  calc e.lines.length = (inp.boxes.zipIdx).length :=
      Sequence.mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

private theorem lggt_no_group_at_b {inp : Input} {o : Options} {res : FamilyResult}
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
private theorem lggt_frameB_x {P : Params} {cg : Graph} {run : Run}
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

private theorem lggt_side_width (source : Proper) (width : Int)
    (hready : OrderImpl.BorderConstructionReady source)
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders source width).nodes[index]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    node.node.w = width := by
  have hP : ∀ n ∈ (OrderImpl.addClusterBorders source width).nodes,
      n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width := by
    rw [OrderImpl.addClusterBorders_eq]
    apply OrderImpl.foldl_inv
      (fun cur : Proper =>
        ∀ n ∈ cur.nodes,
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
          (fun cur : Proper =>
            ∀ n ∈ cur.nodes,
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

private theorem lggt_hull_eq_of_left {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
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
    · have hal := halign e.graph_eq hcomp hrun hproperP (Or.inl hbP) hlastP
        hrec (Or.inl hsideL) hlast
      have heq := (hal.1 (by rw [hbP, hsideL])).1
      omega
    · have halR := halign e.graph_eq hcomp hrun hpropR (Or.inr hbR) hlastR
        hrec (Or.inr hsideR) hlast
      have heqR := (halR.1 (by rw [hbR, hsideR])).1
      have halLR := halign e.graph_eq hcomp hrun hpropL (Or.inl hbL) hlastL
        hpropR (Or.inr hbR) hlastR
      have hle := (halLR.2.2 ⟨hbL, hbR, hrankPair⟩).1
      have halLL := halign e.graph_eq hcomp hrun hpropL (Or.inl hbL) hlastL
        hproperP (Or.inl hbP) hlastP
      have hRL : RouteImpl.leftOf run.proper run.xs mL =
          RouteImpl.leftOf run.proper run.xs mLp :=
        ((halLL.1 (by rw [hbL, hbP])).1)
      omega
  have hge : (Labels.rectAt run.proper run.xs run.ys mLp).x ≤
      (boundsOf (groupBorderRects (componentCandidate e.graph comp candidate) run np.decl) []).minX :=
    boundsOf_minX_ge_of_all hneB hall
  have hminLe := (boundsOf_rect_mem hmemP).1
  rw [hullX]; omega

private theorem lggt_hull_right_eq {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (oo : OrderOptions) (v : Nat) (nodeV : Node)
    (hcomp : comp ∈ components e.graph)
    (hnodeV : (componentCandidate e.graph comp candidate).nodes[v]? = some nodeV)
    (hvtop : nodeV.border = -2)
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured oo = .ok run)
    (halign : SideMarkerSpanAligned)
    (mL mR : Nat) (nL nR : ProperNode)
    (hL : run.proper.nodes[mL]? = some nL) (hbL : nL.node.border = -1)
    (hlL : nL.node.clusterPath.getLast? = some nodeV.decl)
    (hR : run.proper.nodes[mR]? = some nR) (hbR : nR.node.border = 1)
    (hlR : nR.node.clusterPath.getLast? = some nodeV.decl)
    (hrank : rk run.proper.rank mL = rk run.proper.rank mR) :
    (Labels.rectAt run.proper run.xs run.ys mR).x + (Labels.rectAt run.proper run.xs run.ys mR).w = (frameRect default (componentCandidate e.graph comp candidate) run v).x + (frameRect default (componentCandidate e.graph comp candidate) run v).w := by
  have hframe := frameRect_group_span (P := default) (run := run) hnodeV hvtop
  have hall : ∀ r ∈ groupBorderRects (componentCandidate e.graph comp candidate) run nodeV.decl, r.x + r.w ≤ (Labels.rectAt run.proper run.xs run.ys mR).x + (Labels.rectAt run.proper run.xs run.ys mR).w := by
    intro r hr
    obtain ⟨q, nd, hq, hbq, hlastq, hrq⟩ := groupBorderRects_inv hr
    rcases hbq with hbqL | hbqR
    · obtain ⟨heq1, heq2⟩ := (halign e.graph_eq hcomp hrun hq (Or.inl hbqL) hlastq hL (Or.inl hbL) hlL).1 (by rw [hbL, hbqL])
      have hcross := (halign e.graph_eq hcomp hrun hL (Or.inl hbL) hlL hR (Or.inr hbR) hlR).2.2 ⟨hbL, hbR, hrank⟩
      rw [hrq, rectAt_eq run.proper run.xs run.ys q, rectAt_eq run.proper run.xs run.ys mR]
      dsimp only
      omega
    · obtain ⟨heq1, heq2⟩ := (halign e.graph_eq hcomp hrun hq (Or.inr hbqR) hlastq hR (Or.inr hbR) hlR).1 (by rw [hbR, hbqR])
      rw [hrq, rectAt_eq run.proper run.xs run.ys q, rectAt_eq run.proper run.xs run.ys mR]
      dsimp only
      omega
  have hnonnegR := (halign e.graph_eq hcomp hrun hR (Or.inr hbR) hlR hR (Or.inr hbR) hlR).2.1
  have hmemR : Labels.rectAt run.proper run.xs run.ys mR ∈ groupBorderRects (componentCandidate e.graph comp candidate) run nodeV.decl := groupBorderRects_mem_of_record hR (Or.inr hbR) hlR
  have hzero : (0 : Int) ≤ (Labels.rectAt run.proper run.xs run.ys mR).x + (Labels.rectAt run.proper run.xs run.ys mR).w := by rw [rectAt_eq]; exact hnonnegR
  have hright := boundsOf_right_le_of_all hzero hall
  have hge := (boundsOf_rect_mem hmemR).2
  have hframeRW : (frameRect default (componentCandidate e.graph comp candidate) run v).x + (frameRect default (componentCandidate e.graph comp candidate) run v).w = (boundsOf (groupBorderRects (componentCandidate e.graph comp candidate) run nodeV.decl) []).right := by rw [hframe]; dsimp only; omega
  omega

private theorem lggt_bracket_pair {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured orderOptions = .ok run)
    {decl mLp : Nat} {nLp : ProperNode}
    (hproperP : run.proper.nodes[mLp]? = some nLp)
    (hconP : nLp.node.clusterPath.contains decl = true) :
    ∃ (mL mR : Nat) (nL nR : ProperNode), run.coordinateProper.nodes[mL]? = some nL ∧ nL.node.border = -1 ∧ nL.node.clusterPath.getLast? = some decl ∧ run.proper.nodes[mL]? = some nL ∧ run.coordinateProper.nodes[mR]? = some nR ∧ nR.node.border = 1 ∧ nR.node.clusterPath.getLast? = some decl ∧ run.proper.nodes[mR]? = some nR ∧ rk run.proper.rank mL = rk run.proper.rank mR := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ := componentRun_spec hrun
  obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hproxy
  have hranks : run.proper.rank = run.coordinateProper.rank := by rw [← hdrop, OrderImpl.dropSynthetic_rank]; exact hrankEq
  obtain ⟨mL, mR, nL, nR, hcoordL, hbL, hlastL, hrankL, hcoordR, hbR, hlastR, hrankR⟩ := bracketMarkersAtRank' e.graph_eq (lggt_lines_len e) hwf hfp hcomp hrun (rk run.proper.rank mLp).toNat hproperP hconP (Nat.le_refl _) hproperP hconP (Nat.le_refl _)
  obtain ⟨hpropL, _⟩ := componentRun_border_record hrun hcoordL (Or.inl hbL)
  obtain ⟨hpropR, _⟩ := componentRun_border_record hrun hcoordR (Or.inr hbR)
  have hrankPair : rk run.proper.rank mL = rk run.proper.rank mR := by
    have e1 : rk run.proper.rank mL = rk run.coordinateProper.rank mL := by
      rw [hranks]
    have e2 : rk run.proper.rank mR = rk run.coordinateProper.rank mR := by
      rw [hranks]
    rw [e1, e2, hrankL, hrankR]
  exact ⟨mL, mR, nL, nR, hcoordL, hbL, hlastL, hpropL, hcoordR, hbR, hlastR, hpropR, hrankPair⟩

private theorem lggt_top_bound {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    {comp : List Nat} (hcomp : comp ∈ components e.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun e.params (componentCandidate e.graph comp candidate) e.measured orderOptions = .ok run)
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
    (loopFootprint (componentCandidate e.graph comp candidate) run e.measured t).x + (loopFootprint (componentCandidate e.graph comp candidate) run e.measured t).w ≤ (frameRect default (componentCandidate e.graph comp candidate) run mLp).x := by
  have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
  have hext := loopResMarkerCopy_holds e comp candidate orderOptions run hcomp hrun hnt htG hcoordT hbT hlastT
  obtain ⟨hproperP, hxsP⟩ := componentRun_border_record hrun hcoordP (Or.inl hbP)
  have hbne : ¬ (nLp.node.border = -2 ∨ nLp.node.border = 2) := by rw [hbP]; decide
  exact loopResTopReservation_holds e hwf hfp hcomp hrun hnt htG hcoordT hbT hlastT hext halign hcoordP hbne hproperP hxsP hlayer hj hiv hlt

theorem loopResNeighborGapGroupTopWitnessShared_holds {inp : Input} {o : Options} {res : FamilyResult} (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true) (_hx : ForeignBorderChainXAligned) (horder : ForeignBorderLayerOrder) (execution : SceneExecution inp o res) {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat} {run : Run} {orderOptions : OrderOptions} (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run) : LoopResNeighborGapGroupTopWitnessShared execution hcomp hrun := by
  intro t nt hnt htG het pos np hnp hgrp hne hne2 hni1 hni2 hFL hShared
  obtain ⟨a, b, na, nb, hna, hconT, hnb, hconP, hrkEq⟩ := hShared
  have hrkEqNat : (rk run.proper.rank b).toNat = (rk run.proper.rank a).toNat := (congrArg Int.toNat hrkEq).symm
  obtain ⟨mLt, mRt, nLt, nRt, hcoordLt, hbLt, hlastLt, hrkLt, hcoordRt, hbRt, hlastRt, hrkRt⟩ := bracketMarkersAtRank' execution.graph_eq (lggt_lines_len execution) hwf hfp hcomp hrun (rk run.proper.rank a).toNat hna hconT (Nat.le_refl _) hna hconT (Nat.le_refl _)
  obtain ⟨mLp, mRp, nLp, nRp, hcoordLp, hbLp, hlastLp, hrkLp, hcoordRp, hbRp, hlastRp, hrkRp⟩ := bracketMarkersAtRank' execution.graph_eq (lggt_lines_len execution) hwf hfp hcomp hrun (rk run.proper.rank a).toNat hnb hconP (by rw [hrkEqNat]; exact Nat.le_refl _) hnb hconP (by rw [hrkEqNat]; exact Nat.le_refl _)
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, hordOk, hlayers⟩, _, _, _, _, _, _, _, _⟩ := componentRun_spec hrun
  have hlayEq : OrderImpl.lay run.coordinateProper mLp = OrderImpl.lay run.coordinateProper mRt := by simp only [OrderImpl.lay, hrkLp, hrkRt]
  obtain ⟨hlayRtLt, hmemRtOrd⟩ := ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord hordOk hcoordRt
  obtain ⟨_, hmemLpOrd⟩ := ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord hordOk hcoordLp
  have hmemLpOrdEq : mLp ∈ ord.layers.getD (OrderImpl.lay run.coordinateProper mRt) [] := by rw [← hlayEq]; exact hmemLpOrd
  have hlayRunLt : OrderImpl.lay run.coordinateProper mRt < run.layers.length := by rw [← hlayers]; exact hlayRtLt
  have hLmemRun : run.layers.getD (OrderImpl.lay run.coordinateProper mRt) [] ∈ run.layers := layer_getD_mem hlayRunLt
  have hmemRtRun : mRt ∈ run.layers.getD (OrderImpl.lay run.coordinateProper mRt) [] := by rw [← hlayers]; exact hmemRtOrd
  have hmemLpRun : mLp ∈ run.layers.getD (OrderImpl.lay run.coordinateProper mRt) [] := by rw [← hlayers]; exact hmemLpOrdEq
  obtain ⟨j, hjLt, hjEq⟩ := List.mem_iff_getElem.mp hmemRtRun
  obtain ⟨iv, hivLt, hivEq⟩ := List.mem_iff_getElem.mp hmemLpRun
  have hj : (run.layers.getD (OrderImpl.lay run.coordinateProper mRt) [])[j]? = some mRt := by simp only [List.getElem?_eq_getElem hjLt, hjEq]
  have hiv : (run.layers.getD (OrderImpl.lay run.coordinateProper mRt) [])[iv]? = some mLp := by simp only [List.getElem?_eq_getElem hivLt, hivEq]
  have hpathW : np.clusterPath.contains nt.decl = false := by cases hc : np.clusterPath.contains nt.decl with | true => exact absurd (List.contains_iff_mem.mp hc) hni2 | false => rfl
  have hpathU : nt.clusterPath.contains np.decl = false := by cases hc : nt.clusterPath.contains np.decl with | true => exact absurd (List.contains_iff_mem.mp hc) hni1 | false => rfl
  have hDir := horder execution.graph_eq hcomp hrun hnt hnp htG hgrp hne2 hpathW hpathU hLmemRun
  rcases hDir with hBefore | hAfter
  · exact ⟨mRt, mLp, nRt, nLp, run.layers.getD (OrderImpl.lay run.coordinateProper mRt) [], j, iv, hcoordRt, hbRt, hlastRt, hcoordLp, hbLp, hlastLp, hLmemRun, hj, hiv, hBefore j iv mRt mLp nRt nLp hj hiv hcoordRt hcoordLp (Or.inr hbRt) hlastRt (Or.inl hbLp) hlastLp⟩
  · have hltBA : iv < j := hAfter j iv mRt mLp nRt nLp hj hiv hcoordRt hcoordLp (Or.inr hbRt) hlastRt (Or.inl hbLp) hlastLp
    have hordSep := componentRun_nonproxy_ordered_intervals execution.graph_eq hcomp hrun hLmemRun hltBA hiv hj hcoordLp hcoordRt (by rw [hbLp]; decide) (by rw [hbRt]; decide)
    obtain ⟨labeled, hcoordEq, hready⟩ := componentRun_titled_border_ready execution.graph_eq hcomp hrun
    have hcoordLpG : (coordinateGraph execution.params labeled).nodes[mLp]? = some nLp := by rw [hcoordEq]; exact hcoordLp
    have hcoordRtG : (coordinateGraph execution.params labeled).nodes[mRt]? = some nRt := by rw [hcoordEq]; exact hcoordRt
    have horigLp := coordinateGraph_side_original hready hcoordLpG (Or.inl hbLp)
    have horigRt := coordinateGraph_side_original hready hcoordRtG (Or.inr hbRt)
    have hWLeftEq := lggt_side_width _ _ hready horigLp (Or.inl hbLp)
    have hWRightEq := lggt_side_width _ _ hready horigRt (Or.inr hbRt)
    have hWLeftGe : (1 : Int) ≤ nLp.node.w := by rw [hWLeftEq]; exact checkedParams_clusterBorderW_ge_one execution.checked
    obtain ⟨hproperLp, _⟩ := componentRun_border_record hrun hcoordLp (Or.inl hbLp)
    obtain ⟨hproperRt, _⟩ := componentRun_border_record hrun hcoordRt (Or.inr hbRt)
    have hmemLpB : Labels.rectAt run.proper run.xs run.ys mLp ∈ groupBorderRects (componentCandidate execution.graph comp candidate) run np.decl := groupBorderRects_mem_of_record hproperLp (Or.inl hbLp) hlastLp
    have hmemRtB : Labels.rectAt run.proper run.xs run.ys mRt ∈ groupBorderRects (componentCandidate execution.graph comp candidate) run nt.decl := groupBorderRects_mem_of_record hproperRt (Or.inr hbRt) hlastRt
    have hframeP := frameRect_group_span (P := execution.params) (run := run) hnp hgrp
    have hframeT := frameRect_group_span (P := execution.params) (run := run) hnt htG
    have hHpLe : (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).x ≤ (Labels.rectAt run.proper run.xs run.ys mLp).x := by rw [hframeP]; exact (boundsOf_rect_mem hmemLpB).1
    have hgeRt := (boundsOf_rect_mem hmemRtB).2
    have hFtGe : (Labels.rectAt run.proper run.xs run.ys mRt).x + (Labels.rectAt run.proper run.xs run.ys mRt).w ≤ (frameRect execution.params (componentCandidate execution.graph comp candidate) run t).x + (frameRect execution.params (componentCandidate execution.graph comp candidate) run t).w := by simp only [hframeT]; omega
    have hrectLp : (Labels.rectAt run.proper run.xs run.ys mLp).x = RouteImpl.leftOf run.proper run.xs mLp ∧ (Labels.rectAt run.proper run.xs run.ys mLp).w = RouteImpl.nodeW run.proper mLp := ⟨rfl, rfl⟩
    have hrectRt : (Labels.rectAt run.proper run.xs run.ys mRt).x = RouteImpl.leftOf run.proper run.xs mRt ∧ (Labels.rectAt run.proper run.xs run.ys mRt).w = RouteImpl.nodeW run.proper mRt := ⟨rfl, rfl⟩
    have hnodeLp : RouteImpl.nodeW run.proper mLp = nLp.node.w := by simp [RouteImpl.nodeW, hproperLp]
    have hnodeRt : RouteImpl.nodeW run.proper mRt = nRt.node.w := by simp [RouteImpl.nodeW, hproperRt]
    have hWRightGe : (0 : Int) ≤ nRt.node.w := by rw [hWRightEq]; have h1 : (1 : Int) ≤ execution.params.clusterBorderW := checkedParams_clusterBorderW_ge_one execution.checked; omega
    omega

theorem loopResNeighborGapGroupTopShared_holds {inp : Input} {o : Options} {res : FamilyResult} (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true) (hx : ForeignBorderChainXAligned) (execution : SceneExecution inp o res) {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat} {run : Run} {orderOptions : OrderOptions} (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run) (hwit : LoopResNeighborGapGroupTopWitnessShared execution hcomp hrun) {t : Nat} {nt : Node} (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt) (htG : nt.border = -2) (het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges, e.tail = t ∧ e.head = t) {pos : Nat} {np : Node} (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np) (hgrp : np.border = -2) (hne : pos ≠ t) (hne2 : nt.decl ≠ np.decl) (hni1 : np.decl ∉ nt.clusterPath) (hni2 : nt.decl ∉ np.clusterPath) (hFL : (frameRect execution.params (componentCandidate execution.graph comp candidate) run t).x + (frameRect execution.params (componentCandidate execution.graph comp candidate) run t).w ≤ (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).x) (hShared : ∃ (a b : Nat) (na nb : ProperNode), run.proper.nodes[a]? = some na ∧ na.node.clusterPath.contains nt.decl = true ∧ run.proper.nodes[b]? = some nb ∧ nb.node.clusterPath.contains np.decl = true ∧ rk run.proper.rank a = rk run.proper.rank b) : (loopFootprint (componentCandidate execution.graph comp candidate) run execution.measured t).x + (loopFootprint (componentCandidate execution.graph comp candidate) run execution.measured t).w ≤ (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).x := by
  obtain ⟨mRt, mLp, nRt, nLp, layer, j, iv, hcoordT, hbT, hlastT, hcoordP, hbP, hlastP, hlayer, hj, hiv, hlt⟩ := hwit t nt hnt htG het pos np hnp hgrp hne hne2 hni1 hni2 hFL hShared
  have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
  obtain ⟨hproperP, _⟩ := componentRun_border_record hrun hcoordP (Or.inl hbP)
  have hconP : nLp.node.clusterPath.contains np.decl = true := List.contains_iff_mem.mpr (List.mem_of_getLast? hlastP)
  obtain ⟨mL, mR, nL, nR, _, hbL, hlastL, hpropL, _, hbR, hlastR, hpropR, hrankPair⟩ := lggt_bracket_pair execution hwf hfp hcomp hrun hproperP hconP
  have hTop := lggt_top_bound execution hwf hfp hx hcomp hrun hnt htG hcoordT hbT hlastT hcoordP hbP hlayer hj hiv hlt
  have hbne : ¬ (nLp.node.border = -2 ∨ nLp.node.border = 2) := by rw [hbP]; decide
  have hGb := lggt_no_group_at_b execution hcomp hrun hcoordP hbne
  have hframeB := lggt_frameB_x (P := default) hproperP hGb
  have hHull := lggt_hull_eq_of_left execution hcomp hrun hnp hgrp hproperP hbP hlastP halign hpropL hbL hlastL hpropR hbR hlastR hrankPair
  have hsame : (frameRect default (componentCandidate execution.graph comp candidate) run pos).x = (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).x := rfl
  omega

end PipelineImpl
end Layered
end Elegant

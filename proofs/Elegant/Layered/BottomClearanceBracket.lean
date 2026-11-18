import Elegant.Layered.BottomClearanceClosure
import Elegant.Layered.FrameClearanceBottomFacts
import Elegant.Layered.Coords

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RouteImpl

/-- `filterMap` of an `if-then-some` is `filter` then `map`. -/
theorem filterMap_ite_some {α β : Type} (l : List α) (p : α → Bool) (f : α → β) :
    l.filterMap (fun a => if p a then some (f a) else none) =
      (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filterMap_cons, List.filter_cons]
    by_cases hp : p a = true
    · simp [hp, ih]
    · simp [hp, ih]

/-- `markExtras` is the `filter`-`map` form, exposing decl injectivity. -/
theorem markExtras_eq_map (boxes : List ModelBox) :
    markExtras boxes =
      (boxes.zipIdx.filter fun q => q.1.role == .group).map fun q =>
        ({ decl := q.2, w := 0, h := 0
           clusterPath := Compound.path boxes q.1 ++ [q.2], border := 2 } : Node) := by
  unfold markExtras
  rw [filterMap_ite_some]

/-- Bottom-marker declarations in `markExtras` are pairwise distinct. -/
theorem markExtras_decl_nodup (boxes : List ModelBox) :
    ((markExtras boxes).map (·.decl)).Nodup := by
  have hmap : (markExtras boxes).map (·.decl) =
      (boxes.zipIdx.filter fun q => q.1.role == .group).map Prod.snd := by
    rw [markExtras_eq_map, List.map_map]
    apply List.map_congr_left
    intro q _
    rfl
  rw [hmap]
  have hnodup : (boxes.zipIdx.map Prod.snd).Nodup := by
    have h1 : ∀ (l : List ModelBox) (n : Nat),
        (l.zipIdx n).map Prod.snd = List.range' n l.length := by
      intro l
      induction l with
      | nil => intro n; simp
      | cons b bs ih =>
        intro n
        simp only [List.zipIdx_cons, List.map_cons]
        rw [ih (n + 1)]
        show n :: List.range' (n + 1) bs.length = List.range' n (bs.length + 1)
        rw [List.range'_succ]
    have h2 := h1 boxes 0
    rw [h2]
    exact List.nodup_range'
  exact List.Nodup.sublist (List.Sublist.map Prod.snd List.filter_sublist) hnodup
/-! ### Bottom frame clearance: candidate rank-closure hypotheses

Units C and D of the bottom-clearance development are stated here as `Prop`
hypotheses so that `componentRun_bottom_clearance` can consume them before the
sibling induction module lands.  The parent instantiates them from
`Layered/BottomClearanceNesting.lean`. -/

/-- Unit C (candidate top before bottom): for the candidate graph's rank result,
every group top marker whose paired bottom marker exists ranks strictly below
that bottom marker. -/
def CandidateTopRanksBeforeBottom {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (_hgraph : measuredGraph P inp o lines = .ok graph)
    (_hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (_hcomp : comp ∈ components graph) (candidate : Nat) : Prop :=
  ∀ rr : RankImpl.RankResult,
    rankWithBudget (Compound.rankingGraph
      (componentCandidate graph comp candidate)) = .ok rr →
    ∀ top : Node × Nat,
      top ∈ (componentCandidate graph comp candidate).nodes.zipIdx →
      top.1.border = -2 →
      ∃ bottom : Node × Nat,
        (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
          entry.1.border == 2 && entry.1.decl == top.1.decl) = some bottom ∧
        rk rr.ranks top.2 + 1 ≤ rk rr.ranks bottom.2

/-- Unit D (nested bottom before outer bottom): for the candidate graph's rank
result, whenever one candidate group top's cluster path strictly extends another
candidate group top's cluster path, the inner bottom marker ranks strictly below
the outer bottom marker. -/
def CandidateNestedBottomBeforeOuter {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (_hgraph : measuredGraph P inp o lines = .ok graph)
    (_hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (_hcomp : comp ∈ components graph) (candidate : Nat) : Prop :=
  ∀ rr : RankImpl.RankResult,
    rankWithBudget (Compound.rankingGraph
      (componentCandidate graph comp candidate)) = .ok rr →
    ∀ innerTop outerTop : Node × Nat,
      innerTop ∈ (componentCandidate graph comp candidate).nodes.zipIdx →
      innerTop.1.border = -2 →
      outerTop ∈ (componentCandidate graph comp candidate).nodes.zipIdx →
      outerTop.1.border = -2 →
      outerTop.1.clusterPath <+: innerTop.1.clusterPath →
      outerTop.1.clusterPath.length < innerTop.1.clusterPath.length →
      ∃ innerBottom outerBottom : Node × Nat,
        (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
          entry.1.border == 2 && entry.1.decl == innerTop.1.decl) = some innerBottom ∧
        (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
          entry.1.border == 2 && entry.1.decl == outerTop.1.decl) = some outerBottom ∧
        rk rr.ranks innerBottom.2 + 1 ≤ rk rr.ranks outerBottom.2

/-! ### Unit E: bracket side full-path

For a bottom proxy (`border = 2`) the executed pipeline already exposes, through
`componentRun_proxy_bottom_source`, a same-rank border side node whose full
cluster path equals the group top marker's cluster path, together with the
paired bottom marker record.  This is the bracket side full-path fact used by
the bottom clearance argument. -/

theorem bracket_side_full_path
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) {index : Nat} {proxy : ProperNode}
    (hproxy : run.coordinateProper.nodes[index]? = some proxy)
    (hborder : proxy.node.border = -2 ∨ proxy.node.border = 2) :
    ∃ (labeled : Proper) (owner sideIndex : Nat) (side : ProperNode)
      (top bottom : ProperNode × Nat),
      coordinateGraph P labeled = run.coordinateProper ∧
      proxy.node.clusterPath.getLast? = some owner ∧
      run.coordinateProper.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      rk run.coordinateProper.rank sideIndex = rk run.coordinateProper.rank index ∧
      top ∈ (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.filter
        (fun entry => entry.1.node.border == -2) ∧
      ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
      side.node.clusterPath = top.1.node.clusterPath ∧
      top.1.node.clusterPath.getLast? = some owner :=
  componentRun_proxy_bottom_source hgraph hcomp hrun hproxy hborder

/-- Unit F hypothesis (inside rank closure): for every successful component
run, no non-frame node of positive height that shares its `coordinateProper`
rank with a bottom proxy can overlap that proxy's horizontal span. Equivalently
every such node inside the span is a member of the group and ranks strictly
below the proxy (units C and D with the member/child interval lemmas).
The statement WITHOUT the same-rank premise is false: executed witness
`flowchart TD; subgraph g1; a --> m; end; g1 --> z; n0 --> n1; n1 --> z` has a
non-member node at rank 4 overlapping the bottom proxy span at rank 3. -/
def BracketInsideRankBelowBottom {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (_hgraph : measuredGraph P inp o lines = .ok graph)
    (_hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (_hcomp : comp ∈ components graph) (candidate : Nat) : Prop :=
  ∀ (run : Run) (labels : List MeasuredLabel) (orderOptions : OrderOptions),
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ t v : Nat,
      (run.coordinateProper.nodes.getD t default).dummy = false →
      (run.coordinateProper.nodes.getD t default).node.border = 2 →
      (run.coordinateProper.nodes.getD v default).node.border ≠ -2 →
      (run.coordinateProper.nodes.getD v default).node.border ≠ 2 →
      0 < RouteImpl.nodeH run.proper v →
      rk run.coordinateProper.rank v = rk run.coordinateProper.rank t →
      RouteImpl.leftOf run.proper run.xs t <
          RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ∧
        RouteImpl.leftOf run.proper run.xs v <
          RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t →
      False


/-- Bottom frame clearance for a successful component run, with the inside-span
rank closure supplied as the hypothesis `BracketInsideRankBelowBottom`.  The
two outer cases reuse `componentRun_nonproxy_ordered_intervals` through
`componentRun_proxy_border_extrema`; the inside case is discharged by
`hInside` together with same-layer rank equality. -/
theorem componentRun_bottom_clearance_of_inside
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat}
    (hInside : BracketInsideRankBelowBottom hgraph hlines hcomp candidate)
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) :
    ∀ layer ∈ run.layers, ∀ t v : Nat, t ∈ layer → v ∈ layer →
      RouteImpl.IsBottom run.proper t → v ≠ t → ¬ RouteImpl.IsFrame run.proper v →
      0 < RouteImpl.nodeH run.proper v →
      RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t ≤
          RouteImpl.leftOf run.proper run.xs v ∨
        RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤
          RouteImpl.leftOf run.proper run.xs t := by
  obtain ⟨_, _, _, routed, _, _, hcoordinate, _, hcross, hproj, hdropsyn, hroute, _⟩ :=
    componentRun_spec hrun
  obtain ⟨_, hrank, hlength, _, hrecords, _⟩ := proxyWidths_rel hproj
  have hnodes : run.proper.nodes = routed.nodes := by
    rw [← hdropsyn]
    rfl
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdropsyn]
    exact hrank
  have source : ∀ index, index < run.proper.nodes.length →
      ∃ original final : ProperNode,
        run.coordinateProper.nodes[index]? = some original ∧
        run.proper.nodes[index]? = some final ∧
        final.dummy = original.dummy ∧
        final.node.border = original.node.border ∧ final.node.h = original.node.h := by
    intro index hindex
    have hsourceIndex : index < run.coordinateProper.nodes.length := by
      rw [hnodes] at hindex
      omega
    have hsource : run.coordinateProper.nodes[index]? =
        some (run.coordinateProper.nodes[index]'hsourceIndex) :=
      List.getElem?_eq_getElem hsourceIndex
    obtain ⟨final, hfinal, hdummy, hborder, hheight⟩ := hrecords index _ hsource
    exact ⟨_, final, hsource, by rw [hnodes]; exact hfinal, hdummy, hborder, hheight⟩
  have hmembers := (RouteImpl.layersOk_spec
    (RouteImpl.routeWithLanes_geometry hroute).1).2.2.1
  have hsz : ∀ v, v < run.proper.nodes.length →
      0 ≤ RouteImpl.nodeW run.proper v ∧ 0 ≤ RouteImpl.nodeH run.proper v :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.1
  intro layer hlayer t v htmem hvmem hbottom hne hnotFrame hheight
  obtain ⟨layerIndex, hlayerIndex⟩ := List.mem_iff_getElem?.mp hlayer
  obtain ⟨htbound, htrank⟩ := hmembers layerIndex layer hlayerIndex t htmem
  obtain ⟨hvbound, hvrank⟩ := hmembers layerIndex layer hlayerIndex v hvmem
  obtain ⟨proxy, finalProxy, ht, htfinal, htdummy, htborder, _⟩ := source t htbound
  obtain ⟨other, finalOther, hv, hvfinal, hvdummy, hvborderEq, hvheight⟩ := source v hvbound
  have htcoordBound : t < run.coordinateProper.nodes.length :=
    (List.getElem?_eq_some_iff.mp ht).1
  have hvcoordBound : v < run.coordinateProper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hv).1
  have htGetD : run.coordinateProper.nodes.getD t default = proxy := by
    simp [List.getD_eq_getElem?_getD, ht]
  have hvGetD : run.coordinateProper.nodes.getD v default = other := by
    simp [List.getD_eq_getElem?_getD, hv]
  have htBorder : proxy.node.border = -2 ∨ proxy.node.border = 2 := by
    right
    rw [← htborder]
    exact ((isBottom_iff htfinal).mp hbottom).2
  have hvBorder : ¬(other.node.border = -2 ∨ other.node.border = 2) := by
    intro hborder
    have hzero := pc_frame_flat (by rw [hcoordinate]; exact hv) hborder
    have hheightValue : RouteImpl.nodeH run.proper v = finalOther.node.h := by
      simp only [RouteImpl.nodeH, hvfinal]
    rw [hheightValue, hvheight, hzero] at hheight
    omega
  -- same rank in coordinateProper
  have hvrankC : rk run.coordinateProper.rank v = rk run.coordinateProper.rank t := by
    rw [← hranks, hvrank, htrank]
  -- extrema: left/right border nodes at same rank with matching x extents
  obtain ⟨owner, leftIndex, rightIndex, left, right, ownerEq, hleft, hright,
    hleftProper, hrightProper, hleftBorder, hrightBorder, hleftOwner, hrightOwner,
    hleftRank, hrightRank, hleftEq, hrightEq⟩ :=
    componentRun_proxy_border_extrema hrun ht htBorder
  have hleftNotProxy : ¬(left.node.border = -2 ∨ left.node.border = 2) := by
    rcases hleftBorder with hb | hb <;> omega
  have hrightNotProxy : ¬(right.node.border = -2 ∨ right.node.border = 2) := by
    rcases hrightBorder with hb | hb <;> omega
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, hcross, _⟩ := componentRun_spec hrun
  have htk : rk run.coordinateProper.rank t = (layerIndex : Int) := by
    rw [← hranks]; exact htrank
  have hvt : rk run.coordinateProper.rank v = (layerIndex : Int) := by
    rw [hvrankC, htk]
  have hlayV : OrderImpl.lay run.coordinateProper v =
      OrderImpl.lay run.coordinateProper leftIndex := by
    unfold OrderImpl.lay
    rw [hvrankC, ← hleftRank]
  have hlayT : OrderImpl.lay run.coordinateProper t = layerIndex := by
    unfold OrderImpl.lay
    rw [htk]
    simp
  have hlayL : OrderImpl.lay run.coordinateProper leftIndex = layerIndex := by
    unfold OrderImpl.lay
    rw [hleftRank, htk]
    simp
  have hlayR : OrderImpl.lay run.coordinateProper rightIndex = layerIndex := by
    unfold OrderImpl.lay
    rw [hrightRank, htk]
    simp
  obtain ⟨hleftBound, hleftMemOrd⟩ :=
    ExecutedBorderOrder.node_layer _ _ ord horder hleft
  obtain ⟨hrightBound, hrightMemOrd⟩ :=
    ExecutedBorderOrder.node_layer _ _ ord horder hright
  obtain ⟨hvBound, hvMemOrd⟩ := ExecutedBorderOrder.node_layer _ _ ord horder hv
  rw [hlayV, hlayL] at hvMemOrd
  rw [hlayL] at hleftMemOrd
  rw [hlayR] at hrightMemOrd
  have hlayerEq : run.layers[layerIndex]? = some layer := hlayerIndex
  have hlayerBound : layerIndex < run.layers.length :=
    (List.getElem?_eq_some_iff.mp hlayerIndex).1
  have hlayerGet : run.layers[layerIndex]'hlayerBound = layer :=
    (List.getElem?_eq_some_iff.mp hlayerIndex).2
  have hleftIn : leftIndex ∈ run.layers[layerIndex]'hlayerBound := by
    have h1 := hleftMemOrd
    simp only [hlayers, hlayerEq, List.getD_eq_getElem?_getD,
      Option.getD_some] at h1
    rw [hlayerGet]
    exact h1
  have hrightIn : rightIndex ∈ run.layers[layerIndex]'hlayerBound := by
    have h1 := hrightMemOrd
    simp only [hlayers, hlayerEq, List.getD_eq_getElem?_getD,
      Option.getD_some] at h1
    rw [hlayerGet]
    exact h1
  have hvIn : v ∈ run.layers[layerIndex]'hlayerBound := by
    have h1 := hvMemOrd
    simp only [hlayers, hlayerEq, List.getD_eq_getElem?_getD,
      Option.getD_some] at h1
    rw [hlayerGet]
    exact h1
  have hndup : (run.layers[layerIndex]'hlayerBound).Nodup := by
    rw [hlayerGet]
    exact CoordsImpl.cluster_layer_nodup (ng := P.nodeGap) (cp := P.clusterPad)
      hcross layer hlayer
  obtain ⟨leftPos, hleftPos⟩ := List.mem_iff_getElem?.mp hleftIn
  obtain ⟨vPos, hvPos⟩ := List.mem_iff_getElem?.mp hvIn
  obtain ⟨rightPos, hrightPos⟩ := List.mem_iff_getElem?.mp hrightIn
  rw [hlayerGet] at hleftPos hvPos hrightPos
  have hndupL : layer.Nodup := by
    rw [← hlayerGet]; exact hndup
  have hlayerFor : layer ∈ run.layers := hlayer
  have hleftBoundP : leftIndex < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hleftProper).1
  have hrightBoundP : rightIndex < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hrightProper).1
  have hWv := (hsz v hvbound).1
  have hWt := (hsz t htbound).1
  have hWl := (hsz leftIndex hleftBoundP).1
  have hWr := (hsz rightIndex hrightBoundP).1
  have hHv := (hsz v hvbound).2
  have hHl := (hsz leftIndex hleftBoundP).2
  have hHr := (hsz rightIndex hrightBoundP).2
  rcases Nat.lt_trichotomy vPos leftPos with hvl | hvl | hvl
  · -- v strictly left of the left border
    have hsep := componentRun_nonproxy_ordered_intervals hgraph hcomp hrun
      hlayerFor hvl hvPos hleftPos hv hleft hvBorder hleftNotProxy
    right
    rw [hleftEq]
    exact hsep
  · -- vPos = leftPos: v = leftIndex; the rank closure still contradicts hvrankC
    have hvEq : v = leftIndex := by
      have h2 : layer[leftPos]? = some v := by
        have h3 : layer[vPos]? = some v := hvPos
        rw [hvl] at h3
        exact h3
      exact Option.some.inj (h2.symm.trans hleftPos)
    subst hvEq
    refine Classical.byContradiction fun hdisjoint => ?_
    have hspan : RouteImpl.leftOf run.proper run.xs t <
          RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ∧
        RouteImpl.leftOf run.proper run.xs v <
          RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t := by
      omega
    have htB2 : proxy.node.border = 2 := by
      rw [← htborder]; exact ((isBottom_iff htfinal).mp hbottom).2
    exact hInside run labels orderOptions hrun t v
      (by rw [htGetD]; exact htdummy.symm.trans ((isBottom_iff htfinal).mp hbottom).1)
      (by rw [htGetD]; exact htB2)
      (by rw [hvGetD]; intro h; exact hvBorder (Or.inl h))
      (by rw [hvGetD]; intro h; exact hvBorder (Or.inr h))
      hheight hvrankC hspan
  · rcases Nat.lt_trichotomy vPos rightPos with hvr | hvr | hvr
    · -- strictly inside the bracket: rank closure contradicts same-layer rank
      refine Classical.byContradiction fun hdisjoint => ?_
      have hspan : RouteImpl.leftOf run.proper run.xs t <
            RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ∧
          RouteImpl.leftOf run.proper run.xs v <
            RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t := by
        omega
      have htB2 : proxy.node.border = 2 := by
        rw [← htborder]; exact ((isBottom_iff htfinal).mp hbottom).2
      exact hInside run labels orderOptions hrun t v
        (by rw [htGetD]; exact htdummy.symm.trans ((isBottom_iff htfinal).mp hbottom).1)
        (by rw [htGetD]; exact htB2)
        (by rw [hvGetD]; intro h; exact hvBorder (Or.inl h))
        (by rw [hvGetD]; intro h; exact hvBorder (Or.inr h))
        hheight hvrankC hspan
    · -- vPos = rightPos: v = rightIndex; the rank closure still contradicts hvrankC
      have hvEq : v = rightIndex := by
        have h2 : layer[rightPos]? = some v := by
          have h3 : layer[vPos]? = some v := hvPos
          rw [hvr] at h3
          exact h3
        exact Option.some.inj (h2.symm.trans hrightPos)
      subst hvEq
      refine Classical.byContradiction fun hdisjoint => ?_
      have hspan : RouteImpl.leftOf run.proper run.xs t <
            RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ∧
          RouteImpl.leftOf run.proper run.xs v <
            RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t := by
        omega
      have htB2 : proxy.node.border = 2 := by
        rw [← htborder]; exact ((isBottom_iff htfinal).mp hbottom).2
      exact hInside run labels orderOptions hrun t v
        (by rw [htGetD]; exact htdummy.symm.trans ((isBottom_iff htfinal).mp hbottom).1)
        (by rw [htGetD]; exact htB2)
        (by rw [hvGetD]; intro h; exact hvBorder (Or.inl h))
        (by rw [hvGetD]; intro h; exact hvBorder (Or.inr h))
        hheight hvrankC hspan
    · -- v strictly right of the right border
      have hsep := componentRun_nonproxy_ordered_intervals hgraph hcomp hrun
        hlayerFor hvr hrightPos hvPos hright hv hrightNotProxy hvBorder
      left
      rw [hrightEq]
      exact hsep

/-- Bottom frame clearance for a successful component run, consuming the
inside-span rank closure `BracketInsideRankBelowBottom` (discharged from units
C and D by the parent). -/
theorem componentRun_bottom_clearance
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat}
    (hInside : BracketInsideRankBelowBottom hgraph hlines hcomp candidate)
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) :
    ∀ layer ∈ run.layers, ∀ t v : Nat, t ∈ layer → v ∈ layer →
      RouteImpl.IsBottom run.proper t → v ≠ t → ¬ RouteImpl.IsFrame run.proper v →
      0 < RouteImpl.nodeH run.proper v →
      RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t ≤
          RouteImpl.leftOf run.proper run.xs v ∨
        RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤
          RouteImpl.leftOf run.proper run.xs t :=
  componentRun_bottom_clearance_of_inside hgraph hlines hcomp hInside hrun

/-- Full frame clearance for a successful component run: the top conjunct from
`componentRun_top_clearance` and the bottom conjunct from
`componentRun_bottom_clearance_of_inside`. -/
theorem componentRun_frame_clearance
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat}
    (hInside : BracketInsideRankBelowBottom hgraph hlines hcomp candidate)
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) :
    FrameClearance run.proper run.layers run.xs :=
  ⟨componentRun_top_clearance hgraph hcomp hrun,
   componentRun_bottom_clearance_of_inside hgraph hlines hcomp hInside hrun⟩

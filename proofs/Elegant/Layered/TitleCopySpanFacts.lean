import Elegant.Layered.Pipeline
import Elegant.Layered.Coords
import Elegant.Layered.Route
import Elegant.Layered.Rank
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.BottomClearanceInside

/-!
# Title-copy strictness facts (TitleCopyStrictness lane)

Verified semantics (from source, not assumption):

* `RouteImpl.nodeW run.proper v = record.w` and
  `CoordsImpl.nodeW run.coordinateProper v = record.w + 2 * record.loopExtent`
  (`Coords.lean:38`, derived identically at `BottomClearanceInside.lean:439-443`).
* Route and coordinate node positions coincide for every non-proxy node
  (`componentRun_nonproxy_record`) and for every side border
  (`componentRun_border_record`); proxies are the only exception.
* `titleReservations` (`Pipeline.lean:314`) zeroes proxy `w`/`h`, gives every
  copy `border := 3` and `loopExtent := 0` plus the anchor's record width, and
  appends `rank := p.rank ++ titles.map (rk p.rank ·.2)`: a copy's rank entry
  IS its anchor's rank (`titleReservations_copy_facts` below).
* `clusterGap ng cp p a b = if borderMember .. then cp else if ownTitleAnchor ..
  then 0 else ng` (`Coords.lean:3502`); `coordSep` floors coordinate half-widths;
  `cluster_zero_pairs_separated` and `cluster_balance_separated` bound center
  distances on `run.coordinateProper` / `run.coordinateXs`.

Consequences for the sibling's touching obstruction:

* The route-space touch `right(v) = left(t)` translates, through the shared xs,
  into a coordinate distance of exactly `⌈Wᵥ/2⌉ + ⌊W_B/2⌋` against the bracket
  border `B`.  The zero-pairs filter alone forces
  `loopExtent(v) + loopExtent(B) ≤ Wᵥ % 2`, so it is met only by odd-width
  loop-free nodes -- and title copies are exactly such nodes (`loopExtent := 0`,
  inherited anchor width).  The gap term is the discriminator: adding the
  adjacent-pair balance forces `loopExtent(v) + loopExtent(B) + clusterGap + 2*⌊W_u₁/2⌋ ≤ Wᵥ % 2 ≤ 1`.
* With `nodeGap ≥ 2` a surviving gap is `clusterPad = 1` under `borderMember`
  (membership) or `0` under `ownTitleAnchor` (equal cluster paths).  The gap-zero
  chain forces equal paths (`chainPath_of_ownTitleAnchors`), so a positive
  interior overlap (`k ≥ 1` against `right(t)`) is impossible once the same-rank
  premise kills the own-group chain through the copy-rank fact.
* What remains OPEN is the strict seam `titleCopySpanClearStrict`
  (`BottomClearanceInside.lean`), which `BracketInsidePremises` consumes.
  Intended proof: exterior layer positions are separated by
  `componentRun_nonproxy_ordered_intervals`; an interior position forces the
  copy's cluster path to extend the proxy's through `insidePrefixHypothesis`,
  which the named rank residual `TitleCopyNestedRank` (statement below)
  contradicts against the shared rank; the parity lemmas of this file cover the
  touching boundary cases.  `TitleCopyNestedRank` needs the copy-rank fact plus
  the nesting rank induction.
-/

namespace Elegant.Layered.PipelineImpl

/-- An element at `l₂[j]?` sits at `l₁.length + j` of the concatenation. -/
private theorem append_get {α : Type} (l₂ : List α) (j : Nat) (a : α)
    (hj : l₂[j]? = some a) : ∀ l₁ : List α, (l₁ ++ l₂)[l₁.length + j]? = some a := by
  intro l₁
  induction l₁ with
  | nil => simpa using hj
  | cons b bs ih =>
    rw [List.cons_append, List.length_cons]
    have hidx : bs.length + 1 + j = bs.length + j + 1 := by omega
    rw [hidx, List.getElem?_cons_succ]
    exact ih

/-- Source-level copy facts: the appended title copy has `border := 3`,
`loopExtent := 0`, the anchor's record, and its rank entry is the anchor's
rank entry. -/
theorem titleReservations_copy_facts {p : Proper} {j i : Nat} {nd : ProperNode}
    (hlen : p.rank.length = p.nodes.length)
    (hj : (p.nodes.zipIdx.filter (fun q => q.1.node.border == -2))[j]? = some (nd, i)) :
    (titleReservations p).nodes[p.nodes.length + j]? =
        some { nd with node := { nd.node with border := 3, loopExtent := 0 } } ∧
      (titleReservations p).rank[p.nodes.length + j]? = some (rk p.rank i) := by
  have hflt := hj
  constructor
  · have elen : (p.nodes.map (fun node =>
        if node.node.border == -2 || node.node.border == 2 then
          { node with node := { node.node with w := 0, h := 0 } } else node)).length =
      p.nodes.length := by simp
    have hres : (p.nodes.map (fun node =>
        if node.node.border == -2 || node.node.border == 2 then
          { node with node := { node.node with w := 0, h := 0 } } else node) ++
        (p.nodes.zipIdx.filter (fun q => q.1.node.border == -2)).map
          (fun q => { q.1 with node := { q.1.node with border := 3, loopExtent := 0 } })) =
      (titleReservations p).nodes := by simp only [titleReservations]
    rw [← hres, ← elen]
    exact append_get
      ((p.nodes.zipIdx.filter (fun q => q.1.node.border == -2)).map
        (fun q => { q.1 with node := { q.1.node with border := 3, loopExtent := 0 } }))
      j { nd with node := { nd.node with border := 3, loopExtent := 0 } } (by
        rw [List.getElem?_map, hflt]
        simp) (p.nodes.map (fun node =>
          if node.node.border == -2 || node.node.border == 2 then
            { node with node := { node.node with w := 0, h := 0 } } else node))
  · rw [← hlen]
    have hres : (p.rank ++
        (p.nodes.zipIdx.filter (fun q => q.1.node.border == -2)).map
          (fun q => rk p.rank q.2)) =
      (titleReservations p).rank := by simp only [titleReservations]
    rw [← hres]
    exact append_get
      ((p.nodes.zipIdx.filter (fun q => q.1.node.border == -2)).map
        (fun q => rk p.rank q.2)) j (rk p.rank i) (by
        rw [List.getElem?_map, hflt]
        simp) p.rank

/-- Equal-path transport along a gap-zero chain: consecutive `ownTitleAnchor`
pairs in a layer force the endpoints' cluster paths to agree. -/
theorem chainPath_of_ownTitleAnchors {p : Proper} {layer : List Nat}
    (hstep : ∀ i a b : Nat, layer[i]? = some a → layer[i + 1]? = some b →
      CoordsImpl.ownTitleAnchor p a b = true) :
    ∀ d s t s' t' : Nat, s + d = t → layer[s]? = some s' → layer[t]? = some t' →
      (p.nodes.getD s' default).node.clusterPath =
        (p.nodes.getD t' default).node.clusterPath := by
  intro d
  induction d with
  | zero =>
    intro s t s' t' heq hsx hst
    have hx : s' = t' := by
      rw [Nat.add_zero] at heq
      rw [heq] at hsx
      exact Option.some.inj (hsx.symm.trans hst)
    subst hx
    simp
  | succ d ih =>
    intro s t s' t' heq hsx hst
    cases hx1 : layer[s + 1]? with
    | none =>
      have hl1 := List.getElem?_eq_none_iff.mp hx1
      have hlt := (List.getElem?_eq_some_iff.mp hst).1
      omega
    | some u =>
      have hpath : (p.nodes.getD s' default).node.clusterPath =
          (p.nodes.getD u default).node.clusterPath := by
        have h := hstep s s' u hsx hx1
        unfold CoordsImpl.ownTitleAnchor at h
        cases pna : p.nodes[s']? with
        | none => rw [pna] at h; simp at h
        | some na =>
          cases pnb : p.nodes[u]? with
          | none => rw [pnb] at h; simp at h
          | some nb =>
            rw [pna, pnb] at h
            simp only [Bool.and_eq_true] at h
            have hEq := h.1.2
            simp at hEq
            simp only [List.getD_eq_getElem?_getD, pna, pnb, Option.getD_some]
            exact hEq
      have hidx : s + 1 + d = t := by omega
      exact hpath.trans (ih (s + 1) t u t' hidx hx1 hst)

/-- Left outside-touch parity core.  If a border-`3` node `v` lies before the
left border of `t`'s bracket in the shared layer and closed-overlaps `t`'s
span, then the touch `right(v) = left(t)` forces, through zero-pairs plus the
adjacent-pair balance,
`loopExtent(v) + loopExtent(left) + clusterGap(v, u₁) + 2*⌊W(u₁)/2⌋ ≤ W(v) % 2`.
Every term on the left is nonnegative and the right side is at most `1`. -/
theorem componentRun_titleCopy_leftTouch_parity
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    (hcross : CoordsImpl.crossCoordsClusterWith P.nodeGap P.clusterPad
      run.coordinateProper run.layers = .ok run.coordinateXs)
    {layer : List Nat} (hlayerMem : layer ∈ run.layers)
    {t v leftIndex u1 vPos leftPos : Nat}
    {tNode vNode left : ProperNode}
    (_ht' : run.coordinateProper.nodes[t]? = some tNode)
    (_ht2 : tNode.node.border = 2)
    (hvPos : layer[vPos]? = some v)
    (hlPos : layer[leftPos]? = some leftIndex)
    (hlt : vPos < leftPos)
    (hu1 : layer[vPos + 1]? = some u1)
    (hu1lt : vPos + 1 < leftPos)
    (hv' : run.coordinateProper.nodes[v]? = some vNode)
    (hv3 : vNode.node.border = 3)
    (hleft : run.coordinateProper.nodes[leftIndex]? = some left)
    (hleftBorder : left.node.border = -1 ∨ left.node.border = 1)
    (hleftEq : RouteImpl.leftOf run.proper run.xs t =
      RouteImpl.leftOf run.proper run.xs leftIndex)
    (hoverlap1 : RouteImpl.leftOf run.proper run.xs t ≤
      RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v) :
    (vNode.node.loopExtent : Int) + (left.node.loopExtent : Int) +
        CoordsImpl.clusterGap P.nodeGap P.clusterPad run.coordinateProper v u1 +
        2 * (CoordsImpl.nodeW run.coordinateProper u1 / 2) ≤
      RouteImpl.nodeW run.proper v % 2 := by
  have hvNotProxy : ¬(vNode.node.border = -2 ∨ vNode.node.border = 2) := by
    intro h
    rcases h with h | h <;> omega
  have hleftNotProxy : ¬(left.node.border = -2 ∨ left.node.border = 2) := by
    intro h
    rcases hleftBorder with h | h <;> omega
  have hsep := componentRun_nonproxy_ordered_intervals hgraph hcomp hrun
    hlayerMem hlt hvPos hlPos hv' hleft hvNotProxy hleftNotProxy
  have htouchL : RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v =
      RouteImpl.leftOf run.proper run.xs leftIndex := by omega
  obtain ⟨_, hvx⟩ := componentRun_nonproxy_record hrun hv' hvNotProxy
  obtain ⟨_, hleftX⟩ := componentRun_border_record hrun hleft hleftBorder
  have hwv : RouteImpl.nodeW run.proper v = vNode.node.w := by
    simp only [RouteImpl.nodeW]
    rw [show run.proper.nodes[v]? = some vNode from
      (componentRun_nonproxy_record hrun hv' hvNotProxy).1]
  have hcwv : CoordsImpl.nodeW run.coordinateProper v =
      RouteImpl.nodeW run.proper v + 2 * (vNode.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, hv']
    rw [hwv]
  have hwl : RouteImpl.nodeW run.proper leftIndex = left.node.w := by
    simp only [RouteImpl.nodeW]
    rw [show run.proper.nodes[leftIndex]? = some left from
      (componentRun_border_record hrun hleft hleftBorder).1]
  have hcwl : CoordsImpl.nodeW run.coordinateProper leftIndex =
      RouteImpl.nodeW run.proper leftIndex + 2 * (left.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, hleft]
    rw [hwl]
  have e : ∀ w : Int, Int.fdiv w 2 = w / 2 :=
    fun w => Int.fdiv_eq_ediv_of_nonneg w (by decide)
  have hdist : run.coordinateXs.getD leftIndex 0 - run.coordinateXs.getD v 0 =
      RouteImpl.nodeW run.proper v - RouteImpl.nodeW run.proper v / 2 +
        RouteImpl.nodeW run.proper leftIndex / 2 := by
    simp only [RouteImpl.leftOf, RouteImpl.xAt, e] at htouchL
    rw [hvx, hleftX] at htouchL
    omega
  obtain ⟨_, _, _, hsizes, _⟩ := CoordsImpl.crossCoordsClusterWith_spec hcross
  have hcw0 : 0 ≤ CoordsImpl.nodeW run.coordinateProper v :=
    CoordsImpl.nodeW_nonneg hsizes v
  have hcw1 : 0 ≤ CoordsImpl.nodeW run.coordinateProper leftIndex :=
    CoordsImpl.nodeW_nonneg hsizes leftIndex
  have hcwu : 0 ≤ CoordsImpl.nodeW run.coordinateProper u1 :=
    CoordsImpl.nodeW_nonneg hsizes u1
  have hzp := CoordsImpl.cluster_zero_pairs_separated hcross layer hlayerMem
    vPos leftPos v leftIndex hlt hvPos hlPos
  have hbal := CoordsImpl.cluster_balance_separated hcross layer hlayerMem vPos v
    u1 hvPos hu1
  have hzp1 := CoordsImpl.cluster_zero_pairs_separated hcross layer hlayerMem
    (vPos + 1) leftPos u1 leftIndex hu1lt hu1 hlPos
  simp only [CoordsImpl.clusterSep, CoordsImpl.coordSep, e] at hbal
  simp only [e] at hzp hzp1
  have hcwv2 : CoordsImpl.nodeW run.coordinateProper v / 2 =
      RouteImpl.nodeW run.proper v / 2 + (vNode.node.loopExtent : Int) := by
    rw [hcwv]
    omega
  have hcwl2 : CoordsImpl.nodeW run.coordinateProper leftIndex / 2 =
      RouteImpl.nodeW run.proper leftIndex / 2 + (left.node.loopExtent : Int) := by
    rw [hcwl]
    omega
  omega

/-- Adjacent outside-touch parity core: `v` directly precedes the left border
in the shared layer.  The touch plus the balance of that single pair forces
`loopExtent(v) + loopExtent(left) + clusterGap(v, left) ≤ W(v) % 2`. -/
theorem componentRun_titleCopy_adjacentTouch_parity
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    (hcross : CoordsImpl.crossCoordsClusterWith P.nodeGap P.clusterPad
      run.coordinateProper run.layers = .ok run.coordinateXs)
    {layer : List Nat} (hlayerMem : layer ∈ run.layers)
    {t v leftIndex vPos leftPos : Nat}
    {tNode vNode left : ProperNode}
    (_ht' : run.coordinateProper.nodes[t]? = some tNode)
    (_ht2 : tNode.node.border = 2)
    (_hvPos : layer[vPos]? = some v)
    (_hlPos : layer[leftPos]? = some leftIndex)
    (hlt : vPos < leftPos)
    (hnext : vPos + 1 = leftPos)
    (hv' : run.coordinateProper.nodes[v]? = some vNode)
    (hv3 : vNode.node.border = 3)
    (hleft : run.coordinateProper.nodes[leftIndex]? = some left)
    (hleftBorder : left.node.border = -1 ∨ left.node.border = 1)
    (hleftEq : RouteImpl.leftOf run.proper run.xs t =
      RouteImpl.leftOf run.proper run.xs leftIndex)
    (hoverlap1 : RouteImpl.leftOf run.proper run.xs t ≤
      RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v) :
    (vNode.node.loopExtent : Int) + (left.node.loopExtent : Int) +
        CoordsImpl.clusterGap P.nodeGap P.clusterPad run.coordinateProper v
          leftIndex ≤
      RouteImpl.nodeW run.proper v % 2 := by
  have hvNotProxy : ¬(vNode.node.border = -2 ∨ vNode.node.border = 2) := by
    intro h
    rcases h with h | h <;> omega
  have hleftNotProxy : ¬(left.node.border = -2 ∨ left.node.border = 2) := by
    intro h
    rcases hleftBorder with h | h <;> omega
  have hsep := componentRun_nonproxy_ordered_intervals hgraph hcomp hrun
    hlayerMem hlt _hvPos _hlPos hv' hleft hvNotProxy hleftNotProxy
  have htouchL : RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v =
      RouteImpl.leftOf run.proper run.xs leftIndex := by omega
  obtain ⟨_, hvx⟩ := componentRun_nonproxy_record hrun hv' hvNotProxy
  obtain ⟨_, hleftX⟩ := componentRun_border_record hrun hleft hleftBorder
  have hwv : RouteImpl.nodeW run.proper v = vNode.node.w := by
    simp only [RouteImpl.nodeW]
    rw [show run.proper.nodes[v]? = some vNode from
      (componentRun_nonproxy_record hrun hv' hvNotProxy).1]
  have hcwv : CoordsImpl.nodeW run.coordinateProper v =
      RouteImpl.nodeW run.proper v + 2 * (vNode.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, hv']
    rw [hwv]
  have hwl : RouteImpl.nodeW run.proper leftIndex = left.node.w := by
    simp only [RouteImpl.nodeW]
    rw [show run.proper.nodes[leftIndex]? = some left from
      (componentRun_border_record hrun hleft hleftBorder).1]
  have hcwl : CoordsImpl.nodeW run.coordinateProper leftIndex =
      RouteImpl.nodeW run.proper leftIndex + 2 * (left.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, hleft]
    rw [hwl]
  have e : ∀ w : Int, Int.fdiv w 2 = w / 2 :=
    fun w => Int.fdiv_eq_ediv_of_nonneg w (by decide)
  have hdist : run.coordinateXs.getD leftIndex 0 - run.coordinateXs.getD v 0 =
      RouteImpl.nodeW run.proper v - RouteImpl.nodeW run.proper v / 2 +
        RouteImpl.nodeW run.proper leftIndex / 2 := by
    simp only [RouteImpl.leftOf, RouteImpl.xAt, e] at htouchL
    rw [hvx, hleftX] at htouchL
    omega
  obtain ⟨_, _, _, hsizes, _⟩ := CoordsImpl.crossCoordsClusterWith_spec hcross
  have hcw0 : 0 ≤ CoordsImpl.nodeW run.coordinateProper v :=
    CoordsImpl.nodeW_nonneg hsizes v
  have hcw1 : 0 ≤ CoordsImpl.nodeW run.coordinateProper leftIndex :=
    CoordsImpl.nodeW_nonneg hsizes leftIndex
  have hbal := CoordsImpl.cluster_balance_separated hcross layer hlayerMem vPos v
    leftIndex _hvPos (by rw [hnext]; exact _hlPos)
  simp only [CoordsImpl.clusterSep, CoordsImpl.coordSep, e] at hbal
  have hcwv2 : CoordsImpl.nodeW run.coordinateProper v / 2 =
      RouteImpl.nodeW run.proper v / 2 + (vNode.node.loopExtent : Int) := by
    rw [hcwv]
    omega
  have hcwl2 : CoordsImpl.nodeW run.coordinateProper leftIndex / 2 =
      RouteImpl.nodeW run.proper leftIndex / 2 + (left.node.loopExtent : Int) := by
    rw [hcwl]
    omega
  omega

/-- Right outside-touch parity core.  Mirror of
`componentRun_titleCopy_leftTouch_parity` at the right border: the touch
`left(v) = right(t)` forces
`loopExtent(v) + loopExtent(right) ≤ W(right) % 2`. -/
theorem componentRun_titleCopy_rightTouch_parity
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    (hcross : CoordsImpl.crossCoordsClusterWith P.nodeGap P.clusterPad
      run.coordinateProper run.layers = .ok run.coordinateXs)
    {layer : List Nat} (hlayerMem : layer ∈ run.layers)
    {t v rightIndex rightPos vPos : Nat}
    {tNode vNode right : ProperNode}
    (_ht' : run.coordinateProper.nodes[t]? = some tNode)
    (_ht2 : tNode.node.border = 2)
    (hvPos : layer[vPos]? = some v)
    (hrPos : layer[rightPos]? = some rightIndex)
    (hrvt : rightPos < vPos)
    (hv' : run.coordinateProper.nodes[v]? = some vNode)
    (hv3 : vNode.node.border = 3)
    (hright : run.coordinateProper.nodes[rightIndex]? = some right)
    (hrightBorder : right.node.border = -1 ∨ right.node.border = 1)
    (hrightEq : RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t =
      RouteImpl.leftOf run.proper run.xs rightIndex +
        RouteImpl.nodeW run.proper rightIndex)
    (hoverlap2 : RouteImpl.leftOf run.proper run.xs v ≤
      RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t)
    (_hAv0 : 0 ≤ RouteImpl.nodeW run.proper v)
    (_hAr0 : 0 ≤ RouteImpl.nodeW run.proper rightIndex) :
    (vNode.node.loopExtent : Int) + (right.node.loopExtent : Int) ≤
      RouteImpl.nodeW run.proper rightIndex % 2 := by
  have hvNotProxy : ¬(vNode.node.border = -2 ∨ vNode.node.border = 2) := by
    intro h
    rcases h with h | h <;> omega
  have hrightNotProxy : ¬(right.node.border = -2 ∨ right.node.border = 2) := by
    intro h
    rcases hrightBorder with h | h <;> omega
  have hsep := componentRun_nonproxy_ordered_intervals hgraph hcomp hrun
    hlayerMem hrvt hrPos hvPos hright hv' hrightNotProxy hvNotProxy
  have htouchR : RouteImpl.leftOf run.proper run.xs v =
      RouteImpl.leftOf run.proper run.xs rightIndex +
        RouteImpl.nodeW run.proper rightIndex := by omega
  obtain ⟨_, hvx⟩ := componentRun_nonproxy_record hrun hv' hvNotProxy
  obtain ⟨_, hrightX⟩ := componentRun_border_record hrun hright hrightBorder
  have hwv : RouteImpl.nodeW run.proper v = vNode.node.w := by
    simp only [RouteImpl.nodeW]
    rw [show run.proper.nodes[v]? = some vNode from
      (componentRun_nonproxy_record hrun hv' hvNotProxy).1]
  have hcwv : CoordsImpl.nodeW run.coordinateProper v =
      RouteImpl.nodeW run.proper v + 2 * (vNode.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, hv']
    rw [hwv]
  have hwr : RouteImpl.nodeW run.proper rightIndex = right.node.w := by
    simp only [RouteImpl.nodeW]
    rw [show run.proper.nodes[rightIndex]? = some right from
      (componentRun_border_record hrun hright hrightBorder).1]
  have hcwr : CoordsImpl.nodeW run.coordinateProper rightIndex =
      RouteImpl.nodeW run.proper rightIndex + 2 * (right.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, hright]
    rw [hwr]
  have e : ∀ w : Int, Int.fdiv w 2 = w / 2 :=
    fun w => Int.fdiv_eq_ediv_of_nonneg w (by decide)
  have hdist : run.coordinateXs.getD v 0 - run.coordinateXs.getD rightIndex 0 =
      RouteImpl.nodeW run.proper v / 2 +
        (RouteImpl.nodeW run.proper rightIndex -
          RouteImpl.nodeW run.proper rightIndex / 2) := by
    simp only [RouteImpl.leftOf, RouteImpl.xAt, e] at htouchR
    rw [hvx, hrightX] at htouchR
    omega
  obtain ⟨_, _, _, hsizes, _⟩ := CoordsImpl.crossCoordsClusterWith_spec hcross
  have hcw0 : 0 ≤ CoordsImpl.nodeW run.coordinateProper v :=
    CoordsImpl.nodeW_nonneg hsizes v
  have hcwr0 : 0 ≤ CoordsImpl.nodeW run.coordinateProper rightIndex :=
    CoordsImpl.nodeW_nonneg hsizes rightIndex
  have hzp := CoordsImpl.cluster_zero_pairs_separated hcross layer hlayerMem
    rightPos vPos rightIndex v hrvt hrPos hvPos
  simp only [e] at hzp
  have hcwv2 : CoordsImpl.nodeW run.coordinateProper v / 2 =
      RouteImpl.nodeW run.proper v / 2 + (vNode.node.loopExtent : Int) := by
    rw [hcwv]
    omega
  have hcwr2 : CoordsImpl.nodeW run.coordinateProper rightIndex / 2 =
      RouteImpl.nodeW run.proper rightIndex / 2 + (right.node.loopExtent : Int) := by
    rw [hcwr]
    omega
  omega

/-- Residual obligation (statement, deliberately unproved here).  A border-`3`
title copy whose cluster path is the bottom proxy's path or has it as a prefix
(the two shapes produced by the gap-zero chain of
`chainPath_of_ownTitleAnchors` and by the bracket-prefix seam) cannot share the
proxy's rank.  Proof route: the copy's rank entry is its anchor's rank
(`titleReservations_copy_facts` propagated through the executed record
pipeline), `componentRun_group_top_lt_bottom` lifts the anchor strictly below
the group's own bottom proxy, and
`componentRun_nested_bottom_lt_outer_bottom` iterated along the path gives the
nested case. -/
def TitleCopyNestedRank (P : Params) (graph : Graph) : Prop :=
  ∀ comp : List Nat, comp ∈ components graph → ∀ candidate : Nat,
    ∀ run : Run, ∀ labels : List MeasuredLabel, ∀ orderOptions : OrderOptions,
      componentRun P (componentCandidate graph comp candidate) labels orderOptions =
        .ok run →
    ∀ t v : Nat,
      (run.coordinateProper.nodes.getD t default).dummy = false →
      (run.coordinateProper.nodes.getD t default).node.border = 2 →
      (run.coordinateProper.nodes.getD v default).node.border = 3 →
      ((run.coordinateProper.nodes.getD v default).node.clusterPath =
          (run.coordinateProper.nodes.getD t default).node.clusterPath ∨
        (run.coordinateProper.nodes.getD t default).node.clusterPath <+:
          (run.coordinateProper.nodes.getD v default).node.clusterPath) →
      rk run.coordinateProper.rank v ≠ rk run.coordinateProper.rank t

end Elegant.Layered.PipelineImpl

import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Order
import Elegant.Layered.BorderChainUps

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Foreign cluster facts: the border-span seam residuals.

This module discharges the open seam `ForeignBorderSpansSeparated`
(`Elegant/Layered/ForeignSpansFacts.lean`) in three phase-ordered pieces:

* `foreignBorderLayerOrder` (order phase, proved outright modulo one
  construction input): on each layer, the border markers of two unrelated
  group declarations form disjoint blocks.
* `ForeignBorderSideUps` (alignment-phase residual): the executed
  Brandes-Köpf `up` behaviour on each declaration side-chain.
* `ForeignRankPairAnchors` (rank-phase residual): the title-level anchor
  lookups backing the per-rank marker pairs.

The order proof composes the already-proved cluster contiguity
(`OrderImpl.order_clusters_contiguous`), the non-dummy border node paths
(`OrderImpl.border_node` over `componentRun_coordinate_bordersWellFormed`),
and three pure list facts proved below (`prefix_last_mem_contains`,
`prefix_total`, `infix_disjoint_ordered`).
-/

/-- Order-input residual: every side marker of an executed run carries the
cluster path of its own title, and each title path ends in its own
declaration.  This is the executed `addClusterBorders` anchor content: the
fold copies the anchor (`border = -2`) path onto each emitted side marker,
and `markNodes` closes every title path with its own index, which the
group-anchor selection keeps as the declaration.  The statement is about
paths only (no layers or positions); it is pinned to the same three
execution equations as the goal. -/
def ForeignBorderAnchorPaths : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border = -2 → uNode.decl ≠ wNode.decl →
    (uNode.clusterPath.getLast? = some uNode.decl) ∧
    (wNode.clusterPath.getLast? = some wNode.decl) ∧
    ∀ {a : Nat} {na : ProperNode},
    run.coordinateProper.nodes[a]? = some na →
    (na.node.border = -1 ∨ na.node.border = 1) →
    (na.node.clusterPath.getLast? = some uNode.decl →
      na.node.clusterPath = uNode.clusterPath) ∧
    (na.node.clusterPath.getLast? = some wNode.decl →
      na.node.clusterPath = wNode.clusterPath)

/-- Alignment-phase residual: for every declaration, side, pass, and checked
layer table, the side markers form one chain carrying the executed `up`
behaviour.  The chain is identified by border, width, and owner
(`borderChainBlock_of_ups` reduces the block to exactly this `BorderChainUps`
hypothesis); the statement is about alignment pointers only, pinned to the
same three execution equations. -/
def ForeignBorderSideUps : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl : Nat} {side : Int}, side = -1 ∨ side = 1 →
    ∀ {k : Nat}, k < 4 →
    ∀ {pos : Array Nat},
    CoordsImpl.checkLayers
      (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers = .ok pos →
    ∃ chain ordered : List Nat,
      (∀ a, a ∈ chain ↔ ∃ na, run.coordinateProper.nodes[a]? = some na ∧
        na.node.border = side ∧ na.node.w = P.clusterBorderW ∧
        na.node.clusterPath.getLast? = some decl) ∧
      ∀ (hL : CoordsImpl.Lay (CoordsImpl.clusterCtx P.nodeGap P.clusterPad
        (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
        (CoordsImpl.typeOneConflicts
          (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos) k)),
      Elegant.Layered.BorderChainUps P.nodeGap P.clusterPad (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
        (CoordsImpl.typeOneConflicts
          (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos)
        k chain ordered hL

/-- Rank-phase residual: for two executed group declarations, the titled
proper graph carries a top anchor and a path-matched bottom anchor per
declaration.  The coordinate equation and the length alignment pin the same
labeled source (both are proved facts, bundled so the anchors refer to one
source); the open content is the anchor lookups, which is what
`coordinateGraph_rank_pair` consumes. -/
def ForeignRankPairAnchors : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border = -2 → uNode.decl ≠ wNode.decl →
    ∃ (labeled : Proper),
      coordinateGraph P labeled = run.coordinateProper ∧
      (titleReservations (sizeProperPorts P labeled)).nodes.length =
        (titleReservations (sizeProperPorts P labeled)).rank.length ∧
      ∃ (topU botU : ProperNode × Nat),
        topU ∈ (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx ∧
        topU.1.node.border = -2 ∧
        topU.1.node.clusterPath.getLast? = some uNode.decl ∧
        ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find? (fun entry =>
          entry.1.node.border == 2 &&
            entry.1.node.clusterPath == topU.1.node.clusterPath) = some botU) ∧
      ∃ (topW botW : ProperNode × Nat),
        topW ∈ (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx ∧
        topW.1.node.border = -2 ∧
        topW.1.node.clusterPath.getLast? = some wNode.decl ∧
        ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find? (fun entry =>
          entry.1.node.border == 2 &&
            entry.1.node.clusterPath == topW.1.node.clusterPath) = some botW)

/-! ## Pure list facts behind the layer order -/

/-- A prefix ending in `d` forces `d` into any list it prefixes. -/
theorem prefix_last_mem_contains {pref l : List Nat} {d : Nat}
    (hpre : pref.isPrefixOf l = true) (hlast : pref.getLast? = some d) :
    l.contains d = true := by
  apply List.contains_iff_mem.mpr
  have hmem : d ∈ pref := List.mem_of_getLast? hlast
  have hprefix : pref <+: l := List.isPrefixOf_iff_prefix.mp hpre
  obtain ⟨t, rfl⟩ := hprefix
  exact List.mem_append.mpr (Or.inl hmem)

/-- Prefixes of one list are comparable. -/
theorem prefix_total {p1 p2 l : List Nat}
    (h1 : p1 <+: l) (h2 : p2 <+: l) : p1 <+: p2 ∨ p2 <+: p1 := by
  revert p2 l h1 h2
  induction p1 with
  | nil =>
    intro p2 l h1 h2
    exact Or.inl List.nil_prefix
  | cons x xs ih =>
    intro p2 l h1 h2
    cases p2 with
    | nil => exact Or.inr List.nil_prefix
    | cons y ys =>
      cases l with
      | nil =>
        obtain ⟨t, ht⟩ := h1
        have hlen := congrArg List.length ht
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
      | cons z zs =>
        obtain ⟨t1, ht1⟩ := h1
        obtain ⟨t2, ht2⟩ := h2
        simp only [List.cons_append, List.cons.injEq] at ht1 ht2
        obtain ⟨hxz, hxs⟩ := ht1
        obtain ⟨hyz, hys⟩ := ht2
        have h1' : xs <+: zs := ⟨t1, hxs⟩
        have h2' : ys <+: zs := ⟨t2, hys⟩
        rcases ih (p2 := ys) (l := zs) (h1 := h1') (h2 := h2') with h | h
        · obtain ⟨t, ht⟩ := h
          have hyx : y = x := hyz.trans hxz.symm
          exact Or.inl ⟨t, by rw [List.cons_append, ht, hyx]⟩
        · obtain ⟨t, ht⟩ := h
          have hxy : x = y := hxz.trans hyz.symm
          exact Or.inr ⟨t, by rw [List.cons_append, ht, hxy]⟩

/-- Two disjoint infixes of a nodup list are ordered one way or the other. -/
theorem infix_disjoint_ordered {BU BW layer : List Nat}
    (hnd : layer.Nodup)
    (hBU : BU <:+: layer) (hBW : BW <:+: layer)
    (hdisj : ∀ x, x ∈ BU → x ∈ BW → False) :
    (∀ (u : Nat), u ∈ BU → ∀ (w : Nat), w ∈ BW → ∀ (i j : Nat), layer[i]? = some u → layer[j]? = some w → i < j) ∨
    (∀ (u : Nat), u ∈ BU → ∀ (w : Nat), w ∈ BW → ∀ (i j : Nat), layer[i]? = some u → layer[j]? = some w → j < i) := by
  obtain ⟨s1, t1, hs1⟩ := hBU
  obtain ⟨s2, t2, hs2⟩ := hBW
  cases hBUc : BU with
  | nil => exact Or.inl (fun u hu _ _ _ _ _ _ => by simp at hu)
  | cons _ _ =>
    cases hBWc : BW with
    | nil => exact Or.inr (fun u hu w hw _ _ _ _ => by simp at hw)
    | cons _ _ =>
      have hBUpos : 0 < BU.length := by rw [hBUc]; simp
      have hBWpos : 0 < BW.length := by rw [hBWc]; simp
      have hseg1 : (s1 ++ BU).length = s1.length + BU.length := by
        rw [List.length_append]
      have hseg2 : (s2 ++ BW).length = s2.length + BW.length := by
        rw [List.length_append]
      have hL1 : layer.length = s1.length + BU.length + t1.length := by
        rw [← hs1, List.length_append, List.length_append]
      have hL2 : layer.length = s2.length + BW.length + t2.length := by
        rw [← hs2, List.length_append, List.length_append]
      have hnd' : ((s1 ++ BU) ++ t1).Nodup := by rw [hs1]; exact hnd
      obtain ⟨hnds1BU, _, hdisj1⟩ := List.nodup_append.mp hnd'
      have hnd'' : ((s2 ++ BW) ++ t2).Nodup := by rw [hs2]; exact hnd
      obtain ⟨hnds2BW, _, hdisj2⟩ := List.nodup_append.mp hnd''
      obtain ⟨_, _, hdisjSBU⟩ := List.nodup_append.mp hnds1BU
      obtain ⟨_, _, hdisjSBW⟩ := List.nodup_append.mp hnds2BW
      have hord : s1.length + BU.length ≤ s2.length ∨
          s2.length + BW.length ≤ s1.length := by
        apply Classical.byContradiction
        intro hcon
        rw [not_or] at hcon
        obtain ⟨hn1, hn2⟩ := hcon
        have hlt1 : s2.length < s1.length + BU.length := by omega
        have hlt2 : s1.length < s2.length + BW.length := by omega
        obtain ⟨k, hkdef⟩ : ∃ k, k = max s1.length s2.length := ⟨_, rfl⟩
        have hks1 : s1.length ≤ k := by omega
        have hks2 : s2.length ≤ k := by omega
        have hkB1 : k < s1.length + BU.length := by omega
        have hkB2 : k < s2.length + BW.length := by omega
        have hkl : k < layer.length := by omega
        have hkx : layer[k]? = some layer[k] := List.getElem?_eq_getElem hkl
        have hxBU : layer[k] ∈ BU := by
          have hkk : layer[k]? = BU[k - s1.length]? := by
            rw [← hs1, List.getElem?_append_left (by omega : k < (s1 ++ BU).length),
              List.getElem?_append_right (by omega : s1.length ≤ k)]
          rw [hkk] at hkx
          exact List.mem_of_getElem? hkx
        have hxBW : layer[k] ∈ BW := by
          have hkk : layer[k]? = BW[k - s2.length]? := by
            rw [← hs2, List.getElem?_append_left (by omega : k < (s2 ++ BW).length),
              List.getElem?_append_right (by omega : s2.length ≤ k)]
          rw [hkk] at hkx
          exact List.mem_of_getElem? hkx
        exact hdisj _ hxBU hxBW
      rcases hord with hle | hle
      · refine Or.inl (fun u hu w hw i j hi hj => by
          have hiB : i < s1.length + BU.length := by
            apply Classical.byContradiction
            intro hcon
            have hge : s1.length + BU.length ≤ i := by omega
            have ht1mem : u ∈ t1 := by
              have hii : layer[i]? = t1[i - (s1 ++ BU).length]? := by
                rw [← hs1, List.getElem?_append_right (by omega : (s1 ++ BU).length ≤ i)]
              rw [hii] at hi
              exact List.mem_of_getElem? hi
            exact False.elim (hdisj1 u (List.mem_append.mpr (Or.inr (by simpa [hBUc] using hu))) u ht1mem rfl)
          have hjB : s2.length ≤ j := by
            apply Classical.byContradiction
            intro hcon
            have hltJ : j < s2.length := by omega
            have hs2mem : w ∈ s2 := by
              have hjj : layer[j]? = s2[j]? := by
                rw [← hs2, List.getElem?_append_left (by omega : j < (s2 ++ BW).length),
                  List.getElem?_append_left (by omega : j < s2.length)]
              rw [hjj] at hj
              exact List.mem_of_getElem? hj
            exact False.elim (hdisjSBW w hs2mem w (by simpa [hBWc] using hw) rfl)
          omega)
      · refine Or.inr (fun u hu w hw i j hi hj => by
          have hiB : s1.length ≤ i := by
            apply Classical.byContradiction
            intro hcon
            have hltI : i < s1.length := by omega
            have hs1mem : u ∈ s1 := by
              have hii : layer[i]? = s1[i]? := by
                rw [← hs1, List.getElem?_append_left (by omega : i < (s1 ++ BU).length),
                  List.getElem?_append_left (by omega : i < s1.length)]
              rw [hii] at hi
              exact List.mem_of_getElem? hi
            exact False.elim (hdisjSBU u hs1mem u (by simpa [hBUc] using hu) rfl)
          have hjB : j < s2.length + BW.length := by
            apply Classical.byContradiction
            intro hcon
            have hgeJ : s2.length + BW.length ≤ j := by omega
            have ht2mem : w ∈ t2 := by
              have hjj : layer[j]? = t2[j - (s2 ++ BW).length]? := by
                rw [← hs2, List.getElem?_append_right (by omega : (s2 ++ BW).length ≤ j)]
              rw [hjj] at hj
              exact List.mem_of_getElem? hj
            exact False.elim (hdisj2 w (List.mem_append.mpr (Or.inr (by simpa [hBWc] using hw))) w ht2mem rfl)
          omega)

/-! ## The order-phase fact -/

/-- The border markers of two unrelated declarations do not interleave on any
layer: the executed order keeps each title path block contiguous
(`order_clusters_contiguous`), every side marker lies in its title block
(the `ForeignBorderAnchorPaths` input plus non-dummy node paths), and the two
blocks are disjoint (prefix comparability forces a containment against the
unrelatedness hypotheses). -/
theorem foreignBorderLayerOrder (hpaths : ForeignBorderAnchorPaths) :
    ForeignBorderLayerOrder := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions hrun
    u w uNode wNode hu hw hbU hbW _hne hpathW hpathU layer hlayer
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hwf := componentRun_coordinate_bordersWellFormed hgraph hcomp hrun
  have horder' : OrderImpl.order run.coordinateProper orderOptions = .ok run.layers := by
    unfold OrderImpl.order
    rw [horder]
    dsimp only
    rw [hlayers]
  obtain ⟨hUlast, hWlast, hpeq⟩ := hpaths hgraph hcomp hrun hu hw hbU hbW _hne
  have hnp : ∀ (x : Nat) (nx : ProperNode), run.coordinateProper.nodes[x]? = some nx →
      (nx.node.border = -1 ∨ nx.node.border = 1) →
      OrderImpl.nodePath run.coordinateProper x = nx.node.clusterPath := by
    intro x nx hx hxb
    obtain ⟨na, hna, hda, _⟩ := OrderImpl.border_node hwf (by
      have hxb' : (run.coordinateProper.nodes.getD x default).node.border = -1 ∨
          (run.coordinateProper.nodes.getD x default).node.border = 1 := by
        rw [show run.coordinateProper.nodes.getD x default = nx from by
          simp [List.getD_eq_getElem?_getD, hx]]
        exact hxb
      exact hxb')
    rw [OrderImpl.nodePath_of_nondummy hna hda]
    have h1 : nx = na := Option.some.inj (hx.symm.trans hna)
    rw [h1]
  have hmemU : ∀ (x : Nat), x ∈ layer →
      (∃ na, run.coordinateProper.nodes[x]? = some na ∧
        (na.node.border = -1 ∨ na.node.border = 1) ∧
        na.node.clusterPath.getLast? = some uNode.decl) →
      x ∈ layer.filter
        (fun v => uNode.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper v)) := by
    intro x hx h
    obtain ⟨na, hna, hb, ho⟩ := h
    rw [List.mem_filter]
    refine ⟨hx, ?_⟩
    have hnpU := hnp x na hna hb
    have heqU := (hpeq (a := x) (na := na) hna hb).1 ho
    rw [hnpU, heqU]
    exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl
  have hmemW : ∀ (x : Nat), x ∈ layer →
      (∃ na, run.coordinateProper.nodes[x]? = some na ∧
        (na.node.border = -1 ∨ na.node.border = 1) ∧
        na.node.clusterPath.getLast? = some wNode.decl) →
      x ∈ layer.filter
        (fun v => wNode.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper v)) := by
    intro x hx h
    obtain ⟨na, hna, hb, ho⟩ := h
    rw [List.mem_filter]
    refine ⟨hx, ?_⟩
    have hnpW := hnp x na hna hb
    have heqW := (hpeq (a := x) (na := na) hna hb).2 ho
    rw [hnpW, heqW]
    exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl
  have hdisj : ∀ x, x ∈ layer.filter
        (fun v => uNode.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper v)) →
      x ∈ layer.filter
        (fun v => wNode.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper v)) →
      False := by
    intro x hxU hxW
    rw [List.mem_filter] at hxU hxW
    obtain ⟨-, hpreU⟩ := hxU
    obtain ⟨-, hpreW⟩ := hxW
    rcases prefix_total (List.isPrefixOf_iff_prefix.mp hpreU)
      (List.isPrefixOf_iff_prefix.mp hpreW) with hUW | hWU
    · have hcon : wNode.clusterPath.contains uNode.decl = true :=
        prefix_last_mem_contains (List.isPrefixOf_iff_prefix.mpr hUW) hUlast
      rw [hpathW] at hcon
      exact absurd hcon (by decide)
    · have hcon : uNode.clusterPath.contains wNode.decl = true :=
        prefix_last_mem_contains (List.isPrefixOf_iff_prefix.mpr hWU) hWlast
      rw [hpathU] at hcon
      exact absurd hcon (by decide)
  obtain ⟨k, hk, hkl⟩ := List.mem_iff_getElem.mp hlayer
  have hk2 : k < ord.layers.length := by rw [hlayers]; exact hk
  have hndlayer : layer.Nodup := by
    have h := OrderImpl.layer_nodup
      (OrderImpl.orderWithBudget_spec run.coordinateProper orderOptions ord horder).1 hk2
    rw [hlayers, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, hkl,
      Option.getD_some] at h
    exact h
  have hBUinfix := OrderImpl.order_clusters_contiguous run.coordinateProper
    orderOptions run.layers horder' layer hlayer uNode.clusterPath
  have hBWinfix := OrderImpl.order_clusters_contiguous run.coordinateProper
    orderOptions run.layers horder' layer hlayer wNode.clusterPath
  rcases infix_disjoint_ordered hndlayer hBUinfix hBWinfix hdisj with hUfirst | hWfirst
  · exact Or.inl (fun i j a b na nb hi hj hna hnb hbA hoA hbB hoB =>
      hUfirst a (hmemU a (List.mem_of_getElem? hi) ⟨na, hna, hbA, hoA⟩)
        b (hmemW b (List.mem_of_getElem? hj) ⟨nb, hnb, hbB, hoB⟩) i j hi hj)
  · exact Or.inr (fun i j a b na nb hi hj hna hnb hbA hoA hbB hoB =>
      hWfirst a (hmemU a (List.mem_of_getElem? hi) ⟨na, hna, hbA, hoA⟩)
        b (hmemW b (List.mem_of_getElem? hj) ⟨nb, hnb, hbB, hoB⟩) i j hi hj)

/-! ## The alignment-phase step -/

/-- The side chains are single alignment blocks: the `ForeignBorderSideUps`
input feeds `borderChainBlock_of_ups` once the chain is shown nonempty with
all members on executed layers (the layer cover comes from the executed
`routeWithLanes` geometry). -/
theorem foreignBorderSideBlocked (hups : ForeignBorderSideUps)
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {decl : Nat} {side : Int} (hside : side = -1 ∨ side = 1)
    {k : Nat} (hk : k < 4) :
    ∀ {pos : Array Nat}
    (_hpos : CoordsImpl.checkLayers
      (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers = .ok pos)
    (_hL : CoordsImpl.Lay (CoordsImpl.clusterCtx P.nodeGap P.clusterPad
      (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
      (CoordsImpl.typeOneConflicts
        (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos) k)),
    ∃ chain : List Nat,
      (∀ a, a ∈ chain ↔ ∃ na, run.coordinateProper.nodes[a]? = some na ∧
        na.node.border = side ∧ na.node.w = P.clusterBorderW ∧
        na.node.clusterPath.getLast? = some decl) ∧
      (chain ≠ [] → Elegant.Layered.BorderChainBlock P.nodeGap P.clusterPad
        (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
        (CoordsImpl.typeOneConflicts
          (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos) k chain) := by
  intro pos hpos hL
  obtain ⟨chain, ordered, hiff, hupsK⟩ := hups hgraph hcomp hrun hside hk hpos
  have hflat : ∀ v ∈ chain, v ∈ run.layers.flatten := by
    intro v hv
    rw [hiff] at hv
    obtain ⟨na, hna, _, _, _⟩ := hv
    have hlt : v < run.coordinateProper.nodes.length :=
      (List.getElem?_eq_some_iff.mp hna).1
    obtain ⟨_, _, _, _, _, _, _, ⟨_, _, _⟩, _, hproxy, hdrop, hroute, _, _, _, _⟩ :=
      componentRun_spec hrun
    have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
      rw [← hdrop]
      exact (proxyWidths_rel hproxy).2.2.1
    have hltP : v < run.proper.nodes.length := by rw [hlenEq]; exact hlt
    have hcov :=
      (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
    obtain ⟨l, hly, hmem, _⟩ := hcov v hltP
    exact List.mem_flatten.mpr ⟨l, List.mem_of_getElem? hly, hmem⟩
  refine ⟨chain, hiff, fun hne => ?_⟩
  exact Elegant.Layered.borderChainBlock_of_ups (ng := P.nodeGap) (cp := P.clusterPad)
    (p := run.coordinateProper) (layers := run.layers) (k := k)
    (chain := chain) (ordered := ordered) (pos := pos)
    hk hne hflat hpos hL (hupsK hL)

/-! ## The rank-phase step -/

/-- The per-rank marker pairs: the `ForeignRankPairAnchors` input feeds
`coordinateGraph_rank_pair` at every in-bounds rank, transported to the
executed `run.coordinateProper` with title-path owners. -/
theorem foreignRankPairCover (hrank : ForeignRankPairAnchors)
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {u w : Nat} {uNode wNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hw : (componentCandidate graph comp candidate).nodes[w]? = some wNode)
    (hbU : uNode.border = -2) (hbW : wNode.border = -2)
    (hne : uNode.decl ≠ wNode.decl) :
    ∃ (labeled : Proper),
      coordinateGraph P labeled = run.coordinateProper ∧
      ∃ (topU botU topW botW : ProperNode × Nat),
        (∀ {rank : Nat},
          (rk (titleReservations (sizeProperPorts P labeled)).rank topU.2).toNat ≤ rank →
          rank ≤ (rk (titleReservations (sizeProperPorts P labeled)).rank botU.2).toNat →
          ∃ (mLU mRU : Nat) (nLU nRU : ProperNode),
            run.coordinateProper.nodes[mLU]? = some nLU ∧
            nLU.node.border = -1 ∧ nLU.node.clusterPath.getLast? = some uNode.decl ∧
            rk run.coordinateProper.rank mLU = (rank : Int) ∧
            run.coordinateProper.nodes[mRU]? = some nRU ∧
            nRU.node.border = 1 ∧ nRU.node.clusterPath.getLast? = some uNode.decl ∧
            rk run.coordinateProper.rank mRU = (rank : Int)) ∧
        (∀ {rank : Nat},
          (rk (titleReservations (sizeProperPorts P labeled)).rank topW.2).toNat ≤ rank →
          rank ≤ (rk (titleReservations (sizeProperPorts P labeled)).rank botW.2).toNat →
          ∃ (mLW mRW : Nat) (nLW nRW : ProperNode),
            run.coordinateProper.nodes[mLW]? = some nLW ∧
            nLW.node.border = -1 ∧ nLW.node.clusterPath.getLast? = some wNode.decl ∧
            rk run.coordinateProper.rank mLW = (rank : Int) ∧
            run.coordinateProper.nodes[mRW]? = some nRW ∧
            nRW.node.border = 1 ∧ nRW.node.clusterPath.getLast? = some wNode.decl ∧
            rk run.coordinateProper.rank mRW = (rank : Int)) := by
  obtain ⟨labeled, hcoord, haligned, hU⟩ :=
    hrank hgraph hcomp hrun hu hw hbU hbW hne
  obtain ⟨topU, botU, htopU, hbUtop, hlastU, hbotU, hW⟩ := hU
  obtain ⟨topW, botW, htopW, hbWtop, hlastW, hbotW⟩ := hW
  refine ⟨labeled, hcoord, topU, botU, topW, botW, ?_, ?_⟩
  · intro rank hlo hhi
    obtain ⟨lU, rU, hLU, hRU, hrlU, hrrU⟩ :=
      coordinateGraph_rank_pair P labeled haligned htopU hbUtop hbotU hlo hhi
    rw [hcoord] at hLU hRU hrlU hrrU
    have hrkLU : rk run.coordinateProper.rank lU = (rank : Int) := by
      simp only [rk, List.getD_eq_getElem?_getD, hrlU, Option.getD_some]
    have hrkRU : rk run.coordinateProper.rank rU = (rank : Int) := by
      simp only [rk, List.getD_eq_getElem?_getD, hrrU, Option.getD_some]
    exact ⟨lU, rU, _, _, hLU, rfl, hlastU, hrkLU, hRU, rfl, hlastU, hrkRU⟩
  · intro rank hlo hhi
    obtain ⟨lW, rW, hLW, hRW, hrlW, hrrW⟩ :=
      coordinateGraph_rank_pair P labeled haligned htopW hbWtop hbotW hlo hhi
    rw [hcoord] at hLW hRW hrlW hrrW
    have hrkLW : rk run.coordinateProper.rank lW = (rank : Int) := by
      simp only [rk, List.getD_eq_getElem?_getD, hrlW, Option.getD_some]
    have hrkRW : rk run.coordinateProper.rank rW = (rank : Int) := by
      simp only [rk, List.getD_eq_getElem?_getD, hrrW, Option.getD_some]
    exact ⟨lW, rW, _, _, hLW, rfl, hlastW, hrkLW, hRW, rfl, hlastW, hrkRW⟩

end Elegant.Layered.PipelineImpl

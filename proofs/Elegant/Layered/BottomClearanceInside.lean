import Elegant.Layered.BottomClearanceBracket
import Elegant.Layered.BottomClearanceExistence
import Elegant.Layered.CompoundPathFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RouteImpl

/-- The family default `nodeGap` is at least two in both profiles.  A kind whose
`node_spacing` override fires replaces this default with the table value; the
generated array is opaque to proofs, so the override branch is carried as the
explicit hypothesis `hspacing` (the corpus table satisfies it: `2` or `3200`). -/
theorem nodeGap_ge_two (profile : Profile) (kind : String)
    (hspacing : 0 < kindConstant profile kind "node_spacing" →
      2 ≤ kindConstant profile kind "node_spacing") :
    2 ≤ kindOverride profile kind "node_spacing" (LayoutConst.node_gap.get profile) := by
  unfold kindOverride
  split
  · exact hspacing (by omega)
  · cases profile <;> decide

/-- The family default `cluster_pad` is at least one in both profiles.  Unlike
`nodeGap`, no kind override touches it (`Params.forKind` overrides spacing,
rank spacing, wrapping, and canvas margin only), so the plain table value is
the running `Params.clusterPad`. -/
theorem clusterPad_ge_one (profile : Profile) :
    1 ≤ LayoutConst.cluster_pad.get profile := by
  cases profile <;> decide

/-- The measured graph's box demotion: input boxes with a declared fixed size
have their role demoted to `.node`.  This mirrors the list computed inside
`measuredGraph`. -/
private def demoteBox (inp : Input) (box : ModelBox) : ModelBox :=
  if inp.fixedSizes.any (fun fixed : String × Size => fixed.1 == box.id) then
    { box with role := .node } else box

private def demoteBoxes (inp : Input) : List ModelBox :=
  inp.boxes.map (demoteBox inp)

private theorem demoteBox_id {inp : Input} : ∀ b ∈ inp.boxes, (demoteBox inp b).id = b.id := by
  intro b _
  unfold demoteBox
  split <;> rfl

private theorem demoteBox_parent {inp : Input} :
    ∀ b ∈ inp.boxes, (demoteBox inp b).parent = b.parent := by
  intro b _
  unfold demoteBox
  split <;> rfl

/-- `Compound.path` only reads `id` and `parent`, so paths computed against the
demoted list equal the model-level paths of the original boxes. -/
private theorem demoted_path_eq {inp : Input} {i : Nat} {boxO : ModelBox}
    (hbO : inp.boxes[i]? = some boxO) :
    Compound.path (demoteBoxes inp) (demoteBox inp boxO) =
      Compound.path inp.boxes boxO :=
  Compound.path_map inp.boxes (demoteBox inp) demoteBox_id demoteBox_parent
    (List.mem_of_getElem? hbO)

/-- Reading an entry of the demoted list produces the demoted original box. -/
private theorem demoteBoxes_get {inp : Input} {i : Nat} {boxD : ModelBox}
    (h : (demoteBoxes inp)[i]? = some boxD) :
    ∃ boxO : ModelBox, inp.boxes[i]? = some boxO ∧ (demoteBox inp boxO) = boxD := by
  rw [demoteBoxes, List.getElem?_map] at h
  cases hget : inp.boxes[i]? with
  | none => rw [hget] at h; simp at h
  | some boxO =>
      rw [hget] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← hget]
      exact ⟨boxO, hget, h⟩

/-- Chain canonicity: a declaration lying on a node's cluster path forces the
anchor chain of that declaration to be a prefix of the path.  This transports
`Compound.path_ancestor_prefix` through the demoted box list. -/
private theorem chain_prefix_of_mem {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o))
    {d : Nat} {boxD : ModelBox} (hboxD : (demoteBoxes inp)[d]? = some boxD)
    {upath : List Nat} {boxU : ModelBox} {j : Nat}
    (hboxU : (demoteBoxes inp)[j]? = some boxU)
    (hupath : upath = Compound.path (demoteBoxes inp) boxU ∨
      upath = Compound.path (demoteBoxes inp) boxU ++ [j])
    (hmem : d ∈ upath) :
    (Compound.path (demoteBoxes inp) boxD ++ [d]) <+: upath := by
  obtain ⟨boxDO, hbDO, hdemD⟩ := demoteBoxes_get hboxD
  obtain ⟨boxUO, hbUO, hdemU⟩ := demoteBoxes_get hboxU
  have hpd : Compound.path (demoteBoxes inp) boxD = Compound.path inp.boxes boxDO := by
    rw [← hdemD]
    exact demoted_path_eq hbDO
  have hpu : Compound.path (demoteBoxes inp) boxU = Compound.path inp.boxes boxUO := by
    rw [← hdemU]
    exact demoted_path_eq hbUO
  rcases hupath with heq | heq
  · subst heq
    have hmemO : d ∈ Compound.path inp.boxes boxUO := by rw [← hpu]; exact hmem
    have hprefix := Compound.path_ancestor_prefix (inputModel inp o) hwf hbDO hbUO hmemO
    rw [hpd, hpu]
    simpa [inputModel] using hprefix
  · subst heq
    rcases List.mem_append.mp hmem with hmem' | hmem'
    · have hmemO : d ∈ Compound.path inp.boxes boxUO := by rw [← hpu]; exact hmem'
      have hprefix := Compound.path_ancestor_prefix (inputModel inp o) hwf hbDO hbUO hmemO
      refine List.IsPrefix.trans (l₂ := Compound.path inp.boxes boxUO) ?_
        (by rw [hpu]; exact List.prefix_append _ _)
      simpa [inputModel, hpd] using hprefix
    · have hdj : d = j := List.mem_singleton.mp hmem'
      subst hdj
      have hEqU : boxU = boxD := Option.some.inj (hboxU.symm.trans hboxD)
      rw [hEqU]
      exact List.prefix_rfl

/-! ### Inside-span rank closure: seams and the bracket theorem

`BracketInsideRankBelowBottom` (BottomClearanceBracket) demands that no node of
positive height sharing a bottom proxy's rank may overlap the proxy's span.
The theorem below carries out the full position trichotomy: side-border slots
are killed by zero height, the inside interval is killed by the member rank
closure, and the outside positions are killed by the coordinate separation
chain, whose single-pair case forces the touching corner and then either the
`nodeGap ≥ 2` contradiction or plain membership via `borderMember`.

The seam hypotheses isolate six facts that are ordinary consequences of
already-landed phase lemmas (`coordinateGraph_lookup`, `pc_frame_flat`, the
`addClusterBorders` border records, and the compound member-interval lemmas);
their assembly is pending and reported by this unit. -/

/-- Side borders (`±1`) have zero height in a run.  Border `3` title copies
are excluded: they retain the anchor's measured title height. -/
def sideTitleHeightZero (P : Params) (graph : Graph) : Prop :=
  ∀ comp : List Nat, comp ∈ components graph → ∀ candidate : Nat,
    ∀ run : Run, ∀ labels : List MeasuredLabel, ∀ orderOptions : OrderOptions,
      componentRun P (componentCandidate graph comp candidate) labels orderOptions =
        .ok run →
      ∀ v : Nat,
        (run.coordinateProper.nodes.getD v default).node.border = -1 ∨
          (run.coordinateProper.nodes.getD v default).node.border = 1 →
        RouteImpl.nodeH run.proper v = 0


/-- A plain original member whose cluster path contains the proxy group's
declaration ranks strictly below that group's bottom proxy. -/
def plainMemberRankLtProxy (P : Params) (graph : Graph) : Prop :=
  ∀ comp : List Nat, comp ∈ components graph → ∀ candidate : Nat,
    ∀ run : Run, ∀ labels : List MeasuredLabel, ∀ orderOptions : OrderOptions,
      componentRun P (componentCandidate graph comp candidate) labels orderOptions =
        .ok run →
      ∀ t v : Nat,
        (run.coordinateProper.nodes.getD t default).node.border = 2 →
        (run.coordinateProper.nodes.getD v default).dummy = false →
        (run.coordinateProper.nodes.getD v default).node.border = 0 →
        ∀ d : Nat, (run.coordinateProper.nodes.getD t default).node.clusterPath.getLast? =
            some d →
          (run.coordinateProper.nodes.getD v default).node.clusterPath.contains d = true →
          rk run.coordinateProper.rank v < rk run.coordinateProper.rank t

/-- A dummy of positive height cannot share a bottom proxy's rank. -/
def dummyInsideSameRankFalse (P : Params) (graph : Graph) : Prop :=
  ∀ comp : List Nat, comp ∈ components graph → ∀ candidate : Nat,
    ∀ run : Run, ∀ labels : List MeasuredLabel, ∀ orderOptions : OrderOptions,
      componentRun P (componentCandidate graph comp candidate) labels orderOptions =
        .ok run →
      ∀ t v : Nat,
        (run.coordinateProper.nodes.getD t default).node.border = 2 →
        (run.coordinateProper.nodes.getD v default).dummy = true →
        0 < RouteImpl.nodeH run.proper v →
        rk run.coordinateProper.rank v = rk run.coordinateProper.rank t →
        False

/-- A non-dummy node that is not a proxy has border `0`, unless it is a `3`
title copy of a group anchor. -/
def nonDummyBorderPlain (P : Params) (graph : Graph) : Prop :=
  ∀ comp : List Nat, comp ∈ components graph → ∀ candidate : Nat,
    ∀ run : Run, ∀ labels : List MeasuredLabel, ∀ orderOptions : OrderOptions,
      componentRun P (componentCandidate graph comp candidate) labels orderOptions =
        .ok run →
      ∀ v : Nat,
        (run.coordinateProper.nodes.getD v default).dummy = false →
        (run.coordinateProper.nodes.getD v default).node.border ≠ -2 →
        (run.coordinateProper.nodes.getD v default).node.border ≠ 2 →
        RouteImpl.nodeH run.proper v ≠ 0 →
        (run.coordinateProper.nodes.getD v default).node.border = 0 ∨
          (run.coordinateProper.nodes.getD v default).node.border = 3

/-- Title copies (`border = 3`) sharing a bottom proxy's rank have an x-span
disjoint from the proxy's span: `right(t) ≤ left(v) ∨ right(v) ≤ left(t)`,
the disjunction `componentRun_bottom_clearance_of_inside` needs.  Touching
spans are allowed: `cluster_border_w = 1` is odd, so `coordSep` parity permits
`right(v) = left(t)`.  Proved in `TitleCopySpanFacts.lean` from
`componentRun_nonproxy_ordered_intervals` (exterior positions),
`insidePrefixHypothesis` (interior positions reduce to the
`TitleCopyNestedRank` residual), and `componentRun_proxy_border_extrema`
(the proxy span equals its side-border span). -/
def titleCopySpanClearStrict (P : Params) (graph : Graph) : Prop :=
  ∀ comp : List Nat, comp ∈ components graph → ∀ candidate : Nat,
    ∀ run : Run, ∀ labels : List MeasuredLabel, ∀ orderOptions : OrderOptions,
      componentRun P (componentCandidate graph comp candidate) labels orderOptions =
        .ok run →
    ∀ t v : Nat,
      (run.coordinateProper.nodes.getD t default).dummy = false →
      (run.coordinateProper.nodes.getD t default).node.border = 2 →
      (run.coordinateProper.nodes.getD v default).node.border = 3 →
      0 < RouteImpl.nodeH run.proper v →
      rk run.coordinateProper.rank v = rk run.coordinateProper.rank t →
      RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t ≤
          RouteImpl.leftOf run.proper run.xs v ∨
        RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤
          RouteImpl.leftOf run.proper run.xs t

/-- Same-group side borders carry the group's full cluster path and are
non-dummy. -/
def sidePathEq (P : Params) (graph : Graph) : Prop :=
  ∀ comp : List Nat, comp ∈ components graph → ∀ candidate : Nat,
    ∀ run : Run, ∀ labels : List MeasuredLabel, ∀ orderOptions : OrderOptions,
      componentRun P (componentCandidate graph comp candidate) labels orderOptions =
        .ok run →
      ∀ x y : Nat,
        (run.coordinateProper.nodes.getD x default).node.border = 2 →
        ((run.coordinateProper.nodes.getD y default).node.border = -1 ∨
          (run.coordinateProper.nodes.getD y default).node.border = 1) →
        (run.coordinateProper.nodes.getD x default).node.clusterPath.getLast? =
          (run.coordinateProper.nodes.getD y default).node.clusterPath.getLast? →
        (run.coordinateProper.nodes.getD y default).node.clusterPath =
          (run.coordinateProper.nodes.getD x default).node.clusterPath ∧
          (run.coordinateProper.nodes.getD y default).dummy = false

/-- Inside the bracket of a group, every non-dummy layer node has the group's
cluster path as a prefix of its node path (contiguity plus border ends). -/
def insidePrefixHypothesis (run : Run) (_orderOptions : OrderOptions)
    (pref : List Nat) : Prop :=
  OrderImpl.BordersWellFormed run.coordinateProper ∧
    ∀ layer : List Nat, layer ∈ run.layers → ∀ li vpos ri : Nat, ∀ l r v : Nat,
      layer[li]? = some l → layer[vpos]? = some v → layer[ri]? = some r →
      li < vpos → vpos < ri →
      ((run.coordinateProper.nodes.getD l default).node.border = -1 ∨
          (run.coordinateProper.nodes.getD l default).node.border = 1) →
      (run.coordinateProper.nodes.getD l default).node.clusterPath = pref →
      (run.coordinateProper.nodes.getD l default).dummy = false →
      ((run.coordinateProper.nodes.getD r default).node.border = -1 ∨
          (run.coordinateProper.nodes.getD r default).node.border = 1) →
      (run.coordinateProper.nodes.getD r default).node.clusterPath = pref →
      (run.coordinateProper.nodes.getD r default).dummy = false →
      (run.coordinateProper.nodes.getD v default).dummy = false →
      pref <+: OrderImpl.nodePath run.coordinateProper v

/-- A list's last element is a member. -/
private theorem mem_of_getLast?_eq_some {l : List Nat} {a : Nat}
    (h : l.getLast? = some a) : a ∈ l := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
      rw [List.getLast?_cons] at h
      have hinj : xs.getLast?.getD x = a := Option.some.inj h
      cases hgl : xs.getLast? with
      | none =>
          rw [hgl, Option.getD_none] at hinj
          rw [← hinj]
          exact List.mem_cons_self ..
      | some z =>
          rw [hgl, Option.getD_some] at hinj
          have hih : xs.getLast? = some a := by rw [hgl, hinj]
          exact List.mem_cons_of_mem x (ih hih)

/-- A title-anchor pair needs a `±2`/`2` endpoint, so a side border never
forms one. -/
private theorem ownTitleAnchor_false_of_side {p : Proper} {a b : Nat}
    {na nb : ProperNode} (ha : p.nodes[a]? = some na) (hb : p.nodes[b]? = some nb)
    (hnb : nb.node.border = -1 ∨ nb.node.border = 1) :
    CoordsImpl.ownTitleAnchor p a b = false := by
  unfold CoordsImpl.ownTitleAnchor
  simp only [ha, hb]
  rcases hnb with h | h
  · simp [h]
  · simp [h]

/-- A title-anchor pair needs a `±2`/`2`/`3` endpoint, so a plain node of
nonzero height never forms one. -/
private theorem ownTitleAnchor_false_of_plain {p : Proper} {a b : Nat}
    {na nb : ProperNode} (ha : p.nodes[a]? = some na) (hb : p.nodes[b]? = some nb)
    (hna : na.node.border ≠ -2) (hna' : na.node.border ≠ 2)
    (hna'' : na.node.border ≠ 3) :
    CoordsImpl.ownTitleAnchor p a b = false := by
  have hb1 : (na.node.border == -2) = false := by simp [hna]
  have hb2 : (na.node.border == 2) = false := by simp [hna']
  have hb3 : (na.node.border == 3) = false := by simp [hna'']
  unfold CoordsImpl.ownTitleAnchor
  simp only [ha, hb, hb1, hb2, hb3]
  simp

/-- A title-anchor pair needs a `±2`/`2`/`3` endpoint, so a plain node of
nonzero height never forms one (second position). -/
private theorem ownTitleAnchor_false_of_plain_second {p : Proper} {a b : Nat}
    {na nb : ProperNode} (ha : p.nodes[a]? = some na) (hb : p.nodes[b]? = some nb)
    (hnb : nb.node.border ≠ -2) (hnb' : nb.node.border ≠ 2)
    (hnb'' : nb.node.border ≠ 3) :
    CoordsImpl.ownTitleAnchor p a b = false := by
  have hb1 : (nb.node.border == -2) = false := by simp [hnb]
  have hb2 : (nb.node.border == 2) = false := by simp [hnb']
  have hb3 : (nb.node.border == 3) = false := by simp [hnb'']
  unfold CoordsImpl.ownTitleAnchor
  simp only [ha, hb, hb1, hb2, hb3]
  simp

/-- The `borderMember` gap on a `(plain, side)` pair forces the side's group
declaration into the plain node's cluster path. -/
private theorem borderMember_contains_left {p : Proper} {a b : Nat}
    {na nb : ProperNode} {owner : Nat} (ha : p.nodes[a]? = some na)
    (hb : p.nodes[b]? = some nb)
    (hmem : CoordsImpl.borderMember p a b = true)
    (hna : na.node.border ≠ -1 ∧ na.node.border ≠ 1)
    (_hnb : nb.node.border = -1 ∨ nb.node.border = 1)
    (hlast : nb.node.clusterPath.getLast? = some owner) :
    na.node.clusterPath.contains owner = true := by
  unfold CoordsImpl.borderMember at hmem
  simp only [ha, hb] at hmem
  rcases Bool.or_eq_true_iff.mp hmem with h1 | h2
  · rw [Bool.and_eq_true] at h1
    have hba : (na.node.border == -1 || na.node.border == 1) = false := by
      rcases hna with ⟨ha1, ha2⟩
      simp [ha1, ha2]
    rw [hba] at h1
    simp at h1
  · rw [Bool.and_eq_true] at h2
    cases hgl : nb.node.clusterPath.getLast? with
    | none => rw [hgl] at hlast; exact absurd hlast (by simp)
    | some c =>
        rw [hgl] at h2 hlast
        have hco : c = owner := Option.some.inj hlast
        rw [← hco]
        exact h2.2

/-- The `borderMember` gap on a `(side, plain)` pair forces the side's group
declaration into the plain node's cluster path. -/
private theorem borderMember_contains_right {p : Proper} {a b : Nat}
    {na nb : ProperNode} {owner : Nat} (ha : p.nodes[a]? = some na)
    (hb : p.nodes[b]? = some nb)
    (hmem : CoordsImpl.borderMember p a b = true)
    (_hna : na.node.border = -1 ∨ na.node.border = 1)
    (hnb : nb.node.border ≠ -1 ∧ nb.node.border ≠ 1)
    (hlastA : na.node.clusterPath.getLast? = some owner) :
    nb.node.clusterPath.contains owner = true := by
  unfold CoordsImpl.borderMember at hmem
  simp only [ha, hb] at hmem
  rcases Bool.or_eq_true_iff.mp hmem with h1 | h2
  · rw [Bool.and_eq_true] at h1
    cases hgl : na.node.clusterPath.getLast? with
    | none => rw [hgl] at hlastA; exact absurd hlastA (by simp)
    | some c =>
        rw [hgl] at h1 hlastA
        have hco : c = owner := Option.some.inj hlastA
        rw [← hco]
        exact h1.2
  · rw [Bool.and_eq_true] at h2
    have hbb : (nb.node.border == -1 || nb.node.border == 1) = false := by
      rcases hnb with ⟨hb1, hb2⟩
      simp [hb1, hb2]
    rw [hbb] at h2
    simp at h2

theorem bracket_inside_rank_below_bottom {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
    (hside : sideTitleHeightZero P graph)
    (hplainRank : plainMemberRankLtProxy P graph)
    (hdummyRank : dummyInsideSameRankFalse P graph)
    (hborderPlain : nonDummyBorderPlain P graph)
    (htitleSpan : titleCopySpanClearStrict P graph)
    (hsidePath : sidePathEq P graph)
    (hinsidePrefix : ∀ run : Run, ∀ labels : List MeasuredLabel,
      ∀ orderOptions : OrderOptions,
      componentRun P (componentCandidate graph comp candidate) labels orderOptions =
        .ok run →
      ∀ pref : List Nat, insidePrefixHypothesis run orderOptions pref) :
    BracketInsideRankBelowBottom hgraph hlines hcomp candidate := by
  intro run labels orderOptions hrun t v _htdummy htborder hvnotTop hvnotBottom
    hheight hrankEq hoverlapStrict
  have hoverlap : RouteImpl.leftOf run.proper run.xs t ≤
        RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ∧
      RouteImpl.leftOf run.proper run.xs v ≤
        RouteImpl.leftOf run.proper run.xs t + RouteImpl.nodeW run.proper t :=
    ⟨Int.le_of_lt hoverlapStrict.1, Int.le_of_lt hoverlapStrict.2⟩
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, hcross, hproxy,
    hdropsyn, _, _⟩ := componentRun_spec hrun
  obtain ⟨_, _, hlength, _, _, _⟩ := proxyWidths_rel hproxy
  have hnodesEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hlength, ← hdropsyn, OrderImpl.dropSynthetic_nodes]
  have hdefaultBorder : (default : ProperNode).node.border = 0 := rfl
  obtain ⟨proxy, htp⟩ : ∃ x, run.coordinateProper.nodes[t]? = some x := by
    cases hx : run.coordinateProper.nodes[t]? with
    | none =>
        rw [List.getD_eq_getElem?_getD, hx] at htborder
        have hnoneD : (none : Option ProperNode).getD default = default := rfl
        rw [hnoneD, hdefaultBorder] at htborder
        omega
    | some x => exact ⟨x, rfl⟩
  obtain ⟨other, hv0⟩ : ∃ x, run.coordinateProper.nodes[v]? = some x := by
    cases hx : run.coordinateProper.nodes[v]? with
    | none =>
        exfalso
        have := List.getElem?_eq_none_iff.mp hx
        have hnone : run.proper.nodes[v]? = none :=
          List.getElem?_eq_none (by have := hlength; omega)
        have hnh : RouteImpl.nodeH run.proper v = 0 := by
          unfold RouteImpl.nodeH
          rw [hnone]
        rw [hnh] at hheight
        omega
    | some x => exact ⟨x, rfl⟩
  have ht' : run.coordinateProper.nodes[t]? = some proxy := htp
  have hv' : run.coordinateProper.nodes[v]? = some other := hv0
  have htGetD : run.coordinateProper.nodes.getD t default = proxy := by
    simp [List.getD_eq_getElem?_getD, ht']
  have hvGetD : run.coordinateProper.nodes.getD v default = other := by
    simp [List.getD_eq_getElem?_getD, hv']
  have htBorder : proxy.node.border = -2 ∨ proxy.node.border = 2 := by
    right
    have hb := htborder
    rw [htGetD] at hb
    exact hb
  have hvNotProxy : ¬(other.node.border = -2 ∨ other.node.border = 2) := by
    intro hc
    rcases hc with hc | hc
    · exact hvnotTop (by rw [hvGetD]; exact hc)
    · exact hvnotBottom (by rw [hvGetD]; exact hc)
  have hside1 := hside comp hcomp candidate run labels orderOptions hrun
  have hvKilledSide : ¬(other.node.border = -1 ∨ other.node.border = 1) := by
    intro hc
    have := hside1 v (by rw [hvGetD]; exact hc)
    omega
  have hvNotSide1 : other.node.border ≠ -1 := fun hc => hvKilledSide (Or.inl hc)
  have hvNotSide2 : other.node.border ≠ 1 := fun hc => hvKilledSide (Or.inr hc)
  have hvNotTop' : other.node.border ≠ -2 := fun hc => hvNotProxy (Or.inl hc)
  have hvNotBottom' : other.node.border ≠ 2 := fun hc => hvNotProxy (Or.inr hc)
  have hvNotSide3 : other.node.border ≠ 3 := by
    intro hc
    have hclear := htitleSpan comp hcomp candidate run labels orderOptions hrun t v
      _htdummy htborder (by rw [hvGetD]; exact hc) hheight hrankEq
    omega
  -- border records and final widths of v
  obtain ⟨hvp, hvx⟩ := componentRun_nonproxy_record hrun hv' hvNotProxy
  have hwv : RouteImpl.nodeW run.proper v = other.node.w := by
    simp only [RouteImpl.nodeW, hvp]
  have hcoWv : CoordsImpl.nodeW run.coordinateProper v =
      RouteImpl.nodeW run.proper v + 2 * (other.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, hv']
    rw [hwv]
  -- ordering layer of t and v
  obtain ⟨htLen, _⟩ := ExecutedBorderOrder.node_layer run.coordinateProper orderOptions
    ord horder ht'
  obtain ⟨_, hvIn0⟩ := ExecutedBorderOrder.node_layer run.coordinateProper orderOptions
    ord horder hv'
  have hlayTV : OrderImpl.lay run.coordinateProper t = OrderImpl.lay run.coordinateProper v := by
    unfold OrderImpl.lay
    rw [hrankEq]
  rw [← hlayTV] at hvIn0
  have hlayLen : OrderImpl.lay run.coordinateProper t < run.layers.length := by
    rw [← hlayers]; exact htLen
  let layer : List Nat := run.layers[OrderImpl.lay run.coordinateProper t]'hlayLen
  have hlayerMem : layer ∈ run.layers := List.getElem_mem hlayLen
  have hopt : run.layers[OrderImpl.lay run.coordinateProper t]? = some layer :=
    List.getElem?_eq_some_iff.mpr ⟨hlayLen, rfl⟩
  have hvMemL : v ∈ layer := by
    have h1 := hvIn0
    simp only [hlayers, hopt, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  -- same-rank bracket borders of t's group
  obtain ⟨owner, leftIndex, rightIndex, left, right, ownerEq, hleft, hright,
    hleftProper, hrightProper, hleftBorder, hrightBorder, hleftOwner, hrightOwner,
    hleftRank, hrightRank, hleftEq, hrightEq⟩ :=
    componentRun_proxy_border_extrema hrun ht' htBorder
  have hleftNotProxy : ¬(left.node.border = -2 ∨ left.node.border = 2) := by
    rcases hleftBorder with hb | hb <;> omega
  have hrightNotProxy : ¬(right.node.border = -2 ∨ right.node.border = 2) := by
    rcases hrightBorder with hb | hb <;> omega
  have hlayL : OrderImpl.lay run.coordinateProper leftIndex =
      OrderImpl.lay run.coordinateProper t := by
    unfold OrderImpl.lay
    rw [hleftRank]
  have hlayR : OrderImpl.lay run.coordinateProper rightIndex =
      OrderImpl.lay run.coordinateProper t := by
    unfold OrderImpl.lay
    rw [hrightRank]
  obtain ⟨_, hleftMemOrd⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hleft
  obtain ⟨_, hrightMemOrd⟩ := ExecutedBorderOrder.node_layer run.coordinateProper
    orderOptions ord horder hright
  rw [hlayL] at hleftMemOrd
  rw [hlayR] at hrightMemOrd
  have hleftMem : leftIndex ∈ layer := by
    have h1 := hleftMemOrd
    simp only [hlayers, hopt, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  have hrightMem : rightIndex ∈ layer := by
    have h1 := hrightMemOrd
    simp only [hlayers, hopt, List.getD_eq_getElem?_getD, Option.getD_some] at h1
    exact h1
  obtain ⟨leftPos, hleftPos⟩ := List.mem_iff_getElem?.mp hleftMem
  obtain ⟨rightPos, hrightPos⟩ := List.mem_iff_getElem?.mp hrightMem
  obtain ⟨vPos, hvPos⟩ := List.mem_iff_getElem?.mp hvMemL
  -- side borders carry the proxy group's path and are non-dummy
  have hleftGD : run.coordinateProper.nodes.getD leftIndex default = left := by
    simp [List.getD_eq_getElem?_getD, hleft]
  have hrightGD : run.coordinateProper.nodes.getD rightIndex default = right := by
    simp [List.getD_eq_getElem?_getD, hright]
  obtain ⟨hleftPath, hleftDummy⟩ := hsidePath comp hcomp candidate run labels
    orderOptions hrun t leftIndex htborder
    (by rw [hleftGD]; exact hleftBorder) (by rw [htGetD, hleftGD]; exact ownerEq.trans hleftOwner.symm)
  obtain ⟨hrightPath, hrightDummy⟩ := hsidePath comp hcomp candidate run labels
    orderOptions hrun t rightIndex htborder
    (by rw [hrightGD]; exact hrightBorder) (by rw [htGetD, hrightGD]; exact ownerEq.trans hrightOwner.symm)
  have hwl : RouteImpl.nodeW run.proper leftIndex = left.node.w := by
    simp only [RouteImpl.nodeW, hleftProper]
  have hwr : RouteImpl.nodeW run.proper rightIndex = right.node.w := by
    simp only [RouteImpl.nodeW, hrightProper]
  have hcoWl : CoordsImpl.nodeW run.coordinateProper leftIndex =
      RouteImpl.nodeW run.proper leftIndex + 2 * (left.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, hleft]
    rw [hwl]
  have hcoWr : CoordsImpl.nodeW run.coordinateProper rightIndex =
      RouteImpl.nodeW run.proper rightIndex + 2 * (right.node.loopExtent : Int) := by
    simp only [CoordsImpl.nodeW, hright]
    rw [hwr]
  have e : ∀ width : Int, Int.fdiv width 2 = width / 2 :=
    fun width => Int.fdiv_eq_ediv_of_nonneg width (by decide)
  have half0 : ∀ x : Int, 0 ≤ x → 0 ≤ x / 2 := fun x hx => Int.ediv_nonneg hx (by decide)
  obtain ⟨_, _, hrange, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  have hmin : 1 ≤ min P.nodeGap P.clusterPad := by omega
  have hrankClauses := hplainRank comp hcomp candidate run labels orderOptions hrun
  have hdummyClauses := hdummyRank comp hcomp candidate run labels orderOptions hrun
  have hborderClauses := hborderPlain comp hcomp candidate run labels orderOptions hrun
  have hip := hinsidePrefix run labels orderOptions hrun (proxy.node.clusterPath)

  rcases Nat.lt_trichotomy vPos leftPos with hvl | hvl | hvl
  · -- v ordered left of the left border: separation plus overlap force touching
    exfalso
    have hsepL : RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤
        RouteImpl.leftOf run.proper run.xs leftIndex :=
      componentRun_nonproxy_ordered_intervals hgraph hcomp hrun hlayerMem hvl hvPos hleftPos
        hv' hleft hvNotProxy hleftNotProxy
    have htouchL : RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v =
        RouteImpl.leftOf run.proper run.xs leftIndex := by
      have h1 := hoverlap.1
      rw [hleftEq] at h1
      omega
    have hlx : run.xs.getD leftIndex 0 = run.coordinateXs.getD leftIndex 0 :=
      (componentRun_border_record hrun hleft hleftBorder).2
    have heqC : run.coordinateXs.getD leftIndex 0 - run.coordinateXs.getD v 0 =
        RouteImpl.nodeW run.proper v - RouteImpl.nodeW run.proper v / 2 +
          RouteImpl.nodeW run.proper leftIndex / 2 := by
      simp only [RouteImpl.leftOf, RouteImpl.xAt, e] at htouchL
      rw [hvx, hlx] at htouchL
      omega
    have hleftLen : leftPos < layer.length := (List.getElem?_eq_some_iff.mp hleftPos).1
    have hvPosLen : vPos < layer.length := (List.getElem?_eq_some_iff.mp hvPos).1
    cases hlm : layer[leftPos - 1]? with
    | none => have := List.getElem?_eq_none_iff.mp hlm; omega
    | some u =>
      have huBound : u < run.coordinateProper.nodes.length :=
        CoordsImpl.layers_mem_lt hrange hlayerMem hlm
      cases hul : run.coordinateProper.nodes[u]? with
      | none => have := List.getElem?_eq_none_iff.mp hul; omega
      | some un =>
        have hotUL := ownTitleAnchor_false_of_side hul hleft hleftBorder
        have hgapL : min P.nodeGap P.clusterPad ≤
            CoordsImpl.clusterGap P.nodeGap P.clusterPad run.coordinateProper u
              leftIndex :=
          CoordsImpl.clusterGap_ge_min run.coordinateProper u leftIndex hotUL
        have hbal := CoordsImpl.cluster_balance_separated hcross layer hlayerMem (leftPos - 1) u
          leftIndex hlm
          (by rw [Nat.sub_add_cancel (by omega : 1 ≤ leftPos)]; exact hleftPos)
        unfold CoordsImpl.clusterSep CoordsImpl.coordSep CoordsImpl.clusterGap at hbal
        rw [hotUL] at hbal
        simp only [Bool.false_eq_true, ite_false] at hbal
        simp only [e] at hbal
        have hcu0 : 0 ≤ CoordsImpl.nodeW run.coordinateProper u :=
          CoordsImpl.nodeW_nonneg hsizes u
        have hcl0 : 0 ≤ CoordsImpl.nodeW run.coordinateProper leftIndex :=
          CoordsImpl.nodeW_nonneg hsizes leftIndex
        have hcv0 : 0 ≤ CoordsImpl.nodeW run.coordinateProper v :=
          CoordsImpl.nodeW_nonneg hsizes v
        rcases Nat.lt_trichotomy (vPos + 1) leftPos with hk | hk | hk
        · -- multi-pair: the first and last gaps are each at least one
          exfalso
          rcases Nat.lt_trichotomy (vPos + 2) leftPos with hd | hd | hd
          · -- three segments: balances at both ends plus a zero-pair span
            have huGt : vPos + 1 < leftPos - 1 := by omega
            cases hy : layer[vPos + 1]? with
            | none => have := List.getElem?_eq_none_iff.mp hy; omega
            | some y =>
              have hyBound : y < run.coordinateProper.nodes.length :=
                CoordsImpl.layers_mem_lt hrange hlayerMem hy
              cases hyl : run.coordinateProper.nodes[y]? with
              | none => have := List.getElem?_eq_none_iff.mp hyl; omega
              | some yn =>
                have hotVY := ownTitleAnchor_false_of_plain hv' hyl
                  hvNotTop' hvNotBottom' hvNotSide3
                have hgapVY : min P.nodeGap P.clusterPad ≤
                    CoordsImpl.clusterGap P.nodeGap P.clusterPad run.coordinateProper v y :=
                  CoordsImpl.clusterGap_ge_min run.coordinateProper v y hotVY
                have hbalVY := CoordsImpl.cluster_balance_separated hcross layer hlayerMem vPos v
                  y hvPos hy
                unfold CoordsImpl.clusterSep CoordsImpl.coordSep CoordsImpl.clusterGap
                  at hbalVY
                rw [hotVY] at hbalVY
                simp only [Bool.false_eq_true, ite_false] at hbalVY
                simp only [e] at hbalVY
                have hzero := CoordsImpl.cluster_zero_pairs_separated hcross layer hlayerMem
                  (vPos + 1) (leftPos - 1) y u huGt hy hlm
                simp only [e] at hzero
                have hcy0 : 0 ≤ CoordsImpl.nodeW run.coordinateProper y :=
                  CoordsImpl.nodeW_nonneg hsizes y
                have hgapL' : 1 ≤ (if CoordsImpl.borderMember run.coordinateProper u
                    leftIndex then P.clusterPad else P.nodeGap) := by
                  have h1 := hgapL
                  unfold CoordsImpl.clusterGap at h1
                  rw [hotUL] at h1
                  simp only [Bool.false_eq_true, ite_false] at h1
                  omega
                have hgapVY' : 1 ≤ (if CoordsImpl.borderMember run.coordinateProper v
                    y then P.clusterPad else P.nodeGap) := by
                  have h1 := hgapVY
                  unfold CoordsImpl.clusterGap at h1
                  rw [hotVY] at h1
                  simp only [Bool.false_eq_true, ite_false] at h1
                  omega
                have hh1 := half0 _ hcu0
                have hh2 := half0 _ hcy0
                have hh3 := half0 _ hcl0
                have hh4 := half0 _ hcv0
                omega
          · -- leftPos = vPos + 2: the two pairs share their middle node
            cases hy : layer[vPos + 1]? with
            | none => have := List.getElem?_eq_none_iff.mp hy; omega
            | some y =>
              have huy : y = u := by
                rw [← hd] at hlm
                simp at hlm
                rw [hy] at hlm
                exact Option.some.inj hlm
              subst huy
              cases hyl : run.coordinateProper.nodes[y]? with
              | none => have := List.getElem?_eq_none_iff.mp hyl; omega
              | some yn =>
                have hotVY := ownTitleAnchor_false_of_plain hv' hyl
                  hvNotTop' hvNotBottom' hvNotSide3
                have hgapVY : min P.nodeGap P.clusterPad ≤
                    CoordsImpl.clusterGap P.nodeGap P.clusterPad run.coordinateProper v y :=
                  CoordsImpl.clusterGap_ge_min run.coordinateProper v y hotVY
                have hbalVY := CoordsImpl.cluster_balance_separated hcross layer hlayerMem vPos v
                  y hvPos hy
                unfold CoordsImpl.clusterSep CoordsImpl.coordSep CoordsImpl.clusterGap
                  at hbalVY
                rw [hotVY] at hbalVY
                simp only [Bool.false_eq_true, ite_false] at hbalVY
                simp only [e] at hbalVY
                have hcy0 : 0 ≤ CoordsImpl.nodeW run.coordinateProper y :=
                  CoordsImpl.nodeW_nonneg hsizes y
                have hgapL' : 1 ≤ (if CoordsImpl.borderMember run.coordinateProper y
                    leftIndex then P.clusterPad else P.nodeGap) := by
                  have h1 := hgapL
                  unfold CoordsImpl.clusterGap at h1
                  rw [hotUL] at h1
                  simp only [Bool.false_eq_true, ite_false] at h1
                  omega
                have hgapVY' : 1 ≤ (if CoordsImpl.borderMember run.coordinateProper v
                    y then P.clusterPad else P.nodeGap) := by
                  have h1 := hgapVY
                  unfold CoordsImpl.clusterGap at h1
                  rw [hotVY] at h1
                  simp only [Bool.false_eq_true, ite_false] at h1
                  omega
                have hh1 := half0 _ hcy0
                have hh2 := half0 _ hcl0
                have hh3 := half0 _ hcv0
                omega
          · -- leftPos < vPos + 2 contradicts vPos + 1 < leftPos
            omega
        · -- single pair (v, left): touching is impossible
          exfalso
          have hvu : v = u := by
            rw [← hk] at hlm
            simp at hlm
            rw [hvPos] at hlm
            exact Option.some.inj hlm
          subst hvu
          rcases hbmL : CoordsImpl.borderMember run.coordinateProper v leftIndex with _ | _
          · rw [hbmL] at hbal
            simp only [Bool.false_eq_true, ite_false] at hbal
            omega
          · simp only [hbmL, ite_true] at hbal
            by_cases hvDummy : (run.coordinateProper.nodes.getD v default).dummy = true
            · exact hdummyClauses t v htborder hvDummy hheight hrankEq
            · have hvDummyF : other.dummy = false := by
                cases hb : other.dummy with
                | true => exact absurd (by rw [hvGetD]; exact hb) hvDummy
                | false => rfl
              have hmemOwner := borderMember_contains_left hv' hleft hbmL
                ⟨hvNotSide1, hvNotSide2⟩ hleftBorder hleftOwner
              have hvBorder0 := (hborderClauses v (by rw [hvGetD]; exact hvDummyF)
                hvnotTop hvnotBottom (by
                  intro hc
                  rw [hc] at hheight
                  omega)).resolve_right
                (fun hb => absurd (by rw [hvGetD] at hb; exact hb) hvNotSide3)
              have hrankLt := hrankClauses t v htborder
                (by rw [hvGetD]; exact hvDummyF) hvBorder0
                owner (by rw [htGetD]; exact ownerEq) (by rw [hvGetD]; exact hmemOwner)
              omega
        · -- leftPos < vPos + 1 contradicts vPos < leftPos
          omega
  · -- vPos = leftPos: v is the left border, of zero height
    exfalso
    have hvEqL : v = leftIndex := by
      rw [hvl] at hvPos
      rw [hleftPos] at hvPos
      exact Option.some.inj hvPos.symm
    subst hvEqL
    have := hside1 v (by rw [hleftGD]; exact hleftBorder)
    omega
  · rcases Nat.lt_trichotomy vPos rightPos with hvr | hvr | hvr
    · -- strictly inside the bracket: the member rank closure contradicts same rank
      exfalso
      by_cases hvDummy : (run.coordinateProper.nodes.getD v default).dummy = true
      · exact hdummyClauses t v htborder hvDummy hheight hrankEq
      · have hvDummyF : other.dummy = false := by
          cases hb : other.dummy with
          | true => exact absurd (by rw [hvGetD]; exact hb) hvDummy
          | false => rfl
        have hltBound : leftPos < vPos := by omega
        have hvLtR : vPos < rightPos := by omega
        have hipRule := hip.2 layer hlayerMem leftPos vPos rightPos leftIndex rightIndex v
          hleftPos hvPos hrightPos hltBound hvLtR
          (by rw [hleftGD]; exact hleftBorder) (by rw [hleftPath]; rw [htGetD])
          hleftDummy
          (by rw [hrightGD]; exact hrightBorder) (by rw [hrightPath]; rw [htGetD])
          hrightDummy
          (by rw [hvGetD]; exact hvDummyF)
        have hnp : OrderImpl.nodePath run.coordinateProper v = other.node.clusterPath := by
          unfold OrderImpl.nodePath
          rw [hvGetD]
          simp [hvDummyF]
        rw [hnp] at hipRule
        have hownerIn : owner ∈ proxy.node.clusterPath := mem_of_getLast?_eq_some ownerEq
        have hmemOwner : other.node.clusterPath.contains owner = true := by
          have hm : owner ∈ other.node.clusterPath :=
            List.IsPrefix.mem hownerIn hipRule
          simpa using hm
        have hvBorder0 := (hborderClauses v (by rw [hvGetD]; exact hvDummyF)
          hvnotTop hvnotBottom (by
            intro hc
            rw [hc] at hheight
            omega)).resolve_right
          (fun hb => absurd (by rw [hvGetD] at hb; exact hb) hvNotSide3)
        have hrankLt := hrankClauses t v htborder
          (by rw [hvGetD]; exact hvDummyF) hvBorder0
          owner (by rw [htGetD]; exact ownerEq) (by rw [hvGetD]; exact hmemOwner)
        omega
    · -- vPos = rightPos: v is the right border, of zero height
      exfalso
      have hvEqR : v = rightIndex := by
        rw [hvr] at hvPos
        rw [hrightPos] at hvPos
        exact Option.some.inj hvPos.symm
      subst hvEqR
      have := hside1 v (by rw [hrightGD]; exact hrightBorder)
      omega
    · -- v ordered right of the right border: separation plus overlap force touching
      exfalso
      have hsepR : RouteImpl.leftOf run.proper run.xs rightIndex +
          RouteImpl.nodeW run.proper rightIndex ≤ RouteImpl.leftOf run.proper run.xs v :=
        componentRun_nonproxy_ordered_intervals hgraph hcomp hrun hlayerMem hvr hrightPos
          hvPos hright hv' hrightNotProxy hvNotProxy
      have htouchR : RouteImpl.leftOf run.proper run.xs v =
          RouteImpl.leftOf run.proper run.xs rightIndex +
            RouteImpl.nodeW run.proper rightIndex := by
        have h1 := hoverlap.2
        rw [hrightEq] at h1
        omega
      have hlxR : run.xs.getD rightIndex 0 = run.coordinateXs.getD rightIndex 0 :=
        (componentRun_border_record hrun hright hrightBorder).2
      have heqCR : run.coordinateXs.getD v 0 - run.coordinateXs.getD rightIndex 0 =
          RouteImpl.nodeW run.proper v / 2 +
            (RouteImpl.nodeW run.proper rightIndex -
              RouteImpl.nodeW run.proper rightIndex / 2) := by
        simp only [RouteImpl.leftOf, RouteImpl.xAt, e] at htouchR
        rw [hvx, hlxR] at htouchR
        omega
      have hvPosLen : vPos < layer.length := (List.getElem?_eq_some_iff.mp hvPos).1
      have hrightLen : rightPos < layer.length :=
        (List.getElem?_eq_some_iff.mp hrightPos).1
      cases hym : layer[rightPos + 1]? with
      | none => have := List.getElem?_eq_none_iff.mp hym; omega
      | some y =>
        have hyBound : y < run.coordinateProper.nodes.length :=
          CoordsImpl.layers_mem_lt hrange hlayerMem hym
        cases hyl : run.coordinateProper.nodes[y]? with
        | none => have := List.getElem?_eq_none_iff.mp hyl; omega
        | some yn =>
          have hotRY := ownTitleAnchor_false_of_plain hright hyl
            (by rcases hrightBorder with hb | hb <;> omega)
            (by rcases hrightBorder with hb | hb <;> omega)
            (by rcases hrightBorder with hb | hb <;> omega)
          have hgapRY : min P.nodeGap P.clusterPad ≤
              CoordsImpl.clusterGap P.nodeGap P.clusterPad run.coordinateProper
                rightIndex y :=
            CoordsImpl.clusterGap_ge_min run.coordinateProper rightIndex y hotRY
          have hbalRY := CoordsImpl.cluster_balance_separated hcross layer hlayerMem rightPos
            rightIndex y hrightPos hym
          unfold CoordsImpl.clusterSep CoordsImpl.coordSep CoordsImpl.clusterGap at hbalRY
          rw [hotRY] at hbalRY
          simp only [Bool.false_eq_true, ite_false] at hbalRY
          simp only [e] at hbalRY
          have hcy0 : 0 ≤ CoordsImpl.nodeW run.coordinateProper y :=
            CoordsImpl.nodeW_nonneg hsizes y
          have hcr0 : 0 ≤ CoordsImpl.nodeW run.coordinateProper rightIndex :=
            CoordsImpl.nodeW_nonneg hsizes rightIndex
          have hcv0 : 0 ≤ CoordsImpl.nodeW run.coordinateProper v :=
            CoordsImpl.nodeW_nonneg hsizes v
          rcases Nat.lt_trichotomy (rightPos + 2) vPos with hd | hd | hd
          · -- three segments: balances at both ends plus a zero-pair span
            have hyGt : rightPos + 1 < vPos - 1 := by omega
            cases hum : layer[vPos - 1]? with
            | none => have := List.getElem?_eq_none_iff.mp hum; omega
            | some uu =>
              have huBound : uu < run.coordinateProper.nodes.length :=
                CoordsImpl.layers_mem_lt hrange hlayerMem hum
              cases huul : run.coordinateProper.nodes[uu]? with
              | none => have := List.getElem?_eq_none_iff.mp huul; omega
              | some uun =>
                have hotUV := ownTitleAnchor_false_of_plain_second huul hv'
                  hvNotTop' hvNotBottom' hvNotSide3
                have hgapUV : min P.nodeGap P.clusterPad ≤
                    CoordsImpl.clusterGap P.nodeGap P.clusterPad run.coordinateProper
                      uu v :=
                  CoordsImpl.clusterGap_ge_min run.coordinateProper uu v hotUV
                have hbalUV := CoordsImpl.cluster_balance_separated hcross layer hlayerMem
                  (vPos - 1) uu v hum
                  (by rw [Nat.sub_add_cancel (by omega : 1 ≤ vPos)]; exact hvPos)
                unfold CoordsImpl.clusterSep CoordsImpl.coordSep CoordsImpl.clusterGap
                  at hbalUV
                rw [hotUV] at hbalUV
                simp only [Bool.false_eq_true, ite_false] at hbalUV
                simp only [e] at hbalUV
                have hzero := CoordsImpl.cluster_zero_pairs_separated hcross layer hlayerMem
                  (rightPos + 1) (vPos - 1) y uu hyGt hym hum
                simp only [e] at hzero
                have hcu0 : 0 ≤ CoordsImpl.nodeW run.coordinateProper uu :=
                  CoordsImpl.nodeW_nonneg hsizes uu
                have hgapRY' : 1 ≤ (if CoordsImpl.borderMember run.coordinateProper
                    rightIndex y then P.clusterPad else P.nodeGap) := by
                  have h1 := hgapRY
                  unfold CoordsImpl.clusterGap at h1
                  rw [hotRY] at h1
                  simp only [Bool.false_eq_true, ite_false] at h1
                  omega
                have hgapUV' : 1 ≤ (if CoordsImpl.borderMember run.coordinateProper
                    uu v then P.clusterPad else P.nodeGap) := by
                  have h1 := hgapUV
                  unfold CoordsImpl.clusterGap at h1
                  rw [hotUV] at h1
                  simp only [Bool.false_eq_true, ite_false] at h1
                  omega
                have hh1 := half0 _ hcu0
                have hh2 := half0 _ hcy0
                have hh3 := half0 _ hcr0
                have hh4 := half0 _ hcv0
                omega
          · -- vPos = rightPos + 2: the two pairs share their middle node
            cases hum : layer[vPos - 1]? with
            | none => have := List.getElem?_eq_none_iff.mp hum; omega
            | some uu =>
              have huy : uu = y := by
                rw [← hd] at hum
                simp at hum
                rw [hym] at hum
                exact Option.some.inj hum.symm
              subst huy
              cases huul : run.coordinateProper.nodes[uu]? with
              | none => have := List.getElem?_eq_none_iff.mp huul; omega
              | some uun =>
                have hotUV := ownTitleAnchor_false_of_plain_second huul hv'
                  hvNotTop' hvNotBottom' hvNotSide3
                have hgapUV : min P.nodeGap P.clusterPad ≤
                    CoordsImpl.clusterGap P.nodeGap P.clusterPad run.coordinateProper
                      uu v :=
                  CoordsImpl.clusterGap_ge_min run.coordinateProper uu v hotUV
                have hbalUV := CoordsImpl.cluster_balance_separated hcross layer hlayerMem
                  (vPos - 1) uu v hum
                  (by rw [Nat.sub_add_cancel (by omega : 1 ≤ vPos)]; exact hvPos)
                unfold CoordsImpl.clusterSep CoordsImpl.coordSep CoordsImpl.clusterGap
                  at hbalUV
                rw [hotUV] at hbalUV
                simp only [Bool.false_eq_true, ite_false] at hbalUV
                simp only [e] at hbalUV
                have hgapRY' : 1 ≤ (if CoordsImpl.borderMember run.coordinateProper
                    rightIndex uu then P.clusterPad else P.nodeGap) := by
                  have h1 := hgapRY
                  unfold CoordsImpl.clusterGap at h1
                  rw [hotRY] at h1
                  simp only [Bool.false_eq_true, ite_false] at h1
                  omega
                have hgapUV' : 1 ≤ (if CoordsImpl.borderMember run.coordinateProper
                    uu v then P.clusterPad else P.nodeGap) := by
                  have h1 := hgapUV
                  unfold CoordsImpl.clusterGap at h1
                  rw [hotUV] at h1
                  simp only [Bool.false_eq_true, ite_false] at h1
                  omega
                have hh1 := half0 _ hcy0
                have hh2 := half0 _ hcr0
                have hh3 := half0 _ hcv0
                omega
          · -- vPos = rightPos + 1: single pair (right, v)
            have hveq : vPos = rightPos + 1 := by omega
            rw [hveq] at hvPos
            rw [hym] at hvPos
            have hvy : v = y := Option.some.inj hvPos.symm
            subst hvy
            have hbalRV := CoordsImpl.cluster_balance_separated hcross layer hlayerMem rightPos
              rightIndex v hrightPos hym
            unfold CoordsImpl.clusterSep CoordsImpl.coordSep CoordsImpl.clusterGap at hbalRV
            rw [hotRY] at hbalRV
            simp only [Bool.false_eq_true, ite_false] at hbalRV
            simp only [e] at hbalRV
            rcases hbmR : CoordsImpl.borderMember run.coordinateProper rightIndex v
              with _ | _
            · rw [hbmR] at hbalRV
              simp only [Bool.false_eq_true, ite_false] at hbalRV
              omega
            · simp only [hbmR, ite_true] at hbalRV
              by_cases hvDummy : (run.coordinateProper.nodes.getD v default).dummy = true
              · exact hdummyClauses t v htborder hvDummy hheight hrankEq
              · have hvDummyF : other.dummy = false := by
                  cases hb : other.dummy with
                  | true => exact absurd (by rw [hvGetD]; exact hb) hvDummy
                  | false => rfl
                have hmemOwner := borderMember_contains_right hright hv' hbmR hrightBorder
                  ⟨hvNotSide1, hvNotSide2⟩ hrightOwner
                have hvBorder0 := (hborderClauses v (by rw [hvGetD]; exact hvDummyF)
                  hvnotTop hvnotBottom (by
                    intro hc
                    rw [hc] at hheight
                    omega)).resolve_right
                  (fun hb => absurd (by rw [hvGetD] at hb; exact hb) hvNotSide3)
                have hrankLt := hrankClauses t v htborder
                  (by rw [hvGetD]; exact hvDummyF) hvBorder0
                  owner (by rw [htGetD]; exact ownerEq) (by rw [hvGetD]; exact hmemOwner)
                omega

end Elegant.Layered.PipelineImpl


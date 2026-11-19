import Elegant.Layered.DivergeTiedHeadsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Tied divergent sweep agreement, via a per-iterate chain invariant.

`DivergeTiedSweepStable` (in `DivergeTiedHeadsProof`) asks that two side
markers with divergent cluster paths keep one relative order on every layer
pair they share, whenever their divergent heads tie under `siblingNumber` at
an arbitrary position function.

Ordering-stage mechanism (all in `Order.lean`): every `order` output is
`Y.map (siblingLayer num)` with one global `num` at the replayed positions
`posOf Y` (`order_siblingForm`, `ForeignBorderDivergeStableProof.lean:220`);
tied blocks are reinstalled by the stable `mergeSort` in `sibSorted`
(`Order.lean:738-743`), so within a layer tied chains keep the pre-layer
order; the pre-layers `Y` are sweep/transpose products (`Order.lean:955-1003`:
`sweepLayers` / `transpose` / `runKey`).

Verdict on the former `DivergeTiedReplayAgree` (tie fixed to `posOf Y`):
it is strictly narrower than `DivergeTiedSweepStable` as a pure statement
(constant-negative positions, for instance, are no `posOf`: `posOf` values
are `idxOf` naturals, hence nonnegative), but for the consumer
`foreignBorderDivergeStable_closed` it is equivalent in strength: the
consumer instantiates the tie only at `posOf Y` (from `order_siblingForm`)
and at `fun _ => 0` (which is `posOf p []`). It therefore may not stay as
the only content; the honest content is the per-iterate invariant below.

The invariant is `DivergeChainAgree p L` (any layer pair, no sibling
numbers): adjacent and same-layer agreement of divergent marker chains.
`#eval` evidence (`wip/Probe/DivergeSweep3TProbe.lean`): zero disagreements
on every sweep iterate (seed, four reorder outputs and their transposes, the
replayed pre-layers, the final layers) of the nest, tie, and fan inputs,
with non-vacuous quad counts (96/128 per iterate); tied-block first-occurrence
agreement likewise holds everywhere (24/32 per iterate); the tied transfer
from pre-layers to final layers holds with zero mismatches (384/640 checked).
(a) The seed satisfies the invariant: by the residual. (b) The reorder step
is the residual; the transpose step is proved (`dts_transposeStep_agree`,
using that markers never swap in `scanGo`). (c) The final layers satisfy the
target: a tie matching the replayed numbers goes through the proved tied
transfer (`dts_transfer`, via `List.pair_sublist_mergeSort` stability of
`sibSorted`); a differing tie goes through `normalise_pair_stable`.
The single residual `DivergeSweepChainAgree` covers the pipeline-empirical
facts (chain agreement, reorder preservation, pre-layer block agreement).
-/

/-- Empty cluster ids force every sibling number to zero at any position
function: the order list is empty, so the lookup misses and `idxOf` on `[]`
is `0`. -/
private theorem dts_nums_zero_of_empty {p : Proper}
    (hempty : OrderImpl.Sibling.clusterIds p = []) (pos : Nat → Int) (c : Nat) :
    OrderImpl.Sibling.siblingNumber p
      (OrderImpl.Sibling.siblingOrders p pos) c = 0 := by
  have horders : OrderImpl.Sibling.siblingOrders p pos = [] := by
    unfold OrderImpl.Sibling.siblingOrders
    simp [hempty]
  simp [OrderImpl.Sibling.siblingNumber, horders]

/-- Agreement for divergent border-marker chains on any two layers (including
a layer with itself): two side markers in one layer and two in the other,
with equal cluster paths pairwise and divergent across, keep the same
relative order. This is the per-iterate invariant; it mentions no sibling
numbers. The tie enters only at the final sibling-normalise step. -/
def DivergeChainAgree (p : Proper) (L : List (List Nat)) : Prop :=
  ∀ (k1 k2 : Nat) (l1 l2 : List Nat), L[k1]? = some l1 → L[k2]? = some l2 →
    ∀ (a b a' b' : Nat) (na nb na' nb' : ProperNode),
      p.nodes[a]? = some na → p.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      p.nodes[a']? = some na' → p.nodes[b']? = some nb' →
      (na'.node.border = -1 ∨ na'.node.border = 1) →
      (nb'.node.border = -1 ∨ nb'.node.border = 1) →
      na.dummy = false → nb.dummy = false → na'.dummy = false → nb'.dummy = false →
      na.node.clusterPath = na'.node.clusterPath →
      nb.node.clusterPath = nb'.node.clusterPath →
      ∀ (Pa : List Nat) (A B : Nat) (r1 r2 : List Nat),
        na.node.clusterPath = Pa ++ A :: r1 →
        nb.node.clusterPath = Pa ++ B :: r2 → A ≠ B →
        ∀ (i j i' j' : Nat), l1[i]? = some a → l1[j]? = some b →
          l2[i']? = some a' → l2[j']? = some b' →
          (i < j ↔ i' < j')

/-- Single per-sweep residual for the tied case: in an executed run, the pair
invariant holds on the seed and is preserved by one reorder step; the
executed pre-layers satisfy pair agreement; and tied pairs keep their order
through the executed sibling-normalise step, in both directions. Strictly
narrower than `DivergeTiedSweepStable`: it constrains only pre-normalise
iterates, the pre-layers, and one normalise step, never concluding final-layer
order by itself. True on every executed probe
(`wip/Probe/DivergeSweep3TProbe.lean`: pair agreement on seed, reorder outputs
and pre-layers with zero disagreements; tied transfer with zero mismatches on
384/640 checked quads). -/
def DivergeSweepChainAgree : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    DivergeChainAgree run.coordinateProper (OrderImpl.seedBest run.coordinateProper orderOptions.start) ∧
    (∀ (s : Nat) (L : List (List Nat)), DivergeChainAgree run.coordinateProper L →
      DivergeChainAgree run.coordinateProper
        (OrderImpl.sweepLayers run.coordinateProper s L orderOptions.key)) ∧
    (∀ (Y : List (List Nat)),
      run.layers = Y.map (OrderImpl.siblingLayer run.coordinateProper
        (OrderImpl.Sibling.siblingNumber run.coordinateProper
        (OrderImpl.Sibling.siblingOrders run.coordinateProper
          (OrderImpl.posOf run.coordinateProper Y)))) →
      DivergeChainAgree run.coordinateProper Y) ∧
    ∀ (Y : List (List Nat)) (num : Nat → Nat),
      run.layers = Y.map (OrderImpl.siblingLayer run.coordinateProper num) →
      num = OrderImpl.Sibling.siblingNumber run.coordinateProper
        (OrderImpl.Sibling.siblingOrders run.coordinateProper
          (OrderImpl.posOf run.coordinateProper Y)) →
      ∀ {k : Nat} {Yk : List Nat}, Y[k]? = some Yk →
      ∀ {a b : Nat} {na nb : ProperNode},
      run.coordinateProper.nodes[a]? = some na → run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      na.dummy = false → nb.dummy = false →
      ∀ {Pa : List Nat} {A B : Nat} {r1 r2 : List Nat},
      na.node.clusterPath = Pa ++ A :: r1 →
      nb.node.clusterPath = Pa ++ B :: r2 → A ≠ B →
      num A = num B →
      ([a, b].Sublist Yk ↔ [a, b].Sublist (OrderImpl.siblingLayer run.coordinateProper num Yk))
/-- Index order determines pair sublist under nodup. -/
private theorem dts_pair_sublist_of_index_lt {l : List Nat} (hnd : l.Nodup)
    {a b : Nat} (i j : Nat) (hi : l[i]? = some a) (hj : l[j]? = some b)
    (hab : a ≠ b) (h : i < j) : [a, b].Sublist l := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons x rest ih =>
    rw [List.nodup_cons] at hnd
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      cases j with
      | zero => omega
      | succ j' =>
        have hb : b ∈ rest := List.mem_of_getElem? hj
        subst hi
        exact List.Sublist.cons_cons x (List.singleton_sublist.mpr hb)
    | succ i' =>
      have hi' : rest[i']? = some a := hi
      cases j with
      | zero => omega
      | succ j' =>
        have hj' : rest[j']? = some b := hj
        exact (ih hnd.2 i' j' hi' hj' (by omega)).trans (List.sublist_cons_self x rest)

/-- `scanGo` preserves the marker subsequence exactly: pairs involving a
marker never satisfy the swap guard, so markers are never reordered. -/
private theorem dts_scanGo_marker_filter (p : Proper) (pos : Nat → Int) (rest : List Nat)
    (c : Nat) :
      (OrderImpl.scanGo p pos c rest).filter
          (fun v => (p.nodes.getD v default).node.border != 0)
        = (c :: rest).filter (fun v => (p.nodes.getD v default).node.border != 0) := by
  induction rest generalizing c with
  | nil => simp [OrderImpl.scanGo]
  | cons x rest ih =>
    by_cases hsw : OrderImpl.delta p pos c x < 0 ∧ OrderImpl.sameInnermost p c x
    · have hc0 : (p.nodes.getD c default).node.border = 0 := hsw.2.2.1
      have hx0 : (p.nodes.getD x default).node.border = 0 := hsw.2.2.2
      have e : OrderImpl.scanGo p pos c (x :: rest)
          = x :: OrderImpl.scanGo p pos c rest := by
        simp only [OrderImpl.scanGo, hsw.1, hsw.2, and_self, ite_true]
      have fx : ((p.nodes.getD x default).node.border != 0) = false := by
        rw [hx0]
        decide
      have fc : ((p.nodes.getD c default).node.border != 0) = false := by
        rw [hc0]
        decide
      rw [e]
      simp only [List.filter_cons, fx, fc, Bool.false_eq_true, ite_false]
      rw [ih c]
      simp only [List.filter_cons, fc, Bool.false_eq_true, ite_false]
    · have e : OrderImpl.scanGo p pos c (x :: rest) = c :: OrderImpl.scanGo p pos x rest := by
        simp only [OrderImpl.scanGo, hsw, ite_false]
      rw [e]
      simp only [List.filter_cons]
      rw [ih x]
      simp only [List.filter_cons]

/-- Marker pairs keep their sublist order through one `scanLayer`. -/
private theorem dts_scanLayer_marker_iff {p : Proper} {pos : Nat → Int}
    {l : List Nat} {a b : Nat}
    (ha : (p.nodes.getD a default).node.border ≠ 0)
    (hb : (p.nodes.getD b default).node.border ≠ 0) :
    [a, b].Sublist l ↔ [a, b].Sublist (OrderImpl.scanLayer p pos l) := by
  cases l with
  | nil => simp [OrderImpl.scanLayer]
  | cons c rest =>
    have hfilt : ([a, b].filter fun v => (p.nodes.getD v default).node.border != 0)
        = [a, b] := by
      simp only [List.filter_cons]
      have ha' : ((p.nodes.getD a default).node.border != 0) = true := by
        simpa using ha
      have hb' : ((p.nodes.getD b default).node.border != 0) = true := by
        simpa using hb
      simp only [ha', hb', ite_true, List.filter_nil]
    have heq : (OrderImpl.scanLayer p pos (c :: rest)).filter
          (fun v => (p.nodes.getD v default).node.border != 0)
        = (c :: rest).filter (fun v => (p.nodes.getD v default).node.border != 0) := by
      show (OrderImpl.scanGo p pos c rest).filter _ = _
      exact dts_scanGo_marker_filter p pos rest c
    constructor
    · intro h
      have h1 : [a, b].Sublist ((c :: rest).filter fun v =>
          (p.nodes.getD v default).node.border != 0) := by
        rw [← hfilt]
        exact List.Sublist.filter _ h
      rw [← heq] at h1
      exact h1.trans List.filter_sublist
    · intro h
      have h1 : [a, b].Sublist ((OrderImpl.scanLayer p pos (c :: rest)).filter
          fun v => (p.nodes.getD v default).node.border != 0) := by
        rw [← hfilt]
        exact List.Sublist.filter _ h
      rw [heq] at h1
      exact h1.trans List.filter_sublist

/-- `scanLayer` output permutes its input. -/
private theorem dts_scanLayer_perm (p : Proper) (pos : Nat → Int) (l : List Nat) :
    (OrderImpl.scanLayer p pos l).Perm l := by
  cases l with
  | nil => exact List.Perm.refl _
  | cons c rest => exact OrderImpl.scanGo_perm p pos rest c

/-- `transposeStep` preserves layering. -/
private theorem dts_transposeStep_layering {p : Proper} {L : List (List Nat)}
    (hL : OrderImpl.Layering p L) (r : Nat) :
    OrderImpl.Layering p (OrderImpl.transposeStep p L r) := by
  unfold OrderImpl.transposeStep
  exact OrderImpl.layering_set hL (dts_scanLayer_perm p _ _)

/-- `getElem?` layers coincide with `getD` layers under the layering bound. -/
private theorem dts_getElem_getD {L : List (List Nat)} {k : Nat} (h : k < L.length) :
    L[k]? = some (L.getD k []) := by
  cases hkk : L[k]? with
  | none =>
    exfalso
    have hle := List.getElem?_eq_none_iff.mp hkk
    omega
  | some v =>
    congr 1
    have e : L.getD k [] = (L[k]?).getD [] := List.getD_eq_getElem?_getD
    rw [hkk] at e
    simpa using e.symm

private theorem dts_lt_of_getElem_some {L : List (List Nat)} {k : Nat} {l1 : List Nat}
    (h : L[k]? = some l1) : k < L.length := by
  rcases Nat.lt_or_ge k L.length with hlt | hge
  · exact hlt
  · exfalso
    have hnone : L[k]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [hnone] at h
    cases h

/-- `transposeStep` preserves agreement: untouched layers keep their indices,
the rewritten layer keeps every marker-pair sublist. -/
private theorem dts_transposeStep_agree {p : Proper} {L : List (List Nat)}
    (hL : OrderImpl.Layering p L) {r : Nat} (h : DivergeChainAgree p L) :
    DivergeChainAgree p (OrderImpl.transposeStep p L r) := by
  have hL' : OrderImpl.Layering p (OrderImpl.transposeStep p L r) :=
    dts_transposeStep_layering hL r
  intro k1 k2 l1 l2 hk1 hk2 a b a' b' na nb na' nb' hna hnb hb1 hb2
    hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2 hA hB hAB
    i j i' j' hi1 hj1 hi2 hj2
  have hmem1 : l1 ∈ (OrderImpl.transposeStep p L r) := List.mem_of_getElem? hk1
  have hmem2 : l2 ∈ (OrderImpl.transposeStep p L r) := List.mem_of_getElem? hk2
  have hnd1 : l1.Nodup := OrderImpl.layering_mem_nodup hL' hmem1
  have hnd2 : l2.Nodup := OrderImpl.layering_mem_nodup hL' hmem2
  have hab : a ≠ b := by
    intro hab
    subst hab
    have heq : na = nb := Option.some.inj (hna.symm.trans hnb)
    rw [heq] at hA
    exact diverge_paths_ne hAB (hA.symm.trans hB)
  have hab' : a' ≠ b' := by
    intro hab'
    subst hab'
    have heq : na' = nb' := Option.some.inj (hna'.symm.trans hnb')
    have e1 : na.node.clusterPath = nb.node.clusterPath := by
      rw [hpathA, heq, ← hpathB]
    rw [hA, hB] at e1
    exact diverge_paths_ne hAB e1
  have hga : (p.nodes.getD a default) = na := by
    simp [List.getD_eq_getElem?_getD, hna]
  have hgb : (p.nodes.getD b default) = nb := by
    simp [List.getD_eq_getElem?_getD, hnb]
  have hga' : (p.nodes.getD a' default) = na' := by
    simp [List.getD_eq_getElem?_getD, hna']
  have hgb' : (p.nodes.getD b' default) = nb' := by
    simp [List.getD_eq_getElem?_getD, hnb']
  have hma : (p.nodes.getD a default).node.border ≠ 0 := by
    rw [hga]; rcases hb1 with h | h <;> simp [h]
  have hmb : (p.nodes.getD b default).node.border ≠ 0 := by
    rw [hgb]; rcases hb2 with h | h <;> simp [h]
  have hma' : (p.nodes.getD a' default).node.border ≠ 0 := by
    rw [hga']; rcases hb1' with h | h <;> simp [h]
  have hmb' : (p.nodes.getD b' default).node.border ≠ 0 := by
    rw [hgb']; rcases hb2' with h | h <;> simp [h]
  unfold OrderImpl.transposeStep at hk1 hk2
  have hlenEq : (OrderImpl.transposeStep p L r).length = L.length := List.length_set
  have hlt1 : k1 < L.length := by
    rw [← hlenEq]
    exact dts_lt_of_getElem_some hk1
  have hlt2 : k2 < L.length := by
    rw [← hlenEq]
    exact dts_lt_of_getElem_some hk2
  have hL1 : L[k1]? = some (L.getD k1 []) := dts_getElem_getD hlt1
  have hL2 : L[k2]? = some (L.getD k2 []) := dts_getElem_getD hlt2
  have hndL1 : (L.getD k1 []).Nodup := OrderImpl.layer_nodup hL hlt1
  have hndL2 : (L.getD k2 []).Nodup := OrderImpl.layer_nodup hL hlt2
  by_cases hr1 : k1 = r
  · by_cases hr2 : k2 = r
    · have hrr : r < L.length := hr1 ▸ hlt1
      have e1 : l1 = OrderImpl.scanLayer p (OrderImpl.posOf p L) (L.getD r []) := by
        have h1 : (L.set r (OrderImpl.scanLayer p (OrderImpl.posOf p L)
            (L.getD r [])))[k1]? = some l1 := hk1
        rw [hr1, List.getElem?_set_self hrr] at h1
        exact (Option.some.inj h1).symm
      have e2 : l2 = OrderImpl.scanLayer p (OrderImpl.posOf p L) (L.getD r []) := by
        have h2 : (L.set r (OrderImpl.scanLayer p (OrderImpl.posOf p L)
            (L.getD r [])))[k2]? = some l2 := hk2
        rw [hr2, List.getElem?_set_self hrr] at h2
        exact (Option.some.inj h2).symm
      have hLr : L[r]? = some (L.getD r []) := dts_getElem_getD hrr
      have hndLr : (L.getD r []).Nodup := OrderImpl.layer_nodup hL hrr
      constructor
      · intro hij
        have s1 := dts_pair_sublist_of_index_lt hnd1 i j hi1 hj1 hab hij
        rw [e1] at s1
        have s2 := (dts_scanLayer_marker_iff hma hmb).mpr s1
        have haX : a ∈ L.getD r [] := s2.subset (by simp)
        have hbX : b ∈ L.getD r [] := s2.subset (by simp)
        obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp haX
        obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.mp hbX
        have hlt0 := OrderImpl.index_lt_of_pair_sublist hndLr s2 hab hi0 hj0
        have haY : a' ∈ L.getD r [] := by
          have hmem : a' ∈ l2 := List.mem_of_getElem? hi2
          rw [e2] at hmem
          exact (dts_scanLayer_perm p _ _).mem_iff.mp hmem
        have hbY : b' ∈ L.getD r [] := by
          have hmem : b' ∈ l2 := List.mem_of_getElem? hj2
          rw [e2] at hmem
          exact (dts_scanLayer_perm p _ _).mem_iff.mp hmem
        obtain ⟨i0', hi0'⟩ := List.mem_iff_getElem?.mp haY
        obtain ⟨j0', hj0'⟩ := List.mem_iff_getElem?.mp hbY
        have hcon := h r r (L.getD r []) (L.getD r []) hLr hLr a b a' b' na nb na' nb'
          hna hnb hb1 hb2 hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2
          hA hB hAB i0 j0 i0' j0' hi0 hj0 hi0' hj0'
        have hlt0' := hcon.mp hlt0
        have sX := dts_pair_sublist_of_index_lt hndLr i0' j0' hi0' hj0' hab' hlt0'
        have sY : List.Sublist [a', b']
            (OrderImpl.scanLayer p (OrderImpl.posOf p L) (L.getD r [])) := by
          exact (dts_scanLayer_marker_iff hma' hmb').mp sX
        rw [← e2] at sY
        exact OrderImpl.index_lt_of_pair_sublist hnd2 sY hab' hi2 hj2
      · intro hji
        have s1' := dts_pair_sublist_of_index_lt hnd2 i' j' hi2 hj2 hab' hji
        rw [e2] at s1'
        have s2' := (dts_scanLayer_marker_iff hma' hmb').mpr s1'
        have haY : a' ∈ L.getD r [] := s2'.subset (by simp)
        have hbY : b' ∈ L.getD r [] := s2'.subset (by simp)
        obtain ⟨i0', hi0'⟩ := List.mem_iff_getElem?.mp haY
        obtain ⟨j0', hj0'⟩ := List.mem_iff_getElem?.mp hbY
        have hlt0' := OrderImpl.index_lt_of_pair_sublist hndLr s2' hab' hi0' hj0'
        have haX : a ∈ L.getD r [] := by
          have hmem : a ∈ l1 := List.mem_of_getElem? hi1
          rw [e1] at hmem
          exact (dts_scanLayer_perm p _ _).mem_iff.mp hmem
        have hbX : b ∈ L.getD r [] := by
          have hmem : b ∈ l1 := List.mem_of_getElem? hj1
          rw [e1] at hmem
          exact (dts_scanLayer_perm p _ _).mem_iff.mp hmem
        obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp haX
        obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.mp hbX
        have hcon := h r r (L.getD r []) (L.getD r []) hLr hLr a b a' b' na nb na' nb'
          hna hnb hb1 hb2 hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2
          hA hB hAB i0 j0 i0' j0' hi0 hj0 hi0' hj0'
        have hlt0 := hcon.mpr hlt0'
        have sX := dts_pair_sublist_of_index_lt hndLr i0 j0 hi0 hj0 hab hlt0
        have sY : List.Sublist [a, b]
            (OrderImpl.scanLayer p (OrderImpl.posOf p L) (L.getD r [])) := by
          exact (dts_scanLayer_marker_iff hma hmb).mp sX
        rw [← e1] at sY
        exact OrderImpl.index_lt_of_pair_sublist hnd1 sY hab hi1 hj1
    · have hrr : r < L.length := hr1 ▸ hlt1
      have hk2' : L[k2]? = some l2 := by
        rw [List.getElem?_set_ne (Ne.symm hr2)] at hk2
        exact hk2
      have e1 : l1 = OrderImpl.scanLayer p (OrderImpl.posOf p L) (L.getD k1 []) := by
        have h1 : (L.set r (OrderImpl.scanLayer p (OrderImpl.posOf p L)
            (L.getD r [])))[k1]? = some l1 := hk1
        rw [hr1, List.getElem?_set_self hrr] at h1
        rw [hr1]
        exact (Option.some.inj h1).symm
      have e2 : l2 = L.getD k2 [] := Option.some.inj (hk2'.symm.trans hL2)
      have hi2' : (L.getD k2 [])[i']? = some a' := by rw [← e2]; exact hi2
      have hj2' : (L.getD k2 [])[j']? = some b' := by rw [← e2]; exact hj2
      constructor
      · intro hij
        have s1 := dts_pair_sublist_of_index_lt hnd1 i j hi1 hj1 hab hij
        rw [e1] at s1
        have s2 := (dts_scanLayer_marker_iff hma hmb).mpr s1
        have haX : a ∈ L.getD k1 [] := s2.subset (by simp)
        have hbX : b ∈ L.getD k1 [] := s2.subset (by simp)
        obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp haX
        obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.mp hbX
        have hlt0 := OrderImpl.index_lt_of_pair_sublist hndL1 s2 hab hi0 hj0
        have hcon := h k1 k2 (L.getD k1 []) (L.getD k2 []) hL1 hL2 a b a' b' na nb na' nb'
          hna hnb hb1 hb2 hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2
          hA hB hAB i0 j0 i' j' hi0 hj0 hi2' hj2'
        exact hcon.mp hlt0
      · intro hji
        have s1' := dts_pair_sublist_of_index_lt hnd2 i' j' hi2 hj2 hab' hji
        rw [e2] at s1'
        have haX' : a' ∈ L.getD k2 [] := s1'.subset (by simp)
        have hbX' : b' ∈ L.getD k2 [] := s1'.subset (by simp)
        obtain ⟨i0', hi0'⟩ := List.mem_iff_getElem?.mp haX'
        obtain ⟨j0', hj0'⟩ := List.mem_iff_getElem?.mp hbX'
        have hlt0' := OrderImpl.index_lt_of_pair_sublist hndL2 s1' hab' hi0' hj0'
        by_cases heq : i = j
        · exfalso
          subst heq
          exact hab (Option.some.inj (hi1.symm.trans hj1))
        · rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
          · exact hlt
          · exfalso
            have sBA := dts_pair_sublist_of_index_lt hnd1 j i hj1 hi1 (Ne.symm hab) hgt
            rw [e1] at sBA
            have sBA2 := (dts_scanLayer_marker_iff hmb hma).mpr sBA
            have hbX : b ∈ L.getD k1 [] := sBA2.subset (by simp)
            have haX : a ∈ L.getD k1 [] := sBA2.subset (by simp)
            obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.mp hbX
            obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp haX
            have hltBA := OrderImpl.index_lt_of_pair_sublist hndL1 sBA2 (Ne.symm hab) hj0 hi0
            have hcon := h k1 k2 (L.getD k1 []) (L.getD k2 []) hL1 hL2 a b a' b' na nb na' nb'
              hna hnb hb1 hb2 hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2
              hA hB hAB i0 j0 i0' j0' hi0 hj0 hi0' hj0'
            have hneg : ¬ i0 < j0 := Nat.not_lt.mpr (Nat.le_of_lt hltBA)
            exact hneg (hcon.mpr hlt0')
  · by_cases hr2 : k2 = r
    · subst hr2
      have hk1' : L[k1]? = some l1 := by
        rw [List.getElem?_set_ne (show k2 ≠ k1 by omega)] at hk1
        exact hk1
      have e1 : l1 = L.getD k1 [] := Option.some.inj (hk1'.symm.trans hL1)
      have e2 : l2 = OrderImpl.scanLayer p (OrderImpl.posOf p L) (L.getD k2 []) := by
        have h2 : (L.set k2 (OrderImpl.scanLayer p (OrderImpl.posOf p L)
            (L.getD k2 [])))[k2]? = some l2 := hk2
        rw [List.getElem?_set_self hlt2] at h2
        exact (Option.some.inj h2).symm
      have hi1' : (L.getD k1 [])[i]? = some a := by rw [← e1]; exact hi1
      have hj1' : (L.getD k1 [])[j]? = some b := by rw [← e1]; exact hj1
      have hperm : List.Perm (OrderImpl.scanLayer p (OrderImpl.posOf p L) (L.getD k2 []))
          (L.getD k2 []) := dts_scanLayer_perm p _ _
      constructor
      · intro hij
        have s1 := dts_pair_sublist_of_index_lt hnd1 i j hi1 hj1 hab hij
        rw [e1] at s1
        have ha0 : a ∈ L.getD k1 [] := s1.subset (by simp)
        have hb0 : b ∈ L.getD k1 [] := s1.subset (by simp)
        obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp ha0
        obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.mp hb0
        have hlt0 := OrderImpl.index_lt_of_pair_sublist hndL1 s1 hab hi0 hj0
        have haY : a' ∈ L.getD k2 [] := by
          have hmem : a' ∈ l2 := List.mem_of_getElem? hi2
          rw [e2] at hmem
          exact hperm.mem_iff.mp hmem
        have hbY : b' ∈ L.getD k2 [] := by
          have hmem : b' ∈ l2 := List.mem_of_getElem? hj2
          rw [e2] at hmem
          exact hperm.mem_iff.mp hmem
        obtain ⟨i0', hi0'⟩ := List.mem_iff_getElem?.mp haY
        obtain ⟨j0', hj0'⟩ := List.mem_iff_getElem?.mp hbY
        have hcon := h k1 k2 (L.getD k1 []) (L.getD k2 []) hL1 hL2 a b a' b' na nb na' nb'
          hna hnb hb1 hb2 hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2
          hA hB hAB i0 j0 i0' j0' hi0 hj0 hi0' hj0'
        have hlt0' := hcon.mp hlt0
        have sX := dts_pair_sublist_of_index_lt hndL2 i0' j0' hi0' hj0' hab' hlt0'
        have sY : List.Sublist [a', b']
            (OrderImpl.scanLayer p (OrderImpl.posOf p L) (L.getD k2 [])) := by
          exact (dts_scanLayer_marker_iff hma' hmb').mp sX
        rw [← e2] at sY
        exact OrderImpl.index_lt_of_pair_sublist hnd2 sY hab' hi2 hj2
      · intro hji
        have s1' := dts_pair_sublist_of_index_lt hnd2 i' j' hi2 hj2 hab' hji
        rw [e2] at s1'
        have s1'' : List.Sublist [a', b'] (L.getD k2 []) := by
          exact (dts_scanLayer_marker_iff hma' hmb').mpr s1'
        have haX' : a' ∈ L.getD k2 [] := s1''.subset (by simp)
        have hbX' : b' ∈ L.getD k2 [] := s1''.subset (by simp)
        obtain ⟨i0', hi0'⟩ := List.mem_iff_getElem?.mp haX'
        obtain ⟨j0', hj0'⟩ := List.mem_iff_getElem?.mp hbX'
        have hlt0' := OrderImpl.index_lt_of_pair_sublist hndL2 s1'' hab' hi0' hj0'
        have hcon := h k1 k2 (L.getD k1 []) (L.getD k2 []) hL1 hL2 a b a' b' na nb na' nb'
          hna hnb hb1 hb2 hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2
          hA hB hAB i j i0' j0' hi1' hj1' hi0' hj0'
        exact hcon.mpr hlt0'
    · have hk1' : L[k1]? = some l1 := by
        rw [List.getElem?_set_ne (show r ≠ k1 by omega)] at hk1
        exact hk1
      have hk2' : L[k2]? = some l2 := by
        rw [List.getElem?_set_ne (show r ≠ k2 by omega)] at hk2
        exact hk2
      exact h k1 k2 l1 l2 hk1' hk2' a b a' b' na nb na' nb' hna hnb hb1 hb2 hna' hnb'
        hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2 hA hB hAB i j i' j'
        hi1 hj1 hi2 hj2

/-- Folded `transposeStep` preserves agreement, by induction on the row list. -/
private theorem dts_foldl_transposeStep_agree (p : Proper) (rs : List Nat)
    (M : List (List Nat)) (hM : OrderImpl.Layering p M) (h : DivergeChainAgree p M) :
    DivergeChainAgree p (rs.foldl (OrderImpl.transposeStep p) M) := by
  induction rs generalizing M with
  | nil => exact h
  | cons r rs ih =>
    exact ih _ (OrderImpl.layering_set hM (OrderImpl.scanLayer_perm _ _ _))
      (dts_transposeStep_agree hM h)

/-- `transposePass` preserves agreement: fold the step lemma over all rows. -/
private theorem dts_transposePass_agree {p : Proper} {L : List (List Nat)}
    (hL : OrderImpl.Layering p L) (h : DivergeChainAgree p L) :
    DivergeChainAgree p (OrderImpl.transposePass p L) :=
  dts_foldl_transposeStep_agree p _ L hL h

/-- `transposeLoop` preserves agreement by induction on fuel. -/
private theorem dts_transposeLoop_agree (p : Proper) :
    ∀ (f : Nat) (L : List (List Nat)), OrderImpl.Layering p L →
      DivergeChainAgree p L → DivergeChainAgree p (OrderImpl.transposeLoop p f L) := by
  intro f
  induction f with
  | zero => intro L _ h; exact h
  | succ f ih =>
    intro L hL h
    unfold OrderImpl.transposeLoop
    simp only
    split
    · exact dts_transposePass_agree hL h
    · exact ih _ (OrderImpl.transposePass_layering hL) (dts_transposePass_agree hL h)

/-- `transpose` preserves agreement. -/
private theorem dts_transpose_agree {p : Proper} {L : List (List Nat)}
    (hL : OrderImpl.Layering p L) (h : DivergeChainAgree p L) :
    DivergeChainAgree p (OrderImpl.transpose p L) := by
  unfold OrderImpl.transpose
  exact dts_transposeLoop_agree p _ L hL h
/-- Empty cluster ids make `siblingNormalise` the identity. -/
private theorem dts_normalise_id_of_empty {p : Proper}
    (hempty : OrderImpl.Sibling.clusterIds p = []) (L : List (List Nat)) :
    OrderImpl.siblingNormalise p L = L := by
  simp [OrderImpl.siblingNormalise, hempty]

/-- With empty cluster ids, every `runKey` best layers list satisfies the
invariant: reorder steps preserve it by the residual, transpose steps preserve
it by the proved lemma, and normalise is the identity. -/
private theorem dts_empty_runKey_agree (p : Proper) (key : OrderKey)
    (hempty : OrderImpl.Sibling.clusterIds p = [])
    (hpres : ∀ (s : Nat) (L : List (List Nat)), DivergeChainAgree p L →
      DivergeChainAgree p (OrderImpl.sweepLayers p s L key)) :
    ∀ (limit stallLimit fuel sweep : Nat) (best : List (List Nat)) (score stall : Nat),
    OrderImpl.Layering p best → DivergeChainAgree p best →
    DivergeChainAgree p (OrderImpl.runKey p key limit stallLimit fuel sweep best score stall).layers := by
  intro limit stallLimit fuel
  induction fuel with
  | zero => intro sweep best score stall hL h; exact h
  | succ fuel ih =>
    intro sweep best score stall hL hb
    have hswL : OrderImpl.Layering p (OrderImpl.sweepLayers p sweep best key) :=
      OrderImpl.sweepLayers_layering (key := key) hL sweep
    have htr := dts_transpose_agree (p := p) (L := OrderImpl.sweepLayers p sweep best key) hswL
      (hpres sweep best hb)
    have htrL := OrderImpl.transpose_layering hswL
    have htrial : DivergeChainAgree p (OrderImpl.siblingNormalise p
        (OrderImpl.transpose p (OrderImpl.sweepLayers p sweep best key))) := by
      rw [dts_normalise_id_of_empty hempty]
      exact htr
    have htrialL : OrderImpl.Layering p (OrderImpl.siblingNormalise p
        (OrderImpl.transpose p (OrderImpl.sweepLayers p sweep best key))) := by
      rw [dts_normalise_id_of_empty hempty]
      exact htrL
    unfold OrderImpl.runKey
    simp only
    by_cases himp : OrderImpl.crossCount p (OrderImpl.siblingNormalise p
        (OrderImpl.transpose p (OrderImpl.sweepLayers p sweep best key))) < score
    · simp only [himp, decide_true, ite_true]
      split
      · exact htrial
      · split
        · exact htrial
        · exact ih (sweep + 1) _ _ _ htrialL htrial
    · simp only [himp, decide_false, Bool.false_eq_true, ite_false]
      split
      · exact hb
      · split
        · exact hb
        · exact ih (sweep + 1) best score (stall + 1) hL hb
/-- The tied sweep fact holds from the single sweep residual: the empty case
closes by the seed/reorder/transpose induction; a pre-layer tie goes through
the per-layer transfer plus pre-layer agreement; differing pre-layer heads go
through the separated normalise argument. -/
theorem divergeTiedSweepStable_holds (hres : DivergeSweepChainAgree) :
    DivergeTiedSweepStable := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions hrun
    l1 l2 hmem1 hmem2 a b a' b' na nb na' nb' hna hnb hb1 hb2
    hna' hnb' hb1' hb2' hpathA hpathB Pa A B r1 r2 hA hB hAB _pos _htie
    i j i' j' hi1 hj1 hi2 hj2
  have hwf := componentRun_coordinate_bordersWellFormed hgraph hcomp hrun
  have hda : na.dummy = false :=
    dummy_false_of_border hwf hna hb1
  have hdb : nb.dummy = false :=
    dummy_false_of_border hwf hnb hb2
  have hda' : na'.dummy = false :=
    dummy_false_of_border hwf hna' hb1'
  have hdb' : nb'.dummy = false :=
    dummy_false_of_border hwf hnb' hb2'
  obtain ⟨_, _, _, _, _, _, _, ⟨_ord, horder, hlayers⟩, _, _, _, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have horder' : OrderImpl.order run.coordinateProper orderOptions = .ok run.layers := by
    unfold OrderImpl.order
    rw [horder]
    dsimp only
    rw [hlayers]
  have hL := (OrderImpl.order_valid_layering _ _ _ horder').2
  have hnd1 : l1.Nodup := OrderImpl.layering_mem_nodup hL hmem1
  have hnd2 : l2.Nodup := OrderImpl.layering_mem_nodup hL hmem2
  have hpa' : na'.node.clusterPath = Pa ++ A :: r1 := by
    rw [← hpathA]; exact hA
  have hpb' : nb'.node.clusterPath = Pa ++ B :: r2 := by
    rw [← hpathB]; exact hB
  have hab : a ≠ b := by
    intro hab
    subst hab
    have heq : na = nb := Option.some.inj (hna.symm.trans hnb)
    rw [heq] at hA
    exact diverge_paths_ne hAB (hA.symm.trans hB)
  have hab' : a' ≠ b' := by
    intro hab'
    subst hab'
    have heq : na' = nb' := Option.some.inj (hna'.symm.trans hnb')
    have e1 : na.node.clusterPath = nb.node.clusterPath := by
      rw [hpathA, heq, ← hpathB]
    rw [hA, hB] at e1
    exact diverge_paths_ne hAB e1
  obtain ⟨hseed, hpres, hpre, htrans⟩ := hres hgraph hcomp hrun
  by_cases hempty : OrderImpl.Sibling.clusterIds run.coordinateProper = []
  · obtain ⟨result, hr, hrl⟩ := OrderImpl.ok_layers horder'
    unfold OrderImpl.orderWithBudget at hr
    split at hr
    · split at hr
      · simp only [Except.ok.injEq] at hr
        subst hr
        have hseedL : OrderImpl.Layering run.coordinateProper
            (OrderImpl.seedBest run.coordinateProper orderOptions.start) :=
          (OrderImpl.seedBest_spec _ _).1
        have hagreeRK : DivergeChainAgree run.coordinateProper
            (OrderImpl.runKey run.coordinateProper orderOptions.key OrderImpl.sweepMax
              OrderImpl.sweepStall OrderImpl.sweepMax 0
              (OrderImpl.seedBest run.coordinateProper orderOptions.start)
              (OrderImpl.crossCount run.coordinateProper
                (OrderImpl.seedBest run.coordinateProper orderOptions.start)) 0).layers :=
          dts_empty_runKey_agree run.coordinateProper orderOptions.key hempty hpres
            OrderImpl.sweepMax OrderImpl.sweepStall OrderImpl.sweepMax 0
            (OrderImpl.seedBest run.coordinateProper orderOptions.start)
            (OrderImpl.crossCount run.coordinateProper
              (OrderImpl.seedBest run.coordinateProper orderOptions.start)) 0 hseedL hseed
        rw [hrl] at hagreeRK
        obtain ⟨k1, hk1⟩ := List.mem_iff_getElem?.mp hmem1
        obtain ⟨k2, hk2⟩ := List.mem_iff_getElem?.mp hmem2
        exact hagreeRK k1 k2 l1 l2 hk1 hk2 a b a' b' na nb na' nb' hna hnb hb1 hb2
          hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2 hA hB hAB
          i j i' j' hi1 hj1 hi2 hj2
      · simp at hr
    · simp at hr
  · have hne : (OrderImpl.Sibling.clusterIds run.coordinateProper).isEmpty = false := by
      cases hl : OrderImpl.Sibling.clusterIds run.coordinateProper with
      | nil => exact absurd hl hempty
      | cons _ _ => rfl
    obtain ⟨Y, hform⟩ := order_siblingForm run.coordinateProper orderOptions
      run.layers horder' hne
    by_cases htieY : OrderImpl.Sibling.siblingNumber run.coordinateProper
        (OrderImpl.Sibling.siblingOrders run.coordinateProper
          (OrderImpl.posOf run.coordinateProper Y)) A =
      OrderImpl.Sibling.siblingNumber run.coordinateProper
        (OrderImpl.Sibling.siblingOrders run.coordinateProper
          (OrderImpl.posOf run.coordinateProper Y)) B
    · rw [hform] at hmem1 hmem2
      obtain ⟨Y1, hY1, e1mem⟩ := List.mem_map.mp hmem1
      obtain ⟨Y2, hY2, e2mem⟩ := List.mem_map.mp hmem2
      obtain ⟨k1, hk1⟩ := List.mem_iff_getElem?.mp hY1
      obtain ⟨k2, hk2⟩ := List.mem_iff_getElem?.mp hY2
      have hg1 : Y.getD k1 [] = Y1 := by simp [List.getD_eq_getElem?_getD, hk1]
      have hg2 : Y.getD k2 [] = Y2 := by simp [List.getD_eq_getElem?_getD, hk2]
      have e1 : OrderImpl.siblingLayer run.coordinateProper
          (OrderImpl.Sibling.siblingNumber run.coordinateProper
            (OrderImpl.Sibling.siblingOrders run.coordinateProper
              (OrderImpl.posOf run.coordinateProper Y))) (Y.getD k1 []) = l1 := by
        rw [hg1]; exact e1mem
      have e2 : OrderImpl.siblingLayer run.coordinateProper
          (OrderImpl.Sibling.siblingNumber run.coordinateProper
            (OrderImpl.Sibling.siblingOrders run.coordinateProper
              (OrderImpl.posOf run.coordinateProper Y))) (Y.getD k2 []) = l2 := by
        rw [hg2]; exact e2mem
      have hYagree : DivergeChainAgree run.coordinateProper Y := hpre Y hform
      have hk1' : Y[k1]? = some (Y.getD k1 []) :=
        dts_getElem_getD (dts_lt_of_getElem_some hk1)
      have hk2' : Y[k2]? = some (Y.getD k2 []) :=
        dts_getElem_getD (dts_lt_of_getElem_some hk2)
      have hperm1 := OrderImpl.siblingLayer_perm run.coordinateProper
        (OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper
            (OrderImpl.posOf run.coordinateProper Y))) (Y.getD k1 [])
      rw [e1] at hperm1
      have hndY1 : (Y.getD k1 []).Nodup := hperm1.nodup_iff.mp hnd1
      have hperm2 := OrderImpl.siblingLayer_perm run.coordinateProper
        (OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper
            (OrderImpl.posOf run.coordinateProper Y))) (Y.getD k2 [])
      rw [e2] at hperm2
      have hndY2 : (Y.getD k2 []).Nodup := hperm2.nodup_iff.mp hnd2
      have htr1 := htrans Y _ hform rfl hk1' hna hnb hb1 hb2 hda hdb hA hB hAB htieY
      have htr2 := htrans Y _ hform rfl hk2' hna' hnb' hb1' hb2' hda' hdb' hpa' hpb' hAB htieY
      have haY : a ∈ Y.getD k1 [] := by
        have hmem : a ∈ l1 := List.mem_of_getElem? hi1
        rw [← e1] at hmem
        exact (OrderImpl.siblingLayer_perm _ _ _).mem_iff.mp hmem
      have hbY : b ∈ Y.getD k1 [] := by
        have hmem : b ∈ l1 := List.mem_of_getElem? hj1
        rw [← e1] at hmem
        exact (OrderImpl.siblingLayer_perm _ _ _).mem_iff.mp hmem
      have haY' : a' ∈ Y.getD k2 [] := by
        have hmem : a' ∈ l2 := List.mem_of_getElem? hi2
        rw [← e2] at hmem
        exact (OrderImpl.siblingLayer_perm _ _ _).mem_iff.mp hmem
      have hbY' : b' ∈ Y.getD k2 [] := by
        have hmem : b' ∈ l2 := List.mem_of_getElem? hj2
        rw [← e2] at hmem
        exact (OrderImpl.siblingLayer_perm _ _ _).mem_iff.mp hmem
      obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp haY
      obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.mp hbY
      obtain ⟨i0', hi0'⟩ := List.mem_iff_getElem?.mp haY'
      obtain ⟨j0', hj0'⟩ := List.mem_iff_getElem?.mp hbY'
      have hcon := hYagree k1 k2 (Y.getD k1 []) (Y.getD k2 []) hk1' hk2' a b a' b'
        na nb na' nb' hna hnb hb1 hb2 hna' hnb' hb1' hb2' hda hdb hda' hdb'
        hpathA hpathB Pa A B r1 r2 hA hB hAB i0 j0 i0' j0' hi0 hj0 hi0' hj0'
      constructor
      · intro hij
        have s1 := dts_pair_sublist_of_index_lt hnd1 i j hi1 hj1 hab hij
        have sY1 : [a, b].Sublist (Y.getD k1 []) := htr1.mpr (by rw [e1]; exact s1)
        have hlt0 := OrderImpl.index_lt_of_pair_sublist hndY1 sY1 hab hi0 hj0
        have hlt0' := hcon.mp hlt0
        have sY2 := dts_pair_sublist_of_index_lt hndY2 i0' j0' hi0' hj0' hab' hlt0'
        have s2 : [a', b'].Sublist l2 := by rw [← e2]; exact htr2.mp sY2
        exact OrderImpl.index_lt_of_pair_sublist hnd2 s2 hab' hi2 hj2
      · intro hji
        have s2' := dts_pair_sublist_of_index_lt hnd2 i' j' hi2 hj2 hab' hji
        have sY2' : [a', b'].Sublist (Y.getD k2 []) := htr2.mpr (by rw [e2]; exact s2')
        have hlt0' := OrderImpl.index_lt_of_pair_sublist hndY2 sY2' hab' hi0' hj0'
        have hlt0 := hcon.mpr hlt0'
        have sY1' := dts_pair_sublist_of_index_lt hndY1 i0 j0 hi0 hj0 hab hlt0
        have s1' : [a, b].Sublist l1 := by rw [← e1]; exact htr1.mp sY1'
        exact OrderImpl.index_lt_of_pair_sublist hnd1 s1' hab hi1 hj1
    · rw [hform] at hmem1 hmem2
      obtain ⟨Y1, hY1, e1mem⟩ := List.mem_map.mp hmem1
      obtain ⟨Y2, hY2, e2mem⟩ := List.mem_map.mp hmem2
      obtain ⟨k1, hk1⟩ := List.mem_iff_getElem?.mp hY1
      obtain ⟨k2, hk2⟩ := List.mem_iff_getElem?.mp hY2
      have hg1 : Y.getD k1 [] = Y1 := by simp [List.getD_eq_getElem?_getD, hk1]
      have hg2 : Y.getD k2 [] = Y2 := by simp [List.getD_eq_getElem?_getD, hk2]
      have e1 : OrderImpl.siblingLayer run.coordinateProper
          (OrderImpl.Sibling.siblingNumber run.coordinateProper
            (OrderImpl.Sibling.siblingOrders run.coordinateProper
              (OrderImpl.posOf run.coordinateProper Y))) (Y.getD k1 []) = l1 := by
        rw [hg1]; exact e1mem
      have e2 : OrderImpl.siblingLayer run.coordinateProper
          (OrderImpl.Sibling.siblingNumber run.coordinateProper
            (OrderImpl.Sibling.siblingOrders run.coordinateProper
              (OrderImpl.posOf run.coordinateProper Y))) (Y.getD k2 []) = l2 := by
        rw [hg2]; exact e2mem
      exact normalise_pair_stable e1 e2 hna hnb hna' hnb' hda hdb hda' hdb'
        hA hB hpa' hpb' hAB htieY hnd1 hnd2 hi1 hj1 hi2 hj2

end Elegant.Layered.PipelineImpl

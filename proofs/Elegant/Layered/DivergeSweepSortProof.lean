import Elegant.Layered.DivergeSweepStepProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# One rewritten row: sweep sorting preserves divergent-marker order.

Target: `DivergeSweepStepSortAgree` (in `DivergeSweepStepProof.lean`): one
`sweepStep` (downward `aboveOf` or upward `belowOf` reorder with the executed
key) preserves `DivergeChainAgree` on every layer pair touching the rewritten
row `r`.

TRUTH FIRST (executed runs only):
- `wip/Probe/DivergeStepSortTProbe.lean` rechecks every single `sweepStep` of
  the seed (both directions, all rows, declaration / breadthFirst / median-key /
  reversed starts) restricted to pairs touching `r`: zero mismatches on nest
  (1792 quads), tie (2880), deep4 (3584), zero-size boxes (2880), groups-only
  nesting (384); empty-group and self-loop inputs execute with zero divergent
  pairs (vacuous); the ill-formed input is rejected before `componentRun`
  (recorded, not counted).
- The same probe checks the narrower preservation claim below on every
  rewritten row (sorted-row order vs old-row order for divergent markers):
  zero mismatches (nest 64, tie 80, deep4 128, zero-size 80, groups-only 32
  ordered pairs; vacuous elsewhere).

What is proved here: `divergeSweepStepSortAgree_of_preserve` derives the full
rewritten-layer residual from the strictly narrower single-row preservation
residual `DivergeSweepSortPreserve` (same executed premises; one row, one
divergent pair, no cross-layer conclusion). Both-rewritten layers chain two
preservations through old-row self-agreement; one-sided cases chain one
preservation through the old row's agreement with the untouched layer.

What stays open (ONE public residual): `DivergeSweepSortPreserve`, i.e. one
`sweepStep` keeps the relative order of divergent markers of the rewritten
row. True on every probe iterate (see above); the sort-key analysis
(`constrainedLayer` block keys from executed neighbour positions) is not done
here.
-/

/-- Single-row preservation residual for the rewritten-row fact: in an executed
run, one `sweepStep` keeps the relative order of divergent markers inside the
rewritten row (sorted row vs old row). Strictly narrower than
`DivergeSweepStepSortAgree` (one row and one divergent pair; no layer pairs,
no cross-layer conclusion). True on every probe iterate (see header). -/
def DivergeSweepSortPreserve : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ (L : List (List Nat)), DivergeChainAgree run.coordinateProper L →
    ∀ (r : Nat) (up : Bool),
    ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      na.dummy = false → nb.dummy = false →
      ∀ (Pa : List Nat) (A B : Nat) (r1 r2 : List Nat),
        na.node.clusterPath = Pa ++ A :: r1 →
        nb.node.clusterPath = Pa ++ B :: r2 → A ≠ B →
        ∀ (i j i0 j0 : Nat),
          (OrderImpl.sortLayer run.coordinateProper
            (if up then OrderImpl.belowOf run.coordinateProper
              else OrderImpl.aboveOf run.coordinateProper)
            (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
            orderOptions.key)[i]? = some a →
          (OrderImpl.sortLayer run.coordinateProper
            (if up then OrderImpl.belowOf run.coordinateProper
              else OrderImpl.aboveOf run.coordinateProper)
            (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
            orderOptions.key)[j]? = some b →
          (L.getD r [])[i0]? = some a → (L.getD r [])[j0]? = some b →
          (i < j ↔ i0 < j0)

private theorem dssp_getD_some (L : List (List Nat)) (r : Nat)
    (hr : r < L.length) : L[r]? = some (L.getD r []) := by
  cases h : L[r]? with
  | some x =>
      have hgg := List.getD_eq_getElem?_getD (l := L) (i := r) (a := [])
      rw [h] at hgg
      have hx : L.getD r [] = x := by simpa using hgg
      rw [hx]
  | none =>
      have hsome : L[r]? = some (L[r]) :=
        List.getElem?_eq_some_iff.mpr ⟨hr, rfl⟩
      rw [h] at hsome
      cases hsome

private theorem dssp_set_self_eq (L : List (List Nat)) (r : Nat)
    (s l1 : List Nat) (hr : r < L.length)
    (hk1 : (L.set r s)[r]? = some l1) : l1 = s := by
  have h2 := List.getElem?_set_self (l := L) (i := r) (a := s) hr
  have hss : s = l1 := Option.some.inj (h2.symm.trans hk1)
  exact hss.symm

private theorem dssp_lt_of_set_some (L : List (List Nat)) (r : Nat)
    (s l : List Nat) (h : (L.set r s)[r]? = some l) : r < L.length := by
  by_cases hlt : r < L.length
  · exact hlt
  · have hle : L.length ≤ r := by omega
    have hnone : (L.set r s)[r]? = none :=
      List.getElem?_eq_none (by rw [List.length_set]; exact hle)
    rw [hnone] at h
    cases h

private theorem dssp_preserve_both (hres : DivergeSweepSortPreserve)
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    (L : List (List Nat)) (hL : DivergeChainAgree run.coordinateProper L)
    (r : Nat) (up : Bool)
    (hperm : (OrderImpl.sortLayer run.coordinateProper
      (if up then OrderImpl.belowOf run.coordinateProper
        else OrderImpl.aboveOf run.coordinateProper)
      (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
      orderOptions.key).Perm (L.getD r []))
    (hrL : L[r]? = some (L.getD r []))
    {a b a' b' : Nat} {na nb na' nb' : ProperNode}
    (hna : run.coordinateProper.nodes[a]? = some na)
    (hnb : run.coordinateProper.nodes[b]? = some nb)
    (hb1 : na.node.border = -1 ∨ na.node.border = 1)
    (hb2 : nb.node.border = -1 ∨ nb.node.border = 1)
    (hna' : run.coordinateProper.nodes[a']? = some na')
    (hnb' : run.coordinateProper.nodes[b']? = some nb')
    (hb1' : na'.node.border = -1 ∨ na'.node.border = 1)
    (hb2' : nb'.node.border = -1 ∨ nb'.node.border = 1)
    (hda : na.dummy = false) (hdb : nb.dummy = false)
    (hda' : na'.dummy = false) (hdb' : nb'.dummy = false)
    (hpathA : na.node.clusterPath = na'.node.clusterPath)
    (hpathB : nb.node.clusterPath = nb'.node.clusterPath)
    {Pa : List Nat} {A B : Nat} {r1 r2 : List Nat}
    (hA : na.node.clusterPath = Pa ++ A :: r1)
    (hB : nb.node.clusterPath = Pa ++ B :: r2) (hAB : A ≠ B)
    {i j i' j' : Nat}
    (hi1 : (OrderImpl.sortLayer run.coordinateProper
      (if up then OrderImpl.belowOf run.coordinateProper
        else OrderImpl.aboveOf run.coordinateProper)
      (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
      orderOptions.key)[i]? = some a)
    (hj1 : (OrderImpl.sortLayer run.coordinateProper
      (if up then OrderImpl.belowOf run.coordinateProper
        else OrderImpl.aboveOf run.coordinateProper)
      (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
      orderOptions.key)[j]? = some b)
    (hi2 : (OrderImpl.sortLayer run.coordinateProper
      (if up then OrderImpl.belowOf run.coordinateProper
        else OrderImpl.aboveOf run.coordinateProper)
      (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
      orderOptions.key)[i']? = some a')
    (hj2 : (OrderImpl.sortLayer run.coordinateProper
      (if up then OrderImpl.belowOf run.coordinateProper
        else OrderImpl.aboveOf run.coordinateProper)
      (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
      orderOptions.key)[j']? = some b') :
    (i < j ↔ i' < j') := by
  have memA : a ∈ L.getD r [] :=
    hperm.mem_iff.mp (List.mem_of_getElem? hi1)
  have memB : b ∈ L.getD r [] :=
    hperm.mem_iff.mp (List.mem_of_getElem? hj1)
  have memA' : a' ∈ L.getD r [] :=
    hperm.mem_iff.mp (List.mem_of_getElem? hi2)
  have memB' : b' ∈ L.getD r [] :=
    hperm.mem_iff.mp (List.mem_of_getElem? hj2)
  obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp memA
  obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.mp memB
  obtain ⟨i0', hi0'⟩ := List.mem_iff_getElem?.mp memA'
  obtain ⟨j0', hj0'⟩ := List.mem_iff_getElem?.mp memB'
  have hpa' : na'.node.clusterPath = Pa ++ A :: r1 :=
    hpathA.symm.trans hA
  have hpb' : nb'.node.clusterPath = Pa ++ B :: r2 :=
    hpathB.symm.trans hB
  have g1 := hres hgraph hcomp hrun L hL r up
    a b na nb hna hnb hb1 hb2 hda hdb Pa A B r1 r2 hA hB hAB
    i j i0 j0 hi1 hj1 hi0 hj0
  have g2 := hres hgraph hcomp hrun L hL r up
    a' b' na' nb' hna' hnb' hb1' hb2' hda' hdb' Pa A B r1 r2 hpa' hpb' hAB
    i' j' i0' j0' hi2 hj2 hi0' hj0'
  have g0 := hL r r (L.getD r []) (L.getD r []) hrL hrL
    a b a' b' na nb na' nb' hna hnb hb1 hb2
    hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2
    hA hB hAB i0 j0 i0' j0' hi0 hj0 hi0' hj0'
  exact g1.trans (g0.trans g2.symm)

private theorem dssp_preserve_left (hres : DivergeSweepSortPreserve)
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    (L : List (List Nat)) (hL : DivergeChainAgree run.coordinateProper L)
    (r : Nat) (up : Bool)
    (hperm : (OrderImpl.sortLayer run.coordinateProper
      (if up then OrderImpl.belowOf run.coordinateProper
        else OrderImpl.aboveOf run.coordinateProper)
      (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
      orderOptions.key).Perm (L.getD r []))
    (hrL : L[r]? = some (L.getD r []))
    {k2 : Nat} {l2 : List Nat} (hk2' : L[k2]? = some l2)
    {a b a' b' : Nat} {na nb na' nb' : ProperNode}
    (hna : run.coordinateProper.nodes[a]? = some na)
    (hnb : run.coordinateProper.nodes[b]? = some nb)
    (hb1 : na.node.border = -1 ∨ na.node.border = 1)
    (hb2 : nb.node.border = -1 ∨ nb.node.border = 1)
    (hna' : run.coordinateProper.nodes[a']? = some na')
    (hnb' : run.coordinateProper.nodes[b']? = some nb')
    (hb1' : na'.node.border = -1 ∨ na'.node.border = 1)
    (hb2' : nb'.node.border = -1 ∨ nb'.node.border = 1)
    (hda : na.dummy = false) (hdb : nb.dummy = false)
    (hda' : na'.dummy = false) (hdb' : nb'.dummy = false)
    (hpathA : na.node.clusterPath = na'.node.clusterPath)
    (hpathB : nb.node.clusterPath = nb'.node.clusterPath)
    {Pa : List Nat} {A B : Nat} {r1 r2 : List Nat}
    (hA : na.node.clusterPath = Pa ++ A :: r1)
    (hB : nb.node.clusterPath = Pa ++ B :: r2) (hAB : A ≠ B)
    {i j i' j' : Nat}
    (hi1 : (OrderImpl.sortLayer run.coordinateProper
      (if up then OrderImpl.belowOf run.coordinateProper
        else OrderImpl.aboveOf run.coordinateProper)
      (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
      orderOptions.key)[i]? = some a)
    (hj1 : (OrderImpl.sortLayer run.coordinateProper
      (if up then OrderImpl.belowOf run.coordinateProper
        else OrderImpl.aboveOf run.coordinateProper)
      (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
      orderOptions.key)[j]? = some b)
    (hi2 : l2[i']? = some a') (hj2 : l2[j']? = some b') :
    (i < j ↔ i' < j') := by
  have memA : a ∈ L.getD r [] :=
    hperm.mem_iff.mp (List.mem_of_getElem? hi1)
  have memB : b ∈ L.getD r [] :=
    hperm.mem_iff.mp (List.mem_of_getElem? hj1)
  obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp memA
  obtain ⟨j0, hj0⟩ := List.mem_iff_getElem?.mp memB
  have g1 := hres hgraph hcomp hrun L hL r up
    a b na nb hna hnb hb1 hb2 hda hdb Pa A B r1 r2 hA hB hAB
    i j i0 j0 hi1 hj1 hi0 hj0
  have g0 := hL r k2 (L.getD r []) l2 hrL hk2'
    a b a' b' na nb na' nb' hna hnb hb1 hb2
    hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2
    hA hB hAB i0 j0 i' j' hi0 hj0 hi2 hj2
  exact g1.trans g0

private theorem dssp_preserve_right (hres : DivergeSweepSortPreserve)
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    (L : List (List Nat)) (hL : DivergeChainAgree run.coordinateProper L)
    (r : Nat) (up : Bool)
    (hperm : (OrderImpl.sortLayer run.coordinateProper
      (if up then OrderImpl.belowOf run.coordinateProper
        else OrderImpl.aboveOf run.coordinateProper)
      (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
      orderOptions.key).Perm (L.getD r []))
    (hrL : L[r]? = some (L.getD r []))
    {k1 : Nat} {l1 : List Nat} (hk1' : L[k1]? = some l1)
    {a b a' b' : Nat} {na nb na' nb' : ProperNode}
    (hna : run.coordinateProper.nodes[a]? = some na)
    (hnb : run.coordinateProper.nodes[b]? = some nb)
    (hb1 : na.node.border = -1 ∨ na.node.border = 1)
    (hb2 : nb.node.border = -1 ∨ nb.node.border = 1)
    (hna' : run.coordinateProper.nodes[a']? = some na')
    (hnb' : run.coordinateProper.nodes[b']? = some nb')
    (hb1' : na'.node.border = -1 ∨ na'.node.border = 1)
    (hb2' : nb'.node.border = -1 ∨ nb'.node.border = 1)
    (hda : na.dummy = false) (hdb : nb.dummy = false)
    (hda' : na'.dummy = false) (hdb' : nb'.dummy = false)
    (hpathA : na.node.clusterPath = na'.node.clusterPath)
    (hpathB : nb.node.clusterPath = nb'.node.clusterPath)
    {Pa : List Nat} {A B : Nat} {r1 r2 : List Nat}
    (hA : na.node.clusterPath = Pa ++ A :: r1)
    (hB : nb.node.clusterPath = Pa ++ B :: r2) (hAB : A ≠ B)
    {i j i' j' : Nat}
    (hi1 : l1[i]? = some a) (hj1 : l1[j]? = some b)
    (hi2 : (OrderImpl.sortLayer run.coordinateProper
      (if up then OrderImpl.belowOf run.coordinateProper
        else OrderImpl.aboveOf run.coordinateProper)
      (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
      orderOptions.key)[i']? = some a')
    (hj2 : (OrderImpl.sortLayer run.coordinateProper
      (if up then OrderImpl.belowOf run.coordinateProper
        else OrderImpl.aboveOf run.coordinateProper)
      (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
      orderOptions.key)[j']? = some b') :
    (i < j ↔ i' < j') := by
  have memA' : a' ∈ L.getD r [] :=
    hperm.mem_iff.mp (List.mem_of_getElem? hi2)
  have memB' : b' ∈ L.getD r [] :=
    hperm.mem_iff.mp (List.mem_of_getElem? hj2)
  obtain ⟨i0', hi0'⟩ := List.mem_iff_getElem?.mp memA'
  obtain ⟨j0', hj0'⟩ := List.mem_iff_getElem?.mp memB'
  have hpa' : na'.node.clusterPath = Pa ++ A :: r1 :=
    hpathA.symm.trans hA
  have hpb' : nb'.node.clusterPath = Pa ++ B :: r2 :=
    hpathB.symm.trans hB
  have g2 := hres hgraph hcomp hrun L hL r up
    a' b' na' nb' hna' hnb' hb1' hb2' hda' hdb' Pa A B r1 r2 hpa' hpb' hAB
    i' j' i0' j0' hi2 hj2 hi0' hj0'
  have g0 := hL k1 r l1 (L.getD r []) hk1' hrL
    a b a' b' na nb na' nb' hna hnb hb1 hb2
    hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2
    hA hB hAB i j i0' j0' hi1 hj1 hi0' hj0'
  exact g0.trans g2.symm

/-- Rewritten-layer agreement from single-row preservation: untouched pairs
keep their layers, so both-rewritten layers chain two preservations through
old-row self-agreement and one-sided cases chain one preservation through the
old row's agreement with the untouched layer. -/
theorem divergeSweepStepSortAgree_of_preserve (hres : DivergeSweepSortPreserve) :
    DivergeSweepStepSortAgree := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels
    orderOptions hrun L hL r up
  intro k1 k2 l1 l2 hk1 hk2 hkk
  intro a b a' b' na nb na' nb' hna hnb hb1 hb2
    hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2
    hA hB hAB i j i' j' hi1 hj1 hi2 hj2
  have hperm : (OrderImpl.sortLayer run.coordinateProper
      (if up then OrderImpl.belowOf run.coordinateProper
        else OrderImpl.aboveOf run.coordinateProper)
      (OrderImpl.posOf run.coordinateProper L) (L.getD r [])
      orderOptions.key).Perm (L.getD r []) := by
    unfold OrderImpl.sortLayer
    exact OrderImpl.constrainedLayer_perm _ _ _ _ _
  unfold OrderImpl.sweepStep at hk1 hk2
  by_cases h1 : k1 = r
  · have h1s := h1.symm
    subst h1s
    have hr : r < L.length := dssp_lt_of_set_some L r _ l1 hk1
    have hrL := dssp_getD_some L r hr
    have e1 := dssp_set_self_eq L r _ l1 hr hk1
    subst e1
    by_cases h2 : k2 = r
    · have h2s := h2.symm
      subst h2s
      have e2 := dssp_set_self_eq L r _ l2 hr hk2
      subst e2
      exact dssp_preserve_both hres hgraph hcomp hrun L hL r up
        hperm hrL hna hnb hb1 hb2 hna' hnb' hb1' hb2'
        hda hdb hda' hdb' hpathA hpathB hA hB hAB hi1 hj1 hi2 hj2
    · have hk2' : L[k2]? = some l2 := by
        have hne : r ≠ k2 := fun he => h2 he.symm
        rw [List.getElem?_set_ne hne] at hk2
        exact hk2
      exact dssp_preserve_left hres hgraph hcomp hrun L hL r up
        hperm hrL hk2' hna hnb hb1 hb2 hna' hnb' hb1' hb2'
        hda hdb hda' hdb' hpathA hpathB hA hB hAB hi1 hj1 hi2 hj2
  · rcases hkk with hkr1 | hkr2
    · exact absurd hkr1 h1
    · have hkr2s := hkr2.symm
      subst hkr2s
      have hr : r < L.length := dssp_lt_of_set_some L r _ l2 hk2
      have hrL := dssp_getD_some L r hr
      have e2 := dssp_set_self_eq L r _ l2 hr hk2
      subst e2
      have hk1' : L[k1]? = some l1 := by
        have hne : r ≠ k1 := fun he => h1 he.symm
        rw [List.getElem?_set_ne hne] at hk1
        exact hk1
      exact dssp_preserve_right hres hgraph hcomp hrun L hL r up
        hperm hrL hk1' hna hnb hb1 hb2 hna' hnb' hb1' hb2'
        hda hdb hda' hdb' hpathA hpathB hA hB hAB hi1 hj1 hi2 hj2

end Elegant.Layered.PipelineImpl

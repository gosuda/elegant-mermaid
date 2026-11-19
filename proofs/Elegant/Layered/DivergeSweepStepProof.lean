import Elegant.Layered.DivergeSweepSeedStepProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Single `sweepStep` via the rewritten-layer pair lemma.

Target: `DivergeSweepStepAgree` (in `DivergeSweepSeedStepProof.lean`):
one `sweepStep` (downward `aboveOf` or upward `belowOf` reorder with the
executed key) preserves `DivergeChainAgree`.

TRUTH FIRST (executed runs only):
- Baseline `wip/Probe/DivergeSweepSeedStepTProbe.lean` reports zero
  per-step `steps` mismatches (thousands of quads per input) on nest, tie,
  fan, deep4, interleaved, zero-size, empty-group, self-loop, groups-only,
  and ill-formed inputs (ill-formed rejected before `componentRun`).
- New probe `wip/Probe/DivergeStepAgreeTProbe.lean` rechecks every single
  `sweepStep` of the seed (both directions, all rows) restricted to pairs
  touching the rewritten row (`k1 = r ∨ k2 = r`): nest 1792, tie 2880,
  deep4 3584, zero-size 2880, groups-only 384 quads per candidate with zero
  mismatches; empty-group and self-loop vacuous (0 quads); ill-formed input
  rejected before `componentRun` (recorded, not counted).

What is proved here: `divergeSweepStepAgree_holds` derives the full
single-step residual from the strictly narrower rewritten-layer residual
`DivergeSweepStepSortAgree` (same executed premises, conclusion restricted
to pairs with `k1 = r ∨ k2 = r`). Untouched pairs (`k1 ≠ r ∧ k2 ≠ r`) keep
their layers under `L.set`, so the hypothesis applies directly; the hard
rewritten-layer case is isolated in the residual.

What stays open (ONE public residual): `DivergeSweepStepSortAgree`, i.e. the
sorted layer agrees with every other layer and with itself. True on every
probe iterate; the sort-key analysis (`constrainedLayer` block keys from the
executed neighbour positions) is not done here.
-/

/-- Rewritten-layer residual for the single-step fact: in an executed run,
one `sweepStep` preserves the per-iterate invariant on every layer pair
touching the rewritten row (`k1 = r ∨ k2 = r`). Strictly narrower than
`DivergeSweepStepAgree` (fewer layer pairs; untouched pairs excluded).
True on every probe iterate (see header). -/
def DivergeSweepStepSortAgree : Prop :=
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
    ∀ (k1 k2 : Nat) (l1 l2 : List Nat),
      (OrderImpl.sweepStep run.coordinateProper
        (if up then OrderImpl.belowOf run.coordinateProper
          else OrderImpl.aboveOf run.coordinateProper)
        L r orderOptions.key)[k1]? = some l1 →
      (OrderImpl.sweepStep run.coordinateProper
        (if up then OrderImpl.belowOf run.coordinateProper
          else OrderImpl.aboveOf run.coordinateProper)
        L r orderOptions.key)[k2]? = some l2 →
      (k1 = r ∨ k2 = r) →
      ∀ (a b a' b' : Nat) (na nb na' nb' : ProperNode),
        run.coordinateProper.nodes[a]? = some na →
        run.coordinateProper.nodes[b]? = some nb →
        (na.node.border = -1 ∨ na.node.border = 1) →
        (nb.node.border = -1 ∨ nb.node.border = 1) →
        run.coordinateProper.nodes[a']? = some na' →
        run.coordinateProper.nodes[b']? = some nb' →
        (na'.node.border = -1 ∨ na'.node.border = 1) →
        (nb'.node.border = -1 ∨ nb'.node.border = 1) →
        na.dummy = false → nb.dummy = false →
        na'.dummy = false → nb'.dummy = false →
        na.node.clusterPath = na'.node.clusterPath →
        nb.node.clusterPath = nb'.node.clusterPath →
        ∀ (Pa : List Nat) (A B : Nat) (r1 r2 : List Nat),
          na.node.clusterPath = Pa ++ A :: r1 →
          nb.node.clusterPath = Pa ++ B :: r2 → A ≠ B →
          ∀ (i j i' j' : Nat), l1[i]? = some a → l1[j]? = some b →
            l2[i']? = some a' → l2[j']? = some b' →
            (i < j ↔ i' < j')

/-- Single-step agreement from the rewritten-layer residual: untouched
layer pairs keep their layers under `L.set`, so the hypothesis applies;
rewritten-layer pairs use the residual. -/
theorem divergeSweepStepAgree_holds (hres : DivergeSweepStepSortAgree) :
    DivergeSweepStepAgree := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels
    orderOptions hrun L hL r up
  intro k1 k2 l1 l2 hk1 hk2 a b a' b' na nb na' nb' hna hnb hb1 hb2
    hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2
    hA hB hAB i j i' j' hi1 hj1 hi2 hj2
  by_cases h : k1 = r ∨ k2 = r
  · exact hres hgraph hcomp hrun L hL r up k1 k2 l1 l2 hk1 hk2 h a b
      a' b' na nb na' nb' hna hnb hb1 hb2 hna' hnb' hb1' hb2' hda hdb
      hda' hdb' hpathA hpathB Pa A B r1 r2 hA hB hAB i j i' j' hi1 hj1
      hi2 hj2
  · have h1 : k1 ≠ r := fun he => h (Or.inl he)
    have h2 : k2 ≠ r := fun he => h (Or.inr he)
    have hk1' : L[k1]? = some l1 := by
      unfold OrderImpl.sweepStep at hk1
      rw [List.getElem?_set_ne (Ne.symm h1)] at hk1
      exact hk1
    have hk2' : L[k2]? = some l2 := by
      unfold OrderImpl.sweepStep at hk2
      rw [List.getElem?_set_ne (Ne.symm h2)] at hk2
      exact hk2
    exact hL k1 k2 l1 l2 hk1' hk2' a b a' b' na nb na' nb' hna hnb hb1
      hb2 hna' hnb' hb1' hb2' hda hdb hda' hdb' hpathA hpathB Pa A B r1 r2
      hA hB hAB i j i' j' hi1 hj1 hi2 hj2

end Elegant.Layered.PipelineImpl

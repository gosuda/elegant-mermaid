import Elegant.Layered.ForeignBorderDivergeStableProof
import Elegant.Layered.DivergeHeadsSeparatedProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Tied divergent heads keep their order, modulo one sweep fact.

`ForeignBorderDivergeStable` (in `ForeignBorderEdgesNoncrossingProof`) asks that
two side-border markers with divergent cluster paths keep one relative order on
every layer pair. `foreignBorderDivergeStableSeparated_holds` (in
`ForeignBorderDivergeStableProof`) settles the separated case: both divergent
heads lie in `Sibling.clusterIds` with equal `Sibling.parentOf`.

The exact complement, per pair, is the negation of that premise: for the
divergent decomposition `path_a = Pa ++ A :: r1`, `path_b = Pa ++ B :: r2`
with `A ≠ B`, at least one of `A ∈ clusterIds`, `B ∈ clusterIds`,
`parentOf A = parentOf B` fails. Equivalently the open case is the tied case:
the two heads receive EQUAL sibling numbers, so `normalise_pair_stable`
(which needs `num A ≠ num B`) does not apply.

Mechanism (all in `Order.lean`): `siblingNumber p orders c` is
`((lookup (parentOf p c) orders).getD []).idxOf c` (line 726); absent heads
with equal parents miss the same order list and tie
(`siblingNumber_tie_of_absent` in `DivergeHeadsSeparatedProof`). The final
`order` output is one `siblingNormalise` map
(`order_siblingForm` in `ForeignBorderDivergeStableProof`, lines 220-237):
every layer is `siblingLayer num` of a pre-layer, with one global `num`.
`siblingLayer` sorts block items with `decide (num a ≤ num b)` by a stable
`mergeSort` (`sibSorted`, lines 738-740) and reinstalls them with `place`
(lines 731-736), so tied blocks keep their pre-layer relative order; the
divergent pair is then ordered by the pre-layer (`Y`) order on each layer.
Cross-layer stability of tied pairs is therefore produced by the sweep stage
(`sweepLayers`/`transpose`/`runKey`, lines 951-1003): the pre-layers already
agree on the tied pair.

Probe evidence (`wip/Probe/DivergeTiedTProbe.lean`, two-level nesting with
demoted middle groups `A`,`B`, 6 node boxes, 3 candidates): 0 flips over 512
divergent quads per run with 128 number ties and 0 separated pairs; heads
`(1,5)` both absent from `clusterIds` (`[0,2,6]`) with `parentOf = none` on
both sides, `num = 1 = 1`. The same census on the replayed pre-layers `Y`
also shows 0 flips over 512 quads, and the diagnosed quad has `Y` order equal
to output order. No flip was found in 162 runs across four earlier probe
 families either (see the `ForeignBorderDivergeStableProof` header). Hence
the proved result below: `foreignBorderDivergeStable_tied` for the
absent-heads mechanism, and `foreignBorderDivergeStable_closed` from one named
sweep residual.

Residual elided: the per-layer preservation plus cross-layer `Y` agreement
for tied pairs, i.e. exactly `DivergeTiedSweepStable`.
-/

/-- Ordering-stage residual for the tied case: in an executed run, two side
markers whose cluster paths are divergent keep the same relative order on
every pair of layers they share, provided their divergent heads tie under
`siblingNumber` at some position function. This is strictly narrower than
`ForeignBorderDivergeStable` (tied divergent pairs only: one numeric
equality, no layers or positions beyond the goal's own). Probe evidence:
`wip/Probe/DivergeTiedTProbe.lean` reports 0 flips over 512 divergent quads
per run, all tied with absent heads, and 0 flips on the replayed pre-layers.
-/
def DivergeTiedSweepStable : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
     ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {l1 l2 : List Nat}, l1 ∈ run.layers → l2 ∈ run.layers →
    ∀ {a b a' b' : Nat} {na nb na' nb' : ProperNode},
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      run.coordinateProper.nodes[a']? = some na' →
      run.coordinateProper.nodes[b']? = some nb' →
      (na'.node.border = -1 ∨ na'.node.border = 1) →
      (nb'.node.border = -1 ∨ nb'.node.border = 1) →
      na.node.clusterPath = na'.node.clusterPath →
      nb.node.clusterPath = nb'.node.clusterPath →
      ∀ {Pa : List Nat} {A B : Nat} {r1 r2 : List Nat},
        na.node.clusterPath = Pa ++ A :: r1 →
        nb.node.clusterPath = Pa ++ B :: r2 → A ≠ B →
        ∀ {pos : Nat → Int},
        OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper pos) A =
        OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper pos) B →
        ∀ {i j i' j' : Nat}, l1[i]? = some a → l1[j]? = some b →
          l2[i']? = some a' → l2[j']? = some b' →
          (i < j ↔ i' < j')

/-- Empty cluster ids force every sibling number to zero at any position
function: the order list is empty, so the lookup misses and `idxOf` on `[]`
is `0`. -/
private theorem dtt_nums_zero_of_empty {p : Proper}
    (hempty : OrderImpl.Sibling.clusterIds p = []) (pos : Nat → Int) (c : Nat) :
    OrderImpl.Sibling.siblingNumber p
      (OrderImpl.Sibling.siblingOrders p pos) c = 0 := by
  have horders : OrderImpl.Sibling.siblingOrders p pos = [] := by
    unfold OrderImpl.Sibling.siblingOrders
    simp [hempty]
  simp [OrderImpl.Sibling.siblingNumber, horders]

/-- Tied divergent border markers keep their order: the absent-heads mechanism
(both heads outside `clusterIds` with equal parents) forces a tie at every
position function, and the sweep residual concludes. -/
theorem foreignBorderDivergeStable_tied (hres : DivergeTiedSweepStable)
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
     {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
     {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {l1 l2 : List Nat} (hmem1 : l1 ∈ run.layers) (hmem2 : l2 ∈ run.layers)
    {a b a' b' : Nat} {na nb na' nb' : ProperNode}
    (hna : run.coordinateProper.nodes[a]? = some na)
    (hnb : run.coordinateProper.nodes[b]? = some nb)
    (hb1 : na.node.border = -1 ∨ na.node.border = 1)
    (hb2 : nb.node.border = -1 ∨ nb.node.border = 1)
    (hna' : run.coordinateProper.nodes[a']? = some na')
    (hnb' : run.coordinateProper.nodes[b']? = some nb')
    (hb1' : na'.node.border = -1 ∨ na'.node.border = 1)
    (hb2' : nb'.node.border = -1 ∨ nb'.node.border = 1)
    (hpathA : na.node.clusterPath = na'.node.clusterPath)
    (hpathB : nb.node.clusterPath = nb'.node.clusterPath)
    {Pa : List Nat} {A B : Nat} {r1 r2 : List Nat}
    (hA : na.node.clusterPath = Pa ++ A :: r1)
    (hB : nb.node.clusterPath = Pa ++ B :: r2) (hAB : A ≠ B)
    (hmem : A ∉ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
      B ∉ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
      OrderImpl.Sibling.parentOf run.coordinateProper A =
        OrderImpl.Sibling.parentOf run.coordinateProper B)
    {i j i' j' : Nat} (hi1 : l1[i]? = some a) (hj1 : l1[j]? = some b)
    (hi2 : l2[i']? = some a') (hj2 : l2[j']? = some b') :
    (i < j ↔ i' < j') :=
  hres hgraph hcomp hrun hmem1 hmem2 hna hnb hb1 hb2 hna' hnb' hb1' hb2'
    hpathA hpathB hA hB hAB (pos := fun _ => 0)
    (siblingNumber_tie_of_absent hmem.1 hmem.2.1 hmem.2.2) hi1 hj1 hi2 hj2

/-- The full ordering-stage stability, closed modulo the tied sweep residual:
either every divergent decomposition is separated (apply the separated
theorem), or the divergent heads tie or differ at the executed numbers. -/
theorem foreignBorderDivergeStable_closed (hres : DivergeTiedSweepStable) :
    ForeignBorderDivergeStable := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions hrun
    l1 l2 hmem1 hmem2 a b a' b' na nb na' nb' hna hnb hb1 hb2
    hna' hnb' hb1' hb2' hpathA hpathB hdiv i j i' j' hi1 hj1 hi2 hj2
  have hwf := componentRun_coordinate_bordersWellFormed hgraph hcomp hrun
  have hda : na.dummy = false :=
    dummy_false_of_border hwf hna hb1
  have hdb : nb.dummy = false :=
    dummy_false_of_border hwf hnb hb2
  have hda' : na'.dummy = false :=
    dummy_false_of_border hwf hna' hb1'
  have hdb' : nb'.dummy = false :=
    dummy_false_of_border hwf hnb' hb2'
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have horder' : OrderImpl.order run.coordinateProper orderOptions = .ok run.layers := by
    unfold OrderImpl.order
    rw [horder]
    dsimp only
    rw [hlayers]
  have hL := (OrderImpl.order_valid_layering _ _ _ horder').2
  have hnd1 : l1.Nodup := OrderImpl.layering_mem_nodup hL hmem1
  have hnd2 : l2.Nodup := OrderImpl.layering_mem_nodup hL hmem2
  by_cases hsep : (∀ (Pa : List Nat) (A B : Nat) (r1 r2 : List Nat),
    na.node.clusterPath = Pa ++ A :: r1 →
    nb.node.clusterPath = Pa ++ B :: r2 → A ≠ B →
    A ∈ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
    B ∈ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
    OrderImpl.Sibling.parentOf run.coordinateProper A =
      OrderImpl.Sibling.parentOf run.coordinateProper B)
  · refine foreignBorderDivergeStableSeparated_holds hgraph hcomp hrun hmem1 hmem2
      hna hnb hb1 hb2 hna' hnb' hb1' hb2' hpathA hpathB hdiv ?_ hi1 hj1 hi2 hj2
    intro Pa A B r1 r2 hA hB hAB
    exact hsep Pa A B r1 r2 hA hB hAB
  · obtain ⟨Pa, A, B, r1, r2, hA, hB, hAB⟩ := hdiv
    have hpa' : na'.node.clusterPath = Pa ++ A :: r1 := by
      rw [← hpathA]; exact hA
    have hpb' : nb'.node.clusterPath = Pa ++ B :: r2 := by
      rw [← hpathB]; exact hB
    by_cases hempty : OrderImpl.Sibling.clusterIds run.coordinateProper = []
    · have h0 := fun c => dtt_nums_zero_of_empty hempty (fun _ => 0) c
      have htie : OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper (fun _ => 0)) A =
        OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper (fun _ => 0)) B := by
        rw [h0 A, h0 B]
      exact hres hgraph hcomp hrun hmem1 hmem2 hna hnb hb1 hb2 hna' hnb' hb1'
        hb2' hpathA hpathB hA hB hAB (pos := fun _ => 0) htie hi1 hj1 hi2 hj2
    · have hne : (OrderImpl.Sibling.clusterIds run.coordinateProper).isEmpty = false := by
        cases hl : OrderImpl.Sibling.clusterIds run.coordinateProper with
        | nil => exact absurd hl hempty
        | cons _ _ => rfl
      obtain ⟨Y, hform⟩ := order_siblingForm run.coordinateProper orderOptions
        run.layers horder' hne
      by_cases htie : OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper
            (OrderImpl.posOf run.coordinateProper Y)) A =
        OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper
            (OrderImpl.posOf run.coordinateProper Y)) B
      · exact hres hgraph hcomp hrun hmem1 hmem2 hna hnb hb1 hb2 hna' hnb' hb1'
          hb2' hpathA hpathB hA hB hAB htie hi1 hj1 hi2 hj2
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
          hA hB hpa' hpb' hAB htie hnd1 hnd2 hi1 hj1 hi2 hj2

end Elegant.Layered.PipelineImpl

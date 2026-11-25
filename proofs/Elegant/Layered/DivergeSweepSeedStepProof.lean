import Elegant.Layered.DivergeTiedSweepProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Seed agreement (separated heads) and the single reorder step.

Conjuncts of `DivergeSweepChainAgree` (`DivergeTiedSweepProof.lean`):
(1) the seed satisfies the per-iterate invariant, (2) one reorder step
preserves it, (3) executed pre-layers satisfy it, (4) per-layer tied
transfer through `siblingNormalise`.

TRUTH FIRST (executed runs only):
- Baseline `wip/Probe/DivergeSweep3TProbe.lean` prints per-iterate pair
  agreement with zero disagreements on the nest, tie and fan inputs
  (seed, four reorder outputs and their transposes, replayed pre-layers,
  final layers; 96/128 quads per iterate; tied transfer 384/640 with
  zero mismatches).
- Extended `wip/Probe/DivergeSweepSeedStepTProbe.lean` adds the median-key
  candidate (cand 3), the reversed start (cand 4), a four-level nesting,
  and degenerate inputs (zero-size fixed boxes, an empty group, a
  self-loop, groups-only nesting, an ill-formed input), plus per-step
  `steps` agreement for every single `sweepStep` of sweeps 0-3.
  Command: `lake env lean wip/Probe/DivergeSweepSeedStepTProbe.lean`.
  Extended results: seed/reorder/transpose/pre-layer/final iterates agree
  with zero disagreements on every succeeding input; per-step checks
  report zero mismatches (thousands of quads per input); the ill-formed
  input is rejected before `componentRun` (recorded, not counted).
  Head census (`seedSepTied`, separated vs tied divergent pairs in the
  seed): nest/tie/fan/deep4/interleaved/zero all tied (sep=0; 24, 32 or
  56 tied) and all agreeing; groups-only all separated (sep=12, tied=0)
  and all agreeing. Interleaved child declaration does not flip block
  order between layers.
  No executed witness refutes the seed invariant or the reorder step:
  block order never differs between two layers after one reorder.

(1) is proved here for separated divergent heads (both heads in
`Sibling.clusterIds` with equal `parentOf`): both seed layers order the
pair by the same global sibling numbers (`siblingNumber_ne` plus
`siblingLayer_pair_general`), independent of the pre-layer order.
Non-vacuous on probes: the groups-only nesting reports 32 agreeing pairs
with zero tied blocks, i.e. all separated.
The tied-heads case remains open outside framed inputs.
`DivergeSweepStepAgree` can fail during an actual sweep, as shown by
`wip/Probe/DivergeLayeredSweepCounterexample.lean`.
`divergeStepAgree_holds` lifts that assumption to full sweeps.
-/

/-- Single-step preservation assumption. An executed sweep can violate it. -/
def DivergeSweepStepAgree : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ (L : List (List Nat)), DivergeChainAgree run.coordinateProper L →
    ∀ (r : Nat) (up : Bool), DivergeChainAgree run.coordinateProper
      (OrderImpl.sweepStep run.coordinateProper
        (if up then OrderImpl.belowOf run.coordinateProper
          else OrderImpl.aboveOf run.coordinateProper)
        L r orderOptions.key)

/-- Folded `sweepStep`s preserve the invariant, from the single-step
residual. -/
private theorem dsst_foldl_sweepStep_agree (p : Proper) (nb : Nat → List Nat)
    (key : OrderKey) (f : Nat → Nat) (rs : List Nat) (M : List (List Nat))
    (h : DivergeChainAgree p M)
    (hstep : ∀ (L : List (List Nat)), DivergeChainAgree p L → ∀ (r : Nat),
      DivergeChainAgree p (OrderImpl.sweepStep p nb L r key)) :
    DivergeChainAgree p
      (rs.foldl (fun M k => OrderImpl.sweepStep p nb M (f k) key) M) := by
  induction rs generalizing M with
  | nil => exact h
  | cons r rs ih => exact ih _ (hstep M h (f r))

/-- Conjunct (2) from the single-step residual: full sweeps preserve the
invariant by fold induction over the row ranges. -/
theorem divergeStepAgree_holds (hres : DivergeSweepStepAgree)
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    (s : Nat) (L : List (List Nat))
    (hL : DivergeChainAgree run.coordinateProper L) :
    DivergeChainAgree run.coordinateProper
      (OrderImpl.sweepLayers run.coordinateProper s L orderOptions.key) := by
  have hstepE : ∀ (L : List (List Nat)), DivergeChainAgree run.coordinateProper L →
      ∀ (r : Nat), DivergeChainAgree run.coordinateProper
        (OrderImpl.sweepStep run.coordinateProper (OrderImpl.aboveOf run.coordinateProper)
          L r orderOptions.key) :=
    fun L hL r => hres hgraph hcomp hrun L hL r false
  have hstepB : ∀ (L : List (List Nat)), DivergeChainAgree run.coordinateProper L →
      ∀ (r : Nat), DivergeChainAgree run.coordinateProper
        (OrderImpl.sweepStep run.coordinateProper (OrderImpl.belowOf run.coordinateProper)
          L r orderOptions.key) :=
    fun L hL r => hres hgraph hcomp hrun L hL r true
  unfold OrderImpl.sweepLayers
  split
  · exact dsst_foldl_sweepStep_agree _ _ _ _ _ L hL hstepE
  · exact dsst_foldl_sweepStep_agree _ _ _ _ _ L hL hstepB
/-- Conjunct (1) for separated divergent heads: the seed satisfies the
per-iterate invariant whenever the two divergent heads both belong to
`Sibling.clusterIds` with equal `parentOf`. Both seed layers place the
pair in the order of the same global sibling numbers, so the two layers
agree. The tied-heads half stays open (seed analogues of conjuncts
(3, 4)). -/
theorem divergeSeedAgree_holds
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {k1 k2 : Nat} {l1 l2 : List Nat}
    (hk1 : (OrderImpl.seedBest run.coordinateProper orderOptions.start)[k1]? = some l1)
    (hk2 : (OrderImpl.seedBest run.coordinateProper orderOptions.start)[k2]? = some l2)
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
    (hAhead : A ∈ OrderImpl.Sibling.clusterIds run.coordinateProper)
    (hBhead : B ∈ OrderImpl.Sibling.clusterIds run.coordinateProper)
    (hpar : OrderImpl.Sibling.parentOf run.coordinateProper A =
      OrderImpl.Sibling.parentOf run.coordinateProper B)
    {i j i' j' : Nat} (hi1 : l1[i]? = some a) (hj1 : l1[j]? = some b)
    (hi2 : l2[i']? = some a') (hj2 : l2[j']? = some b') :
    (i < j ↔ i' < j') := by
  have hwf := componentRun_coordinate_bordersWellFormed hgraph hcomp hrun
  have hda : na.dummy = false := dummy_false_of_border hwf hna hb1
  have hdb : nb.dummy = false := dummy_false_of_border hwf hnb hb2
  have hda' : na'.dummy = false := dummy_false_of_border hwf hna' hb1'
  have hdb' : nb'.dummy = false := dummy_false_of_border hwf hnb' hb2'
  have hne : (OrderImpl.Sibling.clusterIds run.coordinateProper).isEmpty = false := by
    cases hl : OrderImpl.Sibling.clusterIds run.coordinateProper with
    | nil => simp [hl] at hAhead
    | cons _ _ => rfl
  obtain ⟨Y, hform⟩ := seedBest_siblingForm run.coordinateProper orderOptions.start hne
  have hL : OrderImpl.Layering run.coordinateProper
      (OrderImpl.seedBest run.coordinateProper orderOptions.start) :=
    (OrderImpl.seedBest_spec _ _).1
  have hmem1 : l1 ∈ OrderImpl.seedBest run.coordinateProper orderOptions.start :=
    List.mem_of_getElem? hk1
  have hmem2 : l2 ∈ OrderImpl.seedBest run.coordinateProper orderOptions.start :=
    List.mem_of_getElem? hk2
  have hnd1 : l1.Nodup := OrderImpl.layering_mem_nodup hL hmem1
  have hnd2 : l2.Nodup := OrderImpl.layering_mem_nodup hL hmem2
  rw [hform] at hmem1 hmem2
  obtain ⟨Y1, hY1mem, e1mem⟩ := List.mem_map.mp hmem1
  obtain ⟨Y2, hY2mem, e2mem⟩ := List.mem_map.mp hmem2
  obtain ⟨j1, hq1⟩ := List.mem_iff_getElem?.mp hY1mem
  obtain ⟨j2, hq2⟩ := List.mem_iff_getElem?.mp hY2mem
  have hg1 : Y.getD j1 [] = Y1 := by simp [List.getD_eq_getElem?_getD, hq1]
  have hg2 : Y.getD j2 [] = Y2 := by simp [List.getD_eq_getElem?_getD, hq2]
  have e1 := e1mem
  rw [← hg1] at e1
  have e2 := e2mem
  rw [← hg2] at e2
  have hnum := OrderImpl.siblingNumber_ne run.coordinateProper
    (OrderImpl.posOf run.coordinateProper Y) hAhead hBhead hAB hpar
  have memA : a ∈ Y.getD j1 [] := by
    have ha : a ∈ l1 := List.mem_of_getElem? hi1
    rw [← e1] at ha
    exact (OrderImpl.siblingLayer_perm _ _ _).mem_iff.mp ha
  have memB : b ∈ Y.getD j1 [] := by
    have hb : b ∈ l1 := List.mem_of_getElem? hj1
    rw [← e1] at hb
    exact (OrderImpl.siblingLayer_perm _ _ _).mem_iff.mp hb
  have memA' : a' ∈ Y.getD j2 [] := by
    have ha : a' ∈ l2 := List.mem_of_getElem? hi2
    rw [← e2] at ha
    exact (OrderImpl.siblingLayer_perm _ _ _).mem_iff.mp ha
  have memB' : b' ∈ Y.getD j2 [] := by
    have hb : b' ∈ l2 := List.mem_of_getElem? hj2
    rw [← e2] at hb
    exact (OrderImpl.siblingLayer_perm _ _ _).mem_iff.mp hb
  have hpa' : na'.node.clusterPath = Pa ++ A :: r1 := by
    rw [← hpathA]; exact hA
  have hpb' : nb'.node.clusterPath = Pa ++ B :: r2 := by
    rw [← hpathB]; exact hB
  have npa : OrderImpl.nodePath run.coordinateProper a = Pa ++ A :: r1 :=
    (OrderImpl.nodePath_of_node hna hda).trans hA
  have npb : OrderImpl.nodePath run.coordinateProper b = Pa ++ B :: r2 :=
    (OrderImpl.nodePath_of_node hnb hdb).trans hB
  have npa' : OrderImpl.nodePath run.coordinateProper a' = Pa ++ A :: r1 :=
    (OrderImpl.nodePath_of_node hna' hda').trans hpa'
  have npb' : OrderImpl.nodePath run.coordinateProper b' = Pa ++ B :: r2 :=
    (OrderImpl.nodePath_of_node hnb' hdb').trans hpb'
  have hab : a ≠ b := by
    intro h
    subst h
    have hnn : na = nb := Option.some.inj (hna.symm.trans hnb)
    rw [hnn] at hA
    exact diverge_paths_ne hAB (hA.symm.trans hB)
  have hab' : a' ≠ b' := by
    intro h
    subst h
    have hnn : na' = nb' := Option.some.inj (hna'.symm.trans hnb')
    have e1 : na.node.clusterPath = nb.node.clusterPath := by
      rw [hpathA, hnn, ← hpathB]
    rw [hA, hB] at e1
    exact diverge_paths_ne hAB e1
  rcases Nat.lt_or_gt_of_ne hnum with hlt | hgt
  · have s1 : [a, b].Sublist l1 := by
      rw [← e1]
      exact siblingLayer_pair_general memA memB npa npb hAB hlt
    have s2 : [a', b'].Sublist l2 := by
      rw [← e2]
      exact siblingLayer_pair_general memA' memB' npa' npb' hAB hlt
    have g1 := OrderImpl.index_lt_of_pair_sublist hnd1 s1 hab hi1 hj1
    have g2 := OrderImpl.index_lt_of_pair_sublist hnd2 s2 hab' hi2 hj2
    exact ⟨fun _ => g2, fun _ => g1⟩
  · have s1 : [b, a].Sublist l1 := by
      rw [← e1]
      exact siblingLayer_pair_general memB memA npb npa (Ne.symm hAB) hgt
    have s2 : [b', a'].Sublist l2 := by
      rw [← e2]
      exact siblingLayer_pair_general memB' memA' npb' npa' (Ne.symm hAB) hgt
    have g1 := OrderImpl.index_lt_of_pair_sublist hnd1 s1 (Ne.symm hab) hj1 hi1
    have g2 := OrderImpl.index_lt_of_pair_sublist hnd2 s2 (Ne.symm hab') hj2 hi2
    exact ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

end Elegant.Layered.PipelineImpl

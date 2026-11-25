 import Elegant.Layered.ForeignBorderDivergeStableProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
 # Divergent heads: refuted residuals and the executed tie mechanism.

 Two candidate residuals for `ForeignBorderDivergeStable` are deleted because
 both are false. `DivergeHeadsSeparated` (formerly in
 `ForeignBorderDivergeStableProof`) quantified over arbitrary `Proper` values:
 two `-1` markers with paths `[5, 3]` and `[7]` refute it (`P = []`, `A = 5`,
 `B = 7`: no `-1` path ends at the interior head `5`, so the membership
 conclusion fails by evaluation). It is also false on executed runs: demoting
 an intermediate group via `fixedSizes` removes its exact markers, so
 divergent heads can sit outside `Sibling.clusterIds`. The replayed-number
 residual `DivergeNumsDistinct` is likewise false on executed runs:
 `wip/Probe/DivergeFanProbe.lean` computes the true replayed numbers and finds
 every demoted divergent pair tied (200 of 200 divergent pairs per run, both
 heads absent from `clusterIds`, `separated = 0` throughout; e.g. heads
 `(1, 6)` at number `1` with `parentOf = none` on both sides).

 What remains true is proved below: absent heads with equal parents tie
 (`siblingNumber_tie_of_absent`), the exact mechanism seen on executed runs.
 The separated case of order stability is proved with no residual as
 `foreignBorderDivergeStableSeparated_holds` in
 `ForeignBorderDivergeStableProof`. The unconditional
 `ForeignBorderDivergeStable` is open: no flip was found on any executed
 adversarial sample (see that file's probe census), and the cross-layer
 tie-break is unproved. The file contains no forbidden constructs.
 -/
 /-- Absent heads with equal parents tie: both miss the same order list, so
 both `idxOf` return its length. This is the executed tie mechanism behind the
 demoted-intermediate probes (`DivergeFanProbe`, `DivergeNestProbe`): demoted
 heads sit outside `clusterIds` with `parentOf = none`, and every demoted
 divergent pair ties on the true replayed numbers. -/
 theorem siblingNumber_tie_of_absent {p : Proper} {pos : Nat → Int} {A B : Nat}
     (hA : A ∉ OrderImpl.Sibling.clusterIds p)
     (hB : B ∉ OrderImpl.Sibling.clusterIds p)
     (hpar : OrderImpl.Sibling.parentOf p A = OrderImpl.Sibling.parentOf p B) :
     OrderImpl.Sibling.siblingNumber p (OrderImpl.Sibling.siblingOrders p pos) A =
       OrderImpl.Sibling.siblingNumber p (OrderImpl.Sibling.siblingOrders p pos) B := by
   unfold OrderImpl.Sibling.siblingNumber
   rw [hpar]
   by_cases hmem : OrderImpl.Sibling.parentOf p B ∈
       ((OrderImpl.Sibling.clusterIds p).map (OrderImpl.Sibling.parentOf p)).eraseDups
   · obtain ⟨K, hK, hKperm⟩ : ∃ K, List.lookup (OrderImpl.Sibling.parentOf p B)
         (OrderImpl.Sibling.siblingOrders p pos) = some K ∧
         K.Perm ((OrderImpl.Sibling.clusterIds p).filter fun c =>
           OrderImpl.Sibling.parentOf p c == OrderImpl.Sibling.parentOf p B) :=
       ⟨_, OrderImpl.lookup_map_pair _ _ _ hmem, OrderImpl.kahnOrder_perm _ _ _ _ (Nat.le_refl _)⟩
     have hAK : A ∉ K := fun hAK => hA ((List.mem_filter.mp (hKperm.mem_iff.mp hAK)).1)
     have hBK : B ∉ K := fun hBK => hB ((List.mem_filter.mp (hKperm.mem_iff.mp hBK)).1)
     rw [hK]
     simp only [Option.getD_some]
     rw [List.idxOf_eq_length hAK, List.idxOf_eq_length hBK]
   · have hkeys : (OrderImpl.Sibling.siblingOrders p pos).map Prod.fst =
         ((OrderImpl.Sibling.clusterIds p).map (OrderImpl.Sibling.parentOf p)).eraseDups := by
       unfold OrderImpl.Sibling.siblingOrders
       dsimp only
       rw [List.map_map]
       apply List.map_id''
       intro x
       rfl
     have hnone : List.lookup (OrderImpl.Sibling.parentOf p B)
         (OrderImpl.Sibling.siblingOrders p pos) = none := by
       rw [List.lookup_eq_none_iff]
       intro q hq
       have hq1 : q.1 ∈ ((OrderImpl.Sibling.clusterIds p).map
           (OrderImpl.Sibling.parentOf p)).eraseDups := by
         rw [← hkeys]
         exact List.mem_map.mpr ⟨q, hq, rfl⟩
       cases hb : (OrderImpl.Sibling.parentOf p B != q.1) with
       | true => rfl
       | false =>
         have heq : OrderImpl.Sibling.parentOf p B = q.1 :=
           bne_eq_false_iff_eq.mp hb
         exact absurd (heq.symm ▸ hq1) hmem
     simp [hnone]

 end Elegant.Layered.PipelineImpl

import Elegant.Layered.RegionC8aGroupPlain

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem sumWidthsNonneg (width : Nat → Int) (hwidth : ∀ k, 0 ≤ width k)
    (children : List Nat) : 0 ≤ (children.map width).sum := by
  induction children with
  | nil => simp
  | cons first rest ih => simpa only [List.map_cons, List.sum_cons] using Int.add_nonneg (hwidth first) ih

private theorem childPrefixWidthLe (width : Nat → Int) (hwidth : ∀ k, 0 ≤ width k)
    {children : List Nat} {child i : Nat} (hi : children[i]? = some child) :
    ((children.take i).map width).sum + width child ≤ (children.map width).sum := by
  induction children generalizing i with
  | nil => simp at hi
  | cons first rest ih =>
    cases i with
    | zero =>
      have heq : first = child := Option.some.inj hi
      subst child
      have ht := sumWidthsNonneg width hwidth rest
      simp only [List.take_zero, List.map_nil, List.sum_nil, Int.zero_add,
        List.map_cons, List.sum_cons]
      omega
    | succ i =>
      have ht := ih (show rest[i]? = some child from hi)
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

/-- The reserved frame interval (excluding its loop strip) leaves strict room
around its own bucket and each child's entire allocated interval. This follows
from checked execution even if a member or child width is zero. -/
theorem RegionCrossAllocationStages.active_directAllocationInsets {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {o : Options} {orderOptions : OrderOptions} {rm : ComponentRegions}
    {p : Proper} {minimum : RegionConstraints} {layers : List (List Nat)}
    {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg' labels p minimum layers run.layers
      run.coordinateXs reserved run.coordinateProper)
    (hparams : checkedParams o.profile inp.kind = .ok P)
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm))
    (hmin : constrainR rm P p = .ok minimum) :
    ∀ g < rm.clusters.length,
      let pl := stages.placement
      let a := stages.allocation
      let left := a.lefts.getD g 0
      let right := left + a.widths.getD g 0 - pl.buckets.loopWidth.getD g 0
      let bucketLeft := left + regionInsetOf P
      left < bucketLeft ∧ bucketLeft + pl.buckets.widths.getD g 0 < right ∧
      ∀ {k child : Nat}, (pl.children.getD g [])[k]? = some child →
        left < a.lefts.getD child 0 ∧ a.lefts.getD child 0 + a.widths.getD child 0 < right := by
  have hp := checkedParams_clusterPad_nonneg hparams
  have hb := checkedParams_clusterBorderW_ge_one hparams
  have hinset : 0 < regionInsetOf P := by unfold regionInsetOf; omega
  obtain ⟨hown, hlane, hloop⟩ := componentRunR_active_bucket_signs hrun stages
  have hwEq : stages.allocation.widths = reserveWidths stages.placement P :=
    groupPlain_allocation_width_eq stages.hAllocation
  have hw (i : Nat) : 0 ≤ stages.allocation.widths.getD i 0 := by
    rw [hwEq]
    exact reserveWidths_nonnegative (pl := stages.placement) (P := P)
      (Int.le_of_lt hinset) hown hlane hloop i
  have hparents := activeRegion_parent_count hactive
  intro g hg
  have hgPl : g < stages.placement.rm.clusters.length := by
    rw [stages.hPlacement]
    exact hg
  obtain ⟨_, _, horder, hlast, hread⟩ := (stages.reservation_order hparents hmin).2 g
    (Nat.le_of_lt hg)
  have hroom := reserveWidths_room_from_last_writes (pl := stages.placement) (P := P)
    horder hgPl hlast hread
  dsimp only at hroom ⊢
  rw [← hwEq] at hroom
  have hsum := sumWidthsNonneg (fun c => stages.allocation.widths.getD c 0) hw
    (stages.placement.children.getD g [])
  have hlanes := hlane g
  refine ⟨by omega, by omega, ?_⟩
  intro k child hchild
  have howned := hown g
  have hleft := stages.childBudget_left_from_allocation hactive hmin (Nat.le_of_lt hg) hchild
  rw [ite_eq_right (Nat.ne_of_lt hg), ← hwEq] at hleft
  have hprefix := sumWidthsNonneg (fun c => stages.allocation.widths.getD c 0) hw
    ((stages.placement.children.getD g []).take k)
  have htotal := childPrefixWidthLe (fun c => stages.allocation.widths.getD c 0) hw hchild
  rw [hleft]
  exact ⟨by omega, by omega⟩

theorem componentRunR_active_directAllocationInsets {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {o : Options} {orderOptions : OrderOptions} {rm : ComponentRegions}
    (hparams : checkedParams o.profile inp.kind = .ok P)
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    (hactive : newComponentRegions (some s) P inp cg = .ok (some rm)) :
    ∃ (p : Proper) (minimum : RegionConstraints) (ord : OrderResult) (reserved : List (Option Int)),
      ∃ stages : RegionCrossAllocationStages P rm cg' labels p minimum ord.layers run.layers
        run.coordinateXs reserved run.coordinateProper,
      ∀ g < rm.clusters.length,
        let pl := stages.placement
        let a := stages.allocation
        let left := a.lefts.getD g 0
        let right := left + a.widths.getD g 0 - pl.buckets.loopWidth.getD g 0
        let bucketLeft := left + regionInsetOf P
        left < bucketLeft ∧ bucketLeft + pl.buckets.widths.getD g 0 < right ∧
        ∀ {k child : Nat}, (pl.children.getD g [])[k]? = some child →
          left < a.lefts.getD child 0 ∧ a.lefts.getD child 0 + a.widths.getD child 0 < right := by
  obtain ⟨_, _, _, p, minimum, ord, reserved, _, _, _, _, _, hmin, _, ⟨stages⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  exact ⟨p, minimum, ord, reserved, stages, stages.active_directAllocationInsets hparams hrun
    hactive hmin⟩


end Elegant.Layered.PipelineImpl


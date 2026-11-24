import Elegant.Layered.RegionActiveOrderProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem bucketSetAtLength {α : Type} (xs : List α) (i : Nat) (a : α) :
    (setAt xs i a).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => cases i <;> simp [setAt, ih]

private theorem bucketSetAtGetD {α : Type} (xs : List α) (i j : Nat) (a d : α) :
    (setAt xs i a).getD j d = if j = i ∧ i < xs.length then a else xs.getD j d := by
  induction xs generalizing i j with
  | nil => simp [setAt]
  | cons x xs ih =>
    cases i with
    | zero => cases j <;> simp [setAt]
    | succ i =>
      cases j with
      | zero => simp [setAt]
      | succ j => simpa [setAt, List.getD_cons_succ] using ih i j

private theorem bucketGetDAgrees {α : Type} (xs : List α) (i : Nat) (a d : α)
    (hi : i < xs.length) : xs.getD i a = xs.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem bucketConstantGetD {α : Type} (n : Nat) (a : α) (i : Nat) :
    (List.replicate n a).getD i a = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

private def emptyRegionBuckets (n : Nat) : RegionBuckets :=
  { members := List.replicate n [], widths := List.replicate n 0,
    low := List.replicate n 2147483647, high := List.replicate n (-2147483648),
    lanes := List.replicate n [], laneWidth := List.replicate n 0,
    loopWidth := List.replicate n 0 }

private def bucketGather (groups : List Nat) (x : List Int) (acc : RegionBuckets)
    (q : ProperNode × Nat) : RegionBuckets :=
  if q.1.node.border != 0 then acc else
    let owner := groups.getD q.2 0
    let width := q.1.node.w + 2 * (q.1.node.loopExtent : Int)
    let left := RouteImpl.xAt x q.2 - Int.tdiv width 2
    let right := left + width
    { acc with
      low := setAt acc.low owner (min (acc.low.getD owner 2147483647) left)
      high := setAt acc.high owner (max (acc.high.getD owner (-2147483648)) right)
      members := setAt acc.members owner (acc.members.getD owner [] ++ [q.2]) }

private def bucketAddLane (rm : ComponentRegions) (groups : List Nat) (labelWidths : List Int)
    (acc : RegionBuckets) (q : Edge × Nat) : RegionBuckets :=
  if !q.1.reversed || q.1.tail == q.1.head then acc else
    let root := rm.clusters.length
    let owner := edgeOwnerOf rm groups root q.1.tail q.1.head
    if owner == root then acc else
      { acc with
        lanes := setAt acc.lanes owner (acc.lanes.getD owner [] ++ [q.2])
        laneWidth := setAt acc.laneWidth owner
          (max (acc.laneWidth.getD owner 0) (labelWidths.getD q.2 0)) }

private def bucketLeft (p : Proper) (x : List Int) (v : Nat) : Int :=
  x.getD v 0 - Int.tdiv (CoordsImpl.nodeW p v) 2

private def bucketRight (p : Proper) (x : List Int) (v : Nat) : Int :=
  bucketLeft p x v + CoordsImpl.nodeW p v

private theorem bucketGatherHull (p : Proper) (groups : List Nat) (x : List Int) (n g : Nat) :
    let b := p.nodes.zipIdx.foldl (bucketGather groups x) (emptyRegionBuckets n)
    b.members.length = n ∧ b.low.length = n ∧ b.high.length = n ∧
      ∀ v ∈ b.members.getD g [],
        b.low.getD g 0 ≤ bucketLeft p x v ∧ bucketRight p x v ≤ b.high.getD g 0 := by
  dsimp only
  apply OrderImpl.foldl_inv (fun b : RegionBuckets =>
    b.members.length = n ∧ b.low.length = n ∧ b.high.length = n ∧
      ∀ v ∈ b.members.getD g [],
        b.low.getD g 0 ≤ bucketLeft p x v ∧ bucketRight p x v ≤ b.high.getD g 0)
  · refine ⟨by simp [emptyRegionBuckets], by simp [emptyRegionBuckets],
      by simp [emptyRegionBuckets], ?_⟩
    intro v hv
    change v ∈ (List.replicate n ([] : List Nat)).getD g [] at hv
    simp only [bucketConstantGetD, List.not_mem_nil] at hv
  · intro b hb q hq
    dsimp only [bucketGather]
    split
    · exact hb
    · obtain ⟨hm, hl, hh, hcover⟩ := hb
      refine ⟨by simpa only [bucketSetAtLength] using hm,
        by simpa only [bucketSetAtLength] using hl, by simpa only [bucketSetAtLength] using hh,
        ?_⟩
      simp only [bucketSetAtGetD, hm, hl, hh]
      by_cases hwrite : g = groups.getD q.2 0 ∧ groups.getD q.2 0 < n
      · simp only [ite_eq_left hwrite]
        have hleftBound : groups.getD q.2 0 < b.low.length := hl.symm ▸ hwrite.2
        have hrightBound : groups.getD q.2 0 < b.high.length := hh.symm ▸ hwrite.2
        rw [bucketGetDAgrees _ _ 2147483647 0 hleftBound,
          bucketGetDAgrees _ _ (-2147483648) 0 hrightBound]
        have howner := hwrite.1
        rw [← howner]
        have hqnode := List.mem_zipIdx_iff_getElem?.mp hq
        have hleft : RouteImpl.xAt x q.2 - Int.tdiv (q.1.node.w + 2 * (q.1.node.loopExtent : Int)) 2 =
            bucketLeft p x q.2 := by
          simp only [bucketLeft, RouteImpl.xAt, CoordsImpl.nodeW, hqnode]
        have hright : RouteImpl.xAt x q.2 - Int.tdiv (q.1.node.w + 2 * (q.1.node.loopExtent : Int)) 2 +
            (q.1.node.w + 2 * (q.1.node.loopExtent : Int)) = bucketRight p x q.2 := by
          simp only [bucketRight, bucketLeft, RouteImpl.xAt, CoordsImpl.nodeW, hqnode]
        rw [hright, hleft]
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · obtain ⟨hvl, hvr⟩ := hcover v hv
          exact ⟨Int.le_trans (Int.min_le_left _ _) hvl,
            Int.le_trans hvr (Int.le_max_left _ _)⟩
        · have heq : v = q.2 := List.mem_singleton.mp hv
          subst v
          exact ⟨Int.min_le_right _ _, Int.le_max_right _ _⟩
      · simpa only [ite_eq_right hwrite] using hcover

private theorem bucketLaneFoldHull (rm : ComponentRegions) (groups : List Nat)
    (labelWidths : List Int) (entries : List (Edge × Nat)) (initial : RegionBuckets) :
    let b := entries.foldl (bucketAddLane rm groups labelWidths) initial
    b.members = initial.members ∧ b.low = initial.low ∧ b.high = initial.high := by
  dsimp only
  apply OrderImpl.foldl_inv (fun b : RegionBuckets =>
    b.members = initial.members ∧ b.low = initial.low ∧ b.high = initial.high)
  · exact ⟨rfl, rfl, rfl⟩
  · intro b hb q _
    dsimp only [bucketAddLane]
    split
    · exact hb
    · split <;> exact hb

private theorem newRegionBuckets_width_and_hull (rm : ComponentRegions) (cg : Graph) (p : Proper)
    (groups : List Nat) (labelWidths x : List Int) (hsizes : CoordsImpl.sizesNonneg p = true) :
    let b := newRegionBuckets rm cg p groups labelWidths x
    (∀ g, 0 ≤ b.widths.getD g 0) ∧
    (∀ g v, v ∈ b.members.getD g [] →
      b.low.getD g 0 ≤ bucketLeft p x v ∧ bucketRight p x v ≤ b.low.getD g 0 + b.widths.getD g 0) := by
  let n := rm.clusters.length + 1
  let gathered := p.nodes.zipIdx.foldl (bucketGather groups x) (emptyRegionBuckets n)
  let withLanes := cg.edges.zipIdx.foldl (bucketAddLane rm groups labelWidths) gathered
  let width (g : Nat) := if (gathered.members.getD g []).isEmpty then 0
    else gathered.high.getD g 0 - gathered.low.getD g 0
  let widths := (List.range n).map width
  change (∀ g, 0 ≤ widths.getD g 0) ∧
    (∀ g v, v ∈ withLanes.members.getD g [] →
      withLanes.low.getD g 0 ≤ bucketLeft p x v ∧
        bucketRight p x v ≤ withLanes.low.getD g 0 + widths.getD g 0)
  obtain ⟨hmembers, hlow, _⟩ := bucketLaneFoldHull rm groups labelWidths cg.edges.zipIdx gathered
  change withLanes.members = gathered.members at hmembers
  change withLanes.low = gathered.low at hlow
  rw [hmembers, hlow]
  have wat (g : Nat) (hg : g < n) : widths.getD g 0 = width g := by
    simp only [widths, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hg,
      Option.map_some, Option.getD_some]
  have hcover (g : Nat) : gathered.members.length = n ∧ gathered.low.length = n ∧
      gathered.high.length = n ∧ ∀ v ∈ gathered.members.getD g [],
        gathered.low.getD g 0 ≤ bucketLeft p x v ∧ bucketRight p x v ≤ gathered.high.getD g 0 :=
    bucketGatherHull p groups x n g
  have width_of_mem (g v : Nat) (hv : v ∈ gathered.members.getD g []) :
      width g = gathered.high.getD g 0 - gathered.low.getD g 0 := by
    have hnonempty : ¬ (gathered.members.getD g []).isEmpty = true := by
      intro hempty
      rw [List.nil_of_isEmpty hempty] at hv
      exact List.not_mem_nil hv
    simp only [width, ite_eq_right hnonempty]
  constructor
  · intro g
    by_cases hg : g < n
    · rw [wat g hg]
      cases he : gathered.members.getD g [] with
      | nil =>
        have hempty : (gathered.members.getD g []).isEmpty = true := List.isEmpty_iff.mpr he
        simpa only [width, ite_eq_left hempty] using (Int.le_refl 0)
      | cons v vs =>
        have hmem : v ∈ gathered.members.getD g [] := by
          rw [he]
          exact List.Mem.head vs
        rw [width_of_mem g v hmem]
        obtain ⟨hleft, hright⟩ := (hcover g).2.2.2 v hmem
        change bucketLeft p x v + CoordsImpl.nodeW p v ≤ gathered.high.getD g 0 at hright
        exact Int.sub_nonneg.mpr (Int.le_trans hleft (Int.le_trans
          (Int.le_add_of_nonneg_right (CoordsImpl.nodeW_nonneg hsizes v)) hright))
    · have hnone : widths[g]? = none := List.getElem?_eq_none_iff.mpr (by
        simpa only [widths, List.length_map, List.length_range] using Nat.le_of_not_gt hg)
      simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none, Int.le_refl]
  · intro g v hv
    have hg : g < n := by
      by_cases h : g < n
      · exact h
      · have hlength : gathered.members.length = n := (hcover g).1
        have hnone : gathered.members[g]? = none := List.getElem?_eq_none_iff.mpr (by
          rw [hlength]
          exact Nat.le_of_not_gt h)
        simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none, List.not_mem_nil] at hv
    obtain ⟨hleft, hright⟩ := (hcover g).2.2.2 v hv
    refine ⟨hleft, ?_⟩
    rw [wat g hg, width_of_mem g v hv]
    calc
      bucketRight p x v ≤ gathered.high.getD g 0 := hright
      _ = gathered.low.getD g 0 + (gathered.high.getD g 0 - gathered.low.getD g 0) :=
        (Int.sub_add_cancel _ _).symm.trans (Int.add_comm _ _)

private theorem newRegionBuckets_laneWidth_nonneg (rm : ComponentRegions) (cg : Graph)
    (p : Proper) (groups : List Nat) (labelWidths x : List Int) (g : Nat) :
    0 ≤ (newRegionBuckets rm cg p groups labelWidths x).laneWidth.getD g 0 := by
  change 0 ≤ (cg.edges.zipIdx.foldl (bucketAddLane rm groups labelWidths)
    (p.nodes.zipIdx.foldl (bucketGather groups x)
      (emptyRegionBuckets (rm.clusters.length + 1)))).laneWidth.getD g 0
  apply OrderImpl.foldl_inv (fun b : RegionBuckets => 0 ≤ b.laneWidth.getD g 0)
  · apply OrderImpl.foldl_inv (fun b : RegionBuckets => 0 ≤ b.laneWidth.getD g 0)
    · change 0 ≤ (List.replicate (rm.clusters.length + 1) (0 : Int)).getD g 0
      simp only [bucketConstantGetD, Int.le_refl]
    · intro b hb q _
      dsimp only [bucketGather]
      split <;> exact hb
  · intro b hb q _
    dsimp only [bucketAddLane]
    split
    · exact hb
    · split
      · exact hb
      · rw [bucketSetAtGetD]
        split
        · rename_i hw
          exact Int.le_trans (by simpa only [hw.1] using hb) (Int.le_max_left _ _)
        · exact hb

private theorem newRegionBuckets_loopWidth_nonneg (rm : ComponentRegions) (cg : Graph)
    (p : Proper) (groups : List Nat) (labelWidths x : List Int) (g : Nat) :
    0 ≤ (newRegionBuckets rm cg p groups labelWidths x).loopWidth.getD g 0 := by
  change 0 ≤ (rm.clusters.zipIdx.foldl (fun lw q => setAt lw q.2 (q.1.extent : Int))
    (List.replicate (rm.clusters.length + 1) 0)).getD g 0
  apply OrderImpl.foldl_inv (fun lw : List Int => 0 ≤ lw.getD g 0)
  · simp only [bucketConstantGetD, Int.le_refl]
  · intro lw hlw q _
    rw [bucketSetAtGetD]
    split
    · exact Int.natCast_nonneg _
    · exact hlw

/-- Placement gathers actual member footprints, with nonnegative widths certified by crossing. -/
theorem RegionCrossAllocationStages.bucket_width_and_hull {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed) :
    (∀ g, 0 ≤ stages.placement.buckets.widths.getD g 0) ∧
    (∀ g v, v ∈ stages.placement.buckets.members.getD g [] →
      let w := CoordsImpl.nodeW stages.placement.p v
      let left := stages.before.getD v 0 - Int.tdiv w 2
      stages.placement.buckets.low.getD g 0 ≤ left ∧
        left + w ≤ stages.placement.buckets.low.getD g 0 + stages.placement.buckets.widths.getD g 0) := by
  obtain ⟨_, _, _, hsizes, _⟩ := CoordsImpl.crossCoordsClusterWith_spec stages.hCross
  rw [stages.hPlacement]
  exact newRegionBuckets_width_and_hull rm cg p stages.groups _ stages.before hsizes

/-- The crossing stage needs only the slot sign, which a full component run checks. -/
theorem RegionCrossAllocationStages.bucket_signs {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p placed : Proper} {minimum : RegionConstraints}
    {layers pinned : List (List Nat)} {xs : List Int} {reserved : List (Option Int)}
    (stages : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
    (hslot : 0 ≤ P.slot) :
    (∀ g, 0 ≤ stages.placement.buckets.widths.getD g 0) ∧
    (∀ g, 0 ≤ laneExtentOf stages.placement.buckets P.slot g) ∧
    (∀ g, 0 ≤ stages.placement.buckets.loopWidth.getD g 0) := by
  refine ⟨stages.bucket_width_and_hull.1, ?_, ?_⟩
  · intro g
    rw [stages.hPlacement]
    have hw := newRegionBuckets_laneWidth_nonneg rm cg p stages.groups
      (cg.edges.map fun e => (stackSize cg.slot (routeLabels labels e.decl)).width) stages.before g
    unfold laneExtentOf
    exact Int.mul_nonneg (Int.add_nonneg (Int.mul_nonneg (by decide) hslot) hw)
      (Int.natCast_nonneg _)
  · intro g
    rw [stages.hPlacement]
    exact newRegionBuckets_loopWidth_nonneg rm cg p stages.groups _ stages.before g

theorem componentRunR_slot_pos {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    1 ≤ P.slot := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ⟨_, _⟩, _, stages⟩ := componentRunR_stages hrun
  exact (CoordsImpl.rankCoordsWith_spec stages.hYt).2.1

theorem componentRunR_active_bucket_signs {P : Params} {exact : List Nat}
    {s : RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {rm : ComponentRegions} {p : Proper} {minimum : RegionConstraints}
    {layers : List (List Nat)} {reserved : List (Option Int)}
    (hrun : componentRunR P exact (some s) inp cg labels orderOptions = .ok (cg', run))
    (stages : RegionCrossAllocationStages P rm cg' labels p minimum layers run.layers
      run.coordinateXs reserved run.coordinateProper) :
    (∀ g, 0 ≤ stages.placement.buckets.widths.getD g 0) ∧
    (∀ g, 0 ≤ laneExtentOf stages.placement.buckets P.slot g) ∧
    (∀ g, 0 ≤ stages.placement.buckets.loopWidth.getD g 0) :=
  stages.bucket_signs (Int.le_trans (by decide) (componentRunR_slot_pos hrun))

end Elegant.Layered.PipelineImpl

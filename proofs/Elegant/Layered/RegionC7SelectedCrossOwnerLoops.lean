import Elegant.Layered.RegionFlatC7Selected
import Elegant.Layered.RegionC6ReservedTrunkGeometry
import Elegant.Layered.RegionC6TrunkPlainTransport
import Elegant.Layered.RegionC8aGroupPlain

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl RegionOrdinaryC6

private abbrev bucketLeft (P : Params) (rm : ComponentRegions) (alloc : RegionAllocation)
    (g : Nat) : Int :=
  alloc.lefts.getD g 0 + (if g = rm.clusters.length then 0 else regionInsetOf P)

private abbrev bucketRight (P : Params) (rm : ComponentRegions) (pl : RegionPlacement)
    (alloc : RegionAllocation) (g : Nat) : Int :=
  bucketLeft P rm alloc g + pl.buckets.widths.getD g 0

section Allocation

variable {P : Params} {rm : ComponentRegions} {cg : Graph} {labels : List MeasuredLabel}
  {p placed : Proper} {minimum : RegionConstraints} {layers pinned : List (List Nat)}
  {xs : List Int} {reserved : List (Option Int)}
  (st : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
  (hparents : rm.parents.length = rm.clusters.length) (hmin : constrainR rm P p = .ok minimum)

include hparents hmin

theorem r7_allocatedMember_loopHull {v g : Nat} {n : ProperNode}
    (hn : p.nodes[v]? = some n) (hb : n.node.border = 0) (hg : st.groups.getD v 0 = g) :
    let left := st.shifted.getD v 0 - Int.fdiv n.node.w 2
    bucketLeft P rm st.allocation g ≤ left ∧
      left + n.node.w + (n.node.loopExtent : Int) ≤
        bucketRight P rm st.placement st.allocation g := by
  obtain ⟨hm, hshift⟩ := actualMember_shift st hparents hmin hn hb hg
  have hraw := st.bucket_width_and_hull.2 g v hm
  have hpn : st.placement.p.nodes[v]? = some n := by rw [st.hPlacement]; exact hn
  dsimp only at hraw ⊢
  simp only [CoordsImpl.nodeW, hpn] at hraw
  obtain ⟨_, _, _, hsizes, _⟩ := CoordsImpl.crossCoordsClusterWith_spec st.hCross
  have hw := (sizesNonneg_lookup hsizes v n hn).1
  have he : (0 : Int) ≤ n.node.loopExtent := Int.natCast_nonneg _
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega : 0 ≤ n.node.w + 2 * (n.node.loopExtent : Int)),
    Int.mul_comm 2 (n.node.loopExtent : Int), Int.add_mul_ediv_right _ _ (by decide : (2 : Int) ≠ 0)] at hraw
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide : 0 ≤ (2 : Int)), hshift]
  have hr : st.placement.rm.clusters.length = rm.clusters.length := by rw [st.hPlacement]
  have hstart : (if g != st.placement.rm.clusters.length then st.placement.minimum.origins.getD g 0
      else 0) = (if g = rm.clusters.length then 0 else regionInsetOf P) := by
    rw [hr]
    by_cases heq : g = rm.clusters.length
    · simp [heq]
    · have hgb : g ≤ rm.clusters.length := by rw [← hg]; exact actualMember_group_bound st hn
      rw [actualGroup_inset st hparents hmin (show g < rm.clusters.length from by omega)]
      simp [heq]
  unfold regionBucketShift
  rw [hstart]
  simp only [bucketRight, bucketLeft]
  constructor <;> omega

/-- Parent own buckets precede all child allocations. Independent sibling budgets
are disjoint. These statements concern own buckets, not enclosing frame rectangles. -/
theorem r7_activeDifferentBuckets_gap
    (hinset : 0 < regionInsetOf P) (hslot : 1 ≤ P.slot) {a b : Nat}
    (ha : a ≤ rm.clusters.length) (hb : b ≤ rm.clusters.length) (hne : a ≠ b) :
    bucketRight P rm st.placement st.allocation a ≤ bucketLeft P rm st.allocation b ∨
      bucketRight P rm st.placement st.allocation b ≤ bucketLeft P rm st.allocation a := by
  let L (k : Nat) := st.allocation.lefts.getD k 0
  let W (k : Nat) := st.allocation.widths.getD k 0
  let A := bucketLeft P rm st.allocation
  let B := bucketRight P rm st.placement st.allocation
  have hchild {g c : Nat} (hc : c ∈ st.placement.children.getD g []) :
      c < rm.clusters.length := actualChild_bound st hparents hmin hc
  obtain ⟨hown, hlane, hloop⟩ := st.bucket_signs (by omega : 0 ≤ P.slot)
  have hwidth : ∀ k, 0 ≤ W k := by
    unfold W
    rw [allocationWidths_exact st]
    exact reserveWidths_nonnegative (by omega : 0 ≤ regionInsetOf P) hown hlane hloop
  have totals (lst : List Nat) : 0 ≤ (lst.map W).sum := by
    induction lst with
    | nil => simp
    | cons k ks ih => exact Int.add_nonneg (hwidth k) ih
  have inside {k d : Nat} (hk : k < rm.clusters.length)
      (path : TrunkBranch st.placement.children k d) : L k ≤ A d ∧ B d ≤ L k + W k := by
    have hd : d < rm.clusters.length := by
      revert hk
      induction path with
      | here => exact id
      | @step g c d hc _ ih => exact fun _ => ih (hchild hc)
    have hroom : regionInsetOf P + st.placement.buckets.widths.getD d 0 ≤ W d := by
      obtain ⟨_, _, ho, hlast, hchildren⟩ := (st.reservation_order hparents hmin).2 d
        (Nat.le_of_lt hd)
      have hsmall : d < st.placement.rm.clusters.length := by simpa only [st.hPlacement] using hd
      have hr := reserveWidths_room_from_last_writes (P := P) ho hsmall hlast hchildren
      have hchildrenWidths := totals (st.placement.children.getD d [])
      have hl := hlane d
      have hlo := hloop d
      change (2 * regionInsetOf P + st.placement.buckets.widths.getD d 0 +
        ((st.placement.children.getD d []).map (fun c => (reserveWidths st.placement P).getD c 0)).sum +
        laneExtentOf st.placement.buckets P.slot d ≤
          (reserveWidths st.placement P).getD d 0 - st.placement.buckets.loopWidth.getD d 0) at hr
      unfold W at hchildrenWidths ⊢
      rw [allocationWidths_exact st] at hchildrenWidths ⊢
      omega
    have halloc := actualBranch_budget st hparents hmin hinset hslot hk path
    have hbounds : L d ≤ A d ∧ B d ≤ L d + W d := by
      simp only [L, W, A, B, bucketLeft, bucketRight, ite_eq_right (Nat.ne_of_lt hd)]
      change regionInsetOf P + st.placement.buckets.widths.getD d 0 ≤
        st.allocation.widths.getD d 0 at hroom
      constructor <;> omega
    exact ⟨Int.le_trans halloc.1 hbounds.1, Int.le_trans hbounds.2 halloc.2⟩
  have beforeChild {k c : Nat} (hk : k ≤ rm.clusters.length)
      (hc : c ∈ st.placement.children.getD k []) : B k ≤ L c :=
    (actualChildBudget_inside st hparents hmin hinset hslot hk hc).1
  have left := actualBranch_from_root st hparents hmin ha
  have right := actualBranch_from_root st hparents hmin hb
  have rootBound : rm.clusters.length ≤ rm.clusters.length := Nat.le_refl _
  have gap {g a b : Nat} (left : TrunkBranch st.placement.children g a)
      (hg : g ≤ rm.clusters.length) (right : TrunkBranch st.placement.children g b)
      (hne : a ≠ b) : B a ≤ A b ∨ B b ≤ A a := by
    revert hg right hne
    induction left with
    | here g =>
      intro hg right hne
      cases right with
      | here => exact (hne rfl).elim
      | @step _ c _ hc rest =>
        exact Or.inl (Int.le_trans (beforeChild hg hc) (inside (hchild hc) rest).1)
    | @step g c a hc left ih =>
      intro hg right hne
      cases right with
      | here => exact Or.inr (Int.le_trans (beforeChild hg hc) (inside (hchild hc) left).1)
      | @step _ d _ hd right =>
        by_cases hcd : c = d
        · subst d
          exact ih (Nat.le_of_lt (hchild hc)) right hne
        · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hd
          have hl := inside (hchild hc) left
          have hr := inside (hchild hd) right
          have hij : i ≠ j := fun h => hcd (Option.some.inj (hi.symm.trans (h ▸ hj)))
          rcases Nat.lt_or_gt_of_ne hij with hij | hji
          · have hs := actualSiblingBudget_order st hparents hmin hinset hslot hg hi hj hij
            exact Or.inl (Int.le_trans hl.2 (Int.le_trans hs hr.1))
          · have hs := actualSiblingBudget_order st hparents hmin hinset hslot hg hj hi hji
            exact Or.inr (Int.le_trans hr.2 (Int.le_trans hs hl.1))
  exact gap left rootBound right hne

end Allocation

private def ownerKey (rm : ComponentRegions) (g : Nat) (key : Option Nat) : Prop :=
  match key with
  | none => g = rm.clusters.length
  | some decl => clusterOfDecl rm decl = some g

private theorem ownerKey_unique {rm : ComponentRegions} {g : Nat} {a b : Option Nat}
    (ha : ownerKey rm g a) (hb : ownerKey rm g b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hg : g = rm.clusters.length := ha
      have h : clusterOfDecl rm b = some g := hb
      have hlt := (List.findIdx?_eq_some_iff_getElem.mp h).1
      omega
  | some a =>
    have ha' : clusterOfDecl rm a = some g := ha
    have ⟨hlt, hA, _⟩ := List.findIdx?_eq_some_iff_getElem.mp ha'
    cases b with
    | none =>
      have hg : g = rm.clusters.length := hb
      omega
    | some b =>
      have hb' : clusterOfDecl rm b = some g := hb
      have ⟨_, hB, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hb'
      exact congrArg some ((beq_iff_eq.mp hA).symm.trans (beq_iff_eq.mp hB))

theorem r7_loopFootprint_gap_activeCrossOwnerPlain {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate : Nat} {s : RegionSpec} {rm : ComponentRegions}
    {cg : Graph} {run : Run} {orderOptions : OrderOptions}
    (hcomp : comp ∈ components execution.graph)
    (hrun : componentRunR execution.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) execution.graph comp candidate)
      execution.measured orderOptions = .ok (cg, run))
    (hactive : newComponentRegions (some s) execution.params inp
      (componentCandidateR (some s) execution.graph comp candidate) = .ok (some rm))
    {u v : Nat} {nu nv : Node} (hu : cg.nodes[u]? = some nu) (hv : cg.nodes[v]? = some nv)
    (hbu : nu.border = 0) (hbv : nv.border = 0)
    (howner : nu.clusterPath.getLast? ≠ nv.clusterPath.getLast?) :
    let foot := loopFootprintExt cg run execution.measured u
    let target := RouteImpl.boxRect run.proper run.xs run.ys v
    foot.x + foot.w ≤ target.x ∨ target.x + target.w ≤ foot.x := by
  obtain ⟨_, _, _, _, _, _, _, _, hrank, hnorm, hlab, hcoord, hmin, _, ⟨st⟩⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  obtain ⟨a, ha, hka, _, _, _⟩ :=
    st.activePlain_frame_in_ownerBucket hrun hactive hrank hnorm hlab hcoord hmin hu hbu
  obtain ⟨b, hb, hkb, _, _, _⟩ :=
    st.activePlain_frame_in_ownerBucket hrun hactive hrank hnorm hlab hcoord hmin hv hbv
  have hab : a ≠ b := by
    intro he
    subst b
    exact howner (ownerKey_unique (rm := rm) (g := a) hka hkb)
  obtain ⟨src, hpreU, hbU, hproperU, hxU⟩ :=
    actualPlainNode_record hrun hactive hrank hnorm hlab hcoord st hu hbu
  obtain ⟨dst, hpreV, hbV, hproperV, hxV⟩ :=
    actualPlainNode_record hrun hactive hrank hnorm hlab hcoord st hv hbv
  have hga : st.groups.getD u 0 = a := by
    simp only [List.getD_eq_getElem?_getD, ha, Option.getD_some]
  have hgb : st.groups.getD v 0 = b := by
    simp only [List.getD_eq_getElem?_getD, hb, Option.getD_some]
  have hboundA : a ≤ rm.clusters.length := by
    rw [← hga]
    exact actualMember_group_bound st hpreU
  have hboundB : b ≤ rm.clusters.length := by
    rw [← hgb]
    exact actualMember_group_bound st hpreV
  have hparents := activeRegion_parent_count hactive
  have hinset : 0 < regionInsetOf execution.params := by
    have hpad := (checkedParams_sizing_nonneg execution.checked).2.1
    have hborder := checkedParams_clusterBorderW_ge_one execution.checked
    unfold regionInsetOf
    omega
  have hgaps := r7_activeDifferentBuckets_gap st hparents hmin hinset
    (componentRunR_slot_pos hrun) hboundA hboundB hab
  have hU := r7_allocatedMember_loopHull st hparents hmin hpreU hbU hga
  have hV := allocatedMember_crossHull st hparents hmin hpreV hbV hgb
  have hw := (r7_loopPlainSizing_of_run execution (candidate := candidate)
    hcomp rfl hrun hu hbu).1
  obtain ⟨src', hcoordU, hproperU', _, _⟩ :=
    (componentRunR_region_plain_cross_geometry hrun).2 hu hbu
  have hsame := Option.some.inj (hproperU'.symm.trans hproperU)
  subst src'
  simp only [List.getD_eq_getElem?_getD, hcoordU, Option.getD_some] at hw
  have hborder : (cg.nodes.getD u default).border ≠ -2 := by
    simp [List.getD_eq_getElem?_getD, hu, hbu]
  have hframe := plain_frame_eq_boxRect (default : Params) cg run u
    (List.getElem?_eq_some_iff.mp hproperU).1 hborder
  let foot := loopFootprintExt cg run execution.measured u
  have hfoot : foot.x =
      st.shifted.getD u 0 - Int.fdiv src.node.w 2 + src.node.w := by
    simp only [foot, loopFootprintExt, hframe, RouteImpl.boxRect, RouteImpl.xAt,
      RouteImpl.nodeW, hproperU, hxU]
  have hwidth : 0 ≤ src.node.w :=
    (sizesNonneg_lookup (CoordsImpl.crossCoordsClusterWith_spec st.hCross).2.2.2.1 u src hpreU).1
  let target := RouteImpl.boxRect run.proper run.xs run.ys v
  have htarget : target.x = st.shifted.getD v 0 - Int.fdiv dst.node.w 2 ∧ target.w = dst.node.w := by
    constructor
    · simp only [target, RouteImpl.boxRect, RouteImpl.xAt, RouteImpl.nodeW, hproperV, hxV]
    · simp only [target, RouteImpl.boxRect, RouteImpl.nodeW, hproperV]
  change foot.x + foot.w ≤ target.x ∨ target.x + target.w ≤ foot.x
  change foot.w ≤ (src.node.loopExtent : Int) at hw
  change bucketLeft execution.params rm st.allocation b ≤
      st.shifted.getD v 0 - Int.fdiv dst.node.w 2 ∧
    st.shifted.getD v 0 - Int.fdiv dst.node.w 2 + dst.node.w ≤
      bucketRight execution.params rm st.placement st.allocation b at hV
  dsimp only at hU
  rcases hgaps with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- Newly settled selected route labels. The equal-rank condition keeps this
case disjoint from later-rank work; the horizontal footprint estimate itself is rank-free. -/
def R7_SelectedActiveCrossOwnerPlainLoop {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b) : Prop :=
  pair.rs.isSome = true ∧ pair.edge.tail = pair.edge.head ∧
  (rk pair.run.proper.rank pair.edge.tail).toNat = (rk pair.run.proper.rank pair.target).toNat ∧
  ∃ nu nv : Node, pair.cg.nodes[pair.edge.tail]? = some nu ∧
    pair.cg.nodes[pair.target]? = some nv ∧ nu.border = 0 ∧ nv.border = 0 ∧
    nu.clusterPath.getLast? ≠ nv.clusterPath.getLast?

theorem r7Selected_activeCrossOwnerPlainLoop_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res}
    {l : SceneLabel} {b : Box} (pair : R7_SelectedRoutePair execution l b)
    (hpair : R7_SelectedActiveCrossOwnerPlainLoop pair) :
    R7_OverlapRowsXGap pair.rect (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
  obtain ⟨hregion, hloop, _, nu, nv, hu, hv, hbu, hbv, howner⟩ := hpair
  obtain ⟨rm, hrm⟩ : ∃ rm, pair.rs = some rm := by
    cases h : pair.rs with
    | none => simp [h] at hregion
    | some rm => exact ⟨rm, rfl⟩
  have hregions := componentTrialR_selected_regions pair.candidate pair.regions_eq
  change newComponentRegions (r7Eff idSets o execution.params execution.lines pair.rs)
    execution.params inp
    (componentCandidateR (r7Eff idSets o execution.params execution.lines pair.rs)
      execution.graph pair.part.1 pair.candidate) = .ok pair.rs at hregions
  generalize hs : r7Eff idSets o execution.params execution.lines pair.rs = spec at hregions
  have hrun := pair.run_eq
  change componentRunR execution.params (exactDecls exactIds inp)
    (r7Eff idSets o execution.params execution.lines pair.rs) inp
    (componentCandidateR (r7Eff idSets o execution.params execution.lines pair.rs)
      execution.graph pair.part.1 pair.candidate) execution.measured (candidateOrder pair.candidate) =
      .ok (pair.cg, pair.run) at hrun
  rw [hs] at hrun
  rw [hrm] at hregions
  cases spec with
  | none => cases hregions
  | some s =>
    have hgap := r7_loopFootprint_gap_activeCrossOwnerPlain execution (candidate := pair.candidate)
      pair.comp_mem hrun hregions hu hv hbu hbv howner
    have hfoot : ¬ (loopFootprintExt pair.cg pair.run execution.measured pair.edge.tail).meetsInterior
        (RouteImpl.boxRect pair.run.proper pair.run.xs pair.run.ys pair.target) := by
      unfold Rect.meetsInterior
      dsimp only at hgap
      omega
    have hslot : 0 ≤ pair.cg.slot := by
      rw [r7ComponentRun_slot_of_scene execution (candidate := pair.candidate) hrun]
      have hpos := componentRunR_slot_pos hrun
      omega
    have hn := execution.measured_nonnegR
    have henv := pair.envelope_eq
    unfold labelEnvelope at henv
    obtain ⟨_, _, hrest⟩ := Option.bind_eq_some_iff.mp henv
    have he : (pair.edge.tail == pair.edge.head) = true := by simp [hloop]
    have hcont : (loopFootprintExt pair.cg pair.run execution.measured pair.edge.tail).Contained
        pair.envelope := by
      cases hex : pair.run.exact.contains pair.edge.tail with
      | false =>
        simp only [he, hex] at hrest
        exact X_loopEnvelope_containedExt hslot hn hex pair.edge_eq hloop (Option.some.inj hrest).symm
      | true =>
        simp only [he, hex] at hrest
        exact X_loopExactEnvelope_containedExt hslot hn pair.edge_eq hloop (Option.some.inj hrest).symm hex
    have hclear := Elegant.Layered.loop_branch_clear pair.edge_eq hloop pair.envelope_eq hslot hn
      (List.of_mem_zip pair.stack).2 (Elegant.Layered.not_meetsInterior_of_contained hcont hfoot)
    intro hy hwl hwb
    unfold Rect.meetsInterior at hclear
    omega

end Elegant.Layered.PipelineImpl

import Elegant.Layered.RegionC6TrunkPlacement

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Elegant.Layered.PipelineImpl.RegionOrdinaryC6

open RegionImpl RouteImpl

private def insetAt (P : Params) (rm : ComponentRegions) (g : Nat) : Int :=
  if g = rm.clusters.length then 0 else regionInsetOf P

private theorem sum_split {α : Type} (f : α → Int) (xs : List α) {i : Nat} {c : α}
    (hc : xs[i]? = some c) :
    (xs.map f).sum = ((xs.take i).map f).sum + f c + ((xs.drop (i + 1)).map f).sum := by
  have htake := List.take_add_one (l := xs) (i := i)
  rw [hc] at htake
  have hall := congrArg (fun ys => (ys.map f).sum) (List.take_append_drop (i + 1) xs)
  rw [htake] at hall
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Int.add_zero] at hall
  exact hall.symm

private theorem sum_nonnegative {α : Type} {f : α → Int} (hf : ∀ x, 0 ≤ f x) (xs : List α) :
    0 ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => exact Int.add_nonneg (hf x) ih

private theorem partialSum_mono {α : Type} {f : α → Int} (hf : ∀ x, 0 ≤ f x)
    (xs : List α) {i j : Nat} (hij : i ≤ j) :
    ((xs.take i).map f).sum ≤ ((xs.take j).map f).sum := by
  have h := List.take_add (l := xs) (i := i) (j := j - i)
  rw [show i + (j - i) = j by omega] at h
  rw [h, List.map_append, List.sum_append]
  exact Int.le_add_of_nonneg_right (sum_nonnegative hf _)

section Allocation

private inductive BranchCase (rows : List (List Nat)) (bound owner member : Nat) : Prop
  | within : TrunkBranch rows owner member → BranchCase rows bound owner member
  | above {child : Nat} : member ≤ bound → child ∈ rows.getD member [] →
      TrunkBranch rows child owner → BranchCase rows bound owner member
  | siblings {g a b : Nat} : g ≤ bound → a ∈ rows.getD g [] → b ∈ rows.getD g [] → a ≠ b →
      TrunkBranch rows a owner → TrunkBranch rows b member → BranchCase rows bound owner member

private theorem classifyBranches {rows : List (List Nat)} {bound k owner member : Nat}
    (hchildren : ∀ g c, c ∈ rows.getD g [] → c < bound)
    (a : TrunkBranch rows k owner) (hk : k ≤ bound) (b : TrunkBranch rows k member) :
    BranchCase rows bound owner member := by
  revert hk b
  induction a with
  | here =>
    intro _ b
    exact .within b
  | @step _ child _ hchild path ih =>
    intro hk b
    cases b with
    | here => exact .above hk hchild path
    | @step _ sibling _ hsibling siblingPath =>
      by_cases he : child = sibling
      · subst sibling
        exact ih (Nat.le_of_lt (hchildren _ _ hchild)) siblingPath
      · exact .siblings hk hchild hsibling he path siblingPath

private theorem branch_bound {rows : List (List Nat)} {bound k member : Nat}
    (hchildren : ∀ g c, c ∈ rows.getD g [] → c < bound)
    (h : TrunkBranch rows k member) (hk : k < bound) : member < bound := by
  revert hk
  induction h with
  | here => exact id
  | @step g c _ hg _ ih => exact fun _ => ih (hchildren g c hg)

variable {P : Params} {rm : ComponentRegions} {cg : Graph} {labels : List MeasuredLabel}
  {p placed : Proper} {minimum : RegionConstraints} {layers pinned : List (List Nat)}
  {xs : List Int} {reserved : List (Option Int)}
  (st : RegionCrossAllocationStages P rm cg labels p minimum layers pinned xs reserved placed)
  (hparents : rm.parents.length = rm.clusters.length) (hmin : constrainR rm P p = .ok minimum)
  (hinset : 0 < regionInsetOf P) (hslot : 1 ≤ P.slot)

include hinset hslot

private theorem reservedWidthsNonnegative : ∀ g, 0 ≤ st.allocation.widths.getD g 0 := by
  rw [allocationWidths_exact st]
  obtain ⟨hown, hlane, hloop⟩ := st.bucket_signs (by omega : 0 ≤ P.slot)
  exact reserveWidths_nonnegative (by omega : 0 ≤ regionInsetOf P) hown hlane hloop

omit hinset hslot
include hparents hmin

private theorem reservedWidthsRoom {g : Nat} (hg : g < rm.clusters.length) :
    2 * regionInsetOf P + st.placement.buckets.widths.getD g 0 +
        ((st.placement.children.getD g []).map fun c => st.allocation.widths.getD c 0).sum +
        laneExtentOf st.placement.buckets P.slot g ≤
      st.allocation.widths.getD g 0 - st.placement.buckets.loopWidth.getD g 0 := by
  rw [allocationWidths_exact st]
  obtain ⟨_, _, ho, hgNot, hcNot⟩ := (st.reservation_order hparents hmin).2 g (Nat.le_of_lt hg)
  have hg' : g < st.placement.rm.clusters.length := by simpa only [st.hPlacement] using hg
  exact reserveWidths_room_from_last_writes ho hg' hgNot hcNot

include hinset hslot

/-- Executed child budgets follow the actual child-row order, including siblings at the root. -/
theorem actualSiblingBudget_order {g a b i j : Nat} (hg : g ≤ rm.clusters.length)
    (ha : (st.placement.children.getD g [])[i]? = some a)
    (hb : (st.placement.children.getD g [])[j]? = some b) (hij : i < j) :
    st.allocation.lefts.getD a 0 + st.allocation.widths.getD a 0 ≤
      st.allocation.lefts.getD b 0 := by
  let row := st.placement.children.getD g []
  let f (c : Nat) := st.allocation.widths.getD c 0
  have hf := reservedWidthsNonnegative st hinset hslot
  have hs := congrArg (fun ys : List Nat => (ys.map f).sum)
    (List.take_add_one (l := row) (i := i))
  change row[i]? = some a at ha
  rw [ha] at hs
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Int.add_zero] at hs
  have hp := partialSum_mono hf row (show i + 1 ≤ j by omega)
  rw [hs] at hp
  have hla := actualChildLeft st hparents hmin hg ha
  have hlb := actualChildLeft st hparents hmin hg hb
  change ((row.take (i + 1)).map f).sum = ((row.take i).map f).sum + f a at hs
  change ((row.take i).map f).sum + f a ≤ ((row.take j).map f).sum at hp
  rw [hla, hlb]
  change st.allocation.lefts.getD g 0 + insetAt P rm g + st.placement.buckets.widths.getD g 0 +
    ((row.take i).map f).sum + f a ≤
    st.allocation.lefts.getD g 0 + insetAt P rm g + st.placement.buckets.widths.getD g 0 +
    ((row.take j).map f).sum
  omega

/-- The actual child budget starts after its parent's own bucket and ends strictly
before that non-root parent's reserved lane band. -/
theorem actualChildBudget_inside {g c : Nat} (hg : g ≤ rm.clusters.length)
    (hc : c ∈ st.placement.children.getD g []) :
    st.allocation.lefts.getD g 0 + insetAt P rm g + st.placement.buckets.widths.getD g 0 ≤
      st.allocation.lefts.getD c 0 ∧
    (g < rm.clusters.length →
      st.allocation.lefts.getD c 0 + st.allocation.widths.getD c 0 + regionInsetOf P +
        laneExtentOf st.placement.buckets P.slot g + st.placement.buckets.loopWidth.getD g 0 ≤
      st.allocation.lefts.getD g 0 + st.allocation.widths.getD g 0) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hc
  have hleft := actualChildLeft st hparents hmin hg hi
  let f (c : Nat) := st.allocation.widths.getD c 0
  have hf := reservedWidthsNonnegative st hinset hslot
  have hprefix := sum_nonnegative hf ((st.placement.children.getD g []).take i)
  refine ⟨by rw [hleft]; exact Int.le_add_of_nonneg_right hprefix, ?_⟩
  intro hreal
  have hsplit := sum_split f _ hi
  have hsuffix := sum_nonnegative hf ((st.placement.children.getD g []).drop (i + 1))
  have hwidth := reservedWidthsRoom st hparents hmin hreal
  rw [hleft, ite_eq_right (Nat.ne_of_lt hreal)]
  dsimp only [f] at hsplit hsuffix
  omega

/-- A nested budget preserves both sides of its non-root ancestor's budget. -/
theorem actualBranch_budget {g c : Nat} (hg : g < rm.clusters.length)
    (hc : TrunkBranch st.placement.children g c) :
    st.allocation.lefts.getD g 0 ≤ st.allocation.lefts.getD c 0 ∧
    st.allocation.lefts.getD c 0 + st.allocation.widths.getD c 0 ≤
      st.allocation.lefts.getD g 0 + st.allocation.widths.getD g 0 := by
  revert hg
  induction hc with
  | here _ =>
    intro _
    exact ⟨Int.le_refl _, Int.le_refl _⟩
  | @step g mid _ hm _ ih =>
    intro hg
    have hmb := actualChild_bound st hparents hmin hm
    obtain ⟨hla, hra⟩ := actualChildBudget_inside st hparents hmin hinset hslot (Nat.le_of_lt hg) hm
    have hwidth := st.bucket_width_and_hull.1 g
    obtain ⟨_, hext, hloop⟩ := st.bucket_signs (by omega : 0 ≤ P.slot)
    have heta := hext g
    have hlw := hloop g
    have hr := hra hg
    have hrel := ih hmb
    simp only [insetAt, ite_eq_right (Nat.ne_of_lt hg)] at hla
    constructor <;> omega

omit hinset hslot

/-- The plain-node draw interval lies in its own translated reservation hull;
loop extent is counted by allocation but is not part of the drawn box. -/
theorem allocatedMember_crossHull {v g : Nat} {n : ProperNode}
    (hn : p.nodes[v]? = some n) (hb : n.node.border = 0) (hg : st.groups.getD v 0 = g) :
    let start := st.allocation.lefts.getD g 0 + insetAt P rm g
    let left := st.shifted.getD v 0 - Int.fdiv n.node.w 2
    start ≤ left ∧ left + n.node.w ≤ start + st.placement.buckets.widths.getD g 0 := by
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
      else 0) = insetAt P rm g := by
    rw [hr]
    by_cases heq : g = rm.clusters.length
    · simp [insetAt, heq]
    · have hgb : g ≤ rm.clusters.length := by rw [← hg]; exact actualMember_group_bound st hn
      have hlt : g < rm.clusters.length := by omega
      rw [actualGroup_inset st hparents hmin hlt]
      simp [insetAt, heq]
  unfold regionBucketShift
  rw [hstart]
  constructor <;> omega

include hinset hslot

private theorem memberHullInsideBudget {g : Nat} {x w : Int}
    (hg : g < rm.clusters.length)
    (hbox : st.allocation.lefts.getD g 0 + insetAt P rm g ≤ x ∧
      x + w ≤ st.allocation.lefts.getD g 0 + insetAt P rm g + st.placement.buckets.widths.getD g 0) :
    st.allocation.lefts.getD g 0 ≤ x ∧
      x + w ≤ st.allocation.lefts.getD g 0 + st.allocation.widths.getD g 0 := by
  have hwidth := reservedWidthsRoom st hparents hmin hg
  have hf := reservedWidthsNonnegative st hinset hslot
  have hsum := sum_nonnegative hf (st.placement.children.getD g [])
  obtain ⟨_, hext, hloop⟩ := st.bucket_signs (by omega : 0 ≤ P.slot)
  have heta := hext g
  have hlw := hloop g
  simp only [insetAt, ite_eq_right (Nat.ne_of_lt hg)] at hbox
  constructor <;> omega

private theorem laneWithinOwner {owner : Nat} {lane reach : Int} (ho : owner < rm.clusters.length)
    (hband : st.allocation.lefts.getD owner 0 + st.allocation.widths.getD owner 0 -
        st.placement.buckets.loopWidth.getD owner 0 - regionInsetOf P -
        laneExtentOf st.placement.buckets P.slot owner + P.slot ≤ lane ∧
      lane + reach ≤ st.allocation.lefts.getD owner 0 + st.allocation.widths.getD owner 0 -
        st.placement.buckets.loopWidth.getD owner 0 - regionInsetOf P) :
    st.allocation.lefts.getD owner 0 + regionInsetOf P + st.placement.buckets.widths.getD owner 0 ≤ lane ∧
    lane + reach ≤ st.allocation.lefts.getD owner 0 + st.allocation.widths.getD owner 0 := by
  have hw := reservedWidthsRoom st hparents hmin ho
  have hf := reservedWidthsNonnegative st hinset hslot
  have hs := sum_nonnegative hf (st.placement.children.getD owner [])
  have hl := (st.bucket_signs (by omega : 0 ≤ P.slot)).2.2 owner
  constructor <;> omega

/-- The entire reserved lane band separates from the plain member's draw interval. -/
theorem laneCrossClear_of_bucketHull {owner g : Nat} {lane reach : Int} {rect : Rect}
    (ho : owner < rm.clusters.length)
    (hownerPath : TrunkBranch st.placement.children rm.clusters.length owner)
    (hmemberPath : TrunkBranch st.placement.children rm.clusters.length g)
    (hbox : st.allocation.lefts.getD g 0 + insetAt P rm g ≤ rect.x ∧
      rect.x + rect.w ≤ st.allocation.lefts.getD g 0 + insetAt P rm g + st.placement.buckets.widths.getD g 0)
    (hband : st.allocation.lefts.getD owner 0 + st.allocation.widths.getD owner 0 -
        st.placement.buckets.loopWidth.getD owner 0 - regionInsetOf P -
        laneExtentOf st.placement.buckets P.slot owner + P.slot ≤ lane ∧
      lane + reach ≤ st.allocation.lefts.getD owner 0 + st.allocation.widths.getD owner 0 -
        st.placement.buckets.loopWidth.getD owner 0 - regionInsetOf P) :
    lane + reach ≤ rect.x ∨ rect.x + rect.w ≤ lane := by
  let L (k : Nat) := st.allocation.lefts.getD k 0
  let W (k : Nat) := st.allocation.widths.getD k 0
  let B (k : Nat) := st.placement.buckets.widths.getD k 0
  have hLane := laneWithinOwner st hparents hmin hinset hslot ho hband
  have hlo : L owner ≤ lane := by
    have h := st.bucket_width_and_hull.1 owner
    change 0 ≤ B owner at h
    change L owner + regionInsetOf P + B owner ≤ lane ∧ lane + reach ≤ L owner + W owner at hLane
    omega
  have memberBounds (k : Nat) (hk : k < rm.clusters.length)
      (path : TrunkBranch st.placement.children k g) : L k ≤ rect.x ∧ rect.x + rect.w ≤ L k + W k := by
    have hgb := branch_bound (fun _ _ hm => actualChild_bound st hparents hmin hm) path hk
    have hb := memberHullInsideBudget st hparents hmin hinset hslot hgb hbox
    have hp := actualBranch_budget st hparents hmin hinset hslot hk path
    change L g ≤ rect.x ∧ rect.x + rect.w ≤ L g + W g at hb
    change L k ≤ L g ∧ L g + W g ≤ L k + W k at hp
    exact ⟨Int.le_trans hp.1 hb.1, Int.le_trans hb.2 hp.2⟩
  have hchildren : ∀ g c, c ∈ st.placement.children.getD g [] → c < rm.clusters.length :=
    fun _ _ hc => actualChild_bound st hparents hmin hc
  rcases classifyBranches hchildren hownerPath (Nat.le_refl _) hmemberPath with hwithin |
    ⟨hk, ha, ap⟩ | ⟨hk, ha, hb, hne, ap, bp⟩
  · cases hwithin with
    | here =>
      right
      have hbg := hbox.2
      simp only [insetAt, ite_eq_right (Nat.ne_of_lt ho)] at hbg
      exact Int.le_trans hbg hLane.1
    | @step _ child _ hc path =>
      have hcb := actualChild_bound st hparents hmin hc
      have hr := (actualChildBudget_inside st hparents hmin hinset hslot (Nat.le_of_lt ho) hc).2 ho
      have hv := (memberBounds child hcb path).2
      have hs := hband.1
      change L child + W child + regionInsetOf P + laneExtentOf st.placement.buckets P.slot owner +
        st.placement.buckets.loopWidth.getD owner 0 ≤ L owner + W owner at hr
      change L owner + W owner - st.placement.buckets.loopWidth.getD owner 0 -
        regionInsetOf P - laneExtentOf st.placement.buckets P.slot owner + P.slot ≤ lane at hs
      exact Or.inr (by omega)
  · have hc := (actualChildBudget_inside st hparents hmin hinset hslot hk ha).1
    have hp := (actualBranch_budget st hparents hmin hinset hslot (actualChild_bound st hparents hmin ha) ap).1
    exact Or.inr (Int.le_trans hbox.2 (Int.le_trans hc (Int.le_trans hp hlo)))
  · have hab := actualChild_bound st hparents hmin ha
    have hbb := actualChild_bound st hparents hmin hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
    have hij : i ≠ j := fun h => hne (Option.some.inj (hi.symm.trans (h ▸ hj)))
    have hownerB := actualBranch_budget st hparents hmin hinset hslot hab ap
    have hmemberB := memberBounds _ hbb bp
    rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
    · have hs := actualSiblingBudget_order st hparents hmin hinset hslot hk hi hj hlt
      exact Or.inl (Int.le_trans hLane.2 (Int.le_trans hownerB.2 (Int.le_trans hs hmemberB.1)))
    · have hs := actualSiblingBudget_order st hparents hmin hinset hslot hk hj hi hgt
      exact Or.inr (Int.le_trans hmemberB.2 (Int.le_trans hs (Int.le_trans hownerB.1 hlo)))

end Allocation

end Elegant.Layered.PipelineImpl.RegionOrdinaryC6

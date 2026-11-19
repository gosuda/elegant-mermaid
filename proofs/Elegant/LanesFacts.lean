import Elegant.Lanes

set_option autoImplicit false

/-! Facts about the lanes family for `gitgraph`: the lane order is the sorted lane key and a
bijection onto the branches, the commit levels follow the parent chain, the commit axis is strictly
increasing in the level, and every commit lies on its lane frame inside the canvas. -/

namespace Elegant
namespace Lanes

/-! ### Lists built front to back -/

theorem buildUp_length {α : Type} (f : List α → Nat → α) (k : Nat) :
    (buildUp f k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [buildUp, ih]

theorem buildUp_succ {α : Type} (f : List α → Nat → α) (k : Nat) :
    buildUp f (k + 1) = buildUp f k ++ [f (buildUp f k) k] := rfl

theorem buildUp_prefix {α : Type} (f : List α → Nat → α) (k d : Nat) :
    ∃ r, buildUp f (k + d) = buildUp f k ++ r := by
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨r ++ [f (buildUp f (k + d)) (k + d)], ?_⟩
    rw [← Nat.add_assoc, buildUp_succ, hr, List.append_assoc]

theorem buildUp_getElem? {α : Type} (f : List α → Nat → α) {i k : Nat} (h : i < k) :
    (buildUp f k)[i]? = some (f (buildUp f i) i) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  obtain ⟨r, hr⟩ := buildUp_prefix f (i + 1) d
  have hk : i + d + 1 = i + 1 + d := by omega
  rw [hk, hr, buildUp_succ, List.append_assoc, List.getElem?_append_right (by simp [buildUp_length])]
  simp [buildUp_length]

theorem buildUp_getD {α : Type} (f : List α → Nat → α) {i k : Nat} (h : i < k) (d : α) :
    (buildUp f k).getD i d = f (buildUp f i) i := by
  rw [List.getD_eq_getElem?_getD, buildUp_getElem? f h]
  rfl

/-! ### The lane order -/

theorem laneKeyLe_trans (order : Nat → Int) (a b c : Nat)
    (h1 : laneKeyLe order a b = true) (h2 : laneKeyLe order b c = true) :
    laneKeyLe order a c = true := by
  simp only [laneKeyLe, decide_eq_true_eq] at *
  omega

theorem laneKeyLe_total (order : Nat → Int) (a b : Nat) :
    (laneKeyLe order a b || laneKeyLe order b a) = true := by
  simp only [laneKeyLe, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- The strict lane key: the order, then the declaration index. -/
def LaneKeyLt (order : Nat → Int) (a b : Nat) : Prop :=
  order a < order b ∨ (order a = order b ∧ a < b)

theorem laneOrder_perm (g : GitInput) : (laneOrder g).Perm (List.range g.branches.length) :=
  List.mergeSort_perm _ _

theorem laneOrder_nodup (g : GitInput) : (laneOrder g).Nodup :=
  (laneOrder_perm g).nodup_iff.mpr List.nodup_range

theorem laneOrder_length (g : GitInput) : (laneOrder g).length = g.branches.length := by
  rw [(laneOrder_perm g).length_eq, List.length_range]

/-- The lanes are the branches sorted by the lane key `(order, declaration index)`. -/
theorem gitgraph_lanes_sorted (g : GitInput) :
    (laneOrder g).Pairwise (LaneKeyLt (orderOf g)) ∧
      laneOrder g = (List.range g.branches.length).mergeSort (laneKeyLe (orderOf g)) := by
  refine ⟨?_, rfl⟩
  have hs := List.pairwise_mergeSort (laneKeyLe_trans (orderOf g)) (laneKeyLe_total (orderOf g))
    (List.range g.branches.length)
  have hn : (laneOrder g).Pairwise (fun a b => a ≠ b) := laneOrder_nodup g
  have hb := hs.and hn
  refine hb.imp ?_
  intro a b ⟨hle, hne⟩
  simp only [laneKeyLe, decide_eq_true_eq] at hle
  unfold LaneKeyLt
  omega

/-- Every branch has exactly one lane: the lane order is a permutation of the branches, and a
branch sits at the one position its rank names. -/
theorem gitgraph_one_lane_per_branch (g : GitInput) :
    (laneOrder g).Perm (List.range g.branches.length) ∧ (laneOrder g).Nodup ∧
      ∀ b, b < g.branches.length →
        rankOf g b < g.branches.length ∧ (laneOrder g)[rankOf g b]? = some b ∧
          ∀ k, (laneOrder g)[k]? = some b → k = rankOf g b := by
  refine ⟨laneOrder_perm g, laneOrder_nodup g, fun b hb => ?_⟩
  have hmem : b ∈ laneOrder g := by
    rw [(laneOrder_perm g).mem_iff, List.mem_range]
    exact hb
  have hlt : rankOf g b < (laneOrder g).length := List.idxOf_lt_length_iff.mpr hmem
  refine ⟨by rw [laneOrder_length] at hlt; exact hlt, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem hlt]
    simp [rankOf, List.getElem_idxOf]
  · intro k hk
    have hkl : k < (laneOrder g).length := by
      cases Nat.lt_or_ge k (laneOrder g).length with
      | inl h => exact h
      | inr h =>
        rw [List.getElem?_eq_none h] at hk
        cases hk
    rw [List.getElem?_eq_getElem hkl] at hk
    have hkb : (laneOrder g)[k] = b := by simpa using hk
    have := (laneOrder_nodup g).idxOf_getElem k hkl
    rw [hkb] at this
    rw [rankOf]
    exact this.symm


/-! ### Commit levels -/

theorem foldl_max_le_aux (f : Nat → Nat) (l : List Nat) (a : Nat) :
    a ≤ l.foldl (fun acc p => max acc (f p)) a ∧
      ∀ x ∈ l, f x ≤ l.foldl (fun acc p => max acc (f p)) a := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := ih (max a (f x))
    simp only [List.foldl_cons]
    refine ⟨by omega, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · omega
    · exact h2 y hy

theorem parentsOf_lt {g : GitInput} {i p : Nat} (h : p ∈ parentsOf g i) : p < i := by
  unfold parentsOf at h
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp h
  have := (List.mem_filter.mp hl).2
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at this
  omega

theorem mem_parentsOf {g : GitInput} {l : Link} (hl : l ∈ g.links) (hpick : l.pick = false)
    (hlt : l.src < l.dst) : l.src ∈ parentsOf g l.dst := by
  unfold parentsOf
  refine List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨hl, ?_⟩, rfl⟩
  simp [hpick, hlt]

theorem commitLevels_length (g : GitInput) : (commitLevels g).length = g.commits.length :=
  buildUp_length _ _

theorem levels_getD {g : GitInput} {i : Nat} (h : i < g.commits.length) :
    (commitLevels g).getD i 0 = levelStep g (levelsUpTo g i) i :=
  buildUp_getD (levelStep g) h 0

theorem levelsUpTo_getD {g : GitInput} {i p : Nat} (hp : p < i) (hi : i < g.commits.length) :
    (levelsUpTo g i).getD p 0 = (commitLevels g).getD p 0 := by
  rw [levelsUpTo, buildUp_getD (levelStep g) hp, commitLevels, levelsUpTo,
    buildUp_getD (levelStep g) (Nat.lt_trans hp hi)]

/-- A child sits at least one level below each earlier-declared, non-pick parent. -/
theorem level_succ_le {g : GitInput} {l : Link} (hl : l ∈ g.links) (hpick : l.pick = false)
    (hlt : l.src < l.dst) (hdst : l.dst < g.commits.length) :
    (commitLevels g).getD l.src 0 + 1 ≤ (commitLevels g).getD l.dst 0 := by
  rw [levels_getD hdst]
  have hmem := mem_parentsOf hl hpick hlt
  have hfold := (foldl_max_le_aux (fun p => (levelsUpTo g l.dst).getD p 0 + 1) (parentsOf g l.dst)
    (laneFloor g (levelsUpTo g l.dst) (branchOf g l.dst))).2 l.src hmem
  have hs := levelsUpTo_getD hlt hdst
  unfold levelStep
  simp only [hs] at hfold
  exact hfold

theorem level_lt_count {g : GitInput} {i : Nat} (h : i < g.commits.length) :
    (commitLevels g).getD i 0 < levelCount (commitLevels g) := by
  have hlen : i < (commitLevels g).length := by rw [commitLevels_length]; exact h
  have hmem : (commitLevels g).getD i 0 ∈ commitLevels g := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    exact List.getElem_mem hlen
  have := (foldl_max_le_aux (fun l => l + 1) (commitLevels g) 0).2 _ hmem
  unfold levelCount
  omega

/-- The first commit has level 0. -/
theorem first_level_zero {g : GitInput} (h : 0 < g.commits.length) :
    (commitLevels g).getD 0 0 = 0 := by
  rw [levels_getD h]
  have hp : parentsOf g 0 = [] := by
    cases hpo : parentsOf g 0 with
    | nil => rfl
    | cons p ps =>
      have := parentsOf_lt (g := g) (i := 0) (p := p) (by rw [hpo]; exact List.mem_cons_self)
      omega
  simp [levelStep, hp, laneFloor, levelsUpTo, buildUp]

theorem zip_getElem?_commit (g : GitInput) (s : List Nat) {k : Nat} (hk : k < s.length)
    (hc : k < g.commits.length) :
    (g.commits.zip s)[k]? = some (g.commits[k], s[k]) := by
  simp [List.getElem?_zip_eq_some, hk, hc]

theorem laneFloor_take_succ (g : GitInput) (s : List Nat) (b : Nat) {k : Nat}
    (hk : k < s.length) (hc : k < g.commits.length) :
    ((g.commits.zip s).take (k + 1)).foldl (floorStep b) 0 =
      floorStep b (((g.commits.zip s).take k).foldl (floorStep b) 0) (g.commits[k], s[k]) := by
  rw [List.take_add_one, zip_getElem?_commit g s hk hc]
  simp [List.foldl_append]

theorem branchOf_getElem (g : GitInput) {k : Nat} (hk : k < g.commits.length) :
    branchOf g k = g.commits[k].branch := by
  simp [branchOf, List.getElem?_eq_getElem hk]

theorem laneFloor_ge_aux (g : GitInput) (s : List Nat) (b : Nat) (hs : s.length ≤ g.commits.length)
    (hmono : ∀ q r, q < r → r < s.length → branchOf g q = b → branchOf g r = b →
      s.getD q 0 < s.getD r 0) :
    ∀ k, k ≤ s.length → ∀ p, p < k → branchOf g p = b →
      s.getD p 0 + 1 ≤ ((g.commits.zip s).take k).foldl (floorStep b) 0 := by
  intro k
  induction k with
  | zero =>
    intro _ p hp
    omega
  | succ k ih =>
    intro hk p hp hb
    have hks : k < s.length := by omega
    have hkc : k < g.commits.length := by omega
    have hsk : s.getD k 0 = s[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hks]
      rfl
    rw [laneFloor_take_succ g s b hks hkc]
    by_cases hbr : g.commits[k].branch = b
    · have hbk : branchOf g k = b := by rw [branchOf_getElem g hkc, hbr]
      have hstep : floorStep b (((g.commits.zip s).take k).foldl (floorStep b) 0)
          (g.commits[k], s[k]) = s[k] + 1 := by
        simp [floorStep, hbr]
      rw [hstep]
      rcases Nat.lt_or_ge p k with hpk | hpk
      · have := hmono p k hpk hks hb hbk
        omega
      · have hpe : p = k := by omega
        subst hpe
        omega
    · have hstep : floorStep b (((g.commits.zip s).take k).foldl (floorStep b) 0)
          (g.commits[k], s[k]) = ((g.commits.zip s).take k).foldl (floorStep b) 0 := by
        simp [floorStep, hbr]
      rw [hstep]
      have hpk : p < k := by
        rcases Nat.lt_or_ge p k with h | h
        · exact h
        · have hpe : p = k := by omega
          subst hpe
          exact absurd (by rw [← branchOf_getElem g hkc]; exact hb) hbr
      exact ih (by omega) p hpk hb

theorem laneFloor_ge (g : GitInput) (s : List Nat) (b : Nat) (hs : s.length ≤ g.commits.length)
    (hmono : ∀ q r, q < r → r < s.length → branchOf g q = b → branchOf g r = b →
      s.getD q 0 < s.getD r 0)
    {p : Nat} (hp : p < s.length) (hb : branchOf g p = b) : s.getD p 0 + 1 ≤ laneFloor g s b := by
  have h := laneFloor_ge_aux g s b hs hmono s.length (Nat.le_refl _) p hp hb
  have hz : (g.commits.zip s).length ≤ s.length := by
    rw [List.length_zip]
    exact Nat.min_le_right _ _
  unfold laneFloor
  rwa [List.take_of_length_le hz] at h

/-- Commits of one lane have strictly increasing levels in declaration order. -/
theorem lane_level_lt (g : GitInput) : ∀ i j, j < i → i < g.commits.length →
    branchOf g j = branchOf g i → (commitLevels g).getD j 0 < (commitLevels g).getD i 0 := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro j hji hi hb
    have hlen : (levelsUpTo g i).length = i := buildUp_length _ _
    have hmono : ∀ q r, q < r → r < (levelsUpTo g i).length → branchOf g q = branchOf g i →
        branchOf g r = branchOf g i →
        (levelsUpTo g i).getD q 0 < (levelsUpTo g i).getD r 0 := by
      intro q r hqr hr hbq hbr
      have hri : r < i := by omega
      rw [levelsUpTo_getD (by omega : q < i) hi, levelsUpTo_getD hri hi]
      exact ih r hri q hqr (by omega) (by rw [hbq, hbr])
    have hfloor := laneFloor_ge g (levelsUpTo g i) (branchOf g i) (by omega) hmono
      (by omega : j < (levelsUpTo g i).length) hb
    rw [levelsUpTo_getD hji hi] at hfloor
    rw [levels_getD hi]
    have hfold := (foldl_max_le_aux (fun p => (levelsUpTo g i).getD p 0 + 1) (parentsOf g i)
      (laneFloor g (levelsUpTo g i) (branchOf g i))).1
    unfold levelStep
    omega

/-! ### The commit axis -/

theorem levelGap_ge (d : Direction) (c : GitConsts) (before after : Int) :
    c.commitStep ≤ levelGap d c before after := by
  unfold levelGap
  split <;> omega

theorem reachG_length (g : GitInput) (c : GitConsts) :
    (reachG g c).length = levelCount (commitLevels g) := by
  unfold reachG reachOf
  split <;> simp

theorem axisG_length (g : GitInput) (c : GitConsts) :
    (axisG g c).length = levelCount (commitLevels g) := by
  unfold axisG levelAxis
  rw [buildUp_length, reachG_length]

theorem axis_getD (g : GitInput) (c : GitConsts) {k : Nat} (h : k < (axisG g c).length) :
    (axisG g c).getD k 0 = axisStep g.direction c (reachG g c)
      (buildUp (axisStep g.direction c (reachG g c)) k) k := by
  have e : axisG g c = buildUp (axisStep g.direction c (reachG g c)) (reachG g c).length := rfl
  have hk : k < (reachG g c).length := by
    rw [e, buildUp_length] at h
    exact h
  rw [e]
  exact buildUp_getD _ hk 0

theorem axis_zero (g : GitInput) (c : GitConsts) (h : 0 < (axisG g c).length) :
    (axisG g c).getD 0 0 = 0 := by
  rw [axis_getD g c h]
  simp [axisStep]

theorem axis_succ (g : GitInput) (c : GitConsts) {k : Nat} (h : k + 1 < (axisG g c).length) :
    (axisG g c).getD (k + 1) 0 = (axisG g c).getD k 0 +
      levelGap g.direction c ((reachG g c).getD k 0) ((reachG g c).getD (k + 1) 0) := by
  have hk : k < (axisG g c).length := by omega
  rw [axis_getD g c h, axis_getD g c hk]
  have hb : (buildUp (axisStep g.direction c (reachG g c)) (k + 1)).getD k 0 =
      axisStep g.direction c (reachG g c) (buildUp (axisStep g.direction c (reachG g c)) k) k :=
    buildUp_getD _ (Nat.lt_succ_self k) 0
  have hs : axisStep g.direction c (reachG g c)
      (buildUp (axisStep g.direction c (reachG g c)) (k + 1)) (k + 1) =
      (buildUp (axisStep g.direction c (reachG g c)) (k + 1)).getD k 0 +
        levelGap g.direction c ((reachG g c).getD k 0) ((reachG g c).getD (k + 1) 0) := by
    simp [axisStep]
  rw [hs, hb]

/-- The commit axis is strictly increasing in the level when the level gap is positive. -/
theorem axis_strict (g : GitInput) (c : GitConsts) (hc : 0 < c.commitStep) :
    ∀ j, j < (axisG g c).length → ∀ i, i < j → (axisG g c).getD i 0 < (axisG g c).getD j 0 := by
  intro j
  induction j with
  | zero => intro _ i hi; omega
  | succ j ih =>
    intro hj i hi
    have hjl : j < (axisG g c).length := by omega
    have hgap := levelGap_ge g.direction c ((reachG g c).getD j 0) ((reachG g c).getD (j + 1) 0)
    have hs := axis_succ g c hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hij | rfl
    · have := ih hjl i hij
      omega
    · omega

theorem axis_nonneg (g : GitInput) (c : GitConsts) (hc : 0 < c.commitStep) {j : Nat}
    (hj : j < (axisG g c).length) : 0 ≤ (axisG g c).getD j 0 := by
  cases j with
  | zero => rw [axis_zero g c hj]; exact Int.le_refl 0
  | succ j =>
    have := axis_strict g c hc (j + 1) hj 0 (Nat.succ_pos j)
    have h0 := axis_zero g c (by omega)
    omega

theorem axis_mono (g : GitInput) (c : GitConsts) (hc : 0 < c.commitStep) {i j : Nat}
    (hij : i ≤ j) (hj : j < (axisG g c).length) : (axisG g c).getD i 0 ≤ (axisG g c).getD j 0 := by
  rcases Nat.lt_or_ge i j with h | h
  · exact Int.le_of_lt (axis_strict g c hc j hj i h)
  · have : i = j := Nat.le_antisymm hij h
    subst this
    exact Int.le_refl _

theorem steps_getD (g : GitInput) (c : GitConsts) {i : Nat} (h : i < g.commits.length) :
    (stepsG g c).getD i 0 = (axisG g c).getD ((commitLevels g).getD i 0) 0 := by
  have hlen : i < (commitLevels g).length := by rw [commitLevels_length]; exact h
  unfold stepsG
  have hl : (commitLevels g).getD i 0 = (commitLevels g)[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    rfl
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen, hl]
  simp [List.getD_eq_getElem?_getD]

theorem maxStep_nonneg (g : GitInput) (c : GitConsts) (hc : 0 < c.commitStep) :
    0 ≤ maxStepG g c := by
  unfold maxStepG
  rcases Nat.lt_or_ge (levelCount (commitLevels g) - 1) (axisG g c).length with h | h
  · exact axis_nonneg g c hc h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
    exact Int.le_refl 0

/-- Every commit sits on the commit axis between its origin and the last level. -/
theorem steps_bounds (g : GitInput) (c : GitConsts) (hc : 0 < c.commitStep) {i : Nat}
    (h : i < g.commits.length) : 0 ≤ (stepsG g c).getD i 0 ∧ (stepsG g c).getD i 0 ≤ maxStepG g c := by
  rw [steps_getD g c h]
  have hlt := level_lt_count h
  have hL := axisG_length g c
  refine ⟨axis_nonneg g c hc (by omega), ?_⟩
  unfold maxStepG
  exact axis_mono g c hc (by omega) (by omega)

/-- Each non-root commit sits strictly after each of its parents on the commit axis. -/
theorem gitgraph_commit_steps_increasing (g : GitInput) (c : GitConsts) (hc : 0 < c.commitStep)
    {l : Link} (hl : l ∈ g.links) (hpick : l.pick = false) (hlt : l.src < l.dst)
    (hdst : l.dst < g.commits.length) :
    (stepsG g c).getD l.src 0 < (stepsG g c).getD l.dst 0 := by
  have hsrc : l.src < g.commits.length := Nat.lt_trans hlt hdst
  rw [steps_getD g c hsrc, steps_getD g c hdst]
  have hlv := level_succ_le hl hpick hlt hdst
  have hcount := level_lt_count hdst
  have hL := axisG_length g c
  exact axis_strict g c hc _ (by omega) _ (by omega)

/-- The first commit sits at the origin of the commit axis. -/
theorem gitgraph_first_step_zero (g : GitInput) (c : GitConsts) (h : 0 < g.commits.length) :
    (stepsG g c).getD 0 0 = 0 := by
  rw [steps_getD g c h, first_level_zero h]
  exact axis_zero g c (by have := level_lt_count h; have := axisG_length g c; omega)

/-- A later commit of a lane sits strictly after an earlier one on the commit axis. -/
theorem gitgraph_lane_steps_increasing (g : GitInput) (c : GitConsts) (hc : 0 < c.commitStep)
    {j i : Nat} (hji : j < i) (hi : i < g.commits.length) (hb : branchOf g j = branchOf g i) :
    (stepsG g c).getD j 0 < (stepsG g c).getD i 0 := by
  have hj : j < g.commits.length := Nat.lt_trans hji hi
  rw [steps_getD g c hj, steps_getD g c hi]
  have hlv := lane_level_lt g i j hji hi hb
  have hcount := level_lt_count hi
  have hL := axisG_length g c
  exact axis_strict g c hc _ (by omega) _ (by omega)

/-! ### Points, lane frames and connectors -/

/-- A lane frame is a segment through the commits of its lane along the commit axis. -/
theorem laneBand_contains (d : Direction) (maxStep s lane labelGap h : Int) (hg : 0 ≤ labelGap)
    (hs0 : 0 ≤ s) (hs1 : s ≤ maxStep) (hh : 0 ≤ h) :
    (laneBand (atPoint d maxStep (-labelGap) lane) (atPoint d maxStep (maxStep + h) lane)).Contained
      ⟨(atPoint d maxStep s lane).x, (atPoint d maxStep s lane).y, 0, 0⟩ := by
  cases d <;> simp only [laneBand, atPoint, absI, Rect.Contained] <;> omega

/-- A lane frame has no area. -/
theorem laneBand_flat (d : Direction) (maxStep a b lane : Int) :
    (laneBand (atPoint d maxStep a lane) (atPoint d maxStep b lane)).w = 0 ∨
      (laneBand (atPoint d maxStep a lane) (atPoint d maxStep b lane)).h = 0 := by
  cases d <;> simp [laneBand, atPoint, absI]

theorem atPoint_same_lane (d : Direction) (maxStep a b lane : Int) :
    (atPoint d maxStep a lane).x = (atPoint d maxStep b lane).x ∨
      (atPoint d maxStep a lane).y = (atPoint d maxStep b lane).y := by
  cases d <;> simp [atPoint]

theorem atPoint_same_axis (d : Direction) (maxStep a lane lane' : Int) :
    (atPoint d maxStep a lane).x = (atPoint d maxStep a lane').x ∨
      (atPoint d maxStep a lane).y = (atPoint d maxStep a lane').y := by
  cases d <;> simp [atPoint]

theorem routeOf_orthogonal (sh : Shape) (g : GitInput) (c : GitConsts) (l : Link) :
    Polyline.isOrthogonal (sh.routeOf g c l) = true := by
  unfold Shape.routeOf Shape.pointAt
  dsimp only
  split
  · rename_i hb
    have he : branchOf g l.src = branchOf g l.dst := by simpa using hb
    rw [he]
    simp only [Polyline.isOrthogonal, Bool.and_true, Bool.or_eq_true, decide_eq_true_eq]
    exact atPoint_same_lane _ _ _ _ _
  · simp only [Polyline.isOrthogonal, Bool.and_true, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq]
    exact ⟨atPoint_same_lane _ _ _ _ _, atPoint_same_axis _ _ _ _ _, atPoint_same_lane _ _ _ _ _⟩

theorem routeOf_head (sh : Shape) (g : GitInput) (c : GitConsts) (l : Link) :
    (sh.routeOf g c l).head? = some (sh.commitPoint g l.src) := by
  unfold Shape.routeOf Shape.commitPoint
  dsimp only
  split <;> rfl

theorem routeOf_getLast (sh : Shape) (g : GitInput) (c : GitConsts) (l : Link) :
    (sh.routeOf g c l).getLast? = some (sh.commitPoint g l.dst) := by
  unfold Shape.routeOf Shape.commitPoint
  dsimp only
  split <;> rfl

/-! ### The extent and the frame -/

theorem half_nonneg {v : Int} (h : 0 ≤ v) : 0 ≤ half v := Int.fdiv_nonneg h (by decide)

theorem unionRaw_left (a b : Rect) : (Rect.unionRaw a b).Contained a := by
  simp only [Rect.unionRaw, Rect.Contained]
  omega

theorem unionRaw_right (a b : Rect) : (Rect.unionRaw a b).Contained b := by
  simp only [Rect.unionRaw, Rect.Contained]
  omega

theorem foldl_union (rs : List Rect) (a : Rect) :
    (rs.foldl Rect.unionRaw a).Contained a ∧ ∀ r ∈ rs, (rs.foldl Rect.unionRaw a).Contained r := by
  induction rs generalizing a with
  | nil => exact ⟨Rect.Contained.refl a, by simp⟩
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := ih (Rect.unionRaw a x)
    simp only [List.foldl_cons]
    refine ⟨Rect.Contained.trans h1 (unionRaw_left a x), ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Rect.Contained.trans h1 (unionRaw_right a r)
    · exact h2 r hr

/-- The extent contains every part. -/
theorem extent_contains (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan) {r : Rect}
    (hr : r ∈ p.parts g c profile) : (p.extent g c profile).Contained r := by
  unfold Plan.extent
  cases hp : p.parts g c profile with
  | nil =>
    rw [hp] at hr
    simp at hr
  | cons r0 rest =>
    rw [hp] at hr
    dsimp only
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (foldl_union rest r).1
    · exact (foldl_union rest r0).2 r hr

theorem getElem?_zip_map (n b : Nat) (hb : b < n) {α β γ : Type} (f : Nat → α) (h : Nat → β)
    (k : α × β → γ) :
    (List.map k (List.zip (List.map f (List.range n)) (List.map h (List.range n))))[b]? =
      some (k (f b, h b)) := by
  have : (List.zip (List.map f (List.range n)) (List.map h (List.range n)))[b]? =
      some (f b, h b) := by
    rw [List.getElem?_zip_eq_some]
    simp [List.getElem?_map, List.getElem?_range hb]
  simp [List.getElem?_map, this]

theorem getElem?_map_range {n b : Nat} (hb : b < n) {α : Type} (f : Nat → α) :
    (List.map f (List.range n))[b]? = some (f b) := by
  simp [List.getElem?_map, List.getElem?_range hb]

theorem plan_points_getElem? (g : GitInput) (c : GitConsts) (profile : Profile) {i : Nat}
    (hi : i < g.commits.length) :
    (Plan.build g c profile).points[i]? = some ((Shape.of g c).commitPoint g i) :=
  getElem?_map_range hi _

/-- The frame of lane `b` before the shift. -/
def laneBandOf (g : GitInput) (c : GitConsts) (b : Nat) : Rect :=
  laneBand ((Shape.of g c).pointAt g (-c.labelGap) ((Shape.of g c).laneAxis g b))
    ((Shape.of g c).pointAt g ((Shape.of g c).maxStep + half c.commitStep)
      ((Shape.of g c).laneAxis g b))

def frameOf (g : GitInput) (c : GitConsts) (profile : Profile) : GitResult :=
  (Plan.build g c profile).frame g c profile

def frameDx (g : GitInput) (c : GitConsts) (profile : Profile) : Int :=
  (Plan.build g c profile).dx g c profile

def frameDy (g : GitInput) (c : GitConsts) (profile : Profile) : Int :=
  (Plan.build g c profile).dy g c profile

theorem plan_lanes_getElem? (g : GitInput) (c : GitConsts) (profile : Profile) {b : Nat}
    (hb : b < g.branches.length) :
    (Plan.build g c profile).lanes[b]? = some (laneBandOf g c b) :=
  getElem?_zip_map g.branches.length b hb _ _ _

theorem plan_routes_getElem? (g : GitInput) (c : GitConsts) (profile : Profile) {k : Nat} {l : Link}
    (hl : g.links[k]? = some l) :
    (Plan.build g c profile).routes[k]? = some ((Shape.of g c).routeOf g c l) := by
  simp [Plan.build, List.getElem?_map, hl]

theorem lane_mem_parts (g : GitInput) (c : GitConsts) (profile : Profile) {b : Nat}
    (hb : b < g.branches.length) :
    (Plan.build g c profile).lanes.getD b zeroRect ∈
      (Plan.build g c profile).parts g c profile := by
  unfold Plan.parts
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
  unfold Plan.branchParts
  exact List.mem_flatMap.mpr ⟨b, List.mem_range.mpr hb, by simp⟩

theorem marker_mem_parts (g : GitInput) (c : GitConsts) (profile : Profile) {i : Nat}
    (hi : i < g.commits.length) :
    markerBox c profile ((Plan.build g c profile).points.getD i ⟨0, 0⟩) ∈
      (Plan.build g c profile).parts g c profile := by
  unfold Plan.parts
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
  unfold Plan.commitParts
  refine List.mem_flatMap.mpr ⟨(g.commits[i], i), List.mem_zipIdx_iff_getElem?.mpr ?_, by simp⟩
  simp [List.getElem?_eq_getElem hi]

theorem markerBox_contains_point (c : GitConsts) (profile : Profile) (v : Point)
    (hr : 0 ≤ c.commitRadius) : (markerBox c profile v).Contained ⟨v.x, v.y, 0, 0⟩ := by
  cases profile <;> simp only [markerBox, Rect.Contained] <;> omega

theorem shiftRect_contained {a b : Rect} (dx dy : Int) :
    (shiftRect dx dy a).Contained (shiftRect dx dy b) ↔ a.Contained b := by
  simp only [shiftRect, Rect.Contained]
  omega

theorem isOrthogonal_map_shift (dx dy : Int) :
    ∀ ps : List Point,
      Polyline.isOrthogonal (ps.map (shiftPoint dx dy)) = Polyline.isOrthogonal ps
  | [] => rfl
  | [_] => rfl
  | p :: q :: rest => by
    have ih := isOrthogonal_map_shift dx dy (q :: rest)
    simp only [List.map_cons, shiftPoint] at ih ⊢
    simp [Polyline.isOrthogonal, ih]

theorem frame_lanes_eq (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan) :
    (p.frame g c profile).lanes = p.lanes.map (shiftRect (p.dx g c profile) (p.dy g c profile)) :=
  rfl

theorem frame_points_eq (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan) :
    (p.frame g c profile).points = p.points.map (shiftPoint (p.dx g c profile) (p.dy g c profile)) :=
  rfl

theorem frame_routes_eq (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan) :
    (p.frame g c profile).routes =
      p.routes.map (·.map (shiftPoint (p.dx g c profile) (p.dy g c profile))) :=
  rfl

theorem frame_canvas_eq (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan) :
    (p.frame g c profile).canvas =
      ⟨(p.extent g c profile).w + 2 * c.canvasMargin, (p.extent g c profile).h + 2 * c.canvasMargin⟩ :=
  rfl

theorem frame_lengths (g : GitInput) (c : GitConsts) (profile : Profile) :
    ((Plan.build g c profile).frame g c profile).lanes.length = g.branches.length ∧
      ((Plan.build g c profile).frame g c profile).points.length = g.commits.length ∧
      ((Plan.build g c profile).frame g c profile).routes.length = g.links.length := by
  simp [Plan.frame, Plan.build]

/-- A part of the extent lies inside the canvas once shifted by the frame. -/
theorem part_in_canvas (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan)
    (hm : 0 ≤ c.canvasMargin) {r : Rect} (hr : r ∈ p.parts g c profile) :
    0 ≤ r.x + p.dx g c profile ∧
      r.x + p.dx g c profile + r.w ≤ (p.frame g c profile).canvas.w ∧
      0 ≤ r.y + p.dy g c profile ∧
      r.y + p.dy g c profile + r.h ≤ (p.frame g c profile).canvas.h := by
  have h := extent_contains g c profile p hr
  simp only [Rect.Contained] at h
  rw [frame_canvas_eq]
  unfold Plan.dx Plan.dy
  dsimp only
  omega

theorem shifted_bounds (g : GitInput) (c : GitConsts) (profile : Profile) (p : Plan)
    (hm : 0 ≤ c.canvasMargin) {r : Rect} (h : (p.extent g c profile).Contained r) :
    0 ≤ r.x + p.dx g c profile ∧
      r.x + p.dx g c profile + r.w ≤ (p.frame g c profile).canvas.w ∧
      0 ≤ r.y + p.dy g c profile ∧
      r.y + p.dy g c profile + r.h ≤ (p.frame g c profile).canvas.h := by
  simp only [Rect.Contained] at h
  rw [frame_canvas_eq]
  unfold Plan.dx Plan.dy
  dsimp only
  omega

/-- Every lane frame lies inside the canvas and has no area. -/
theorem frame_lane (g : GitInput) (c : GitConsts) (profile : Profile) (hc : c.Pos) {b : Nat}
    (hb : b < g.branches.length) :
    (frameOf g c profile).lanes[b]? =
        some (shiftRect (frameDx g c profile) (frameDy g c profile) (laneBandOf g c b)) ∧
      0 ≤ (laneBandOf g c b).x + frameDx g c profile ∧
      (laneBandOf g c b).x + frameDx g c profile + (laneBandOf g c b).w ≤
        (frameOf g c profile).canvas.w ∧
      0 ≤ (laneBandOf g c b).y + frameDy g c profile ∧
      (laneBandOf g c b).y + frameDy g c profile + (laneBandOf g c b).h ≤
        (frameOf g c profile).canvas.h ∧
      ((laneBandOf g c b).w = 0 ∨ (laneBandOf g c b).h = 0) := by
  have hl := plan_lanes_getElem? g c profile hb
  have hgd : (Plan.build g c profile).lanes.getD b zeroRect = laneBandOf g c b := by
    rw [List.getD_eq_getElem?_getD, hl]
    rfl
  have hmem := lane_mem_parts g c profile hb
  rw [hgd] at hmem
  have hin := part_in_canvas g c profile _ hc.canvasMargin hmem
  refine ⟨?_, hin.1, hin.2.1, hin.2.2.1, hin.2.2.2, laneBand_flat _ _ _ _ _⟩
  rw [frameOf, frame_lanes_eq, List.getElem?_map, hl]
  rfl

/-- Every commit lies on the frame of its lane and inside the canvas. -/
theorem frame_point (g : GitInput) (c : GitConsts) (profile : Profile) (hc : c.Pos) (hwf : g.WF)
    {i : Nat} (hi : i < g.commits.length) :
    (frameOf g c profile).points[i]? =
        some (shiftPoint (frameDx g c profile) (frameDy g c profile)
          ((Shape.of g c).commitPoint g i)) ∧
      (frameOf g c profile).lanes[branchOf g i]? =
        some (shiftRect (frameDx g c profile) (frameDy g c profile)
          (laneBandOf g c (branchOf g i))) ∧
      0 ≤ ((Shape.of g c).commitPoint g i).x + frameDx g c profile ∧
      ((Shape.of g c).commitPoint g i).x + frameDx g c profile ≤ (frameOf g c profile).canvas.w ∧
      0 ≤ ((Shape.of g c).commitPoint g i).y + frameDy g c profile ∧
      ((Shape.of g c).commitPoint g i).y + frameDy g c profile ≤ (frameOf g c profile).canvas.h ∧
      (laneBandOf g c (branchOf g i)).Contained
        ⟨((Shape.of g c).commitPoint g i).x, ((Shape.of g c).commitPoint g i).y, 0, 0⟩ := by
  have hcm : g.commits[i]? = some g.commits[i] := List.getElem?_eq_getElem hi
  have hbr : branchOf g i = g.commits[i].branch := by simp [branchOf, hcm]
  have hb : branchOf g i < g.branches.length := by
    rw [hbr]
    exact hwf.branch _ (List.getElem_mem hi)
  have hl := plan_lanes_getElem? g c profile hb
  have hpt := plan_points_getElem? g c profile hi
  have hgd : (Plan.build g c profile).points.getD i ⟨0, 0⟩ = (Shape.of g c).commitPoint g i := by
    rw [List.getD_eq_getElem?_getD, hpt]
    rfl
  have hmem := marker_mem_parts g c profile hi
  rw [hgd] at hmem
  have hbound := steps_bounds g c hc.commitStep hi
  have hmk := markerBox_contains_point c profile ((Shape.of g c).commitPoint g i) hc.commitRadius
  have hrect := Rect.Contained.trans (extent_contains g c profile _ hmem) hmk
  have hsb := shifted_bounds g c profile _ hc.canvasMargin hrect
  refine ⟨?_, ?_, hsb.1, ?_, hsb.2.2.1, ?_, ?_⟩
  · rw [frameOf, frame_points_eq, List.getElem?_map, hpt]
    rfl
  · rw [frameOf, frame_lanes_eq, List.getElem?_map, hl]
    rfl
  · have := hsb.2.1
    simp only [frameDx, frameOf] at this ⊢
    omega
  · have := hsb.2.2.2
    simp only [frameDy, frameOf] at this ⊢
    omega
  · exact laneBand_contains g.direction (Shape.of g c).maxStep ((Shape.of g c).steps.getD i 0)
      ((Shape.of g c).laneAxis g (branchOf g i)) c.labelGap (half c.commitStep) hc.labelGap
      hbound.1 hbound.2 (half_nonneg (Int.le_of_lt hc.commitStep))

/-- Every connector is orthogonal and joins the points of its two commits. -/
theorem frame_route (g : GitInput) (c : GitConsts) (profile : Profile) (hwf : g.WF) {k : Nat}
    {l : Link} (hl : g.links[k]? = some l) :
    ∃ pts, (frameOf g c profile).routes[k]? = some pts ∧ Polyline.isOrthogonal pts = true ∧
      pts.head? = (frameOf g c profile).points[l.src]? ∧
      pts.getLast? = (frameOf g c profile).points[l.dst]? := by
  have hmem : l ∈ g.links := List.mem_of_getElem? hl
  have hb := hwf.link l hmem
  refine ⟨((Shape.of g c).routeOf g c l).map (shiftPoint (frameDx g c profile) (frameDy g c profile)),
    ?_, ?_, ?_, ?_⟩
  · rw [frameOf, frame_routes_eq, List.getElem?_map, plan_routes_getElem? g c profile hl]
    rfl
  · rw [isOrthogonal_map_shift]
    exact routeOf_orthogonal _ _ _ _
  · rw [List.head?_map, routeOf_head, frameOf, frame_points_eq, List.getElem?_map,
      plan_points_getElem? g c profile hb.1]
    rfl
  · rw [List.getLast?_map, routeOf_getLast, frameOf, frame_points_eq, List.getElem?_map,
      plan_points_getElem? g c profile hb.2]
    rfl

/-- Right to left is not a gitgraph direction: the family rejects it. -/
theorem gitgraph_rejects_rl (g : GitInput) (profile : Profile) (h : g.direction = .RL) :
    gitgraph g profile = .error .domain := by
  have hy : (g.direction == .RL) = true := by simp [h]
  unfold gitgraph
  simp only [hy, ↓reduceIte]
  rfl

/-- A gitgraph result is the frame of the plan under the loaded constants, and its direction
is a supported one. -/
theorem gitgraph_frame {g : GitInput} {profile : Profile} {res : GitResult}
    (h : gitgraph g profile = .ok res) :
    g.direction ≠ .RL ∧ ∃ c, GitConsts.load profile = .ok c ∧ res = frameOf g c profile := by
  by_cases hrl : g.direction = .RL
  · rw [gitgraph_rejects_rl g profile hrl] at h
    cases h
  · have hn : (g.direction == .RL) = false := by simp [hrl]
    unfold gitgraph at h
    simp only [hn, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
    refine ⟨hrl, ?_⟩
    cases hl : GitConsts.load profile with
    | error e =>
      simp only [hl] at h
      cases h
    | ok c =>
      simp only [hl] at h
      split at h
      · exact ⟨c, rfl, (Except.ok.inj h).symm⟩
      · cases h

namespace Timeline

theorem eventRects_lower (c : TimelineConsts) (x w top : Int) (es : List Event)
    (hg : 0 ≤ c.eventGap) (hh : ∀ e ∈ es, 0 ≤ eventHeight c e) :
    ∀ r ∈ eventRects c x w top es, top ≤ r.y := by
  induction es generalizing top with
  | nil => simp [eventRects]
  | cons e es ih =>
    intro r hr
    simp only [eventRects, List.mem_cons] at hr
    rcases hr with hr | hr
    · subst r
      exact Int.le_refl _
    · have he := hh e (by simp)
      have ht := ih (top + eventHeight c e + c.eventGap)
        (fun e he => hh e (by simp [he])) r hr
      omega

theorem timeline_events_stack_disjoint (c : TimelineConsts) (x w top : Int)
    (es : List Event) (hg : 0 ≤ c.eventGap)
    (hh : ∀ e ∈ es, 0 ≤ eventHeight c e) :
    (eventRects c x w top es).Pairwise
      (fun a b => a.y + a.h ≤ b.y ∧ Disjoint a b) := by
  induction es generalizing top with
  | nil => simp [eventRects]
  | cons e es ih =>
    rw [eventRects, List.pairwise_cons]
    constructor
    · intro r hr
      have lower := eventRects_lower c x w (top + eventHeight c e + c.eventGap) es hg
        (fun e he => hh e (by simp [he])) r hr
      constructor
      · simp only
        omega
      · unfold Disjoint Rect.meetsInterior
        simp only
        omega
    · exact ih (top + eventHeight c e + c.eventGap) (fun e he => hh e (by simp [he]))

end Timeline

namespace Eventmodeling

theorem frameSize_width_lower (c : EventConsts) (f : Frame) :
    c.boxMinWidth + 2 * c.boxPadding ≤ (frameSize c f).w := by
  unfold frameSize clamp
  simp only
  have h := Int.le_max_left c.boxMinWidth
    (min c.boxMaxWidth (max f.name.w ((f.data.map (·.w)).getD 0)))
  omega

theorem columnWalk_lower (c : EventConsts)
    (hc : c.boxOverlap < c.boxMinWidth + 3 * c.boxPadding)
    (hp : 0 ≤ c.boxPadding)
    (fs : List Frame) (reach : Int) (floor : List Int) :
    ∀ r ∈ columnWalk c reach floor fs, reach - c.boxOverlap + c.boxPadding ≤ r.x := by
  induction fs generalizing reach floor with
  | nil => simp [columnWalk]
  | cons f fs ih =>
    intro r hr
    simp only [columnWalk, List.mem_cons] at hr
    let x := max (reach - c.boxOverlap + c.boxPadding) (floor.getD f.lane 0)
    have hx : reach - c.boxOverlap + c.boxPadding ≤ x := Int.le_max_left _ _
    rcases hr with hr | hr
    · subst r
      exact hx
    · have hl := ih (x + (frameSize c f).w + c.boxPadding)
        (floor.set f.lane (x + (frameSize c f).w + c.boxPadding)) r hr
      have hw := frameSize_width_lower c f
      dsimp [x] at hx hl
      omega

theorem columnWalk_ordered (c : EventConsts)
    (hc : c.boxOverlap < c.boxMinWidth + 3 * c.boxPadding)
    (hp : 0 ≤ c.boxPadding)
    (fs : List Frame) (reach : Int) (floor : List Int) :
    (columnWalk c reach floor fs).Pairwise (fun a b => a.x < b.x) := by
  induction fs generalizing reach floor with
  | nil => simp [columnWalk]
  | cons f fs ih =>
    rw [columnWalk, List.pairwise_cons]
    constructor
    · intro r hr
      have hl := columnWalk_lower c hc hp fs _ _ r hr
      have hw := frameSize_width_lower c f
      dsimp only at hl ⊢
      omega
    · exact ih _ _

theorem eventmodeling_timeframes_ordered (g : Input) (profile : Profile) :
    (columns g (EventConsts.load profile)).Pairwise (fun a b => a.x < b.x) := by
  have hc := (event_constants_positive profile).2.2.2.2.1
  exact columnWalk_ordered (EventConsts.load profile) hc
    (Int.le_of_lt (event_constants_positive profile).2.2.2.1) g.frames _ _

theorem foldl_ge_initial {α : Type} (f : Int → α → Int)
    (hf : ∀ a x, a ≤ f a x) (xs : List α) (a : Int) :
    a ≤ xs.foldl f a := by
  induction xs generalizing a with
  | nil => exact Int.le_refl _
  | cons x xs ih =>
    exact Int.le_trans (hf a x) (ih (f a x))

theorem laneHeight_lower (g : Input) (c : EventConsts) (frames : List Rect) (i : Nat) :
    c.laneMinHeight + 2 * c.lanePadding ≤ laneHeight g c frames i := by
  unfold laneHeight
  have hf := foldl_ge_initial
    (fun h (p : Frame × Rect) => if p.1.lane == i then max h p.2.h else h)
    (by intro a x; split <;> first | exact Int.le_max_left _ _ | exact Int.le_refl _)
    (g.frames.zip frames)
    (max c.laneMinHeight ((((g.lanes[i]?).bind (·.caption)).map (·.h)).getD 0))
  have hm := Int.le_max_left c.laneMinHeight
    ((((g.lanes[i]?).bind (·.caption)).map (·.h)).getD 0)
  dsimp only at hf ⊢
  omega

theorem bandWalk_lower (height : Nat → Int) (gap width top : Int) (indices : List Nat)
    (hg : 0 ≤ gap) (hh : ∀ i, 0 ≤ height i) :
    ∀ b ∈ (bandWalk height gap width top indices).map Prod.snd, top ≤ b.y := by
  induction indices generalizing top with
  | nil => simp [bandWalk]
  | cons i indices ih =>
    intro b hb
    simp only [bandWalk, List.map_cons, List.mem_cons] at hb
    rcases hb with hb | hb
    · subst b
      exact Int.le_refl _
    · have hl := ih (top + height i + gap) b hb
      have hi := hh i
      omega

theorem bandWalk_disjoint (height : Nat → Int) (gap width top : Int) (indices : List Nat)
    (hg : 0 ≤ gap) (hh : ∀ i, 0 ≤ height i) :
    ((bandWalk height gap width top indices).map Prod.snd).Pairwise
      (fun a b => a.y + a.h ≤ b.y ∧ Disjoint a b) := by
  induction indices generalizing top with
  | nil => simp [bandWalk]
  | cons i indices ih =>
    simp only [bandWalk, List.map_cons, List.pairwise_cons]
    constructor
    · intro b hb
      have hl := bandWalk_lower height gap width (top + height i + gap) indices hg hh b hb
      constructor
      · omega
      · unfold Disjoint Rect.meetsInterior
        simp only
        omega
    · exact ih (top + height i + gap)

theorem eventmodeling_entity_lanes_disjoint (g : Input) (profile : Profile)
    (frames : List Rect) :
    ((laneBands g (EventConsts.load profile) frames).map Prod.snd).Pairwise
      (fun a b => a.y + a.h ≤ b.y ∧ Disjoint a b) := by
  have signs := event_constants_positive profile
  have hh : ∀ i, 0 ≤ laneHeight g (EventConsts.load profile) frames i := by
    intro i
    have lower := laneHeight_lower g (EventConsts.load profile) frames i
    have hm := signs.1
    have hp := signs.2.1
    omega
  exact bandWalk_disjoint _ _ _ _ _ (Int.le_of_lt signs.2.2.1) hh

end Eventmodeling

namespace Timeline

theorem cardWidth_lower (g : Input) (c : TimelineConsts) : c.cardWidth ≤ cardWidth g c := by
  let periodStep := fun (w : Int) (p : Period) =>
    p.events.foldl (fun w e => max w (e.caption.w + 2 * c.cardPadding))
      (max w (p.caption.w + 2 * c.cardPadding))
  have hp : c.cardWidth ≤ g.periods.foldl periodStep c.cardWidth := by
    apply Eventmodeling.foldl_ge_initial
    intro w p
    exact Int.le_trans (Int.le_max_left _ _)
      (Eventmodeling.foldl_ge_initial
        (fun w e => max w (e.caption.w + 2 * c.cardPadding))
        (fun _ _ => Int.le_max_left _ _) p.events _)
  let sectionStep := fun (w : Int) (p : Card × Nat) =>
    let n : Int := if horizontal g then span g p.2 else 1
    let need := p.1.caption.w + 2 * c.cardPadding - (n - 1) * c.columnGap
    if 0 < need then max w (Int.fdiv (need + n - 1) n) else w
  have hs := Eventmodeling.foldl_ge_initial sectionStep
    (by
      intro w p
      dsimp only [sectionStep]
      split <;> (try dsimp only) <;> split
      all_goals first | exact Int.le_max_left _ _ | exact Int.le_refl _)
    g.sections.zipIdx (g.periods.foldl periodStep c.cardWidth)
  exact Int.le_trans hp hs

theorem timeline_period_columns_disjoint (g : Input) (profile : Profile)
    (height y : Int) (i j : Nat) (hij : i < j) :
    let c := TimelineConsts.load profile
    let w := cardWidth g c
    let a := periodColumn c w height y i
    let b := periodColumn c w height y j
    a.x < b.x ∧ a.x + a.w ≤ b.x ∧ Disjoint a b := by
  dsimp only
  have signs := timeline_constants_positive profile
  have hw := cardWidth_lower g (TimelineConsts.load profile)
  let c := TimelineConsts.load profile
  let w := cardWidth g c
  have hg : 0 < c.columnGap := signs.2.1
  have hwp : 0 < w := by
    dsimp only [w, c]
    have hmin := signs.1
    omega
  have hstep : 0 ≤ w + c.columnGap := by omega
  have hij' : (i : Int) + 1 ≤ (j : Int) := by omega
  have hm := Int.mul_le_mul_of_nonneg_right hij' hstep
  rw [Int.add_mul, Int.one_mul] at hm
  change c.leftMargin + (i : Int) * (w + c.columnGap) <
      c.leftMargin + (j : Int) * (w + c.columnGap) ∧
    c.leftMargin + (i : Int) * (w + c.columnGap) + w ≤
      c.leftMargin + (j : Int) * (w + c.columnGap) ∧ _
  refine ⟨by omega, by omega, ?_⟩
  change ¬ (periodColumn c w height y i).meetsInterior (periodColumn c w height y j)
  unfold Rect.meetsInterior periodColumn
  simp only
  omega

theorem horizontal_period_rect {g : Input} {c : TimelineConsts} {i : Nat} {p : Period}
    (hi : g.periods[i]? = some p) :
    (horizontalPlan g c).periods[i]? =
      some (periodColumn c (cardWidth g c) (periodHeight g c)
        (contentTop g c + if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap)
        (slot g i p)) := by
  simp only [horizontalPlan, List.getElem?_map, List.getElem?_zipIdx, hi, Option.map_some, Nat.zero_add]

theorem horizontal_periods_separated {g : Input} {profile : Profile}
    {i j : Nat} {p q : Period} {a b : Rect}
    (hi : g.periods[i]? = some p) (hj : g.periods[j]? = some q)
    (ha : (horizontalPlan g (TimelineConsts.load profile)).periods[i]? = some a)
    (hb : (horizontalPlan g (TimelineConsts.load profile)).periods[j]? = some b)
    (hslots : slot g i p < slot g j q) :
    a.x < b.x ∧ a.x + a.w ≤ b.x ∧ Disjoint a b := by
  have hai := horizontal_period_rect hi (c := TimelineConsts.load profile)
  have hbj := horizontal_period_rect hj (c := TimelineConsts.load profile)
  rw [ha] at hai
  rw [hb] at hbj
  cases hai
  cases hbj
  exact timeline_period_columns_disjoint g profile _ _ _ _ hslots

end Timeline

end Lanes
end Elegant

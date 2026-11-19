import Elegant.GridGrown

set_option autoImplicit false

/-! The lattice of the router: its lines are strictly increasing, and a lattice step is an
axis-aligned segment that misses the interior of every leaf. -/

namespace Elegant
namespace Grid

/-! ### Sorted lines -/

theorem dedup_mem : ∀ (l : List Int) (x : Int), x ∈ dedup l → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; simp [dedup] at h
  | cons a t ih =>
    cases t with
    | nil => intro x h; simpa [dedup] using h
    | cons b rest =>
      intro x h
      simp only [dedup] at h
      split at h
      · exact List.mem_cons_of_mem _ (ih x h)
      · rcases List.mem_cons.mp h with rfl | h'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih x h')

theorem dedup_pairwise : ∀ (l : List Int), List.Pairwise (· ≤ ·) l →
    List.Pairwise (· < ·) (dedup l) := by
  intro l
  induction l with
  | nil => intro _; simp [dedup]
  | cons a t ih =>
    cases t with
    | nil => intro _; simp [dedup]
    | cons b rest =>
      intro hp
      have hcons := List.pairwise_cons.mp hp
      have hab : a ≤ b := hcons.1 b (List.mem_cons_self ..)
      have htail := ih hcons.2
      simp only [dedup]
      split
      · exact htail
      · rename_i hne
        refine List.Pairwise.cons ?_ htail
        intro y hy
        have hy' := dedup_mem _ _ hy
        rcases List.mem_cons.mp hy' with rfl | hy''
        · omega
        · have := (List.pairwise_cons.mp hcons.2).1 y hy''
          have := hcons.1 y (List.mem_cons_of_mem _ hy'')
          omega

theorem sortedUnique_pairwise (xs : List Int) : List.Pairwise (· < ·) (sortedUnique xs) := by
  unfold sortedUnique
  apply dedup_pairwise
  have := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≤ b))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) xs
  exact this.imp (fun h => by simpa using h)

theorem getD_lt_of_pairwise {L : List Int} (h : List.Pairwise (· < ·) L) {i j : Nat} (hij : i < j)
    (hj : j < L.length) : L.getD i 0 < L.getD j 0 := by
  have hi : i < L.length := by omega
  have := List.pairwise_iff_getElem.mp h i j hi hj hij
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj]
  exact this

theorem toArray_getD (L : List Int) (i : Nat) : L.toArray.getD i 0 = L.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

structure Lat.Sorted (l : Lat) : Prop where
  xs : ∀ i j, i < j → j < l.xs.size → l.xs.getD i 0 < l.xs.getD j 0
  ys : ∀ i j, i < j → j < l.ys.size → l.ys.getD i 0 < l.ys.getD j 0

theorem buildLat_sorted {inp : RouteIn} {lat : Lat} (h : buildLat inp = .ok lat) : lat.Sorted := by
  unfold buildLat at h
  dsimp only at h
  split at h
  · cases h
  · injection h with h
    subst h
    constructor
    · intro i j hij hj
      simp only [toArray_getD]
      exact getD_lt_of_pairwise (sortedUnique_pairwise _) hij (by simpa using hj)
    · intro i j hij hj
      simp only [toArray_getD]
      exact getD_lt_of_pairwise (sortedUnique_pairwise _) hij (by simpa using hj)

theorem buildLat_leaves {inp : RouteIn} {lat : Lat} (h : buildLat inp = .ok lat) :
    lat.leaves = inp.leaves := by
  unfold buildLat at h
  dsimp only at h
  split at h
  · cases h
  · injection h with h
    subst h
    rfl

/-! ### Lattice steps -/

def AxMiss (o : Rect) (p q : Point) : Prop :=
  max p.x q.x ≤ o.x ∨ o.x + o.w ≤ min p.x q.x ∨ max p.y q.y ≤ o.y ∨ o.y + o.h ≤ min p.y q.y

def Aligned (p q : Point) : Prop := p.x = q.x ∨ p.y = q.y

theorem AxMiss.symm {o : Rect} {p q : Point} (h : AxMiss o p q) : AxMiss o q p := by
  unfold AxMiss at *
  omega

theorem AxMiss.segMisses {o : Rect} {p q : Point} (h : AxMiss o p q) : Polyline.segMisses p q o := by
  unfold AxMiss at h
  unfold Polyline.segMisses
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem Lat.point_vertex (l : Lat) {i j : Nat} (hj : j < l.ny) :
    l.point (i * l.ny + j) = ⟨l.xs.getD i 0, l.ys.getD j 0⟩ := by
  have hn : 0 < l.ny := by omega
  have h1 : (i * l.ny + j) / l.ny = i := by
    rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hj]
    rfl
  have h2 : (i * l.ny + j) % l.ny = j := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  unfold Lat.point
  rw [h1, h2]

theorem Lat.freeH_miss {l : Lat} (hs : l.Sorted) {i j : Nat} (hi : i + 1 < l.xs.size)
    (h : l.freeH i j = true) {o : Rect} (ho : o ∈ l.leaves) :
    AxMiss o ⟨l.xs.getD i 0, l.ys.getD j 0⟩ ⟨l.xs.getD (i + 1) 0, l.ys.getD j 0⟩ := by
  have hlt := hs.xs i (i + 1) (by omega) hi
  unfold Lat.freeH at h
  simp only [Bool.not_eq_true', List.any_eq_false] at h
  have := h o ho
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at this
  unfold AxMiss
  simp only
  omega

theorem Lat.freeV_miss {l : Lat} (hs : l.Sorted) {i j : Nat} (hj : j + 1 < l.ys.size)
    (h : l.freeV i j = true) {o : Rect} (ho : o ∈ l.leaves) :
    AxMiss o ⟨l.xs.getD i 0, l.ys.getD j 0⟩ ⟨l.xs.getD i 0, l.ys.getD (j + 1) 0⟩ := by
  have hlt := hs.ys j (j + 1) (by omega) hj
  unfold Lat.freeV at h
  simp only [Bool.not_eq_true', List.any_eq_false] at h
  have := h o ho
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at this
  unfold AxMiss
  simp only
  omega

theorem Lat.div_vertex (l : Lat) {i j : Nat} (hj : j < l.ny) :
    (i * l.ny + j) / l.ny = i ∧ (i * l.ny + j) % l.ny = j := by
  have hn : 0 < l.ny := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hj]
    rfl
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem Lat.exists_vertex (l : Lat) {v : Nat} (hv : v < l.cells) :
    ∃ i j : Nat, i < l.xs.size ∧ j < l.ys.size ∧ v = i * l.ny + j := by
  have hn : 0 < l.ny := by
    unfold Lat.cells at hv
    unfold Lat.ny
    rcases Nat.eq_zero_or_pos l.ys.size with h | h
    · rw [h] at hv
      simp at hv
    · exact h
  refine ⟨v / l.ny, v % l.ny, ?_, Nat.mod_lt _ hn, (Nat.div_add_mod' v l.ny).symm⟩
  unfold Lat.cells at hv
  unfold Lat.ny
  exact (Nat.div_lt_iff_lt_mul hn).mpr hv

theorem Lat.step_east {l : Lat} (hs : l.Sorted) {I J : Nat} (hI : I + 1 < l.xs.size)
    (hJ : J < l.ys.size) (hf : l.free (I * l.ny + J) ((I + 1) * l.ny + J) 0 = true) {o : Rect}
    (ho : o ∈ l.leaves) :
    AxMiss o (l.point (I * l.ny + J)) (l.point ((I + 1) * l.ny + J)) ∧
      Aligned (l.point (I * l.ny + J)) (l.point ((I + 1) * l.ny + J)) := by
  have hJ' : J < l.ny := hJ
  have hmin : min (I * l.ny + J) ((I + 1) * l.ny + J) = I * l.ny + J := by
    apply Nat.min_eq_left
    rw [Nat.add_mul, Nat.one_mul]
    omega
  unfold Lat.free at hf
  simp only [hmin, (Lat.div_vertex l hJ').1, (Lat.div_vertex l hJ').2] at hf
  simp only [show 0 < 2 by decide, ↓reduceIte] at hf
  rw [Lat.point_vertex l hJ', Lat.point_vertex l hJ']
  exact ⟨Lat.freeH_miss hs hI hf ho, Or.inr rfl⟩

theorem Lat.step_west {l : Lat} (hs : l.Sorted) {I J : Nat} (hI : I + 1 < l.xs.size)
    (hJ : J < l.ys.size) (hf : l.free ((I + 1) * l.ny + J) (I * l.ny + J) 1 = true) {o : Rect}
    (ho : o ∈ l.leaves) :
    AxMiss o (l.point ((I + 1) * l.ny + J)) (l.point (I * l.ny + J)) ∧
      Aligned (l.point ((I + 1) * l.ny + J)) (l.point (I * l.ny + J)) := by
  have hJ' : J < l.ny := hJ
  have hmin : min ((I + 1) * l.ny + J) (I * l.ny + J) = I * l.ny + J := by
    apply Nat.min_eq_right
    rw [Nat.add_mul, Nat.one_mul]
    omega
  unfold Lat.free at hf
  simp only [hmin, (Lat.div_vertex l hJ').1, (Lat.div_vertex l hJ').2] at hf
  simp only [show 1 < 2 by decide, ↓reduceIte] at hf
  rw [Lat.point_vertex l hJ', Lat.point_vertex l hJ']
  exact ⟨(Lat.freeH_miss hs hI hf ho).symm, Or.inr rfl⟩

theorem Lat.step_south {l : Lat} (hs : l.Sorted) {I J : Nat}
    (hJ : J + 1 < l.ys.size) (hf : l.free (I * l.ny + J) (I * l.ny + (J + 1)) 2 = true) {o : Rect}
    (ho : o ∈ l.leaves) :
    AxMiss o (l.point (I * l.ny + J)) (l.point (I * l.ny + (J + 1))) ∧
      Aligned (l.point (I * l.ny + J)) (l.point (I * l.ny + (J + 1))) := by
  have hJ' : J < l.ny := by have : J < l.ys.size := by omega
                            exact this
  have hJ2 : J + 1 < l.ny := hJ
  have hmin : min (I * l.ny + J) (I * l.ny + (J + 1)) = I * l.ny + J := by
    apply Nat.min_eq_left
    omega
  unfold Lat.free at hf
  simp only [hmin, (Lat.div_vertex l hJ').1, (Lat.div_vertex l hJ').2] at hf
  simp only [show ¬ (2 < 2) by decide, ↓reduceIte] at hf
  rw [Lat.point_vertex l hJ', Lat.point_vertex l hJ2]
  exact ⟨Lat.freeV_miss hs hJ hf ho, Or.inl rfl⟩

theorem Lat.step_north {l : Lat} (hs : l.Sorted) {I J d : Nat} (hd : 3 ≤ d)
    (hJ : J + 1 < l.ys.size) (hf : l.free (I * l.ny + (J + 1)) (I * l.ny + J) d = true) {o : Rect}
    (ho : o ∈ l.leaves) :
    AxMiss o (l.point (I * l.ny + (J + 1))) (l.point (I * l.ny + J)) ∧
      Aligned (l.point (I * l.ny + (J + 1))) (l.point (I * l.ny + J)) := by
  have hJ' : J < l.ny := by have : J < l.ys.size := by omega
                            exact this
  have hJ2 : J + 1 < l.ny := hJ
  have hmin : min (I * l.ny + (J + 1)) (I * l.ny + J) = I * l.ny + J := by
    apply Nat.min_eq_right
    omega
  unfold Lat.free at hf
  simp only [hmin, (Lat.div_vertex l hJ').1, (Lat.div_vertex l hJ').2] at hf
  have hnd : ¬ d < 2 := by omega
  simp only [hnd, ↓reduceIte] at hf
  rw [Lat.point_vertex l hJ', Lat.point_vertex l hJ2]
  exact ⟨(Lat.freeV_miss hs hJ hf ho).symm, Or.inl rfl⟩

theorem Lat.step_geom {l : Lat} (hs : l.Sorted) {v d u : Nat} {len : Int}
    (h : l.step v d = some (u, len)) {o : Rect} (ho : o ∈ l.leaves) :
    AxMiss o (l.point v) (l.point u) ∧ Aligned (l.point v) (l.point u) := by
  unfold Lat.step at h
  cases hn : l.neighbour v d with
  | none => simp [hn] at h
  | some u' =>
    simp only [hn] at h
    by_cases hf : l.free v u' d = true
    · simp only [hf, ↓reduceIte] at h
      have hu : u' = u := (Prod.mk.inj (Option.some.inj h)).1
      subst hu
      unfold Lat.neighbour at hn
      dsimp only at hn
      split at hn
      · rename_i hc
        injection hn with hn
        obtain ⟨hvc, hi0, hi1, hj0, hj1⟩ := hc
        obtain ⟨I, J, hI, hJ, rfl⟩ := l.exists_vertex hvc
        have hd' := Lat.div_vertex l (i := I) (j := J) hJ
        simp only [hd'.1, hd'.2] at hi0 hi1 hj0 hj1 hn
        obtain rfl | rfl | rfl | hd3 : d = 0 ∨ d = 1 ∨ d = 2 ∨ 3 ≤ d := by omega
        · simp only [dirDelta] at hi0 hi1 hj0 hj1 hn
          have e1 : (↑I + 1 : Int).toNat = I + 1 := by omega
          have e2 : (↑J + 0 : Int).toNat = J := by omega
          rw [e1, e2] at hn
          subst hn
          exact Lat.step_east hs (by omega) hJ hf ho
        · simp only [dirDelta] at hi0 hi1 hj0 hj1 hn
          obtain ⟨I', rfl⟩ : ∃ I', I = I' + 1 := ⟨I - 1, by omega⟩
          have e1 : (↑(I' + 1) + -1 : Int).toNat = I' := by omega
          have e2 : (↑J + 0 : Int).toNat = J := by omega
          rw [e1, e2] at hn
          subst hn
          exact Lat.step_west hs (by omega) hJ hf ho
        · simp only [dirDelta] at hi0 hi1 hj0 hj1 hn
          have e1 : (↑I + 0 : Int).toNat = I := by omega
          have e2 : (↑J + 1 : Int).toNat = J + 1 := by omega
          rw [e1, e2] at hn
          subst hn
          exact Lat.step_south hs (by omega) hf ho
        · obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := ⟨d - 3, by omega⟩
          simp only [dirDelta] at hi0 hi1 hj0 hj1 hn
          obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
          have e1 : (↑I + 0 : Int).toNat = I := by omega
          have e2 : (↑(J' + 1) + -1 : Int).toNat = J' := by omega
          rw [e1, e2] at hn
          subst hn
          exact Lat.step_north hs hd3 (by omega) hf ho
      · cases hn
    · simp [hf] at h

theorem Lat.neighbour_aligned {l : Lat} {v d u : Nat}
    (hn : l.neighbour v d = some u) : Aligned (l.point v) (l.point u) := by
  unfold Lat.neighbour at hn
  dsimp only at hn
  split at hn
  · rename_i hc
    injection hn with hn
    obtain ⟨hvc, hi0, hi1, hj0, hj1⟩ := hc
    obtain ⟨I, J, _hI, hJ, rfl⟩ := l.exists_vertex hvc
    have hd := Lat.div_vertex l (i := I) (j := J) hJ
    simp only [hd.1, hd.2] at hi0 hi1 hj0 hj1 hn
    obtain rfl | rfl | rfl | hd3 : d = 0 ∨ d = 1 ∨ d = 2 ∨ 3 ≤ d := by omega
    · simp only [dirDelta] at hi0 hi1 hj0 hj1 hn
      have e1 : (↑I + 1 : Int).toNat = I + 1 := by omega
      have e2 : (↑J + 0 : Int).toNat = J := by omega
      rw [e1, e2] at hn
      subst hn
      rw [Lat.point_vertex l hJ, Lat.point_vertex l hJ]
      exact Or.inr rfl
    · simp only [dirDelta] at hi0 hi1 hj0 hj1 hn
      obtain ⟨I', rfl⟩ : ∃ I', I = I' + 1 := ⟨I - 1, by omega⟩
      have e1 : (↑(I' + 1) + -1 : Int).toNat = I' := by omega
      have e2 : (↑J + 0 : Int).toNat = J := by omega
      rw [e1, e2] at hn
      subst hn
      rw [Lat.point_vertex l hJ, Lat.point_vertex l hJ]
      exact Or.inr rfl
    · simp only [dirDelta] at hi0 hi1 hj0 hj1 hn
      have e1 : (↑I + 0 : Int).toNat = I := by omega
      have e2 : (↑J + 1 : Int).toNat = J + 1 := by omega
      rw [e1, e2] at hn
      subst hn
      have hJ' : J + 1 < l.ny := by
        change J + 1 < l.ys.size
        omega
      rw [Lat.point_vertex l hJ, Lat.point_vertex l hJ']
      exact Or.inl rfl
    · obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := ⟨d - 3, by omega⟩
      simp only [dirDelta] at hi0 hi1 hj0 hj1 hn
      obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
      have e1 : (↑I + 0 : Int).toNat = I := by omega
      have e2 : (↑(J' + 1) + -1 : Int).toNat = J' := by omega
      rw [e1, e2] at hn
      subst hn
      have hJ' : J' < l.ny := by
        change J' < l.ys.size
        omega
      rw [Lat.point_vertex l hJ, Lat.point_vertex l hJ']
      exact Or.inl rfl
  · cases hn

theorem Lat.step_aligned {l : Lat} {v d u : Nat} {len : Int}
    (h : l.step v d = some (u, len)) : Aligned (l.point v) (l.point u) := by
  unfold Lat.step at h
  cases hn : l.neighbour v d with
  | none => simp [hn] at h
  | some u' =>
    simp only [hn] at h
    split at h
    · have hu : u' = u := (Prod.mk.inj (Option.some.inj h)).1
      subst hu
      exact Lat.neighbour_aligned hn
    · cases h

end Grid
end Elegant

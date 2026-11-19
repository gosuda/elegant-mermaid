import ElegantGeometry.Basic

set_option autoImplicit false

/-! The shared scales of the chart family (`spec/layout/charts.md`, charts-107): the linear scale,
the band scale, and the tick rule. Every operation is integer arithmetic with the floor division of
the geometry kernel, so Go, Rust, and Lean compute the same values.

The tick rule is stated in closed form: the ticks are the multiples of the step in the domain,
counted from the first one, and at most `tickCap` of them are kept. Go builds the same list with a
loop that appends `v`, `v + step`, ... while `v <= last`, and stops at the cap. -/

namespace Elegant
namespace Chart

/-! ### Integer helpers -/

theorem ite_t {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_f {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem le_fdiv_of_mul_le {t D a : Int} (hD : 0 < D) (h : D * a ≤ t) : a ≤ Int.fdiv t D := by
  have hhi := Int.lt_fdiv_add_one_mul_self t hD
  by_cases hle : a ≤ Int.fdiv t D
  · exact hle
  · have hle' : Int.fdiv t D + 1 ≤ a := by omega
    have h2 := Int.mul_le_mul_of_nonneg_left hle' (Int.le_of_lt hD)
    rw [Int.mul_add, Int.mul_one] at h2
    rw [Int.add_mul, Int.one_mul, Int.mul_comm (Int.fdiv t D) D] at hhi
    omega

theorem fdiv_le_of_le_mul {t D b : Int} (hD : 0 < D) (h : t ≤ D * b) : Int.fdiv t D ≤ b := by
  have hq := Int.mul_fdiv_add_fmod t D
  have hlo := Int.fmod_nonneg_of_pos t hD
  exact Int.le_of_mul_le_mul_left (by omega) hD

theorem fdiv_between (t D a b : Int) (hD : 0 < D) (h1 : D * a ≤ t) (h2 : t ≤ D * b) :
    a ≤ Int.fdiv t D ∧ Int.fdiv t D ≤ b :=
  ⟨le_fdiv_of_mul_le hD h1, fdiv_le_of_le_mul hD h2⟩

theorem fdiv_mono {t t' D : Int} (hD : 0 < D) (h : t ≤ t') : Int.fdiv t D ≤ Int.fdiv t' D := by
  have hq := Int.mul_fdiv_add_fmod t D
  have hlo := Int.fmod_nonneg_of_pos t hD
  exact le_fdiv_of_mul_le hD (by omega)

theorem fdiv_neg_neg (a b : Int) (hb : b ≠ 0) : Int.fdiv (-a) (-b) = Int.fdiv a b := by
  have h1 := Int.mul_fdiv_add_fmod (-a) (-b)
  have h2 := Int.mul_fdiv_add_fmod a b
  have h3 := Int.neg_fmod_neg a b
  have h4 : (-b) * Int.fdiv (-a) (-b) = (-b) * Int.fdiv a b := by
    rw [h3] at h1
    have h5 : (-b) * Int.fdiv (-a) (-b) = -(b * Int.fdiv a b) := by omega
    rw [h5, Int.neg_mul]
  exact Int.eq_of_mul_eq_mul_left (by omega) h4

/-! ### Clamp -/

def clamp (v a b : Int) : Int := max (min v (max a b)) (min a b)

theorem clamp_between (v a b : Int) : min a b ≤ clamp v a b ∧ clamp v a b ≤ max a b := by
  unfold clamp
  omega

theorem clamp_of_between {v a b : Int} (h1 : min a b ≤ v) (h2 : v ≤ max a b) : clamp v a b = v := by
  unfold clamp
  omega

/-! ### The linear scale -/

structure Linear where
  d0 : Int
  d1 : Int
  r0 : Int
  r1 : Int
  deriving DecidableEq, Repr

/-- `map(v) = r0 + floor_div((v - d0) * (r1 - r0), d1 - d0)`; a zero-width domain maps every value
to the midpoint of the range. -/
def Linear.map (l : Linear) (v : Int) : Int :=
  if l.d1 = l.d0 then Int.fdiv (l.r0 + l.r1) 2
  else l.r0 + Int.fdiv ((v - l.d0) * (l.r1 - l.r0)) (l.d1 - l.d0)

theorem linear_monotone {l : Linear} {v v' : Int} (hd : l.d0 < l.d1) (hr : l.r0 ≤ l.r1)
    (hv : v ≤ v') : l.map v ≤ l.map v' := by
  unfold Linear.map
  rw [ite_f (by omega), ite_f (by omega)]
  have hk : 0 ≤ l.r1 - l.r0 := by omega
  have hm : (v - l.d0) * (l.r1 - l.r0) ≤ (v' - l.d0) * (l.r1 - l.r0) :=
    Int.mul_le_mul_of_nonneg_right (by omega) hk
  have := fdiv_mono (D := l.d1 - l.d0) (by omega) hm
  omega

theorem linear_antitone {l : Linear} {v v' : Int} (hd : l.d0 < l.d1) (hr : l.r1 ≤ l.r0)
    (hv : v ≤ v') : l.map v' ≤ l.map v := by
  unfold Linear.map
  rw [ite_f (by omega), ite_f (by omega)]
  have hk : l.r1 - l.r0 ≤ 0 := by omega
  have hm : (v' - l.d0) * (l.r1 - l.r0) ≤ (v - l.d0) * (l.r1 - l.r0) :=
    Int.mul_le_mul_of_nonpos_right (by omega) hk
  have := fdiv_mono (D := l.d1 - l.d0) (by omega) hm
  omega

/-- The core of `linear_into_plot` for an increasing domain: the quotient lies between 0 and the
range width. -/
theorem fdiv_scaled_between (e D k : Int) (hD : 0 < D) (h0 : 0 ≤ e) (h1 : e ≤ D) :
    min 0 k ≤ Int.fdiv (e * k) D ∧ Int.fdiv (e * k) D ≤ max 0 k := by
  rcases Int.le_total 0 k with hk | hk
  · have hm1 : 0 ≤ e * k := Int.mul_nonneg h0 hk
    have hm2 : e * k ≤ D * k := Int.mul_le_mul_of_nonneg_right h1 hk
    have := fdiv_between (e * k) D 0 k hD (by omega) hm2
    omega
  · have hm1 : e * k ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos h0 hk
    have hm2 : D * k ≤ e * k := Int.mul_le_mul_of_nonpos_right h1 hk
    have := fdiv_between (e * k) D k 0 hD hm2 (by omega)
    omega

/-- A value inside the domain maps inside the range, for either direction of the domain. -/
theorem linear_into_plot (l : Linear) (v : Int) (hv1 : min l.d0 l.d1 ≤ v) (hv2 : v ≤ max l.d0 l.d1) :
    min l.r0 l.r1 ≤ l.map v ∧ l.map v ≤ max l.r0 l.r1 := by
  unfold Linear.map
  by_cases heq : l.d1 = l.d0
  · rw [ite_t heq]
    exact fdiv_between (l.r0 + l.r1) 2 (min l.r0 l.r1) (max l.r0 l.r1) (by decide)
      (by omega) (by omega)
  · rw [ite_f heq]
    rcases Int.lt_or_gt_of_ne heq with hlt | hgt
    · have hneg : Int.fdiv ((v - l.d0) * (l.r1 - l.r0)) (l.d1 - l.d0) =
          Int.fdiv ((l.d0 - v) * (l.r1 - l.r0)) (l.d0 - l.d1) := by
        have h := fdiv_neg_neg ((v - l.d0) * (l.r1 - l.r0)) (l.d1 - l.d0) (by omega)
        rw [← h]
        have e1 : -((v - l.d0) * (l.r1 - l.r0)) = (l.d0 - v) * (l.r1 - l.r0) := by
          rw [← Int.neg_mul]
          congr 1
          omega
        have e2 : -(l.d1 - l.d0) = l.d0 - l.d1 := by omega
        rw [e1, e2]
      rw [hneg]
      have := fdiv_scaled_between (l.d0 - v) (l.d0 - l.d1) (l.r1 - l.r0) (by omega) (by omega)
        (by omega)
      omega
    · have := fdiv_scaled_between (v - l.d0) (l.d1 - l.d0) (l.r1 - l.r0) (by omega) (by omega)
        (by omega)
      omega

/-! ### The band scale -/

/-- Category `index` of `count` categories over `[r0, r1]`; a band has width 0. -/
def bandPosition (index count : Nat) (r0 r1 : Int) : Int :=
  if count < 2 then r0 + Int.fdiv (r1 - r0) 2
  else r0 + Int.fdiv ((index : Int) * (r1 - r0)) ((count : Int) - 1)

theorem band_in_range {index count : Nat} {r0 r1 : Int} (hi : index < count) (hr : r0 ≤ r1) :
    r0 ≤ bandPosition index count r0 r1 ∧ bandPosition index count r0 r1 ≤ r1 := by
  unfold bandPosition
  by_cases hc : count < 2
  · rw [ite_t hc]
    have := fdiv_between (r1 - r0) 2 0 (r1 - r0) (by decide) (by omega) (by omega)
    omega
  · rw [ite_f hc]
    have hd : (0 : Int) < (count : Int) - 1 := by omega
    have hidx : (index : Int) ≤ (count : Int) - 1 := by omega
    have h1 : 0 ≤ (index : Int) * (r1 - r0) := Int.mul_nonneg (by omega) (by omega)
    have h2 : (index : Int) * (r1 - r0) ≤ ((count : Int) - 1) * (r1 - r0) :=
      Int.mul_le_mul_of_nonneg_right hidx (by omega)
    have := fdiv_between ((index : Int) * (r1 - r0)) ((count : Int) - 1) 0 (r1 - r0) hd
      (by omega) h2
    omega

/-- Bands do not overlap: a later category starts at or after an earlier one (width 0). -/
theorem band_disjoint {i j count : Nat} {r0 r1 : Int} (hij : i < j) (hj : j < count) (hr : r0 ≤ r1) :
    bandPosition i count r0 r1 ≤ bandPosition j count r0 r1 := by
  unfold bandPosition
  by_cases hc : count < 2
  · omega
  · rw [ite_f hc, ite_f hc]
    have hd : (0 : Int) < (count : Int) - 1 := by omega
    have hm : (i : Int) * (r1 - r0) ≤ (j : Int) * (r1 - r0) :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    have := fdiv_mono (D := (count : Int) - 1) hd hm
    omega

/-- With room for one unit per step the bands are strictly ordered. -/
theorem band_strict {i j count : Nat} {r0 r1 : Int} (hij : i < j) (hj : j < count)
    (hr : (count : Int) - 1 ≤ r1 - r0) :
    bandPosition i count r0 r1 < bandPosition j count r0 r1 := by
  unfold bandPosition
  by_cases hc : count < 2
  · omega
  · rw [ite_f hc, ite_f hc]
    have hd : (0 : Int) < (count : Int) - 1 := by omega
    have hm : (i : Int) * (r1 - r0) + ((count : Int) - 1) ≤ (j : Int) * (r1 - r0) := by
      have h1 : ((i : Int) + 1) * (r1 - r0) ≤ (j : Int) * (r1 - r0) :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      rw [Int.add_mul, Int.one_mul] at h1
      omega
    have h2 := fdiv_mono (D := (count : Int) - 1) hd hm
    have h3 : Int.fdiv ((i : Int) * (r1 - r0) + 1 * ((count : Int) - 1)) ((count : Int) - 1) =
        Int.fdiv ((i : Int) * (r1 - r0)) ((count : Int) - 1) + 1 :=
      Int.add_mul_fdiv_right _ _ (by omega)
    rw [Int.one_mul] at h3
    omega

/-! ### The tick rule -/

/-- The scan of the exponent `e` with `10^e * 10 <= d`: `fuel` is the scan cap over two. -/
def scanLoop (d : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | f + 1, e, acc => if d < 10 ^ e * 10 then acc else scanLoop d f (e + 1) e

def scanExp (d : Nat) : Nat := scanLoop d 20 0 0

theorem scanLoop_spec (d : Nat) : ∀ (f e acc : Nat), 10 ^ acc * 10 ≤ d → e ≤ acc + 1 →
    10 ^ (scanLoop d f e acc) * 10 ≤ d ∧
      (f + e ≤ scanLoop d f e acc + 1 ∨ d < 10 ^ (scanLoop d f e acc + 1) * 10)
  | 0, e, acc, h1, h2 => by
    simp only [scanLoop]
    exact ⟨h1, Or.inl (by omega)⟩
  | f + 1, e, acc, h1, h2 => by
    unfold scanLoop
    by_cases hlt : d < 10 ^ e * 10
    · rw [ite_t hlt]
      refine ⟨h1, Or.inr ?_⟩
      have : 10 ^ e ≤ 10 ^ (acc + 1) := Nat.pow_le_pow_right (by decide) h2
      omega
    · rw [ite_f hlt]
      have ih := scanLoop_spec d f (e + 1) e (by omega) (by omega)
      refine ⟨ih.1, ?_⟩
      rcases ih.2 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h

private theorem scanExp_core {D : Nat} (hC : 10 ≤ D) (hD : D < 2 ^ 31) :
    10 ^ scanExp D * 10 ≤ D ∧ D < 10 ^ (scanExp D + 1) * 10 := by
  have h : 10 ^ scanExp D * 10 ≤ D ∧
      (20 + 0 ≤ scanExp D + 1 ∨ D < 10 ^ (scanExp D + 1) * 10) :=
    scanLoop_spec D 20 0 0 (by simpa using hC) (by omega)
  refine ⟨h.1, ?_⟩
  rcases h.2 with h2 | h2
  · exfalso
    have h19 : 10 ^ 19 ≤ 10 ^ scanExp D := Nat.pow_le_pow_right (by decide) (by omega)
    have h31 : (2 : Nat) ^ 31 < 10 ^ 19 := by decide
    have := h.1
    omega
  · exact h2

/-- The scan finds the exponent: `10^e * C <= D < 10^(e+1) * C` with `C = 10`. -/
theorem ticks_scan_fuel_sufficient {D : Nat} (hC : 10 ≤ D) (hD : D < 2 ^ 31) :
    ∃ e, e ≤ 9 ∧ 10 ^ e * 10 ≤ D ∧ D < 10 ^ (e + 1) * 10 := by
  have h := scanExp_core hC hD
  refine ⟨scanExp D, ?_, h.1, h.2⟩
  by_cases hle : scanExp D ≤ 9
  · exact hle
  · have h10 : 10 ^ 10 ≤ 10 ^ scanExp D := Nat.pow_le_pow_right (by decide) (by omega)
    have h31 : (2 : Nat) ^ 31 < 10 ^ 10 := by decide
    have := h.1
    omega

/-- The step for a domain of width `d`, given the power of ten `p` found by the scan: the squared
comparisons are `d / (C * p) >= sqrt 50`, `sqrt 10`, `sqrt 2`. -/
def stepOf (d p : Nat) : Nat :=
  if 100 * (p * p) * 50 ≤ d * d then 10 * p
  else if 100 * (p * p) * 10 ≤ d * d then 5 * p
  else if 100 * (p * p) * 2 ≤ d * d then 2 * p
  else p

def tickStep (d : Nat) : Nat := if d < 10 then 1 else stepOf d (10 ^ scanExp d)

private theorem sq_lt_of {d p k m : Nat} (hkk : k * k = m) (h : d * d < m * (p * p)) :
    d < k * p := by
  refine Nat.mul_self_lt_mul_self_iff.mp ?_
  have e : (k * p) * (k * p) = (k * k) * (p * p) := by
    rw [Nat.mul_assoc, Nat.mul_left_comm p k p, ← Nat.mul_assoc, ← Nat.mul_assoc]
  rw [e, hkk]
  exact h

private theorem stepOf_pos {d p : Nat} (hp : 0 < p) : 0 < stepOf d p := by
  unfold stepOf
  split <;> try omega
  split <;> try omega
  split <;> omega

theorem tickStep_pos (d : Nat) : 0 < tickStep d := by
  unfold tickStep
  split
  · omega
  · exact stepOf_pos (Nat.pow_pos (by decide))

private theorem stepOf_covers {d p : Nat} (h2 : d < 100 * p) : d < 21 * stepOf d p := by
  unfold stepOf
  by_cases c1 : 100 * (p * p) * 50 ≤ d * d
  · rw [ite_t c1]; omega
  · rw [ite_f c1]
    by_cases c2 : 100 * (p * p) * 10 ≤ d * d
    · rw [ite_t c2]
      have : d < 105 * p := sq_lt_of (k := 105) (m := 11025) (by decide) (by omega)
      omega
    · rw [ite_f c2]
      by_cases c3 : 100 * (p * p) * 2 ≤ d * d
      · rw [ite_t c3]
        have : d < 32 * p := sq_lt_of (k := 32) (m := 1024) (by decide) (by omega)
        omega
      · rw [ite_f c3]
        have : d < 15 * p := sq_lt_of (k := 15) (m := 225) (by decide) (by omega)
        omega

/-- The step covers the domain in at most `2 * C + 1` steps, where `C` is the tick count 10. -/
theorem ticks_domain_le_steps {D : Nat} (hD : D < 2 ^ 31) : D < 21 * tickStep D := by
  unfold tickStep
  by_cases h10 : D < 10
  · rw [ite_t h10]; omega
  · rw [ite_f h10]
    have h := scanExp_core (by omega) hD
    have e : 10 ^ (scanExp D + 1) = 10 ^ scanExp D * 10 := by rw [Nat.pow_succ]
    exact stepOf_covers (by omega)

/-- The step is one of 1, 2, 5 times a power of ten. -/
theorem ticks_step_is_125 (D : Nat) :
    ∃ e m, tickStep D = 10 ^ e * m ∧ (m = 1 ∨ m = 2 ∨ m = 5) := by
  unfold tickStep
  by_cases h10 : D < 10
  · rw [ite_t h10]
    exact ⟨0, 1, by simp, Or.inl rfl⟩
  · rw [ite_f h10]
    unfold stepOf
    by_cases c1 : 100 * (10 ^ scanExp D * 10 ^ scanExp D) * 50 ≤ D * D
    · rw [ite_t c1]
      exact ⟨scanExp D + 1, 1, by rw [Nat.pow_succ]; omega, Or.inl rfl⟩
    · rw [ite_f c1]
      by_cases c2 : 100 * (10 ^ scanExp D * 10 ^ scanExp D) * 10 ≤ D * D
      · rw [ite_t c2]
        exact ⟨scanExp D, 5, by omega, Or.inr (Or.inr rfl)⟩
      · rw [ite_f c2]
        by_cases c3 : 100 * (10 ^ scanExp D * 10 ^ scanExp D) * 2 ≤ D * D
        · rw [ite_t c3]
          exact ⟨scanExp D, 2, by omega, Or.inr (Or.inl rfl)⟩
        · rw [ite_f c3]
          exact ⟨scanExp D, 1, by omega, Or.inl rfl⟩

def tickCap : Nat := 64

/-- The first multiple of `step` that is at least `first`. -/
def tickStart (first step : Int) : Int := -Int.fdiv (-first) step * step

/-- The number of multiples of `step` in `[first, last]`. -/
def tickTotal (first last step : Int) : Nat :=
  if last < tickStart first step then 0 else ((last - tickStart first step) / step).toNat + 1

/-- The ticks of the domain `[lo, hi]`: the first `tickCap` multiples of the step, reversed when the
domain is descending, and whether the cap cut the list. -/
def tickList (lo hi step : Int) : List Int × Bool :=
  let first := min lo hi
  let last := max lo hi
  let total := tickTotal first last step
  let list := (List.range (min total tickCap)).map fun (k : Nat) =>
    tickStart first step + (k : Int) * step
  ((if hi < lo then list.reverse else list), tickCap < total)

def ticksOf (lo hi : Int) : Except LayoutError (List Int × Bool) :=
  let span := if hi - lo < 0 then lo - hi else hi - lo
  if span > I32_MAX then .error .overflow
  else if span = 0 then .ok ([lo], false)
  else .ok (tickList lo hi (tickStep span.toNat))

theorem tickStart_ge (first : Int) {step : Int} (hs : 0 < step) : first ≤ tickStart first step := by
  unfold tickStart
  have h1 := Int.mul_fdiv_add_fmod (-first) step
  have h2 := Int.fmod_nonneg_of_pos (-first) hs
  have h3 : step * Int.fdiv (-first) step = Int.fdiv (-first) step * step := Int.mul_comm _ _
  rw [Int.neg_mul]
  omega

theorem tickStart_lt (first : Int) {step : Int} (hs : 0 < step) : tickStart first step < first + step := by
  unfold tickStart
  have h2 := Int.lt_fdiv_add_one_mul_self (-first) hs
  rw [Int.add_mul, Int.one_mul] at h2
  rw [Int.neg_mul]
  omega

theorem tickList_mem {lo hi step : Int} (hs : 0 < step) :
    ∀ t ∈ (tickList lo hi step).1, min lo hi ≤ t ∧ t ≤ max lo hi := by
  intro t ht
  unfold tickList at ht
  simp only [] at ht
  have hmem : t ∈ (List.range (min (tickTotal (min lo hi) (max lo hi) step) tickCap)).map
      (fun (k : Nat) => tickStart (min lo hi) step + (k : Int) * step) := by
    split at ht
    · exact List.mem_reverse.mp ht
    · exact ht
  obtain ⟨k, hk, hkt⟩ := List.mem_map.mp hmem
  rw [← hkt]
  have hk' : k < tickTotal (min lo hi) (max lo hi) step := by
    have := List.mem_range.mp hk
    omega
  have hge := tickStart_ge (min lo hi) hs
  constructor
  · have : 0 ≤ (k : Int) * step := Int.mul_nonneg (by omega) (by omega)
    omega
  · unfold tickTotal at hk'
    by_cases hl : max lo hi < tickStart (min lo hi) step
    · rw [ite_t hl] at hk'; omega
    · rw [ite_f hl] at hk'
      have hnn : 0 ≤ (max lo hi - tickStart (min lo hi) step) / step :=
        Int.ediv_nonneg (by omega) (Int.le_of_lt hs)
      have hk2 : (k : Int) ≤ (max lo hi - tickStart (min lo hi) step) / step := by
        have := Int.toNat_of_nonneg hnn
        omega
      have h4 : (k : Int) * step ≤ ((max lo hi - tickStart (min lo hi) step) / step) * step :=
        Int.mul_le_mul_of_nonneg_right hk2 (Int.le_of_lt hs)
      have := Int.ediv_mul_le (max lo hi - tickStart (min lo hi) step) (Int.ne_of_gt hs)
      omega

theorem tickList_length_le {lo hi step : Int} :
    (tickList lo hi step).1.length ≤ tickTotal (min lo hi) (max lo hi) step := by
  unfold tickList
  simp only []
  split <;> simp <;> omega

/-- Every tick lies inside the domain. -/
theorem ticks_inside_domain {lo hi : Int} {ticks : List Int} {capped : Bool}
    (h : ticksOf lo hi = .ok (ticks, capped)) : ∀ t ∈ ticks, min lo hi ≤ t ∧ t ≤ max lo hi := by
  unfold ticksOf at h
  by_cases hov : (if hi - lo < 0 then lo - hi else hi - lo) > I32_MAX
  · rw [ite_t hov] at h; cases h
  · rw [ite_f hov] at h
    by_cases hz : (if hi - lo < 0 then lo - hi else hi - lo) = 0
    · rw [ite_t hz] at h
      cases h
      intro t ht
      simp only [List.mem_singleton] at ht
      rw [ht]
      have : hi - lo = 0 ∨ lo - hi = 0 := by split at hz <;> omega
      omega
    · rw [ite_f hz] at h
      injection h with h
      have hlist := (Prod.mk.inj h).1.symm
      have hpos : (0 : Int) < (tickStep (if hi - lo < 0 then lo - hi else hi - lo).toNat : Int) := by
        have := tickStep_pos (if hi - lo < 0 then lo - hi else hi - lo).toNat
        omega
      rw [hlist]
      exact tickList_mem hpos

/-- The tick count is at most `2 * C + 1` with `C = 10`, whatever the cap. -/
theorem ticks_count_le {lo hi : Int} {ticks : List Int} {capped : Bool}
    (h : ticksOf lo hi = .ok (ticks, capped)) : ticks.length ≤ 21 := by
  unfold ticksOf at h
  by_cases hov : (if hi - lo < 0 then lo - hi else hi - lo) > I32_MAX
  · rw [ite_t hov] at h; cases h
  · rw [ite_f hov] at h
    by_cases hz : (if hi - lo < 0 then lo - hi else hi - lo) = 0
    · rw [ite_t hz] at h
      cases h
      simp
    · rw [ite_f hz] at h
      injection h with h
      have hlist := (Prod.mk.inj h).1.symm
      obtain ⟨d, hd⟩ : ∃ d : Nat, d = (if hi - lo < 0 then lo - hi else hi - lo).toNat := ⟨_, rfl⟩
      rw [← hd] at hlist
      have hspan : (if hi - lo < 0 then lo - hi else hi - lo) = (d : Int) := by
        rw [hd, Int.toNat_of_nonneg]
        split <;> omega
      have hD : d < 2 ^ 31 := by
        have h1 : (d : Int) ≤ I32_MAX := by omega
        have h31 : (I32_MAX : Int) < 2 ^ 31 := by decide
        omega
      have hcov := ticks_domain_le_steps hD
      have hpos := tickStep_pos d
      have hdd : (d : Int) = max lo hi - min lo hi := by
        have : hi - lo < 0 ∨ ¬ hi - lo < 0 := Decidable.em _
        rcases this with h1 | h1
        · rw [ite_t h1] at hspan; omega
        · rw [ite_f h1] at hspan; omega
      have hlen := tickList_length_le (lo := lo) (hi := hi) (step := tickStep d)
      rw [← hd] at h
      rw [h] at hlen
      refine Nat.le_trans hlen ?_
      have hstart := tickStart_ge (min lo hi) (step := (tickStep d : Int)) (by omega)
      unfold tickTotal
      by_cases hl : max lo hi < tickStart (min lo hi) (tickStep d)
      · rw [ite_t hl]; omega
      · rw [ite_f hl]
        have hlt : max lo hi - tickStart (min lo hi) (tickStep d) < 21 * (tickStep d : Int) := by
          omega
        have := Int.ediv_lt_of_lt_mul (by omega : (0 : Int) < (tickStep d : Int)) (by omega :
          max lo hi - tickStart (min lo hi) (tickStep d) < 21 * (tickStep d : Int))
        omega

end Chart
end Elegant

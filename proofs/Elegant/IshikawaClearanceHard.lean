import Elegant.IshikawaClearanceFacts

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-- Rib-local foreign clearance, stated without importing
`Elegant.Kinds.IshikawaC6Facts` (which imports this module's predecessor and
would create an import cycle). The parent connects this to
`RibLocalForeignClearance`. -/
def RibLocalClearance (placed : Rib) : Prop :=
  ∀ (i : Nat) (rectI : Rect) (pointsI : List Point),
    (i, rectI, pointsI) ∈ placed.pieces →
    ∀ (j : Nat) (rectJ : Rect) (pointsJ : List Point),
      (j, rectJ, pointsJ) ∈ placed.pieces → i ≠ j →
        ¬ Polyline.hitsRect pointsI ⟨rectJ.x, rectJ.y, rectJ.w, rectJ.h⟩

section IshikawaC6RibHardHelpers

private theorem fdiv_bounds (a d : Int) (hd : 0 < d) :
    d * Int.fdiv a d ≤ a ∧ a < d * Int.fdiv a d + d := by
  have h := Int.mul_fdiv_add_fmod a d
  have hf := Int.fmod_nonneg_of_pos a hd
  have hlt := Int.fmod_lt_of_pos a hd
  omega

private theorem run_bounds (p : Params) (x : Int) (hx : 0 ≤ x) (hcos : 0 ≤ p.cos)
    (hsin : 0 < p.sin) :
    p.sin * run p x ≤ x * p.cos ∧ x * p.cos < p.sin * (run p x + 1) := by
  unfold run
  have hnum : 0 ≤ x * p.cos := Int.mul_nonneg hx hcos
  have hb := fdiv_bounds (x * p.cos) p.sin hsin
  have hmul : p.sin * ((x * p.cos).fdiv p.sin + 1) =
      p.sin * (x * p.cos).fdiv p.sin + p.sin := by
    rw [Int.mul_add, Int.mul_one]
  rw [hmul]
  omega

private theorem pos_of_pos_mul {a b : Int} (ha : 0 < a) (h : 0 < a * b) : 0 < b := by
  rcases Int.lt_trichotomy b 0 with hb | hb | hb
  · have hz : a * b ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt ha) (Int.le_of_lt hb)
    omega
  · subst hb; simp at h
  · exact hb

/-- Master-diagonal offset: the descent of `masterX` over `[t0, t0 + w]` plus the
rise `run p w` loses at most `2` to floor-division rounding, uniformly in the
span scale. This is the arithmetic core of the odd-bone x-envelope. -/
theorem span_fdiv_offset_bound (p : Params) (L t0 w span : Int)
    (hL : 0 < L) (hcos : 0 ≤ p.cos) (hsin : 0 < p.sin)
    (hspan : 0 < span) (hw0 : 0 ≤ w) (hws : w ≤ span) :
    Int.fdiv ((-run p L) * (t0 + w)) L - Int.fdiv ((-run p L) * t0) L +
      Int.fdiv ((run p span) * w) span ≥ -2 := by
  have hbL := run_bounds p L (Int.le_of_lt hL) hcos hsin
  have hbS := run_bounds p span (Int.le_of_lt hspan) hcos hsin
  have hspan0 : 0 ≤ span := Int.le_of_lt hspan
  have hX : 1 ≤ L * (run p span + 1) - span * run p L := by
    have h1 : L * (span * p.cos) < L * (p.sin * (run p span + 1)) :=
      Int.mul_lt_mul_of_pos_left hbS.2 hL
    have h2 : span * (p.sin * run p L) ≤ span * (L * p.cos) :=
      Int.mul_le_mul_of_nonneg_left hbL.1 hspan0
    have n1 : L * (p.sin * (run p span + 1)) = p.sin * (L * (run p span + 1)) := by
      simp only [Int.mul_left_comm]
    have n3 : span * (p.sin * run p L) = p.sin * (span * run p L) := by
      simp only [Int.mul_left_comm]
    have n4 : span * (L * p.cos) = L * (span * p.cos) := by
      simp only [Int.mul_left_comm]
    rw [n1] at h1
    rw [n3, n4] at h2
    have h3 : p.sin * (L * (run p span + 1)) > p.sin * (span * run p L) := by omega
    have h4 : 0 < p.sin * (L * (run p span + 1) - span * run p L) := by
      have heq : p.sin * (L * (run p span + 1) - span * run p L) =
          p.sin * (L * (run p span + 1)) - p.sin * (span * run p L) :=
        Int.mul_sub p.sin _ _
      rw [heq]
      omega
    have h5 : 0 < L * (run p span + 1) - span * run p L := pos_of_pos_mul hsin h4
    omega
  have hA := fdiv_bounds ((-run p L) * t0) L hL
  have hB := fdiv_bounds ((-run p L) * (t0 + w)) L hL
  have hC := fdiv_bounds ((run p span) * w) span hspan
  have lB : span * (L * Int.fdiv ((-run p L) * (t0 + w)) L) >
      span * ((-run p L) * (t0 + w) - L) := by
    have h1 : (-run p L) * (t0 + w) - L < L * Int.fdiv ((-run p L) * (t0 + w)) L := by omega
    exact Int.mul_lt_mul_of_pos_left h1 hspan
  have lA : span * (L * Int.fdiv ((-run p L) * t0) L) ≤
      span * ((-run p L) * t0) := by
    exact Int.mul_le_mul_of_nonneg_left hA.1 hspan0
  have lC : L * (span * Int.fdiv ((run p span) * w) span) >
      L * ((run p span) * w - span) := by
    have h1 : (run p span) * w - span < span * Int.fdiv ((run p span) * w) span := by omega
    exact Int.mul_lt_mul_of_pos_left h1 hL
  have key : L * span * (Int.fdiv ((-run p L) * (t0 + w)) L -
        Int.fdiv ((-run p L) * t0) L + Int.fdiv ((run p span) * w) span) ≥
      -3 * (L * span) + span + 1 := by
    have hexp : L * span * (Int.fdiv ((-run p L) * (t0 + w)) L -
          Int.fdiv ((-run p L) * t0) L + Int.fdiv ((run p span) * w) span) =
        span * (L * Int.fdiv ((-run p L) * (t0 + w)) L) -
        span * (L * Int.fdiv ((-run p L) * t0) L) +
        L * (span * Int.fdiv ((run p span) * w) span) := by
      simp only [Int.mul_add, Int.mul_sub, Int.mul_left_comm, Int.mul_assoc]
    rw [hexp]
    have eSum : span * ((-run p L) * (t0 + w) - L) - span * ((-run p L) * t0) +
        L * ((run p span) * w - span) =
      w * (L * run p span - span * run p L) - (L * span) - (L * span) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.mul_left_comm,
        Int.mul_comm, Int.mul_neg]
      omega
    have hXeq : L * (run p span + 1) = L * run p span + L := by
      rw [Int.mul_add, Int.mul_one]
    have hX' : -L + 1 ≤ L * run p span - span * run p L := by omega
    have hwX : w * (L * run p span - span * run p L) ≥ -(L * span) + span := by
      have h1 : w * (L * run p span - span * run p L) ≥ w * (-L + 1) :=
        Int.mul_le_mul_of_nonneg_left hX' hw0
      have h2 : w * (-L + 1) ≥ span * (-L + 1) := by
        apply Int.mul_le_mul_of_nonpos_right hws
        omega
      have h3 : span * (-L + 1) = -(L * span) + span := by
        have e : span * (-L + 1) = span * (-L) + span * 1 := by rw [Int.mul_add]
        rw [e]
        have e2 : span * (-L) = -(L * span) := by
          rw [Int.mul_neg, Int.mul_comm]
        have e3 : span * 1 = span := Int.mul_one _
        rw [e2, e3]
      omega
    omega
  have hP : 0 < L * span := Int.mul_pos hL hspan
  have hfin : 0 < L * span * (Int.fdiv ((-run p L) * (t0 + w)) L -
        Int.fdiv ((-run p L) * t0) L + Int.fdiv ((run p span) * w) span + 3) := by
    have heq : L * span * (Int.fdiv ((-run p L) * (t0 + w)) L -
          Int.fdiv ((-run p L) * t0) L + Int.fdiv ((run p span) * w) span + 3) =
        L * span * (Int.fdiv ((-run p L) * (t0 + w)) L -
          Int.fdiv ((-run p L) * t0) L + Int.fdiv ((run p span) * w) span) +
        3 * (L * span) := by
      have e1 : L * span * (Int.fdiv ((-run p L) * (t0 + w)) L -
            Int.fdiv ((-run p L) * t0) L + Int.fdiv ((run p span) * w) span + 3) =
          L * span * (Int.fdiv ((-run p L) * (t0 + w)) L -
            Int.fdiv ((-run p L) * t0) L + Int.fdiv ((run p span) * w) span) +
          L * span * 3 := by
        rw [Int.mul_add]
      rw [e1, Int.mul_comm (L * span) 3]
    rw [heq]
    omega
  have hS : 0 < Int.fdiv ((-run p L) * (t0 + w)) L -
      Int.fdiv ((-run p L) * t0) L + Int.fdiv ((run p span) * w) span + 3 :=
    pos_of_pos_mul hP hfin
  omega

/-- Copied from `IshikawaClearanceFacts.run_scaled_cross_bound` (private there):
scaling a `run` across heights versus spans. -/
theorem run_scaled_cross_bound (p : Params) (height span : Int)
    (hh : 0 ≤ height) (ht : 0 ≤ span) (hsin : 0 < p.sin) :
    height * run p span ≤ span * (run p height + 1) := by
  have hq := Int.mul_fdiv_add_fmod (span * p.cos) p.sin
  have hr := Int.fmod_nonneg_of_pos (span * p.cos) hsin
  have hlo : p.sin * run p span ≤ span * p.cos := by
    dsimp only [run]
    omega
  have hhi : height * p.cos ≤ p.sin * (run p height + 1) := by
    have h := Int.le_of_lt (Int.lt_fdiv_add_one_mul_self (height * p.cos) hsin)
    simpa only [run, Int.mul_comm] using h
  have hfirst := Int.mul_le_mul_of_nonneg_right hlo hh
  have hsecond := Int.mul_le_mul_of_nonneg_right hhi ht
  apply Int.le_of_mul_le_mul_left (a := p.sin) _ hsin
  calc
    p.sin * (height * run p span) = (p.sin * run p span) * height := by
      simp only [Int.mul_comm, Int.mul_left_comm]
    _ ≤ (span * p.cos) * height := hfirst
    _ = (height * p.cos) * span := by
      simp only [Int.mul_comm, Int.mul_left_comm]
    _ ≤ (p.sin * (run p height + 1)) * span := hsecond
    _ = p.sin * (span * (run p height + 1)) := by
      simp only [Int.mul_comm, Int.mul_left_comm]

/-- Copied from `IshikawaClearanceFacts.interpolated_box_diagonal_miss`
(private there): a diagonal route misses a box sitting `reservation` to its
left at ordinate `t`, provided the coverage inequality holds. -/
theorem interpolated_box_diagonal_miss
    (x0 x1 t0 t1 t width height reservation spine : Int) (up : Bool)
    (ht : t0 < t1) (hx : x1 ≤ x0) (hw : 0 ≤ width) (hh : 0 ≤ height)
    (hcoverage : (x0 - x1) * height ≤ (t1 - t0) * reservation) :
    ¬ Polyline.hitsRect
      [⟨x0, ordinate spine up t0⟩, ⟨x1, ordinate spine up t1⟩]
      ⟨x0 + Int.fdiv ((x1 - x0) * (t - t0)) (t1 - t0) - reservation - width,
        ordinate spine up t - Int.fdiv height 2, width, height⟩ := by
  let span := t1 - t0
  let fall := x0 - x1
  let q := Int.fdiv ((x1 - x0) * (t - t0)) span
  have hspan : 0 < span := by dsimp only [span]; omega
  have hfall : 0 ≤ fall := by dsimp only [fall]; omega
  have hnormalX : x1 - x0 = -fall := by dsimp only [fall]; omega
  have hfloor : span * q ≤ -(fall * t) + fall * t0 := by
    have hq := Int.mul_fdiv_add_fmod ((x1 - x0) * (t - t0)) span
    have hr := Int.fmod_nonneg_of_pos ((x1 - x0) * (t - t0)) hspan
    have hraw : span * q ≤ (x1 - x0) * (t - t0) := by
      dsimp only [q]
      omega
    rw [hnormalX] at hraw
    simp only [Int.mul_sub, Int.neg_mul] at hraw
    omega
  have hhalf : 0 ≤ Int.fdiv height 2 ∧ Int.fdiv height 2 ≤ height := by
    rw [Tree.fdiv2]
    omega
  have hwidthProduct := Int.mul_nonneg (Int.le_of_lt hspan) hw
  have hhalfProduct := Int.mul_nonneg hfall hhalf.1
  have hremainingProduct := Int.mul_nonneg hfall
    (show 0 ≤ height - Int.fdiv height 2 by omega)
  simp only [Int.mul_sub] at hremainingProduct
  change fall * height ≤ span * reservation at hcoverage
  change ¬ Polyline.hitsRect
    [⟨x0, ordinate spine up t0⟩, ⟨x1, ordinate spine up t1⟩]
    ⟨x0 + q - reservation - width, ordinate spine up t - Int.fdiv height 2,
      width, height⟩
  have hneq : (⟨x0, ordinate spine up t0⟩ : Point) ≠
      ⟨x1, ordinate spine up t1⟩ := by
    intro heq
    have hy := congrArg Point.y heq
    cases up <;> simp only [ordinate, Bool.false_eq_true, ↓reduceIte] at hy <;> omega
  intro hhit
  apply hhit.2.2
  constructor
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    refine ⟨hneq, ?_⟩
    cases up with
    | false =>
      apply Or.inl
      have hnormalY : (spine + t0) - (spine + t1) = -span := by
        dsimp only [span]
        omega
      simp only [Polyline.minCorner, Int.le_min]
      constructor <;> constructor
      all_goals
        simp only [ordinate, Bool.false_eq_true, ↓reduceIte, Polyline.dot]
        rw [hnormalY, hnormalX]
        simp only [Int.mul_add, Int.mul_sub, Int.neg_mul]
        omega
    | true =>
      apply Or.inr
      have hnormalY : (spine - t0) - (spine - t1) = span := by
        dsimp only [span]
        omega
      simp only [Polyline.maxCorner, Int.max_le]
      constructor <;> constructor
      all_goals
        simp only [ordinate, ↓reduceIte, Polyline.dot]
        rw [hnormalY, hnormalX]
        simp only [Int.mul_add, Int.mul_sub, Int.neg_mul]
        omega
  · trivial

/-- Copied from `IshikawaClearanceFacts.positive_gap_lt` (private there). -/
theorem positive_gap_lt (a b height : Int) (hh : 0 < height)
    (hgap : a + height ≤ b) : a < b := by
  omega

/-- Copied from `IshikawaClearanceFacts.successful_slope_parameters`
(private there). -/
theorem successful_slope_parameters (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hne : ns ≠ []) (hrun : layout ns p = .ok raw) :
    0 ≤ p.cos ∧ 1 ≤ p.sin := by
  cases ns with
  | nil => exact False.elim (hne rfl)
  | cons head rest =>
    unfold layout at hrun
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hrun
    split at hrun
    · simp only [bind, Except.bind] at hrun
      cases hrun
    · split at hrun
      · simp only [bind, Except.bind] at hrun
        cases hrun
      · rename_i hparameters
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hparameters
        omega

/-- Copied from `IshikawaClearanceFacts.nonroot_parent_index` (private there). -/
theorem nonroot_parent_index (parent : Int) (hlb : -1 ≤ parent)
    (hne : parent ≠ -1) : ∃ i : Nat, parent = (i : Int) := by
  exact ⟨parent.toNat, by omega⟩

/-- Copied from `IshikawaClearanceFacts.parent_depth_even` (private there). -/
theorem parent_depth_even (parent child : Nat) (hd : child = parent + 1)
    (hodd : child % 2 ≠ 0) : parent % 2 = 0 := by
  have hm := Nat.mod_lt parent (by decide : 0 < 2)
  omega

/-- Copied from `IshikawaClearanceFacts.even_native_reservation` (private there). -/
theorem even_native_reservation (p : Params) (par : Bone) (depth : Nat)
    (t : Int) (count : Nat) (margin : Int) (hd : depth % 2 = 0) :
    let b := depthBone p par depth t count margin
    0 < b.count + 1 ∧ (b.count + 1) * margin ≤ b.x0 - b.x1 := by
  let b := depthBone p par depth t count margin
  have hc : b.count = (count : Int) := by
    unfold b depthBone
    split <;> rfl
  have he := (depthBone_even_endpoints p par depth t count margin hd).2.2
  have hr : ((count : Int) + 1) * margin ≤ boneLength p count margin :=
    Int.le_max_right _ _
  constructor
  · rw [hc]
    omega
  · rw [hc]
    change ((count : Int) + 1) * margin ≤ b.x0 - b.x1
    change b.x1 = b.x0 - boneLength p count margin at he
    omega

/-- Copied from `IshikawaClearanceFacts.child_depth_even` (private there). -/
theorem child_depth_even (parent child : Nat) (hd : child = parent + 1)
    (hodd : parent % 2 ≠ 0) : child % 2 = 0 := by
  have hm := Nat.mod_lt parent (by decide : 0 < 2)
  omega

/-- Copied from `IshikawaClearanceFacts.boneLength_margin` (private there). -/
theorem boneLength_margin (p : Params) (count : Nat) (margin : Int)
    (hmargin : 0 ≤ margin) : margin ≤ boneLength p count margin := by
  have hcount : (1 : Int) ≤ (count : Int) + 1 := by omega
  have hmul := Int.mul_le_mul_of_nonneg_right hcount hmargin
  have hreserve : ((count : Int) + 1) * margin ≤ boneLength p count margin :=
    Int.le_max_right _ _
  exact Int.le_trans (by simpa only [Int.one_mul] using hmul) hreserve

/-- Copied from `IshikawaClearanceFacts.attachment_start_margin` (private there). -/
theorem attachment_start_margin (left right count drawn margin : Int)
    (hden : 0 < count + 1) (hmargin : 0 ≤ margin)
    (hreserve : (count + 1) * margin ≤ left - right)
    (hdrawn : drawn + 1 ≤ count) :
    left + Int.fdiv ((right - left) * (count - drawn)) (count + 1) + margin ≤ left := by
  have hspan : 0 ≤ left - right :=
    Int.le_trans (Int.mul_nonneg (Int.le_of_lt hden) hmargin) hreserve
  have hmul := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ count - drawn by omega) hspan
  simp only [Int.mul_one] at hmul
  have halgebra : (right - left) * (count - drawn) =
      -((left - right) * (count - drawn)) := by
    simp only [Int.sub_mul]
    omega
  have hbound : (right - left) * (count - drawn) ≤ (count + 1) * (-margin) := by
    rw [Int.mul_neg]
    omega
  have hquot := Chart.fdiv_le_of_le_mul hden hbound
  omega

end IshikawaC6RibHardHelpers

end Elegant.Ishikawa

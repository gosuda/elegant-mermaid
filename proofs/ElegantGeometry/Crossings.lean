import ElegantGeometry.Basic

/-! Crossings: axis-aligned segment crossing, the inversion count, and the identity
between the crossing count of two layers and the inversion count of the bottom
positions.

Rational points are encoded without a rational type: a point is `⟨nx, ny, d⟩`, meaning
`(nx / d, ny / d)` with `0 < d`. Membership in an open segment is stated with the
denominator cleared by cross-multiplication, so every test is an integer test.

The crossing predicate of `spec/geometry-kernel.md` is `Segment.Crosses`: two segments
cross exactly when their open interiors share a point. A zero-length segment never
crosses, because its open interval is empty; perpendicular segments cross exactly when
the crossing point is strictly inside both; collinear segments cross exactly when their
open intervals overlap in positive length; touching at an endpoint never crosses. -/

set_option autoImplicit false

/-- An axis-aligned segment. -/
structure Segment where
  a : Point
  b : Point
deriving DecidableEq, Repr

/-- A rational point: the pair `(nx / d, ny / d)` with `d > 0`. -/
structure QPoint where
  nx : Int
  ny : Int
  d : Int
deriving DecidableEq, Repr

/-- `2` is a positive denominator, for the collinear midpoint witness. -/
theorem valid_two : (0 : Int) < 2 := by decide

namespace Segment

/-- The segment is vertical: both endpoints share one `x`. -/
abbrev vertical (s : Segment) : Prop := s.a.x = s.b.x

/-- The segment is horizontal: both endpoints share one `y`. -/
abbrev horizontal (s : Segment) : Prop := s.a.y = s.b.y

/-- The segment is axis-aligned. -/
abbrev isAxisAligned (s : Segment) : Prop := s.vertical ∨ s.horizontal

/-- The `x` projections of two horizontal segments overlap with positive length. -/
abbrev ovH (s t : Segment) : Prop :=
  max (min s.a.x s.b.x) (min t.a.x t.b.x) < min (max s.a.x s.b.x) (max t.a.x t.b.x)

/-- The `y` projections of two vertical segments overlap with positive length. -/
abbrev ovV (s t : Segment) : Prop :=
  max (min s.a.y s.b.y) (min t.a.y t.b.y) < min (max s.a.y s.b.y) (max t.a.y t.b.y)

theorem ovH_comm (s t : Segment) : ovH s t = ovH t s := by
  unfold ovH
  rw [Int.max_comm (min s.a.x s.b.x) (min t.a.x t.b.x),
    Int.min_comm (max s.a.x s.b.x) (max t.a.x t.b.x)]

theorem ovV_comm (s t : Segment) : ovV s t = ovV t s := by
  unfold ovV
  rw [Int.max_comm (min s.a.y s.b.y) (min t.a.y t.b.y),
    Int.min_comm (max s.a.y s.b.y) (max t.a.y t.b.y)]

/-- The open interiors of two axis-aligned segments share a point. The collinear cases
require a positive-length overlap, so a zero-length segment never crosses anything. -/
abbrev Crosses (s t : Segment) : Prop :=
  (s.vertical ∧ t.horizontal ∧
      min s.a.y s.b.y < t.a.y ∧ t.a.y < max s.a.y s.b.y ∧
      min t.a.x t.b.x < s.a.x ∧ s.a.x < max t.a.x t.b.x) ∨
    (t.vertical ∧ s.horizontal ∧
      min t.a.y t.b.y < s.a.y ∧ s.a.y < max t.a.y t.b.y ∧
      min s.a.x s.b.x < t.a.x ∧ t.a.x < max s.a.x s.b.x) ∨
    (s.horizontal ∧ t.horizontal ∧ s.a.y = t.a.y ∧ ovH s t) ∨
    (s.vertical ∧ t.vertical ∧ s.a.x = t.a.x ∧ ovV s t)

theorem crosses_comm (s t : Segment) : s.Crosses t ↔ t.Crosses s := by
  unfold Crosses
  constructor
  · rintro (h | h | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl ⟨b, a, c.symm, (ovH_comm s t) ▸ d⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨b, a, c.symm, (ovV_comm s t) ▸ d⟩))
  · rintro (h | h | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl ⟨b, a, c.symm, (ovH_comm t s) ▸ d⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨b, a, c.symm, (ovV_comm t s) ▸ d⟩))

/-- The checked crossing test: `ok` for axis-aligned segments, `domain` otherwise. -/
def cross (s t : Segment) : Except LayoutError Bool :=
  if s.isAxisAligned ∧ t.isAxisAligned then .ok (decide (s.Crosses t))
  else .error .domain

/-- `Segment.cross_comm`: the crossing test is symmetric. -/
theorem cross_comm (s t : Segment) : s.cross t = t.cross s := by
  unfold cross
  by_cases h : s.isAxisAligned ∧ t.isAxisAligned
  · have h' : t.isAxisAligned ∧ s.isAxisAligned := ⟨h.2, h.1⟩
    rw [ite_eq_left h, ite_eq_left h']
    exact congrArg Except.ok (decide_eq_of_iff (crosses_comm s t))
  · have h' : ¬(t.isAxisAligned ∧ s.isAxisAligned) := fun ht => h ⟨ht.2, ht.1⟩
    rw [ite_eq_right h, ite_eq_right h']

end Segment

namespace QPoint

/-- A point with a positive denominator. -/
abbrev Valid (p : QPoint) : Prop := 0 < p.d

theorem d_one (a b : Int) : (⟨a, b, 1⟩ : QPoint).d = 1 := rfl

theorem pos_d_one (a b : Int) : Valid ⟨a, b, 1⟩ := by
  unfold Valid
  rw [d_one]
  decide

/-- `p` lies strictly inside the vertical segment `s`. -/
abbrev inVertical (p : QPoint) (s : Segment) : Prop :=
  p.Valid ∧ p.nx = s.a.x * p.d ∧
    min s.a.y s.b.y * p.d < p.ny ∧ p.ny < max s.a.y s.b.y * p.d

/-- `p` lies strictly inside the horizontal segment `s`. -/
abbrev inHorizontal (p : QPoint) (s : Segment) : Prop :=
  p.Valid ∧ p.ny = s.a.y * p.d ∧
    min s.a.x s.b.x * p.d < p.nx ∧ p.nx < max s.a.x s.b.x * p.d

/-- `p` lies in the open interior of `s`. -/
abbrev inOpenSegment (p : QPoint) (s : Segment) : Prop :=
  (s.vertical ∧ p.inVertical s) ∨ (s.horizontal ∧ p.inHorizontal s)

end QPoint

/-- The witness point of the first perpendicular orientation. -/
def perpWitness (s t : Segment) : QPoint := ⟨s.a.x, t.a.y, 1⟩

/-- The witness point of the second perpendicular orientation. -/
def perpWitness' (s t : Segment) : QPoint := ⟨t.a.x, s.a.y, 1⟩

/-- The witness point of an overlap of two collinear horizontal segments: the midpoint of
the overlap, with denominator 2 so that every product stays linear. -/
def colWitnessH (s t : Segment) : QPoint :=
  ⟨max (min s.a.x s.b.x) (min t.a.x t.b.x) + min (max s.a.x s.b.x) (max t.a.x t.b.x),
    s.a.y * 2, 2⟩

/-- The witness point of an overlap of two collinear vertical segments. -/
def colWitnessV (s t : Segment) : QPoint :=
  ⟨s.a.x * 2,
    max (min s.a.y s.b.y) (min t.a.y t.b.y) + min (max s.a.y s.b.y) (max t.a.y t.b.y), 2⟩

/-- A positive factor distributes over `max`. -/
theorem max_mul_right {a b c : Int} (hc : 0 ≤ c) : max a b * c = max (a * c) (b * c) := by
  rcases Int.le_total a b with h | h
  · rw [Int.max_eq_right h, Int.max_eq_right (Int.mul_le_mul_of_nonneg_right h hc)]
  · rw [Int.max_eq_left h, Int.max_eq_left (Int.mul_le_mul_of_nonneg_right h hc)]

/-- A positive factor distributes over `min`. -/
theorem min_mul_right {a b c : Int} (hc : 0 ≤ c) : min a b * c = min (a * c) (b * c) := by
  rcases Int.le_total a b with h | h
  · rw [Int.min_eq_left h, Int.min_eq_left (Int.mul_le_mul_of_nonneg_right h hc)]
  · rw [Int.min_eq_right h, Int.min_eq_right (Int.mul_le_mul_of_nonneg_right h hc)]

/-- Division-free consequence of a cleared-denominator inequality. -/
theorem lt_div {a b d : Int} (hd : 0 < d) (h : a * d < b * d) : a < b :=
  (Int.mul_lt_mul_right hd).mp h

/-- Division-free consequence of a cleared-denominator equation. -/
theorem eq_div {a b d : Int} (hd : d ≠ 0) (h : a * d = b * d) : a = b :=
  Int.eq_of_mul_eq_mul_right hd h

/-- The cleared form of the collinear overlap: the scaled overlaps interleave. -/
theorem scaled_overlap {a a' b b' ny pd : Int}
    (h1 : a * pd < ny) (h2 : ny < a' * pd) (h3 : b * pd < ny) (h4 : ny < b' * pd) :
    max (a * pd) (b * pd) < min (a' * pd) (b' * pd) :=
  Int.max_lt.mpr
    ⟨Int.lt_min.mpr ⟨Int.lt_trans h1 h2, Int.lt_trans h1 h4⟩,
      Int.lt_min.mpr ⟨Int.lt_trans h3 h2, Int.lt_trans h3 h4⟩⟩

/-- A positive factor and a negative product: `m < 0` and `m * n < 0` give `0 < n`. -/
theorem pos_of_neg_mul {m n : Int} (hm : m < 0) (h : m * n < 0) : 0 < n := by
  have hk : 0 < -m := Int.neg_pos.mpr hm
  have h1 : 0 < -m * n := by rw [Int.neg_mul]; exact Int.neg_pos.mpr h
  have h3 : -m * (0 : Int) < -m * n ↔ (0 : Int) < n := Int.mul_lt_mul_left hk
  rw [Int.mul_zero] at h3
  exact h3.mp h1

/-- The left bound of the collinear horizontal witness, for `s`. -/
theorem col_left {m M m' M' : Int} (h : max m m' < min M M') :
    m * 2 < max m m' + min M M' := by
  have h1 : m ≤ max m m' := Int.le_max_left _ _
  have h2 : m < min M M' := Int.lt_of_le_of_lt h1 h
  omega

/-- The left bound of the collinear horizontal witness, for `t`. -/
theorem col_left' {m M m' M' : Int} (h : max m m' < min M M') :
    m' * 2 < max m m' + min M M' := by
  have h1 : m' ≤ max m m' := Int.le_max_right _ _
  have h2 : m' < min M M' := Int.lt_of_le_of_lt h1 h
  omega

/-- The right bound of the collinear horizontal witness, for `s`. -/
theorem col_right {m M m' M' : Int} (h : max m m' < min M M') :
    max m m' + min M M' < M * 2 := by
  have h1 : min M M' ≤ M := Int.min_le_left _ _
  have h2 : max m m' < M := Int.lt_of_lt_of_le h h1
  omega

/-- The right bound of the collinear horizontal witness, for `t`. -/
theorem col_right' {m M m' M' : Int} (h : max m m' < min M M') :
    max m m' + min M M' < M' * 2 := by
  have h1 : min M M' ≤ M' := Int.min_le_right _ _
  have h2 : max m m' < M' := Int.lt_of_lt_of_le h h1
  omega

/-- The cleared denominator of a scaled overlap: the overlap of the scaled intervals
gives the overlap of the intervals. -/
theorem lt_of_scaled {m m' M M' d : Int} (hd : 0 < d)
    (h : max (m * d) (m' * d) < min (M * d) (M' * d)) : max m m' < min M M' := by
  have h' : max m m' * d < min M M' * d := by
    rw [max_mul_right (Int.le_of_lt hd), min_mul_right (Int.le_of_lt hd)]
    exact h
  exact lt_div hd h'

namespace Segment

/-- A crossing gives a rational point inside both open interiors. -/
theorem crosses_witness {s t : Segment} (h : s.Crosses t) :
    ∃ p : QPoint, p.inOpenSegment s ∧ p.inOpenSegment t := by
  rcases h with ⟨hsv, hth, hy1, hy2, hx1, hx2⟩ | ⟨htv, hsh, hy1, hy2, hx1, hx2⟩ |
    ⟨hsh, hth, hy, hov⟩ | ⟨hsv, htv, hx, hov⟩
  · refine ⟨perpWitness s t, ?_, ?_⟩
    · exact Or.inl ⟨hsv, QPoint.pos_d_one _ _, by simp [perpWitness],
        by simpa [perpWitness] using hy1, by simpa [perpWitness] using hy2⟩
    · exact Or.inr ⟨hth, QPoint.pos_d_one _ _, by simp [perpWitness],
        by simpa [perpWitness] using hx1, by simpa [perpWitness] using hx2⟩
  · refine ⟨perpWitness' s t, ?_, ?_⟩
    · exact Or.inr ⟨hsh, QPoint.pos_d_one _ _, by simp [perpWitness'],
        by simpa [perpWitness'] using hx1, by simpa [perpWitness'] using hx2⟩
    · exact Or.inl ⟨htv, QPoint.pos_d_one _ _, by simp [perpWitness'],
        by simpa [perpWitness'] using hy1, by simpa [perpWitness'] using hy2⟩
  · refine ⟨colWitnessH s t, ?_, ?_⟩
    · exact Or.inr ⟨hsh, valid_two, rfl, col_left hov, col_right hov⟩
    · exact Or.inr ⟨hth, valid_two, by show s.a.y * 2 = t.a.y * 2; rw [hy],
        col_left' hov, col_right' hov⟩
  · refine ⟨colWitnessV s t, ?_, ?_⟩
    · exact Or.inl ⟨hsv, valid_two, rfl, col_left hov, col_right hov⟩
    · exact Or.inl ⟨htv, valid_two, by show s.a.x * 2 = t.a.x * 2; rw [hx],
        col_left' hov, col_right' hov⟩

/-- A rational point inside both open interiors means the segments cross. -/
theorem witness_crosses {s t : Segment} {p : QPoint}
    (hs : p.inOpenSegment s) (ht : p.inOpenSegment t) : s.Crosses t := by
  obtain ⟨hsv, hpd, hnx, sy1, sy2⟩ | ⟨hsh, hpd, hny, sx1, sx2⟩ := hs
  · obtain ⟨htv, _, tnx, ty1, ty2⟩ | ⟨hth, _, tny, tx1, tx2⟩ := ht
    · refine Or.inr (Or.inr (Or.inr ⟨hsv, htv, ?_, ?_⟩))
      · exact eq_div (Int.ne_of_gt hpd) (by rw [← hnx, ← tnx])
      · exact lt_of_scaled hpd (scaled_overlap sy1 sy2 ty1 ty2)
    · refine Or.inl ⟨hsv, hth, ?_, ?_, ?_, ?_⟩
      · rw [tny] at sy1; exact lt_div hpd sy1
      · rw [tny] at sy2; exact lt_div hpd sy2
      · rw [hnx] at tx1; exact lt_div hpd tx1
      · rw [hnx] at tx2; exact lt_div hpd tx2
  · obtain ⟨htv, _, tnx, ty1, ty2⟩ | ⟨hth, _, tny, tx1, tx2⟩ := ht
    · refine Or.inr (Or.inl ⟨htv, hsh, ?_, ?_, ?_, ?_⟩)
      · rw [hny] at ty1; exact lt_div hpd ty1
      · rw [hny] at ty2; exact lt_div hpd ty2
      · rw [tnx] at sx1; exact lt_div hpd sx1
      · rw [tnx] at sx2; exact lt_div hpd sx2
    · refine Or.inr (Or.inr (Or.inl ⟨hsh, hth, ?_, ?_⟩))
      · exact eq_div (Int.ne_of_gt hpd) (by rw [← hny, ← tny])
      · exact lt_of_scaled hpd (scaled_overlap sx1 sx2 tx1 tx2)

/-- Two segments cross exactly when a rational point lies in both open interiors. -/
theorem crosses_iff_common_interior_point (s t : Segment) :
    s.Crosses t ↔ ∃ p : QPoint, p.inOpenSegment s ∧ p.inOpenSegment t :=
  ⟨crosses_witness, fun ⟨_, hs, ht⟩ => witness_crosses hs ht⟩

/-- A crossing forces both segments to be axis-aligned. -/
theorem isAxisAligned_of_crosses {s t : Segment} (h : s.Crosses t) :
    s.isAxisAligned ∧ t.isAxisAligned := by
  rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
  · exact ⟨Or.inl h1, Or.inr h2⟩
  · exact ⟨Or.inr h2, Or.inl h1⟩
  · exact ⟨Or.inr h1, Or.inr h2⟩
  · exact ⟨Or.inl h1, Or.inl h2⟩

/-- `Segment.cross_iff_common_interior_point`: the checked crossing test is true exactly
when a rational point lies in both open interiors. The open interior is that of an
axis-aligned segment. A segment that is not axis-aligned gives `error domain`, and it has
no interior point in the kernel, so both sides are then false. -/
theorem cross_iff_common_interior_point (s t : Segment) :
    s.cross t = .ok true ↔ ∃ p : QPoint, p.inOpenSegment s ∧ p.inOpenSegment t := by
  unfold cross
  by_cases h : s.isAxisAligned ∧ t.isAxisAligned
  · rw [ite_eq_left h, Except.ok.injEq, decide_eq_true_eq]
    exact crosses_iff_common_interior_point s t
  · rw [ite_eq_right h]
    refine ⟨(fun hcontra => nomatch hcontra), ?_⟩
    rintro ⟨p, hs, ht⟩
    exact absurd (isAxisAligned_of_crosses (witness_crosses hs ht)) h

end Segment

/-! ## Inversions

The inversion count of a list, and the identity between the crossings of two layers and
the inversion count of the bottom positions. -/

/-- The unscaled inversion count of a list, as a `Nat`: the number of index pairs `i < j`
with `xs[i] > xs[j]`. -/
def countInversionsNat : List Int → Nat
  | [] => 0
  | x :: rest => rest.countP (fun y => decide (x > y)) + countInversionsNat rest

/-- The unscaled inversion count of a list. -/
def countInversionsRaw (xs : List Int) : Int := Int.ofNat (countInversionsNat xs)

/-- The number of pairs `i < j` with `xs[i] > xs[j]`, checked against the int32 range. -/
def countInversions (xs : List Int) : Except LayoutError Int :=
  if countInversionsRaw xs ≤ I32_MAX then .ok (countInversionsRaw xs) else .error .overflow

/-- One edge between two adjacent layers: its upper endpoint and its lower endpoint. -/
structure LayerEdge where
  top : Int
  bot : Int
deriving DecidableEq, Repr

/-- The sort key of an edge: the position of its upper endpoint, then the position of its
lower endpoint. -/
def edgeKey (P Q : Int → Int) (e : LayerEdge) : Int × Int := (P e.top, Q e.bot)

/-- The lexicographic order on key pairs that the ordering phase sorts by. -/
abbrev KeyLe (x y : Int × Int) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)

theorem keyLe_trans {x y z : Int × Int} (h1 : KeyLe x y) (h2 : KeyLe y z) : KeyLe x z := by
  rcases h1 with h1 | ⟨h1a, h1b⟩
  · rcases h2 with h2 | ⟨h2a, _⟩
    · exact Or.inl (Int.lt_trans h1 h2)
    · exact Or.inl (h2a ▸ h1)
  · rcases h2 with h2 | ⟨h2a, h2b⟩
    · exact Or.inl (h1a ▸ h2)
    · exact Or.inr ⟨h1a.trans h2a, Int.le_trans h1b h2b⟩

theorem keyLe_total (x y : Int × Int) : KeyLe x y ∨ KeyLe y x := by
  rcases Int.lt_trichotomy x.1 y.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases Int.le_total x.2 y.2 with h2 | h2
    · exact Or.inl (Or.inr ⟨h, h2⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h2⟩)
  · exact Or.inr (Or.inl h)

/-- The key list in the order sorted by `(P top, Q bot)`. -/
def sortKeys (ks : List (Int × Int)) : List (Int × Int) :=
  ks.mergeSort (fun a b => decide (KeyLe a b))

theorem sortKeys_perm (ks : List (Int × Int)) : (sortKeys ks).Perm ks :=
  List.mergeSort_perm ks _

theorem sortKeys_pairwise (ks : List (Int × Int)) : List.Pairwise KeyLe (sortKeys ks) := by
  refine List.Pairwise.imp (fun h => of_decide_eq_true h)
    (List.pairwise_mergeSort (le := fun a b => decide (KeyLe a b)) ?_ ?_ ks)
  · intro a b c hab hbc
    exact decide_eq_true (keyLe_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  · intro a b
    rcases keyLe_total a b with h | h
    · rw [decide_eq_true h]; rfl
    · rw [decide_eq_true h]; exact Bool.or_true _

/-- Two key pairs cross when their position differences have opposite signs. -/
abbrev crossesKey (x y : Int × Int) : Prop := (x.1 - y.1) * (x.2 - y.2) < 0

/-- The executable form of `crossesKey`. -/
def crossesKeyB (x y : Int × Int) : Bool := decide (crossesKey x y)

/-- The number of unordered key pairs that cross, counted over index pairs `i < j`. -/
def crossCountN : List (Int × Int) → Nat
  | [] => 0
  | k :: rest => rest.countP (crossesKeyB k) + crossCountN rest

/-- The number of unordered key pairs that cross, as an `Int`. -/
def crossCount (ks : List (Int × Int)) : Int := Int.ofNat (crossCountN ks)

theorem crossesKey_comm (x y : Int × Int) : crossesKey x y ↔ crossesKey y x := by
  unfold crossesKey
  rw [show y.1 - x.1 = -(x.1 - y.1) from (Int.neg_sub _ _).symm,
    show y.2 - x.2 = -(x.2 - y.2) from (Int.neg_sub _ _).symm, Int.neg_mul_neg]

theorem crossesKeyB_comm (x y : Int × Int) : crossesKeyB x y = crossesKeyB y x :=
  decide_eq_of_iff (crossesKey_comm x y)

theorem countP_cons_true {α : Type} {p : α → Bool} {a : α} {l : List α}
    (h : p a = true) : List.countP p (a :: l) = List.countP p l + 1 := by
  rw [List.countP_cons]; simp [h]

theorem countP_cons_false {α : Type} {p : α → Bool} {a : α} {l : List α}
    (h : p a = false) : List.countP p (a :: l) = List.countP p l := by
  rw [List.countP_cons]; simp [h]

theorem crossCountN_swap (x y : Int × Int) (l : List (Int × Int)) :
    crossCountN (y :: x :: l) = crossCountN (x :: y :: l) := by
  have e1 : crossCountN (y :: x :: l)
      = List.countP (crossesKeyB y) (x :: l)
        + (List.countP (crossesKeyB x) l + crossCountN l) := rfl
  have e2 : crossCountN (x :: y :: l)
      = List.countP (crossesKeyB x) (y :: l)
        + (List.countP (crossesKeyB y) l + crossCountN l) := rfl
  rw [e1, e2]
  by_cases h : crossesKeyB y x = true
  · have h2 : crossesKeyB x y = true := by rw [crossesKeyB_comm x y]; exact h
    rw [countP_cons_true (p := crossesKeyB y) (a := x) (l := l) h,
      countP_cons_true (p := crossesKeyB x) (a := y) (l := l) h2]
    omega
  · have hf : crossesKeyB y x = false := by cases hv : crossesKeyB y x <;> simp_all
    have h2 : crossesKeyB x y = false := by rw [crossesKeyB_comm x y]; exact hf
    rw [countP_cons_false (p := crossesKeyB y) (a := x) (l := l) hf,
      countP_cons_false (p := crossesKeyB x) (a := y) (l := l) h2]
    omega

theorem crossCountN_perm {l l' : List (Int × Int)} (h : l.Perm l') :
    crossCountN l = crossCountN l' := by
  induction h with
  | nil => rfl
  | @cons x l₁ l₂ hp ih =>
    show List.countP (crossesKeyB x) l₁ + crossCountN l₁
        = List.countP (crossesKeyB x) l₂ + crossCountN l₂
    rw [hp.countP_eq (crossesKeyB x), ih]
  | swap x y l => exact crossCountN_swap x y l
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- For a key pair `k` that precedes `k'` in the lexicographic order, the bottom position
of `k` exceeds that of `k'` exactly when the pair crosses. -/
theorem keyLe_snd_iff {k k' : Int × Int} (h : KeyLe k k') :
    k.2 > k'.2 ↔ crossesKey k k' := by
  unfold crossesKey
  rcases h with h | ⟨h1, h2⟩
  · have hm : k.1 - k'.1 < 0 := Int.sub_neg_of_lt h
    constructor
    · intro hg
      exact Int.mul_neg_of_neg_of_pos hm (Int.sub_pos_of_lt hg)
    · intro hc
      have hp := pos_of_neg_mul hm hc
      omega
  · constructor
    · intro hg
      omega
    · intro hc
      rw [h1, Int.sub_self, Int.zero_mul] at hc
      exact absurd hc (Int.lt_irrefl 0)

/-- For a list sorted by `(P top, Q bot)`, the inversion count of the bottom positions is
the number of pairs whose position differences have opposite signs. -/
theorem inversions_sorted (l : List (Int × Int)) (h : List.Pairwise KeyLe l) :
    countInversionsNat (l.map (fun k => k.2)) = crossCountN l := by
  induction l with
  | nil => rfl
  | cons k rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
    have hc : List.countP (fun y => decide (k.2 > y)) (rest.map (fun k => k.2))
        = List.countP (crossesKeyB k) rest := by
      rw [List.countP_map]
      refine List.countP_congr (fun k' hk' => ?_)
      show decide (k.2 > k'.2) = true ↔ decide (crossesKey k k') = true
      rw [decide_eq_true_iff, decide_eq_true_iff]
      exact keyLe_snd_iff (hhead k' hk')
    have e1 : countInversionsNat ((k :: rest).map (fun k => k.2))
        = List.countP (fun y => decide (k.2 > y)) (rest.map (fun k => k.2))
          + countInversionsNat (rest.map (fun k => k.2)) := rfl
    have e2 : crossCountN (k :: rest)
        = List.countP (crossesKeyB k) rest + crossCountN rest := rfl
    rw [e1, e2, hc, ih htail]

/-- The bottom-position inversion count of the sorted keys is the crossing count of the
edges. -/
theorem inversions_eq_crossings_raw (P Q : Int → Int) (es : List LayerEdge) :
    countInversionsRaw ((sortKeys (es.map (edgeKey P Q))).map (fun k => k.2)) =
      crossCount (es.map (edgeKey P Q)) := by
  unfold countInversionsRaw crossCount
  rw [inversions_sorted _ (sortKeys_pairwise _), crossCountN_perm (sortKeys_perm _)]

/-- `inversions_eq_crossings`: for edges between two layers with position maps `P` and
`Q`, `countInversions` of the bottom positions, taken in the order sorted by
`(P top, Q bot)`, is the number `n` of unordered edge pairs whose position differences
have opposite signs when `n` fits the int32 range, and the kernel's `overflow` error
otherwise, as `spec/geometry-kernel.md` requires. It holds for every input. -/
theorem inversions_eq_crossings (P Q : Int → Int) (es : List LayerEdge) :
    countInversions ((sortKeys (es.map (edgeKey P Q))).map (fun k => k.2)) =
      if crossCount (es.map (edgeKey P Q)) ≤ I32_MAX
      then .ok (crossCount (es.map (edgeKey P Q)))
      else .error .overflow := by
  unfold countInversions
  rw [inversions_eq_crossings_raw]

/-- The case of `inversions_eq_crossings` in which the count fits the int32 range: the
result is `.ok n`. -/
theorem inversions_eq_crossings_of_le (P Q : Int → Int) (es : List LayerEdge)
    (h : crossCount (es.map (edgeKey P Q)) ≤ I32_MAX) :
    countInversions ((sortKeys (es.map (edgeKey P Q))).map (fun k => k.2)) =
      .ok (crossCount (es.map (edgeKey P Q))) := by
  rw [inversions_eq_crossings, ite_eq_left h]

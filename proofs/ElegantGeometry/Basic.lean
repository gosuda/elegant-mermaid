set_option autoImplicit false

/-! Integer geometry kernel: points, sizes, rectangles, intervals, and the checked
rectangular operations of the specification. Every operation reports a
`LayoutError.domain` for an invalid argument and a `LayoutError.overflow` for a
result that leaves the int32 range. -/

/-- The smallest int32 value. -/
def I32_MIN : Int := -2147483648

/-- The largest int32 value. -/
def I32_MAX : Int := 2147483647

/-- The coordinate bound that keeps the separating-axis test exact in int64. -/
def COORD_LIMIT : Int := 536870912

/-- `n` is an int32 value. -/
abbrev InI32 (n : Int) : Prop := I32_MIN ≤ n ∧ n ≤ I32_MAX

/-- An integer point. -/
structure Point where
  x : Int
  y : Int
deriving DecidableEq, Repr, Inhabited

/-- An integer size. -/
structure Size where
  w : Int
  h : Int
deriving DecidableEq, Repr, Inhabited

/-- An axis-aligned rectangle with integer fields. -/
structure Rect where
  x : Int
  y : Int
  w : Int
  h : Int
deriving DecidableEq, Repr, Inhabited

/-- A closed integer interval. -/
structure Interval where
  lo : Int
  hi : Int
deriving DecidableEq, Repr, Inhabited

/-- The axis of a one-dimensional sweep. -/
inductive Axis where
  | X
  | Y
deriving DecidableEq, Repr

/-- The two kernel errors. -/
inductive LayoutError where
  | overflow
  | domain
deriving DecidableEq, Repr

/-- Equivalent propositions have equal `decide` values. -/
theorem decide_eq_of_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  by_cases hp : p
  · simp [hp, h.mp hp]
  · have hq : ¬q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

namespace Size

/-- A size is valid when both of its fields are non-negative. -/
abbrev Valid (s : Size) : Prop := 0 ≤ s.w ∧ 0 ≤ s.h

end Size

namespace Rect

/-- A rectangle is valid when its fields and both of its far edges are int32 values
and its sizes are non-negative. -/
abbrev Valid (r : Rect) : Prop :=
  0 ≤ r.w ∧ 0 ≤ r.h ∧ InI32 r.x ∧ InI32 r.y ∧ InI32 r.w ∧ InI32 r.h ∧
    InI32 (r.x + r.w) ∧ InI32 (r.y + r.h)

/-- `outer` contains `inner` inclusively on all four sides. -/
abbrev Contained (outer inner : Rect) : Prop :=
  outer.x ≤ inner.x ∧ inner.x + inner.w ≤ outer.x + outer.w ∧
    outer.y ≤ inner.y ∧ inner.y + inner.h ≤ outer.y + outer.h

theorem Contained.refl (a : Rect) : a.Contained a := by
  unfold Contained
  omega

theorem Contained.trans {a b c : Rect} (hab : a.Contained b) (hbc : b.Contained c) :
    a.Contained c := by
  unfold Contained at *
  omega

/-- The open interiors of two rectangles share a point. -/
abbrev meetsInterior (a b : Rect) : Prop :=
  max a.x b.x < min (a.x + a.w) (b.x + b.w) ∧
    max a.y b.y < min (a.y + a.h) (b.y + b.h)

theorem meetsInterior_comm (a b : Rect) : a.meetsInterior b ↔ b.meetsInterior a := by
  unfold meetsInterior
  constructor <;> intro h <;> omega

/-- The translated rectangle, before its validity is checked. -/
def translateRaw (r : Rect) (dx dy : Int) : Rect := ⟨r.x + dx, r.y + dy, r.w, r.h⟩

/-- The inflated rectangle, before its validity is checked. -/
def inflateRaw (r : Rect) (d : Int) : Rect := ⟨r.x - d, r.y - d, r.w + 2 * d, r.h + 2 * d⟩

/-- The bounding rectangle of two rectangles, before its validity is checked. -/
def unionRaw (a b : Rect) : Rect :=
  ⟨min a.x b.x, min a.y b.y, max (a.x + a.w) (b.x + b.w) - min a.x b.x,
    max (a.y + a.h) (b.y + b.h) - min a.y b.y⟩

/-- The rectangle `s` placed after the far edge of `a` on `axis`, before its validity
is checked. -/
def placeAfterRaw (axis : Axis) (a : Rect) (gap : Int) (s : Size) : Rect :=
  match axis with
  | .X => ⟨a.x + a.w + gap, a.y, s.w, s.h⟩
  | .Y => ⟨a.x, a.y + a.h + gap, s.w, s.h⟩

/-- Move a rectangle by `(dx, dy)`. -/
def translate (r : Rect) (dx dy : Int) : Except LayoutError Rect :=
  if r.Valid then
    if (r.translateRaw dx dy).Valid then .ok (r.translateRaw dx dy) else .error .overflow
  else .error .domain

/-- Grow a rectangle by `d` on each of its four sides. -/
def inflate (r : Rect) (d : Int) : Except LayoutError Rect :=
  if r.Valid then
    if 0 ≤ (r.inflateRaw d).w ∧ 0 ≤ (r.inflateRaw d).h then
      if (r.inflateRaw d).Valid then .ok (r.inflateRaw d) else .error .overflow
    else .error .domain
  else .error .domain

/-- The smallest rectangle that contains both closed rectangles. -/
def union (a b : Rect) : Except LayoutError Rect :=
  if a.Valid ∧ b.Valid then
    if (a.unionRaw b).Valid then .ok (a.unionRaw b) else .error .overflow
  else .error .domain

/-- Two rectangles meet when their open interiors share a point. -/
def intersects (a b : Rect) : Except LayoutError Bool :=
  if a.Valid ∧ b.Valid then .ok (decide (a.meetsInterior b)) else .error .domain

/-- Inclusive containment. -/
def contains (outer inner : Rect) : Except LayoutError Bool :=
  if outer.Valid ∧ inner.Valid then .ok (decide (outer.Contained inner))
  else .error .domain

/-- Place a size after the far edge of `a` on `axis`, offset by `gap`. -/
def placeAfter (axis : Axis) (a : Rect) (gap : Int) (s : Size) : Except LayoutError Rect :=
  if a.Valid ∧ 0 ≤ gap ∧ s.Valid then
    if (a.placeAfterRaw axis gap s).Valid then .ok (a.placeAfterRaw axis gap s)
    else .error .overflow
  else .error .domain

theorem translate_ok {r : Rect} {dx dy : Int} {r' : Rect}
    (h : r.translate dx dy = .ok r') :
    r.Valid ∧ r' = r.translateRaw dx dy ∧ r'.Valid := by
  unfold Rect.translate at h
  split at h
  · rename_i hr
    split at h
    · rename_i hr'
      have he : r.translateRaw dx dy = r' := Except.ok.inj h
      exact ⟨hr, he.symm, he ▸ hr'⟩
    · simp at h
  · simp at h

theorem inflate_ok {r : Rect} {d : Int} {r' : Rect} (h : r.inflate d = .ok r') :
    r.Valid ∧ r' = r.inflateRaw d ∧ r'.Valid := by
  unfold Rect.inflate at h
  split at h
  · rename_i hr
    split at h
    · split at h
      · rename_i hr'
        have he : r.inflateRaw d = r' := Except.ok.inj h
        exact ⟨hr, he.symm, he ▸ hr'⟩
      · simp at h
    · simp at h
  · simp at h

theorem union_ok {a b c : Rect} (h : a.union b = .ok c) :
    a.Valid ∧ b.Valid ∧ c.Valid ∧ c.Contained a ∧ c.Contained b := by
  unfold Rect.union at h
  split at h
  · rename_i hv
    split at h
    · rename_i hc
      have he : a.unionRaw b = c := Except.ok.inj h
      subst he
      exact ⟨hv.1, hv.2, hc,
        by unfold Rect.Contained Rect.unionRaw; simp only; omega,
        by unfold Rect.Contained Rect.unionRaw; simp only; omega⟩
    · simp at h
  · simp at h

theorem intersects_eq_true_iff (a b : Rect) :
    a.intersects b = .ok true ↔ a.Valid ∧ b.Valid ∧ a.meetsInterior b := by
  unfold Rect.intersects
  split
  · rename_i hv
    simp only [Except.ok.injEq, decide_eq_true_eq]
    exact ⟨fun h => ⟨hv.1, hv.2, h⟩, fun h => h.2.2⟩
  · rename_i hv
    simp only [reduceCtorEq, false_iff]
    intro h
    exact hv ⟨h.1, h.2.1⟩

theorem contains_eq_true_iff (a b : Rect) :
    a.contains b = .ok true ↔ a.Valid ∧ b.Valid ∧ a.Contained b := by
  unfold Rect.contains
  split
  · rename_i hv
    simp only [Except.ok.injEq, decide_eq_true_eq]
    exact ⟨fun h => ⟨hv.1, hv.2, h⟩, fun h => h.2.2⟩
  · rename_i hv
    simp only [reduceCtorEq, false_iff]
    intro h
    exact hv ⟨h.1, h.2.1⟩

theorem placeAfter_ok {axis : Axis} {a : Rect} {gap : Int} {s : Size} {p : Rect}
    (h : a.placeAfter axis gap s = .ok p) :
    a.Valid ∧ 0 ≤ gap ∧ s.Valid ∧ p = a.placeAfterRaw axis gap s ∧ p.Valid := by
  unfold Rect.placeAfter at h
  split at h
  · rename_i hv
    split at h
    · rename_i hp
      have he : a.placeAfterRaw axis gap s = p := Except.ok.inj h
      exact ⟨hv.1, hv.2.1, hv.2.2, he.symm, he ▸ hp⟩
    · simp at h
  · simp at h

/-- The bounding-box fold from an accumulator. -/
def bboxAux (acc : Rect) : List Rect → Except LayoutError Rect
  | [] => .ok acc
  | r :: rs =>
    match acc.union r with
    | .ok a' => bboxAux a' rs
    | .error e => .error e

/-- The bounding box of a non-empty list of rectangles. -/
def bbox : List Rect → Except LayoutError Rect
  | [] => .error .domain
  | r :: rs => bboxAux r rs

theorem bboxAux_contains (acc : Rect) (rs : List Rect) (b : Rect)
    (hacc : acc.Valid) (hrs : ∀ r ∈ rs, r.Valid)
    (h : bboxAux acc rs = .ok b) :
    b.Valid ∧ b.Contained acc ∧ ∀ r ∈ rs, b.Contained r := by
  induction rs generalizing acc b with
  | nil =>
    simp only [bboxAux, Except.ok.injEq] at h
    subst h
    exact ⟨hacc, Rect.Contained.refl acc, by simp⟩
  | cons x xs ih =>
    have hx : x.Valid := hrs x (by simp)
    have hxs : ∀ r ∈ xs, r.Valid := fun r hr => hrs r (by simp [hr])
    unfold bboxAux at h
    cases hux : acc.union x with
    | ok a' =>
      rw [hux] at h
      obtain ⟨_, _, ha'v, hacc', ha'x⟩ := Rect.union_ok hux
      obtain ⟨hbv, hbacc, hbx⟩ := ih a' b ha'v hxs h
      refine ⟨hbv, hbacc.trans hacc', ?_⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hbacc.trans ha'x
      · exact hbx r hr
    | error e => rw [hux] at h; simp at h

/-- The bounding box of a list of rectangles contains every list member. -/
theorem bbox_contains {rs : List Rect} {b : Rect} (h : Rect.bbox rs = .ok b)
    (hv : ∀ r ∈ rs, r.Valid) : ∀ r ∈ rs, b.contains r = .ok true := by
  cases rs with
  | nil => simp [Rect.bbox] at h
  | cons x xs =>
    simp only [Rect.bbox] at h
    obtain ⟨hbvalid, hbacc, hcont⟩ :=
      Rect.bboxAux_contains x xs b (hv x (by simp)) (fun r hr => hv r (by simp [hr])) h
    intro r hr
    rw [Rect.contains_eq_true_iff]
    refine ⟨hbvalid, hv r hr, ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact hbacc
    · exact hcont r hr'

/-- Transitivity of containment, stated on the checked operation. -/
theorem contains_trans {a b c : Rect} (hab : a.contains b = .ok true)
    (hbc : b.contains c = .ok true) : a.contains c = .ok true := by
  rw [Rect.contains_eq_true_iff] at *
  exact ⟨hab.1, hbc.2.1, hab.2.2.trans hbc.2.2⟩

/-- Translation preserves containment. -/
theorem contains_translate {a b a' b' : Rect} {dx dy : Int}
    (ha : a.translate dx dy = .ok a') (hb : b.translate dx dy = .ok b') :
    a.contains b = a'.contains b' := by
  obtain ⟨hav, hae, ha'v⟩ := Rect.translate_ok ha
  obtain ⟨hbv, hbe, hb'v⟩ := Rect.translate_ok hb
  subst hae hbe
  unfold Rect.contains
  rw [ite_eq_left (show a.Valid ∧ b.Valid from ⟨hav, hbv⟩),
      ite_eq_left (show (a.translateRaw dx dy).Valid ∧ (b.translateRaw dx dy).Valid
        from ⟨ha'v, hb'v⟩),
      Except.ok.injEq]
  apply decide_eq_of_iff
  unfold Rect.Contained Rect.translateRaw
  simp only
  omega

/-- The largest `m ≥ 0` with `m * m ≤ n`. -/
def isqrt (n : Int) : Except LayoutError Int :=
  if 0 ≤ n then .ok (Int.ofNat n.toNat.sqrt) else .error .domain

theorem isqrt_spec {n m : Int} (h : isqrt n = .ok m) : 0 ≤ m ∧ m * m ≤ n := by
  unfold Rect.isqrt at h
  split at h
  · rename_i hn
    have hm : m = Int.ofNat n.toNat.sqrt := (Except.ok.inj h).symm
    subst hm
    refine ⟨Int.natCast_nonneg _, ?_⟩
    have h' : ((n.toNat.sqrt * n.toNat.sqrt : Nat) : Int) ≤ ((n.toNat : Nat) : Int) :=
      Int.ofNat_le.mpr (Nat.sqrt_le n.toNat)
    have hmul : ((Int.ofNat n.toNat.sqrt) : Int) * (Int.ofNat n.toNat.sqrt)
        = ((n.toNat.sqrt * n.toNat.sqrt : Nat) : Int) := by
      push_cast
      rfl
    have hnat : ((n.toNat : Nat) : Int) = n := by omega
    omega
  · simp at h

end Rect

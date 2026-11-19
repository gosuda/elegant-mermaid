import ElegantGeometry.Disjoint

/-! Polylines: orthogonality, and the exact separating-axis test for whether a
polyline meets the open interior of a rectangle.

The test is the one the plan fixes. A segment from `p` to `q` misses the open interior of
`r` exactly when one of these holds:

* `max p.x q.x <= r.x`, `min p.x q.x >= r.x + r.w`, `max p.y q.y <= r.y`, or
  `min p.y q.y >= r.y + r.h`;
* `p != q` and the segment's normal separates it from the rectangle: with
  `n = (p.y - q.y, q.x - p.x)` and `c = dot n p`, one has `c <= m` or `c >= M`, where `m`
  and `M` are the least and greatest `dot n k` over the four corners `k` of `r`.

For a one-point polyline only the four axis tests apply. -/

set_option autoImplicit false

namespace Polyline

/-- Every consecutive pair has equal `x` or equal `y`. Zero-point and one-point
polylines are orthogonal. -/
def isOrthogonal : List Point → Bool
  | [] => true
  | [_] => true
  | p :: q :: rest => (p.x = q.x || p.y = q.y) && isOrthogonal (q :: rest)

theorem isOrthogonal_cons (p q : Point) (rest : List Point) :
    isOrthogonal (p :: q :: rest) =
      ((p.x = q.x || p.y = q.y) && isOrthogonal (q :: rest)) := rfl

/-- The dot product of a normal `(nx, ny)` with a point. -/
def dot (nx ny : Int) (p : Point) : Int := nx * p.x + ny * p.y

/-- The four corner products of `r` under the normal `(nx, ny)`. -/
def cornerDots (nx ny : Int) (r : Rect) : List Int :=
  [dot nx ny ⟨r.x, r.y⟩, dot nx ny ⟨r.x + r.w, r.y⟩,
   dot nx ny ⟨r.x, r.y + r.h⟩, dot nx ny ⟨r.x + r.w, r.y + r.h⟩]

/-- The least corner product. -/
def minCorner (nx ny : Int) (r : Rect) : Int :=
  min (min (dot nx ny ⟨r.x, r.y⟩) (dot nx ny ⟨r.x + r.w, r.y⟩))
      (min (dot nx ny ⟨r.x, r.y + r.h⟩) (dot nx ny ⟨r.x + r.w, r.y + r.h⟩))

/-- The greatest corner product. -/
def maxCorner (nx ny : Int) (r : Rect) : Int :=
  max (max (dot nx ny ⟨r.x, r.y⟩) (dot nx ny ⟨r.x + r.w, r.y⟩))
      (max (dot nx ny ⟨r.x, r.y + r.h⟩) (dot nx ny ⟨r.x + r.w, r.y + r.h⟩))

/-- One closed segment misses the open interior of `r`. -/
abbrev segMisses (p q : Point) (r : Rect) : Prop :=
  max p.x q.x ≤ r.x ∨ min p.x q.x ≥ r.x + r.w ∨
    max p.y q.y ≤ r.y ∨ min p.y q.y ≥ r.y + r.h ∨
      (p ≠ q ∧
        (dot (p.y - q.y) (q.x - p.x) p ≤ minCorner (p.y - q.y) (q.x - p.x) r ∨
         dot (p.y - q.y) (q.x - p.x) p ≥ maxCorner (p.y - q.y) (q.x - p.x) r))

/-- One closed segment meets the open interior of `r`. -/
abbrev segHits (p q : Point) (r : Rect) : Prop := ¬ segMisses p q r

/-- Every consecutive pair of a polyline misses `r`. -/
def allSegsMiss : List Point → Rect → Prop
  | [], _ => True
  | [_], _ => True
  | p :: q :: rest, r => segMisses p q r ∧ allSegsMiss (q :: rest) r

/-- The polyline misses the open interior of `r`. A zero-area rectangle is never hit. -/
abbrev hitsRect (points : List Point) (r : Rect) : Prop :=
  0 < r.w ∧ 0 < r.h ∧ ¬ allSegsMiss points r

/-- `segMisses` is decidable, because every disjunct is an integer comparison. -/
instance decidableSegMisses (p q : Point) (r : Rect) : Decidable (segMisses p q r) := by
  unfold segMisses
  infer_instance

/-- The executable form of `segMisses`. -/
def segMissesB (p q : Point) (r : Rect) : Bool :=
  decide (max p.x q.x ≤ r.x ∨ min p.x q.x ≥ r.x + r.w ∨
    max p.y q.y ≤ r.y ∨ min p.y q.y ≥ r.y + r.h ∨
      (p ≠ q ∧
        (dot (p.y - q.y) (q.x - p.x) p ≤ minCorner (p.y - q.y) (q.x - p.x) r ∨
         dot (p.y - q.y) (q.x - p.x) p ≥ maxCorner (p.y - q.y) (q.x - p.x) r)))

theorem segMissesB_iff (p q : Point) (r : Rect) :
    segMissesB p q r = true ↔ segMisses p q r :=
  decide_eq_true_iff

/-- The executable form of `allSegsMiss`. -/
def allSegsMissB : List Point → Rect → Bool
  | [], _ => true
  | [_], _ => true
  | p :: q :: rest, r => segMissesB p q r && allSegsMissB (q :: rest) r

theorem allSegsMissB_iff : ∀ (points : List Point) (r : Rect),
    allSegsMissB points r = true ↔ allSegsMiss points r
  | [], _ => by simp [allSegsMissB, allSegsMiss]
  | [_], _ => by simp [allSegsMissB, allSegsMiss]
  | p :: q :: rest, r => by
    rw [allSegsMissB, Bool.and_eq_true, segMissesB_iff, allSegsMissB_iff (q :: rest) r]
    simp only [allSegsMiss]

/-- The executable form of `hitsRect`. -/
def hitsRectB (points : List Point) (r : Rect) : Bool :=
  decide (0 < r.w) && decide (0 < r.h) && !(allSegsMissB points r)
theorem hitsRectB_iff (points : List Point) (r : Rect) :
    hitsRectB points r = true ↔ hitsRect points r := by
  unfold hitsRectB hitsRect
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · intro ⟨⟨hw, hh⟩, hfalse⟩
    refine ⟨hw, hh, ?_⟩
    intro habs
    have : allSegsMissB points r = true := (allSegsMissB_iff points r).mpr habs
    rw [this] at hfalse
    exact Bool.noConfusion hfalse
  · intro ⟨hw, hh, hmiss⟩
    refine ⟨⟨hw, hh⟩, ?_⟩
    cases h : allSegsMissB points r with
    | false => rfl
    | true => exact absurd ((allSegsMissB_iff points r).mp h) hmiss

theorem hitsRectB_eq_false_iff (points : List Point) (r : Rect) :
    hitsRectB points r = false ↔ ¬ hitsRect points r := by
  constructor
  · intro h hh
    have hb := (hitsRectB_iff points r).mpr hh
    rw [h] at hb
    exact Bool.noConfusion hb
  · intro h
    cases hb : hitsRectB points r with
    | false => rfl
    | true => exact absurd ((hitsRectB_iff points r).mp hb) h

/-- A miss on the `x` axis means the segment's `x` projection stays clear of the open
interval. -/
theorem segMisses_of_x_le {p q : Point} {r : Rect} (h : max p.x q.x ≤ r.x) :
    segMisses p q r :=
  Or.inl h

theorem segMisses_of_y_le {p q : Point} {r : Rect} (h : max p.y q.y ≤ r.y) :
    segMisses p q r :=
  Or.inr (Or.inr (Or.inl h))

/-- A polyline whose segments all miss `r` hits nothing. -/
theorem not_hits_of_allMiss {points : List Point} {r : Rect}
    (h : allSegsMiss points r) : ¬ hitsRect points r := by
  unfold hitsRect
  intro hh
  exact hh.2.2 h

/-- The open interior of a zero-area rectangle is empty, so no polyline hits it. -/
theorem not_hits_of_zero {points : List Point} {r : Rect} (h : r.w ≤ 0 ∨ r.h ≤ 0) :
    ¬ hitsRect points r := by
  unfold hitsRect
  omega

end Polyline

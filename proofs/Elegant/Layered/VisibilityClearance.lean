import Std.Data.HashMap
import Elegant.Layered.VisibilityRoute
import ElegantGeometry.Route
import Elegant.Layered.RouteTransport
set_option autoImplicit false
namespace Elegant
namespace Layered
namespace Visibility
deriving instance ReflBEq for Vertex

deriving instance LawfulBEq for Vertex

deriving instance DecidableEq for Vertex

open Polyline

/-- If a segment is axis-aligned and `sideHits` rejects it against a positive-size rect,
it misses the open interior. -/
theorem segMisses_of_not_sideHits {a b : Point} {r : Rect}
    (haxis : a.x = b.x ∨ a.y = b.y)
    (hw : 0 < r.w) (hh : 0 < r.h)
    (h : sideHits a b r = false) :
    segMisses a b r := by
  unfold sideHits at h
  rw [ite_eq_right (by
    intro hc
    rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hc
    omega)] at h
  by_cases hy : a.y = b.y
  · rw [ite_eq_left (by rw [beq_iff_eq]; exact hy)] at h
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
    rcases h with ((h1 | h2) | h3) | h4 <;> omega
  · rw [ite_eq_right (by rw [beq_iff_eq]; exact hy)] at h
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
    rcases h with ((h1 | h2) | h3) | h4
    · refine Or.inl ?_
      rcases haxis with hx | hyy
      · omega
      · exact absurd hyy hy
    · refine Or.inr (Or.inl ?_)
      rcases haxis with hx | hyy
      · omega
      · exact absurd hyy hy
    · exact Or.inr (Or.inr (Or.inr (by omega)))
    · exact Or.inr (Or.inr (Or.inl (by omega)))

/-- A vertical segment at a shared `x` misses `r` once one of the four axis bounds holds. -/
theorem segMisses_vert {a b : Point} {r : Rect} (hx : a.x = b.x)
    (h : max a.y b.y ≤ r.y ∨ min a.y b.y ≥ r.y + r.h ∨ a.x ≤ r.x ∨ a.x ≥ r.x + r.w) :
    Polyline.segMisses a b r := by
  unfold Polyline.segMisses
  rcases h with h | h | h | h
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))

/-- A horizontal segment at a shared `y` misses `r` once one of the four axis bounds holds. -/
theorem segMisses_horiz {a b : Point} {r : Rect} (hy : a.y = b.y)
    (h : max a.x b.x ≤ r.x ∨ min a.x b.x ≥ r.x + r.w ∨ a.y ≤ r.y ∨ a.y ≥ r.y + r.h) :
    Polyline.segMisses a b r := by
  unfold Polyline.segMisses
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))

theorem minCorner_vert_normal (nx : Int) (r : Rect) :
    Polyline.minCorner nx 0 r = min (nx * r.x) (nx * (r.x + r.w)) := by
  unfold Polyline.minCorner Polyline.dot
  simp only [Int.zero_mul, Int.add_zero]
  exact Int.min_self _

theorem maxCorner_vert_normal (nx : Int) (r : Rect) :
    Polyline.maxCorner nx 0 r = max (nx * r.x) (nx * (r.x + r.w)) := by
  unfold Polyline.maxCorner Polyline.dot
  simp only [Int.zero_mul, Int.add_zero]
  exact Int.max_self _

theorem minCorner_horiz_normal (ny : Int) (r : Rect) :
    Polyline.minCorner 0 ny r = min (ny * r.y) (ny * (r.y + r.h)) := by
  unfold Polyline.minCorner Polyline.dot
  simp only [Int.zero_mul, Int.zero_add, Int.min_self]

theorem maxCorner_horiz_normal (ny : Int) (r : Rect) :
    Polyline.maxCorner 0 ny r = max (ny * r.y) (ny * (r.y + r.h)) := by
  unfold Polyline.maxCorner Polyline.dot
  simp only [Int.zero_mul, Int.zero_add, Int.max_self]

/-- Positive multiplier cancels an `Int` product inequality. -/
theorem le_of_mul_le_mul_pos {k x y : Int} (hk : 0 < k) (h : k * x ≤ k * y) : x ≤ y :=
  Int.le_of_not_gt fun hlt =>
    absurd (Int.mul_lt_mul_of_pos_left hlt hk) (Int.not_lt.mpr h)

/-- Negative multiplier reverses an `Int` product inequality. -/
theorem le_of_mul_le_mul_neg {k x y : Int} (hk : k < 0) (h : k * x ≤ k * y) : y ≤ x := by
  have hk' : 0 < -k := by omega
  have h2 : (-k) * y ≤ (-k) * x := by
    rw [Int.neg_mul, Int.neg_mul]
    omega
  exact le_of_mul_le_mul_pos hk' h2

/-- The five-way miss disjunction for a vertical segment reduces to the four axis bounds:
under a positive-size rectangle the separating-normal disjunct is one of the axis bounds. -/
theorem vertBound_of_segMisses {a b : Point} {r : Rect}
    (hx : a.x = b.x) (h : Polyline.segMisses a b r) :
    max a.y b.y ≤ r.y ∨ min a.y b.y ≥ r.y + r.h ∨ a.x ≤ r.x ∨ a.x ≥ r.x + r.w := by
  unfold Polyline.segMisses at h
  rcases h with h1 | h2 | h3 | h4 | ⟨hne, h5⟩
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))
  · exact Or.inl h3
  · exact Or.inr (Or.inl h4)
  · have hny : b.x - a.x = 0 := by omega
    have hd : Polyline.dot (a.y - b.y) (b.x - a.x) a = (a.y - b.y) * a.x := by
      rw [hny]
      unfold Polyline.dot
      rw [Int.zero_mul, Int.add_zero]
    rw [hd, hny, minCorner_vert_normal, maxCorner_vert_normal] at h5
    have hne0 : a.y - b.y ≠ 0 := by
      intro hz
      exact hne ((point_ext_iff a b).mpr ⟨hx, by omega⟩)
    rcases h5 with h5 | h5
    · have hB : (a.y - b.y) * a.x ≤ (a.y - b.y) * (r.x + r.w) :=
        Int.le_trans h5 (Int.min_le_right _ _)
      have hA : (a.y - b.y) * a.x ≤ (a.y - b.y) * r.x :=
        Int.le_trans h5 (Int.min_le_left _ _)
      rcases Int.lt_trichotomy (a.y - b.y) 0 with hlt | heq | hgt
      · exact Or.inr (Or.inr (Or.inr (by have := le_of_mul_le_mul_neg hlt hB; omega)))
      · exact absurd heq hne0
      · exact Or.inr (Or.inr (Or.inl (le_of_mul_le_mul_pos hgt hA)))
    · have hA : (a.y - b.y) * r.x ≤ (a.y - b.y) * a.x :=
        Int.le_trans (Int.le_max_left _ _) h5
      have hB : (a.y - b.y) * (r.x + r.w) ≤ (a.y - b.y) * a.x :=
        Int.le_trans (Int.le_max_right _ _) h5
      rcases Int.lt_trichotomy (a.y - b.y) 0 with hlt | heq | hgt
      · exact Or.inr (Or.inr (Or.inl (by have := le_of_mul_le_mul_neg hlt hA; omega)))
      · exact absurd heq hne0
      · exact Or.inr (Or.inr (Or.inr (le_of_mul_le_mul_pos hgt hB)))

/-- The five-way miss disjunction for a horizontal segment reduces to the four axis bounds. -/
theorem horizBound_of_segMisses {a b : Point} {r : Rect}
    (hy : a.y = b.y) (h : Polyline.segMisses a b r) :
    max a.x b.x ≤ r.x ∨ min a.x b.x ≥ r.x + r.w ∨ a.y ≤ r.y ∨ a.y ≥ r.y + r.h := by
  unfold Polyline.segMisses at h
  rcases h with h1 | h2 | h3 | h4 | ⟨hne, h5⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))
  · have hnx : a.y - b.y = 0 := by omega
    have hd : Polyline.dot (a.y - b.y) (b.x - a.x) a = (b.x - a.x) * a.y := by
      rw [hnx]
      unfold Polyline.dot
      rw [Int.zero_mul, Int.zero_add]
    rw [hd, hnx, minCorner_horiz_normal, maxCorner_horiz_normal] at h5
    have hne0 : b.x - a.x ≠ 0 := by
      intro hz
      exact hne ((point_ext_iff a b).mpr ⟨by omega, hy⟩)
    rcases h5 with h5 | h5
    · have hB : (b.x - a.x) * a.y ≤ (b.x - a.x) * (r.y + r.h) :=
        Int.le_trans h5 (Int.min_le_right _ _)
      have hA : (b.x - a.x) * a.y ≤ (b.x - a.x) * r.y :=
        Int.le_trans h5 (Int.min_le_left _ _)
      rcases Int.lt_trichotomy (b.x - a.x) 0 with hlt | heq | hgt
      · exact Or.inr (Or.inr (Or.inr (by have := le_of_mul_le_mul_neg hlt hB; omega)))
      · exact absurd heq hne0
      · exact Or.inr (Or.inr (Or.inl (le_of_mul_le_mul_pos hgt hA)))
    · have hA : (b.x - a.x) * r.y ≤ (b.x - a.x) * a.y :=
        Int.le_trans (Int.le_max_left _ _) h5
      have hB : (b.x - a.x) * (r.y + r.h) ≤ (b.x - a.x) * a.y :=
        Int.le_trans (Int.le_max_right _ _) h5
      rcases Int.lt_trichotomy (b.x - a.x) 0 with hlt | heq | hgt
      · exact Or.inr (Or.inr (Or.inl (by have := le_of_mul_le_mul_neg hlt hA; omega)))
      · exact absurd heq hne0
      · exact Or.inr (Or.inr (Or.inr (le_of_mul_le_mul_pos hgt hB)))

/-- Dropping the middle point of a collinear triple keeps the merged segment clear of `r`. -/
theorem segMisses_merge {b c p : Point} {r : Rect} (hpos : 0 < r.w ∧ 0 < r.h)
    (hcol : collinear b c p = true)
    (h1 : Polyline.segMisses c b r) (h2 : Polyline.segMisses p c r) :
    Polyline.segMisses p b r := by
  unfold collinear at hcol
  rw [Bool.or_eq_true] at hcol
  rcases hcol with hx | hy
  · rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hx
    obtain ⟨hbc, hcp⟩ := hx
    have hpb : p.x = b.x := by omega
    have hcb := vertBound_of_segMisses (by omega : c.x = b.x) h1
    have hpc := vertBound_of_segMisses (by omega : p.x = c.x) h2
    rcases hcb with h | h | h | h <;> rcases hpc with h' | h' | h' | h' <;>
      exact segMisses_vert hpb (by omega)
  · rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hy
    obtain ⟨hbc, hcp⟩ := hy
    have hpb : p.y = b.y := by omega
    have hcb := horizBound_of_segMisses (by omega : c.y = b.y) h1
    have hpc := horizBound_of_segMisses (by omega : p.y = c.y) h2
    rcases hcb with h | h | h | h <;> rcases hpc with h' | h' | h' | h' <;>
      exact segMisses_horiz hpb (by omega)

/-- The normal of a segment is unchanged (up to sign) when the endpoints swap. -/
theorem dot_neg (nx ny : Int) (p : Point) :
    Polyline.dot (-nx) (-ny) p = - Polyline.dot nx ny p := by
  unfold Polyline.dot; grind

/-- The normal dot product is the same evaluated at either endpoint. -/
theorem dot_same (p q : Point) :
    Polyline.dot (p.y - q.y) (q.x - p.x) p = Polyline.dot (p.y - q.y) (q.x - p.x) q := by
  unfold Polyline.dot; grind

/-- Nested min of negated values is the negated nested max. -/
theorem min4_neg (a b c d : Int) :
    min (min (-a) (-b)) (min (-c) (-d)) = - max (max a b) (max c d) := by
  omega

/-- Nested max of negated values is the negated nested min. -/
theorem max4_neg (a b c d : Int) :
    max (max (-a) (-b)) (max (-c) (-d)) = - min (min a b) (min c d) := by
  omega

/-- Corner minimum under a negated normal is the negated corner maximum. -/
theorem minCorner_neg (nx ny : Int) (r : Rect) :
    Polyline.minCorner (-nx) (-ny) r = - Polyline.maxCorner nx ny r := by
  unfold Polyline.minCorner Polyline.maxCorner
  simp only [dot_neg]
  exact min4_neg _ _ _ _

/-- Corner maximum under a negated normal is the negated corner minimum. -/
theorem maxCorner_neg (nx ny : Int) (r : Rect) :
    Polyline.maxCorner (-nx) (-ny) r = - Polyline.minCorner nx ny r := by
  unfold Polyline.minCorner Polyline.maxCorner
  simp only [dot_neg]
  exact max4_neg _ _ _ _

/-- `segMisses` is symmetric in its endpoints. -/
theorem segMisses_symm {p q : Point} {r : Rect} (h : Polyline.segMisses p q r) :
    Polyline.segMisses q p r := by
  unfold Polyline.segMisses at h ⊢
  rcases h with h1 | h2 | h3 | h4 | ⟨hne, hd⟩
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))
  · rw [show q.y - p.y = -(p.y - q.y) from by omega,
        show p.x - q.x = -(q.x - p.x) from by omega]
    simp only [dot_neg, minCorner_neg, maxCorner_neg]
    rw [← dot_same p q]
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨fun h' => hne h'.symm, ?_⟩)))
    rcases hd with h1 | h2
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)

/-- A cleared axis-aligned pair misses every positive-size obstacle. -/
theorem segMisses_of_clear {g : Grid} {a b : Point} {r : Rect}
    (hclear : g.clear a b = true)
    (haxis : a.x = b.x ∨ a.y = b.y)
    (hr : r ∈ g.obstacles) (hw : 0 < r.w) (hh : 0 < r.h) :
    Polyline.segMisses a b r := by
  unfold Grid.clear at hclear
  rw [Bool.and_eq_true] at hclear
  obtain ⟨_, hno⟩ := hclear
  apply segMisses_of_not_sideHits haxis hw hh
  have hfalse : g.obstacles.any (sideHits a b) = false := by
    simpa using hno
  have hall := List.any_eq_false.mp hfalse
  exact Bool.of_not_eq_true (hall r hr)

/-- Neighbour vertices differ in exactly one grid index, so their points share `x` or `y`. -/
theorem neighbour_axis {g : Grid} {v w : Vertex}
    (h : w ∈ g.neighbours v) :
    (g.point v).x = (g.point w).x ∨ (g.point v).y = (g.point w).y := by
  unfold Grid.neighbours at h
  simp only [List.mem_append, or_assoc] at h
  rcases h with h | h | h | h
  · by_cases hc : 0 < v.x
    · rw [ite_eq_left hc] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl
      exact Or.inr rfl
    · rw [ite_eq_right hc] at h
      simp at h
  · by_cases hc : v.x + 1 < g.xs.size
    · rw [ite_eq_left hc] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl
      exact Or.inr rfl
    · rw [ite_eq_right hc] at h
      simp at h
  · by_cases hc : 0 < v.y
    · rw [ite_eq_left hc] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl
      exact Or.inl rfl
    · rw [ite_eq_right hc] at h
      simp at h
  · by_cases hc : v.y + 1 < g.ys.size
    · rw [ite_eq_left hc] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl
      exact Or.inl rfl
    · rw [ite_eq_right hc] at h
      simp at h

/-- `collinear` is symmetric under swapping the outer arguments. -/
theorem collinear_symm {a b c : Point} (h : collinear a b c = true) :
    collinear c b a = true := by
  unfold collinear at h ⊢
  rw [Bool.or_eq_true] at h ⊢
  rcases h with hx | hy
  · rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hx
    obtain ⟨h1, h2⟩ := hx
    apply Or.inl
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
    exact ⟨h2.symm, h1.symm⟩
  · rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hy
    obtain ⟨h1, h2⟩ := hy
    apply Or.inr
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
    exact ⟨h2.symm, h1.symm⟩

/-- The fold step of `compress`, named for reasoning. -/
def compressStep (acc : List Point) (p : Point) : List Point :=
  match acc with
  | c :: b :: rest => if collinear b c p then p :: b :: rest else p :: acc
  | _ => p :: acc
/-- `compress` is a fold of `compressStep`. -/
theorem compress_eq_foldl (pts : List Point) :
    compress pts = (List.foldl compressStep [] pts).reverse := rfl

/-- Removing the middle point `c` of a collinear triple keeps `allSegsMiss`. -/
theorem allSegsMiss_remove_mid {xs ys : List Point} {b c p : Point} {r : Rect}
    (h : Polyline.allSegsMiss (xs ++ b :: c :: p :: ys) r)
    (hm : Polyline.segMisses b p r) :
    Polyline.allSegsMiss (xs ++ b :: p :: ys) r := by
  revert h
  induction xs with
  | nil =>
      intro h
      simp only [List.nil_append] at h ⊢
      obtain ⟨_, hrest⟩ := h
      exact ⟨hm, hrest.2⟩
  | cons x xs' ih =>
      intro h
      cases xs' with
      | nil =>
          simp only [List.cons_append, List.nil_append] at h ⊢
          obtain ⟨hxb, hrest⟩ := h
          exact ⟨hxb, ih hrest⟩
      | cons x' xs'' =>
          simp only [List.cons_append] at h ⊢
          obtain ⟨hxx', hrest⟩ := h
          exact ⟨hxx', ih hrest⟩

/-- The two segments adjacent to a removed middle point are extractable. -/
theorem allSegsMiss_mid {xs ys : List Point} {b c p : Point} {r : Rect}
    (h : Polyline.allSegsMiss (xs ++ b :: c :: p :: ys) r) :
    Polyline.segMisses b c r ∧ Polyline.segMisses c p r := by
  revert h
  induction xs with
  | nil =>
      intro h
      simp only [List.nil_append] at h
      exact ⟨h.1, h.2.1⟩
  | cons x xs' ih =>
      intro h
      cases xs' with
      | nil =>
          simp only [List.cons_append, List.nil_append] at h
          obtain ⟨_, hrest⟩ := h
          exact ih hrest
      | cons x' xs'' =>
          simp only [List.cons_append] at h
          obtain ⟨_, hrest⟩ := h
          exact ih hrest

/-- One `compressStep` preserves the all-miss invariant on the reversed accumulator
concatenated with the remaining input. -/
theorem compressStep_miss {acc pts : List Point} {p : Point} {r : Rect}
    (hpos : 0 < r.w ∧ 0 < r.h)
    (hP : Polyline.allSegsMiss (acc.reverse ++ p :: pts) r) :
    Polyline.allSegsMiss ((compressStep acc p).reverse ++ pts) r := by
  cases acc with
  | nil =>
      simp only [compressStep]
      simpa using hP
  | cons a acc' =>
      cases acc' with
      | nil =>
          simp only [compressStep]
          simpa using hP
      | cons b rest =>
          simp only [compressStep]
          by_cases hc : collinear b a p = true
          · rw [ite_eq_left hc]
            have hnorm : Polyline.allSegsMiss
                (rest.reverse ++ b :: a :: p :: pts) r := by
              simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
                List.nil_append] using hP
            have hmid := allSegsMiss_mid hnorm
            have hmerged : Polyline.segMisses b p r := by
              have hcol : collinear p a b = true := collinear_symm hc
              exact segMisses_merge hpos hcol hmid.2 hmid.1
            have hres := allSegsMiss_remove_mid hnorm hmerged
            simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
              List.nil_append] using hres
          · rw [ite_eq_right hc]
            have hnorm : Polyline.allSegsMiss
                (rest.reverse ++ b :: a :: p :: pts) r := by
              simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
                List.nil_append] using hP
            simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
              List.nil_append] using hnorm

/-- `compress` preserves the all-segments-miss property for positive-size rectangles. -/
theorem compress_allSegsMiss {pts : List Point} {r : Rect}
    (hpos : 0 < r.w ∧ 0 < r.h)
    (h : Polyline.allSegsMiss pts r) :
    Polyline.allSegsMiss (compress pts) r := by
  rw [compress_eq_foldl]
  suffices key : ∀ (acc pts : List Point),
      Polyline.allSegsMiss (acc.reverse ++ pts) r →
      Polyline.allSegsMiss ((List.foldl compressStep acc pts).reverse) r by
    have := key [] pts (by simpa using h)
    simpa using this
  intro acc pts hP
  induction pts generalizing acc with
  | nil =>
      show Polyline.allSegsMiss acc.reverse r
      simpa using hP
  | cons p pts ih =>
      rw [List.foldl_cons]
      exact ih _ (compressStep_miss hpos hP)

/-- Neighbour-step segments are axis-aligned, so a cleared step misses obstacles. -/
theorem step_segMisses {g : Grid} {entry : Entry} {next : Vertex} {r : Rect}
    (hnext : next ∈ g.neighbours entry.vertex)
    (hclear : g.clear (g.point entry.vertex) (g.point next) = true)
    (hr : r ∈ g.obstacles) (hw : 0 < r.w) (hh : 0 < r.h) :
    Polyline.segMisses (g.point entry.vertex) (g.point next) r :=
  segMisses_of_clear hclear (neighbour_axis hnext) hr hw hh

/-- The `prev`-edge property, bundled for reuse. -/
def PrevOK (g : Grid) (s : Search) : Prop :=
  ∀ v w, s.prev[v]? = some w →
    g.clear (g.point w) (g.point v) = true ∧
    ((g.point w).x = (g.point v).x ∨ (g.point w).y = (g.point v).y)

/-- The fold step of `Grid.relax`, named for reasoning. -/
def relaxStep (g : Grid) (entry : Entry) (s : Search) (next : Vertex) : Search :=
  if !g.clear (g.point entry.vertex) (g.point next) then s
  else
    let candidate := g.step entry.vertex next entry.cost
    let better := match s.dist[next]? with
      | some old => candidate.lt old
      | none => true
    if better then
      { frontier := s.frontier.push ⟨candidate, next⟩
        dist := s.dist.insert next candidate
        prev := s.prev.insert next entry.vertex }
    else s

/-- A single `relaxStep` preserves `PrevOK`. -/
theorem relax_step_prev (g : Grid) (entry : Entry) (s : Search) (next : Vertex)
    (h : PrevOK g s) (hnext : next ∈ g.neighbours entry.vertex) :
    PrevOK g (relaxStep g entry s next) := by
  intro v w hvw
  by_cases hc : g.clear (g.point entry.vertex) (g.point next) = true
  · have key : (relaxStep g entry s next).prev = s.prev ∨
        (relaxStep g entry s next).prev = s.prev.insert next entry.vertex := by
      unfold relaxStep
      simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hd : s.dist[next]? with
      | none => exact Or.inr rfl
      | some old =>
        by_cases hb : (g.step entry.vertex next entry.cost).lt old = true
        · simp only [hb, ↓reduceIte]
          exact Or.inr trivial
        · simp only [hb, Bool.false_eq_true, ↓reduceIte]
          exact Or.inl trivial
    rcases key with hk | hk
    · rw [hk] at hvw
      exact h v w hvw
    · rw [hk, Std.HashMap.getElem?_insert] at hvw
      split at hvw
      · rename_i heq
        injection hvw with hw
        subst hw
        have hv : v = next := (beq_iff_eq.mp heq).symm
        subst hv
        exact ⟨hc, neighbour_axis hnext⟩
      · exact h v w hvw
  · have key : (relaxStep g entry s next).prev = s.prev := by
      unfold relaxStep
      have hc' : g.clear (g.point entry.vertex) (g.point next) = false := by
        simpa using hc
      simp only [hc', Bool.not_false, ↓reduceIte]
    rw [key] at hvw
    exact h v w hvw

/-- Folding `relaxStep` over a neighbour list preserves `PrevOK`. -/
theorem foldl_prev (g : Grid) (entry : Entry) :
    ∀ (ns : List Vertex) (s : Search), PrevOK g s →
      (∀ next, next ∈ ns → next ∈ g.neighbours entry.vertex) →
      PrevOK g (ns.foldl (relaxStep g entry) s) := by
  intro ns
  induction ns with
  | nil =>
      intro s h _
      exact h
  | cons next ns' ih =>
      intro s h hmem
      rw [List.foldl_cons]
      apply ih
      · exact relax_step_prev g entry s next h
          (hmem next List.mem_cons_self)
      · intro x hx
        exact hmem x (List.mem_cons.mpr (Or.inr hx))

/-- `Grid.relax` preserves `PrevOK`. -/
theorem relax_prev (g : Grid) (entry : Entry) (s : Search) (h : PrevOK g s) :
    PrevOK g (g.relax entry s) := by
  show PrevOK g ((g.neighbours entry.vertex).foldl (relaxStep g entry) s)
  exact foldl_prev g entry _ s h (fun next hn => hn)

/-- Every `prev` edge in the search result was written by a cleared neighbour step. -/
theorem run_prev (g : Grid) (ends : List Point) :
    ∀ fuel s, PrevOK g s → ∀ last s', g.run ends fuel s = some (last, s') → PrevOK g s' := by
  intro fuel
  induction fuel with
  | zero =>
      intro s _ last s' hr
      simp [Grid.run] at hr
  | succ f ih =>
      intro s h last s' hr
      unfold Grid.run at hr
      split at hr
      · simp at hr
      · rename_i entry rest _
        have hs : PrevOK g ({ s with frontier := rest } : Search) := fun v w hvw => h v w hvw
        dsimp only at hr
        split at hr
        · exact ih _ hs last s' hr
        · rename_i current _
          split at hr
          · exact ih _ hs last s' hr
          · split at hr
            · simp only [Option.some.injEq, Prod.mk.injEq] at hr
              rw [← hr.2]
              exact hs
            · exact ih _ (relax_prev g entry _ hs) last s' hr

/-- The reconstructed chain misses `r` on every segment, given `prev` edges miss. -/
theorem chain_allSegsMiss {g : Grid} {prev : Std.HashMap Vertex Vertex} {r : Rect}
    (hseg : ∀ v w, prev[v]? = some w →
      Polyline.segMisses (g.point w) (g.point v) r) :
    ∀ fuel v acc,
      Polyline.allSegsMiss acc r →
      (∀ a, acc.head? = some a → Polyline.segMisses (g.point v) a r) →
      Polyline.allSegsMiss (g.chain prev fuel v acc) r := by
  intro fuel
  induction fuel with
  | zero =>
      intro v acc hacc hhead
      show Polyline.allSegsMiss (g.point v :: acc) r
      cases acc with
      | nil => trivial
      | cons a t =>
          show Polyline.segMisses (g.point v) a r ∧ Polyline.allSegsMiss (a :: t) r
          refine ⟨?_, hacc⟩
          exact hhead a (by simp)
  | succ f ih =>
      intro v acc hacc hhead
      show Polyline.allSegsMiss
        (match prev[v]? with
         | none => g.point v :: acc
         | some p => g.chain prev f p (g.point v :: acc)) r
      cases hv : prev[v]? with
      | none =>
          show Polyline.allSegsMiss (g.point v :: acc) r
          cases acc with
          | nil => trivial
          | cons a t =>
              show Polyline.segMisses (g.point v) a r ∧ Polyline.allSegsMiss (a :: t) r
              refine ⟨?_, hacc⟩
              exact hhead a (by simp)
      | some p =>
          show Polyline.allSegsMiss (g.chain prev f p (g.point v :: acc)) r
          apply ih
          · cases acc with
            | nil => trivial
            | cons a t =>
                show Polyline.segMisses (g.point v) a r ∧ Polyline.allSegsMiss (a :: t) r
                refine ⟨?_, hacc⟩
                exact hhead a (by simp)
          · intro a ha
            simp at ha
            subst a
            exact hseg v p hv

/-- `seed` never writes `prev` links: the fold only updates `frontier` and `dist`, so every
seeded search has an empty `prev` map. -/
theorem seed_prev_empty {g : Grid} {starts : List Point} {s : Search}
    (h : g.seed starts = some s) : s.prev = {} := by
  unfold Grid.seed at h
  have hstep : ∀ (st : Search) (p : Point) (r : Search),
      (if !g.inside p then some st
       else (g.vertexAt p).map fun v =>
         { st with frontier := st.frontier.push ⟨⟨0, 0⟩, v⟩,
                   dist := st.dist.insert v ⟨0, 0⟩ }) = some r →
      r.prev = st.prev := by
    intro st p r hF
    split at hF
    · rename_i _
      injection hF with h
      subst r
      rfl
    · rw [Option.map_eq_some_iff] at hF
      obtain ⟨_, _, hr⟩ := hF
      rw [← hr]
  suffices aux : ∀ (l : List Point) (acc s' : Search),
      List.foldlM
          (fun (st : Search) (p : Point) =>
            if !g.inside p then some st
            else (g.vertexAt p).map fun v =>
              { st with frontier := st.frontier.push ⟨⟨0, 0⟩, v⟩,
                        dist := st.dist.insert v ⟨0, 0⟩ })
        acc l = some s' →
      acc.prev = {} → s'.prev = {} by
    exact aux starts ⟨#[], {}, {}⟩ s h rfl
  intro l
  induction l with
  | nil =>
      intro acc s' h hp
      rw [List.foldlM_nil] at h
      have h' : (some acc : Option Search) = some s' := h
      injection h' with h'
      subst s'
      exact hp
  | cons p l ih =>
      intro acc s' h hp
      rw [List.foldlM_cons] at h
      obtain ⟨acc', hF, h2⟩ := Option.bind_eq_some_iff.mp h
      have h2' : List.foldlM
          (fun st p =>
            if !g.inside p then some st
            else (g.vertexAt p).map fun v =>
              { st with frontier := st.frontier.push ⟨⟨0, 0⟩, v⟩,
                        dist := st.dist.insert v ⟨0, 0⟩ })
          acc' l = some s' := h2
      have hprev' : acc'.prev = {} := (hstep acc p acc' hF).trans hp
      exact ih acc' s' h2' hprev'

/-- The shortest path misses every positive-size obstacle it was routed around. -/
theorem shortest_misses_obstacles {g : Grid} {starts ends : List Point}
    {pts : List Point} {rect : Rect}
    (h : g.shortest starts ends = some pts)
    (hr : rect ∈ g.obstacles) (hw : 0 < rect.w) (hh : 0 < rect.h) :
    ¬ Polyline.hitsRect pts rect := by
  unfold Grid.shortest at h
  obtain ⟨seeded, hseed, hrest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨last, s⟩, hrun, hG⟩ := Option.bind_eq_some_iff.mp hrest
  have hpts : compress (g.chain s.prev (s.prev.size + 1) last []) = pts :=
    Option.some.inj hG
  have hprev0 : PrevOK g seeded := by
    intro v w hvw
    rw [seed_prev_empty hseed] at hvw
    simp at hvw
  have hprev : PrevOK g s := run_prev g ends _ seeded hprev0 last s hrun
  have hseg : ∀ v w, s.prev[v]? = some w →
      Polyline.segMisses (g.point w) (g.point v) rect := by
    intro v w hvw
    obtain ⟨hclear, haxis⟩ := hprev v w hvw
    exact segMisses_of_clear hclear haxis hr hw hh
  have hchain := chain_allSegsMiss (g := g) (prev := s.prev) (r := rect) hseg
    (s.prev.size + 1) last []
  have hall := compress_allSegsMiss ⟨hw, hh⟩
    (hchain (by simp [Polyline.allSegsMiss]) (fun a ha => by simp at ha))
  rw [hpts] at hall
  exact Polyline.not_hits_of_allMiss hall
end Visibility
end Layered
end Elegant

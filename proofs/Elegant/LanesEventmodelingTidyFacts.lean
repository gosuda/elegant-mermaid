import Elegant.Lanes
import Elegant.GridSimplify

set_option autoImplicit false

namespace Elegant.Lanes.Eventmodeling

open Elegant.Grid

theorem straightThrough_axis {a b p : Point}
    (hab : Aligned a b) (hbp : Aligned b p)
    (h : straightThrough a b p = true) :
    Elegant.Grid.collinear a b p = true := by
  rw [Elegant.Grid.collinear_iff]
  have hc : (b.x - a.x) * (p.y - b.y) -
      (b.y - a.y) * (p.x - b.x) = 0 := by
    have hs := h
    simp only [straightThrough, Bool.and_eq_true, beq_iff_eq] at hs
    exact hs.1
  rcases hab with hx | hy <;> rcases hbp with hx' | hy'
  · exact Or.inl ⟨hx, hx'⟩
  · have hz : (b.y - a.y) * (p.x - b.x) = 0 := by
      simp only [hx, Int.sub_self, Int.zero_mul, Int.zero_sub] at hc
      omega
    rcases Int.mul_eq_zero.mp hz with hz | hz
    · right; omega
    · left; omega
  · have hz : (b.x - a.x) * (p.y - b.y) = 0 := by
      simpa only [hy, Int.sub_self, Int.zero_mul, Int.sub_zero] using hc
    rcases Int.mul_eq_zero.mp hz with hz | hz
    · left; omega
    · right; omega
  · exact Or.inr ⟨hy, hy'⟩

private theorem product_inside {d x l u : Int} (hd : d ≠ 0)
    (hl : l < x) (hu : x < u) :
    min (d * l) (d * u) < d * x ∧ d * x < max (d * l) (d * u) := by
  by_cases hp : 0 < d
  · have h₁ := (Int.mul_lt_mul_left hp).mpr hl
    have h₂ := (Int.mul_lt_mul_left hp).mpr hu
    omega
  · have hn : d < 0 := by omega
    have h₁ := (Int.mul_lt_mul_left_of_neg hn).mpr hl
    have h₂ := (Int.mul_lt_mul_left_of_neg hn).mpr hu
    omega

theorem aligned_segMisses_axis {a b : Point} {box : Rect}
    (ha : Aligned a b) (hm : Polyline.segMisses a b box) : AxMiss box a b := by
  apply Classical.byContradiction
  intro hn
  unfold AxMiss at hn
  have bounds : box.x < max a.x b.x ∧ min a.x b.x < box.x + box.w ∧
      box.y < max a.y b.y ∧ min a.y b.y < box.y + box.h := by omega
  rcases hm with h | h | h | h | ⟨hne, h | h⟩
  all_goals try omega
  all_goals
    rcases ha with hx | hy
    · have hd : a.y - b.y ≠ 0 := by
        intro he
        apply hne
        have he' : a.y = b.y := by omega
        cases a; cases b
        simp_all
      simp only [hx, Int.min_self, Int.max_self] at bounds
      have hi := product_inside hd bounds.1 bounds.2.1
      simp [Polyline.dot, Polyline.minCorner, Polyline.maxCorner, hx] at h
      omega
    · have hd : b.x - a.x ≠ 0 := by
        intro he
        apply hne
        have he' : a.x = b.x := by omega
        cases a; cases b
        simp_all
      simp only [hy, Int.min_self, Int.max_self] at bounds
      have hi := product_inside hd bounds.2.2.1 bounds.2.2.2
      simp [Polyline.dot, Polyline.minCorner, Polyline.maxCorner, hy] at h
      omega

private def ClearStep (box : Rect) (a b : Point) : Prop :=
  Aligned a b ∧ AxMiss box a b

private theorem clearStep_merge {box : Rect} (hw : 0 < box.w) (hh : 0 < box.h)
    {a b p : Point} (hs : straightThrough a b p = true)
    (hab : ClearStep box a b) (hbp : ClearStep box b p) : ClearStep box a p := by
  have hc := straightThrough_axis hab.1 hbp.1 hs
  exact ⟨mrg_aligned a b p hc hab.1 hbp.1,
    mrg_axmiss hw hh a b p hc hab.2 hbp.2⟩

private theorem tidyPush_head (acc : List Point) (p : Point) :
    (tidyPush acc p).head? = some p := by
  induction acc with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil =>
      by_cases h : a = p
      · subst p; simp [tidyPush]
      · simp [tidyPush, h]
    | cons b tail =>
      by_cases h : a = p
      · subst p; simp [tidyPush]
      · by_cases hs : straightThrough b a p = true
        · simpa [tidyPush, h, hs] using ih
        · simp [tidyPush, h, hs]

private theorem tidyPush_clear {box : Rect} (hw : 0 < box.w) (hh : 0 < box.h)
    (p : Point) : ∀ (acc : List Point), RChain (ClearStep box) acc →
      (∀ a, acc.head? = some a → ClearStep box a p) →
      RChain (ClearStep box) (tidyPush acc p) := by
  intro acc
  induction acc with
  | nil => intro _ _; trivial
  | cons a rest ih =>
    intro hc hp
    cases rest with
    | nil =>
      by_cases h : a = p
      · subst p; simpa [tidyPush] using hc
      · simpa [tidyPush, h, RChain] using hp a rfl
    | cons b tail =>
      by_cases h : a = p
      · subst p; simpa [tidyPush] using hc
      · by_cases hs : straightThrough b a p = true
        · have hbp := clearStep_merge hw hh hs hc.1 (hp a rfl)
          have hi := ih hc.2 (by
            intro q hq
            have he : b = q := Option.some.inj hq
            subst q
            exact hbp)
          simpa [tidyPush, h, hs] using hi
        · simpa [tidyPush, h, hs, RChain] using And.intro (hp a rfl) hc

private theorem tidyFold_clear {box : Rect} (hw : 0 < box.w) (hh : 0 < box.h) :
    ∀ (points acc : List Point), RChain (ClearStep box) acc →
      Chain (ClearStep box) points →
      (∀ p, points.head? = some p → ∀ a, acc.head? = some a → ClearStep box a p) →
      RChain (ClearStep box) (points.foldl tidyPush acc) := by
  intro points
  induction points with
  | nil => intro acc hc _ _; exact hc
  | cons p points ih =>
    intro acc hc hs hp
    simp only [List.foldl_cons]
    apply ih _ (tidyPush_clear hw hh p acc hc (hp p rfl))
    · cases points with
      | nil => trivial
      | cons q tail => exact hs.2
    · intro q hq a ha
      rw [tidyPush_head] at ha
      have he : p = a := Option.some.inj ha
      subst a
      cases points with
      | nil => simp at hq
      | cons q' tail =>
        have he : q' = q := Option.some.inj hq
        subst q
        exact hs.1

private theorem input_clear {box : Rect} : ∀ (points : List Point),
    Polyline.isOrthogonal points = true → Polyline.allSegsMiss points box →
    Chain (ClearStep box) points
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: rest, ho, hm => by
    have ho' : Aligned a b ∧ Polyline.isOrthogonal (b :: rest) = true := by
      simpa only [Polyline.isOrthogonal, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq, Aligned] using ho
    exact ⟨⟨ho'.1, aligned_segMisses_axis ho'.1 hm.1⟩,
      input_clear (b :: rest) ho'.2 hm.2⟩

theorem tidy_allSegsMiss {points : List Point} {box : Rect}
    (hw : 0 < box.w) (hh : 0 < box.h)
    (ho : Polyline.isOrthogonal points = true)
    (hm : Polyline.allSegsMiss points box) :
    Polyline.allSegsMiss (tidy points) box := by
  have hc := tidyFold_clear hw hh points [] (by trivial) (input_clear points ho hm)
    (by intro p _ a ha; simp at ha)
  have hf : Chain (ClearStep box) (tidy points) := chain_reverse hc
  exact Chain.misses (Chain.mono (fun _ _ h => h.2) hf)

theorem tidy_not_hitsRect {points : List Point} {box : Rect}
    (ho : Polyline.isOrthogonal points = true)
    (hm : ¬ Polyline.hitsRect points box) :
    ¬ Polyline.hitsRect (tidy points) box := by
  intro hit
  have hinput : Polyline.allSegsMiss points box := by
    apply Classical.byContradiction
    intro hn
    exact hm ⟨hit.1, hit.2.1, hn⟩
  exact hit.2.2 (tidy_allSegsMiss hit.1 hit.2.1 ho hinput)

/-- An orthogonal polyline is an `Aligned` chain: every consecutive pair shares a
coordinate. -/
theorem chain_aligned_of_orthogonal : ∀ (points : List Point),
    Polyline.isOrthogonal points = true → Chain Aligned points
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: rest, ho => by
    have ho' := ho
    rw [Polyline.isOrthogonal_cons, Bool.and_eq_true] at ho'
    exact ⟨by simpa only [Aligned, Bool.or_eq_true, decide_eq_true_eq] using ho'.1,
      chain_aligned_of_orthogonal (b :: rest) ho'.2⟩

/-- Two aligned steps that `straightThrough` accepts share one line, so their outer
endpoints are aligned too. -/
theorem straightThrough_aligned {a b p : Point}
    (hab : Aligned a b) (hbp : Aligned b p) (h : straightThrough a b p = true) :
    Aligned a p := by
  have hc := straightThrough_axis hab hbp h
  rw [Elegant.Grid.collinear_iff] at hc
  unfold Aligned at *
  omega

/-- `tidyPush` keeps an aligned chain aligned. -/
theorem tidyPush_aligned (p : Point) : ∀ (acc : List Point), RChain Aligned acc →
    (∀ a, acc.head? = some a → Aligned a p) → RChain Aligned (tidyPush acc p) := by
  intro acc
  induction acc with
  | nil => intro _ _; trivial
  | cons a rest ih =>
    intro hc hp
    cases rest with
    | nil =>
      by_cases h : a = p
      · subst p; simpa [tidyPush] using hc
      · simpa [tidyPush, h, RChain] using hp a rfl
    | cons b tail =>
      by_cases h : a = p
      · subst p; simpa [tidyPush] using hc
      · by_cases hs : straightThrough b a p = true
        · have hbp : Aligned b p := straightThrough_aligned hc.1 (hp a rfl) hs
          have hi := ih hc.2 (by
            intro q hq
            have he : b = q := Option.some.inj hq
            subst q
            exact hbp)
          simpa [tidyPush, h, hs] using hi
        · simpa [tidyPush, h, hs, RChain] using And.intro (hp a rfl) hc

/-- Folding `tidyPush` over an aligned chain keeps the chain aligned. -/
theorem tidyFold_aligned :
    ∀ (points acc : List Point), RChain Aligned acc → Chain Aligned points →
      (∀ p, points.head? = some p → ∀ a, acc.head? = some a → Aligned a p) →
      RChain Aligned (points.foldl tidyPush acc) := by
  intro points
  induction points with
  | nil => intro acc hc _ _; exact hc
  | cons p points ih =>
    intro acc hc hs hp
    simp only [List.foldl_cons]
    apply ih _ (tidyPush_aligned p acc hc (hp p rfl))
    · cases points with
      | nil => trivial
      | cons q tail => exact hs.2
    · intro q hq a ha
      rw [tidyPush_head] at ha
      have he : p = a := Option.some.inj ha
      subst a
      cases points with
      | nil => simp at hq
      | cons q' tail =>
        have he : q' = q := Option.some.inj hq
        subst q
        exact hs.1

/-- `tidy` keeps an orthogonal polyline orthogonal: it only drops the repeated or
interior collinear points of an aligned chain. -/
theorem tidy_orthogonal {points : List Point}
    (ho : Polyline.isOrthogonal points = true) :
    Polyline.isOrthogonal (tidy points) = true := by
  have hc := tidyFold_aligned points [] (by trivial)
    (chain_aligned_of_orthogonal points ho) (by intro p _ a ha; simp at ha)
  exact Chain.orthogonal (chain_reverse hc)

end Elegant.Lanes.Eventmodeling

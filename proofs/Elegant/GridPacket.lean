theorem padding_nonneg (p : Params) (hp : p.valid) : 0 ≤ padding p := by
  obtain ⟨_, _, _, _, hy, hs, _, _⟩ := hp
  unfold padding
  split <;> omega

theorem pitch_pos (p : Params) (hp : p.valid) : 0 < pitch p := by
  have hpad := padding_nonneg p hp
  unfold pitch
  obtain ⟨_, _, hh, _⟩ := hp
  omega

theorem rect_width_bounds (p : Params) (f : Piece) (hp : p.valid)
    (hf : f.first ≤ f.last) :
    0 ≤ (rect p f).w ∧ (rect p f).w ≤ count f * p.width := by
  have hn : 0 ≤ count f := by unfold count; omega
  have hw : 0 ≤ p.width := Int.le_of_lt hp.2.1
  have hprod := Int.mul_nonneg hn hw
  have hpad := hp.2.2.2.1
  simp only [rect]
  constructor <;> omega

theorem rect_horizontal_bounds (p : Params) (f : Piece) (hp : p.valid)
    (hf : f.first ≤ f.last) (hc : 0 ≤ column p f)
    (hfit : column p f + count f ≤ p.bits) :
    p.margin ≤ (rect p f).x ∧
      (rect p f).x + (rect p f).w ≤ p.bits * p.width + p.margin := by
  have hn : 0 ≤ count f := by unfold count; omega
  have hw : 0 ≤ p.width := Int.le_of_lt hp.2.1
  have widths := rect_width_bounds p f hp hf
  cases hd : p.descending with
  | false =>
    have hleft := Int.mul_nonneg hc hw
    have hright := Int.mul_le_mul_of_nonneg_right hfit hw
    rw [Int.add_mul] at hright
    simp only [rect, hd, Bool.false_eq_true, ↓reduceIte] at widths ⊢
    omega
  | true =>
    have hleft := Int.mul_nonneg (show 0 ≤ p.bits - column p f - count f by omega) hw
    have hright := Int.mul_le_mul_of_nonneg_right
      (show p.bits - column p f ≤ p.bits by omega) hw
    simp only [rect, hd, ↓reduceIte] at widths ⊢
    simp only [Int.sub_mul] at hleft hright ⊢
    omega

theorem rect_canvas_containment (p : Params) (f : Piece) (rows : Int)
    (hp : p.valid) (hf : f.first ≤ f.last)
    (hc : 0 ≤ column p f) (hfit : column p f + count f ≤ p.bits)
    (hr : 0 ≤ row p f) (hrows : row p f + 1 ≤ rows) :
    (⟨0, 0, p.bits * p.width + 2 * p.margin,
      rows * pitch p + padding p⟩ : Rect).Contained (rect p f) := by
  have hx := rect_horizontal_bounds p f hp hf hc hfit
  simp only [rect] at hx
  have hpad := padding_nonneg p hp
  have hpitch : 0 ≤ pitch p := Int.le_of_lt (pitch_pos p hp)
  have hy := Int.mul_nonneg hr hpitch
  have hyend := Int.mul_le_mul_of_nonneg_right hrows hpitch
  rw [Int.add_mul] at hyend
  have hm := hp.2.2.2.2.2.2.1
  have hpitchEq : pitch p = p.height + padding p := rfl
  unfold Rect.Contained
  simp only [rect]
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

theorem rect_rows_separated (p : Params) (a b : Piece) (hp : p.valid)
    (hrow : row p a + 1 ≤ row p b) :
    ¬ (rect p a).meetsInterior (rect p b) := by
  have hpad := padding_nonneg p hp
  have hprod := Int.mul_le_mul_of_nonneg_right hrow
    (Int.le_of_lt (pitch_pos p hp))
  rw [Int.add_mul] at hprod
  have hpitchEq : pitch p = p.height + padding p := rfl
  simp only [rect, Rect.meetsInterior]
  omega

theorem rect_columns_separated (p : Params) (a b : Piece) (hp : p.valid)
    (ha : a.first ≤ a.last) (hb : b.first ≤ b.last)
    (hcols : column p a + count a ≤ column p b) :
    ¬ (rect p a).meetsInterior (rect p b) := by
  have wa := rect_width_bounds p a hp ha
  have wb := rect_width_bounds p b hp hb
  have hprod := Int.mul_le_mul_of_nonneg_right hcols (Int.le_of_lt hp.2.1)
  rw [Int.add_mul] at hprod
  cases hd : p.descending with
  | false =>
    simp only [rect, hd, Bool.false_eq_true, ↓reduceIte, Rect.meetsInterior] at wa wb ⊢
    omega
  | true =>
    simp only [rect, hd, ↓reduceIte, Rect.meetsInterior] at wa wb ⊢
    simp only [Int.sub_mul]
    omega

theorem fits_coordinates (p : Params) (f : Piece) (hp : p.valid) (hf : fits p f) :
    0 ≤ row p f ∧ 0 ≤ column p f ∧
      f.first = p.bits * row p f + column p f := by
  refine ⟨Int.fdiv_nonneg hf.1 (Int.le_of_lt hp.1),
    Int.fmod_nonneg hf.1 (Int.le_of_lt hp.1), ?_⟩
  have h := Int.fmod_def f.first p.bits
  change column p f = f.first - p.bits * row p f at h
  omega

theorem rect_fields_separated (p : Params) (a b : Piece) (hp : p.valid)
    (ha : fits p a) (hb : fits p b)
    (hfields : a.last < b.first ∨ b.last < a.first) :
    ¬ (rect p a).meetsInterior (rect p b) := by
  by_cases hr : row p a = row p b
  · have hca := (fits_coordinates p a hp ha).2.2
    have hcb := (fits_coordinates p b hp hb).2.2
    rw [hr] at hca
    rcases hfields with hab | hba
    · apply rect_columns_separated p a b hp ha.2.1 hb.2.1
      unfold count
      omega
    · have hs := rect_columns_separated p b a hp hb.2.1 ha.2.1
        (show column p b + count b ≤ column p a by unfold count; omega)
      intro hit
      exact hs ((Rect.meetsInterior_comm _ _).mp hit)
  · by_cases hab : row p a < row p b
    · exact rect_rows_separated p a b hp (by omega)
    · have hs := rect_rows_separated p b a hp (by omega : row p b + 1 ≤ row p a)
      intro hit
      exact hs ((Rect.meetsInterior_comm _ _).mp hit)

theorem bitRect_above_field (p : Params) (f : Piece) (w : Int) (trail : Bool)
    (hshow : p.showBits = true) :
    (bitRect p f w trail).y + (bitRect p f w trail).h = (rect p f).y := by
  simp [bitRect, hshow]

theorem bitRect_avoids_same_row (p : Params) (a b : Piece) (w : Int) (trail : Bool)
    (hrow : row p a = row p b) :
    ¬ (bitRect p a w trail).meetsInterior (rect p b) := by
  by_cases hshow : p.showBits = true
  · have he := bitRect_above_field p a w trail hshow
    have hy : (rect p a).y = (rect p b).y := by simp [rect, hrow]
    unfold Rect.meetsInterior
    omega
  · cases hs : p.showBits <;> simp_all [bitRect, Rect.meetsInterior] <;> omega

theorem bitRect_avoids_field (p : Params) (a b : Piece) (w : Int) (trail : Bool)
    (hp : p.valid) :
    ¬ (bitRect p a w trail).meetsInterior (rect p b) := by
  cases hs : p.showBits with
  | false =>
    simp only [bitRect, hs, Bool.not_false, ↓reduceIte, Rect.meetsInterior]
    omega
  | true =>
    have hpad := padding_nonneg p hp
    have hpitch : 0 ≤ pitch p := Int.le_of_lt (pitch_pos p hp)
    have he : pitch p = p.height + padding p := rfl
    by_cases hr : row p a ≤ row p b
    · have hm := Int.mul_le_mul_of_nonneg_right hr hpitch
      simp only [bitRect, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        rect, Rect.meetsInterior]
      omega
    · have hm := Int.mul_le_mul_of_nonneg_right
        (show row p b + 1 ≤ row p a by omega) hpitch
      rw [Int.add_mul] at hm
      simp only [bitRect, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        rect, Rect.meetsInterior]
      omega


/-- The title occupies the final allocated row, after every field and its bit
label band. This uses the executed row maximum, not a bound on label width. -/
theorem field_avoids_title (p : Params) (f : Piece) (rows : Int)
    (hp : p.valid) (hrows : row p f + 1 ≤ rows) :
    ¬ (rect p f).meetsInterior
      ⟨p.margin, rows * pitch p + padding p, p.bits * p.width, p.height⟩ := by
  have hm := Int.mul_le_mul_of_nonneg_right hrows
    (Int.le_of_lt (pitch_pos p hp))
  have hpad := padding_nonneg p hp
  have he : pitch p = p.height + padding p := rfl
  rw [Int.add_mul] at hm
  simp only [rect, Rect.meetsInterior]
  omega

theorem bitRect_avoids_title (p : Params) (f : Piece) (rows w : Int)
    (trail : Bool) (hp : p.valid) (hn : 0 ≤ rows)
    (hrows : row p f + 1 ≤ rows) :
    ¬ (bitRect p f w trail).meetsInterior
      ⟨p.margin, rows * pitch p + padding p, p.bits * p.width, p.height⟩ := by
  have hpad := padding_nonneg p hp
  have hpitch := Int.le_of_lt (pitch_pos p hp)
  cases hs : p.showBits with
  | false =>
    have hm := Int.mul_nonneg hn hpitch
    simp only [bitRect, hs, Bool.not_false, ↓reduceIte, Rect.meetsInterior]
    omega
  | true =>
    have hm := Int.mul_le_mul_of_nonneg_right
      (show row p f ≤ rows by omega) hpitch
    simp only [bitRect, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      rect, Rect.meetsInterior]
    omega
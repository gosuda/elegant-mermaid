import Elegant.Scene
import Elegant.Gen.Layoutconst
import Elegant.StyledMeasure

set_option autoImplicit false

namespace Elegant.GridPacket

structure Params where
  bits : Int
  width : Int
  height : Int
  padX : Int
  padY : Int
  showPad : Int
  margin : Int
  lineHeight : Int
  showBits : Bool := true
  descending : Bool := false
  deriving Repr

def defaults (p : Profile) : Params :=
  ⟨LayoutConst.packet_bits_per_row.get p, LayoutConst.packet_bit_width.get p,
   LayoutConst.packet_row_height.get p, LayoutConst.packet_padding_x.get p,
   LayoutConst.packet_padding_y.get p, LayoutConst.packet_show_bits_pad.get p,
   LayoutConst.packet_margin_x.get p, LayoutConst.line_h.get p, true, false⟩

def configure (profile : Profile) (p : Params) (entry : String × ConfigValue) : Params :=
  match entry with
  | ("showBits", .boolean b) => { p with showBits := b }
  | ("bitOrder", .string s) => { p with descending := s == "descending" }
  | ("bitsPerRow", .integer n) => { p with bits := n }
  | ("bitWidth", .integer n) => if profile == .vector then { p with width := n * 64 } else p
  | ("rowHeight", .integer n) => if profile == .vector then { p with height := n * 64 } else p
  | ("paddingX", .integer n) => if profile == .vector then { p with padX := n * 64 } else p
  | ("paddingY", .integer n) => if profile == .vector then { p with padY := n * 64 } else p
  | _ => p

def Params.valid (p : Params) : Prop :=
  0 < p.bits ∧ 0 < p.width ∧ 0 < p.height ∧ 0 ≤ p.padX ∧ 0 ≤ p.padY ∧
  0 ≤ p.showPad ∧ 0 ≤ p.margin ∧ 0 ≤ p.lineHeight
instance (p : Params) : Decidable p.valid := inferInstanceAs (Decidable (_ ∧ _))

def padding (p : Params) : Int := p.padY + if p.showBits then p.showPad else 0

def pitch (p : Params) : Int := p.height + padding p

structure Piece where
  first : Int
  last : Int
  deriving DecidableEq, Repr

def row (p : Params) (f : Piece) : Int := Int.fdiv f.first p.bits

def column (p : Params) (f : Piece) : Int := Int.fmod f.first p.bits

def count (f : Piece) : Int := f.last - f.first + 1

def fits (p : Params) (f : Piece) : Prop :=
  0 ≤ f.first ∧ f.first ≤ f.last ∧ column p f + count f ≤ p.bits
instance (p : Params) (f : Piece) : Decidable (fits p f) := inferInstanceAs (Decidable (_ ∧ _))

def rect (p : Params) (f : Piece) : Rect :=
  let c := if p.descending then p.bits - column p f - count f else column p f
  ⟨c * p.width + p.margin, row p f * pitch p + padding p,
    max (count f * p.width - p.padX) 0, p.height⟩

def bitRect (p : Params) (f : Piece) (w : Int) (trail : Bool) : Rect :=
  if !p.showBits then ⟨0, 0, 0, 0⟩ else
  let r := rect p f
  let h := min p.lineHeight (padding p)
  ⟨if trail then max (r.x + r.w - w) 0
    else if count f = 1 then max (r.x + Int.fdiv r.w 2 - Int.fdiv w 2) 0 else r.x,
    r.y - h, w, h⟩

/-- Field splitting is a model-stage operation. These consecutive half-open ranges
are its mathematical partition, independently of the display padding. -/
def bitRange (start length : Nat) : List Nat := (List.range length).map (start + ·)

theorem packet_bits_partitioned (start length : Nat) (b : Nat) :
    b ∈ bitRange start length ↔ start ≤ b ∧ b < start + length := by
  simp only [bitRange, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h
    exact ⟨b - start, by omega, by omega⟩

theorem packet_rows_fit (p : Params) (f : Piece) (h : fits p f) :
    column p f + count f ≤ p.bits := h.2.2

def pieceBitWidths (pieces : List Piece) : Int := (pieces.map count).sum

theorem packet_piece_widths_sum (pieces : List Piece) (total : Int)
    (partition : (pieces.map count).sum = total) : pieceBitWidths pieces = total := partition

theorem packet_piece_widths_append (a b : List Piece) :
    pieceBitWidths (a ++ b) = pieceBitWidths a + pieceBitWidths b := by
  simp [pieceBitWidths, List.map_append, List.sum_append]

structure Span where
  start : Nat
  length : Nat
  deriving DecidableEq, Repr

/-- The next row boundary clips the current field, preserving its remaining
bits for the following row. Zero row width is treated as one only in this
standalone splitter; the layout rejects it before geometry is computed. -/
def splitField (bits start remaining : Nat) : List Span :=
  if remaining = 0 then [] else
    let n := min remaining (max 1 bits - start % max 1 bits)
    ⟨start, n⟩ :: splitField bits (start + n) (remaining - n)
termination_by remaining
decreasing_by
  have hm := Nat.mod_lt start (by omega : 0 < max 1 bits)
  have : 0 < min remaining (max 1 bits - start % max 1 bits) := by omega
  omega

theorem splitField_widths_sum (bits start remaining : Nat) :
    ((splitField bits start remaining).map (·.length)).sum = remaining := by
  rw [splitField]
  split
  · rename_i h; simp [h]
  · rename_i h
    simp only [List.map_cons, List.sum_cons]
    rw [splitField_widths_sum]
    have hm := Nat.mod_lt start (by omega : 0 < max 1 bits)
    have hn : min remaining (max 1 bits - start % max 1 bits) ≤ remaining := Nat.min_le_left _ _
    omega
termination_by remaining
decreasing_by
  have hm := Nat.mod_lt start (by omega : 0 < max 1 bits)
  have : 0 < min remaining (max 1 bits - start % max 1 bits) := by omega
  omega

theorem splitField_coverage (bits start remaining b : Nat) :
    (∃ s ∈ splitField bits start remaining, s.start ≤ b ∧ b < s.start + s.length) ↔
      start ≤ b ∧ b < start + remaining := by
  rw [splitField]
  split
  · rename_i h; simp [h]
  · rename_i h
    simp only [List.mem_cons, exists_eq_or_imp]
    rw [splitField_coverage]
    have hn : min remaining (max 1 bits - start % max 1 bits) ≤ remaining := Nat.min_le_left _ _
    constructor
    · intro hmem
      rcases hmem with hmem | hmem <;> omega
    · intro hb
      by_cases hb' : b < start + min remaining (max 1 bits - start % max 1 bits)
      · exact Or.inl ⟨hb.1, hb'⟩
      · exact Or.inr ⟨by omega, by omega⟩
termination_by remaining
decreasing_by
  have hm := Nat.mod_lt start (by omega : 0 < max 1 bits)
  have : 0 < min remaining (max 1 bits - start % max 1 bits) := by omega
  omega

theorem splitField_rows_fit (bits start remaining : Nat) :
    ∀ s ∈ splitField bits start remaining,
      s.start % max 1 bits + s.length ≤ max 1 bits := by
  rw [splitField]
  split
  · simp
  · intro s hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · dsimp
      have hm := Nat.mod_lt start (by omega : 0 < max 1 bits)
      have hn := Nat.min_le_right remaining (max 1 bits - start % max 1 bits)
      omega
    · exact splitField_rows_fit bits _ _ s hs
termination_by remaining
decreasing_by
  have hm := Nat.mod_lt start (by omega : 0 < max 1 bits)
  have : 0 < min remaining (max 1 bits - start % max 1 bits) := by omega
  omega

theorem splitField_bounds (bits start remaining : Nat) :
    ∀ s ∈ splitField bits start remaining,
      start ≤ s.start ∧ s.start + s.length ≤ start + remaining ∧ 0 < s.length := by
  rw [splitField]
  split
  · simp
  · rename_i h
    intro s hs
    simp only [List.mem_cons] at hs
    have hm := Nat.mod_lt start (by omega : 0 < max 1 bits)
    have hn : min remaining (max 1 bits - start % max 1 bits) ≤ remaining := Nat.min_le_left _ _
    have hp : 0 < min remaining (max 1 bits - start % max 1 bits) := by omega
    rcases hs with rfl | hs
    · dsimp; omega
    · have ih := splitField_bounds bits _ _ s hs
      omega
termination_by remaining
decreasing_by
  have _hm := Nat.mod_lt start (by omega : 0 < max 1 bits)
  have : 0 < min remaining (max 1 bits - start % max 1 bits) := by omega
  omega

theorem splitField_disjoint (bits start remaining : Nat) :
    (splitField bits start remaining).Pairwise
      (fun a b => a.start + a.length ≤ b.start) := by
  rw [splitField]
  split
  · exact List.Pairwise.nil
  · apply List.Pairwise.cons
    · intro s hs
      exact (splitField_bounds bits _ _ s hs).1
    · exact splitField_disjoint bits _ _
termination_by remaining
decreasing_by
  have hm := Nat.mod_lt start (by omega : 0 < max 1 bits)
  have : 0 < min remaining (max 1 bits - start % max 1 bits) := by omega
  omega

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
end Elegant.GridPacket

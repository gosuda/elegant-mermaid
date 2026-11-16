import Elegant.GridTree

set_option autoImplicit false

/-! The gap bands around a child rectangle: a rectangle grown by the gaps of its track is
separated from every sibling, and lies inside the frame of its group. A route stub or a self-loop
stays inside this grown rectangle, so it cannot reach another box. -/

namespace Elegant
namespace Grid

def grow (r : Rect) (gx gy : Int) : Rect := ⟨r.x - gx, r.y - gy, r.w + 2 * gx, r.h + 2 * gy⟩

theorem childRect_grown_sep {columns gapX gapY : Int} {F : Rect} {t : Track} {s u : Slot}
    (hw : TrackWf columns gapX gapY t) (hgx : 0 ≤ gapX) (hgy : 0 ≤ gapY) (hs : s ∈ t.slots)
    (hu : u ∈ t.slots) (hlt : linpos columns s + s.eff ≤ linpos columns u) :
    Sep (childRect gapX gapY F t s) (grow (childRect gapX gapY F t u) gapX gapY) ∧
      Sep (childRect gapX gapY F t u) (grow (childRect gapX gapY F t s) gapX gapY) := by
  have fs := childRect_facts (F := F) hw hgx hgy hs
  have fu := childRect_facts (F := F) hw hgx hgy hu
  have hsep := slot_separated (columns := columns)
    (let ⟨a, b, c, d, e, _⟩ := hw.props s hs; ⟨a, b, c, d, e⟩)
    (let ⟨a, b, c, d, e, _⟩ := hw.props u hu; ⟨a, b, c, d, e⟩) hlt
  have hq : 0 ≤ t.unit + gapX := by have := hw.unitNonneg; omega
  simp only [Sep, grow]
  rcases hsep with hrow | ⟨hrow, hcol⟩
  · have h1 := rowTop_le_of_le F.y gapY t.rows (r := s.row.toNat + 1) (r' := u.row.toNat)
      hw.rowsNonneg hgy (by have := (hw.props s hs).2.2.1; omega)
    have := fs.bottom
    have := fu.yEq
    have := fs.yEq
    have := fu.bottom
    exact ⟨Or.inr (Or.inr (Or.inl (by omega))), Or.inr (Or.inr (Or.inr (by omega)))⟩
  · have hmul : (s.col + s.eff) * (t.unit + gapX) ≤ u.col * (t.unit + gapX) :=
      Int.mul_le_mul_of_nonneg_right hcol hq
    have := fs.right
    have := fu.left
    have := fu.right
    have hxu : (childRect gapX gapY F t u).x = F.x + gapX + u.col * (t.unit + gapX) := rfl
    have hxs : (childRect gapX gapY F t s).x = F.x + gapX + s.col * (t.unit + gapX) := rfl
    have : u.col * (t.unit + gapX) ≥ 0 := Int.mul_nonneg (hw.props u hu).2.1 hq
    have : s.col * (t.unit + gapX) ≥ 0 := Int.mul_nonneg (hw.props s hs).2.1 hq
    exact ⟨Or.inl (by omega), Or.inr (Or.inl (by omega))⟩

theorem childRect_grown_contained {columns gapX gapY : Int} {F : Rect} {t : Track} {s : Slot}
    (hw : TrackWf columns gapX gapY t) (hgx : 0 ≤ gapX) (hgy : 0 ≤ gapY) (hs : s ∈ t.slots)
    (hW : t.width ≤ F.w) (hH : t.height ≤ F.h) :
    F.Contained (grow (childRect gapX gapY F t s) gapX gapY) := by
  have hf := childRect_facts (F := F) hw hgx hgy hs
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hw.props s hs
  have hrow : s.row.toNat < t.rows.length := by
    have := hw.nrows s hs
    have := hw.rowsLength
    omega
  have hq : 0 ≤ t.unit + gapX := by have := hw.unitNonneg; omega
  have hmul : (s.col + s.eff) * (t.unit + gapX) ≤ t.ncols * (t.unit + gapX) :=
    Int.mul_le_mul_of_nonneg_right (hw.ncols s hs) hq
  have hwidth := hw.width
  have e1 : t.ncols * (t.unit + gapX) = t.ncols * t.unit + t.ncols * gapX := Int.mul_add _ _ _
  have e2 : (t.ncols + 1) * gapX = t.ncols * gapX + gapX := by rw [Int.add_mul, Int.one_mul]
  have hbot : rowTop F.y gapY t.rows (s.row.toNat + 1) ≤ rowTop F.y gapY t.rows t.rows.length :=
    rowTop_le_of_le F.y gapY t.rows hw.rowsNonneg hgy (by omega)
  rw [rowTop_full] at hbot
  have hlen : (t.rows.length : Int) = t.nrows := by
    have := hw.rowsLength
    have := hw.nrowsNonneg
    omega
  have hheight := hw.height
  have e3 : (t.nrows + 1) * gapY = t.nrows * gapY + gapY := by rw [Int.add_mul, Int.one_mul]
  rw [hlen] at hbot
  simp only [Rect.Contained, grow]
  have := hf.left
  have := hf.right
  have := hf.top
  have := hf.bottom
  have hxs : (childRect gapX gapY F t s).x = F.x + gapX + s.col * (t.unit + gapX) := rfl
  have : s.col * (t.unit + gapX) ≥ 0 := Int.mul_nonneg p2 hq
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem Ctx.rect_grown_sep {c : Ctx} (hc : c.Wf) {i j : Nat} (hi : i < c.n) (hj : j < c.n)
    (hne : i ≠ j) (hs : c.slotOf i = c.slotOf j) :
    Sep (c.rect j) (grow (c.rect i) c.gapX c.gapY) := by
  have si := c.slotFor_spec (c.mem_children hc hi)
  have sj := c.slotFor_spec (c.mem_children hc hj)
  rw [← hs] at sj
  have hw := c.parentTrack_wf hc (c.slotOf i)
  have hdist : slotFor (c.parentTrack (c.slotOf i)) i ≠ slotFor (c.parentTrack (c.slotOf i)) j := by
    intro h
    rw [h] at si
    exact hne (si.2.1.symm.trans sj.2.1)
  rw [c.rect_eq hc hi, c.rect_eq hc hj, ← hs]
  rcases pairwise_total hw.pairwise _ si.1 _ sj.1 hdist with h | h
  · exact (childRect_grown_sep hw hc.gapX hc.gapY si.1 sj.1 h).2
  · exact (childRect_grown_sep hw hc.gapX hc.gapY sj.1 si.1 h).1

theorem Ctx.grown_contained {c : Ctx} (hc : c.Wf) {i : Nat} (hi : i < c.n) :
    (c.frame (c.slotOf i)).Contained (grow (c.rect i) c.gapX c.gapY) := by
  have hp : c.slotOf i = c.n ∨ (c.slotOf i < c.n ∧ (c.box (c.slotOf i)).kind = Kind.composite) := by
    rcases c.slotOf_cases hc hi with h | ⟨hlt, hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hk⟩
  have hfit := c.frame_fits hc hp
  rw [c.rect_eq hc hi]
  exact childRect_grown_contained (c.parentTrack_wf hc _) hc.gapX hc.gapY
    (c.slotFor_spec (c.mem_children hc hi)).1 hfit.1 hfit.2

theorem Sep.shrink {a b s : Rect} (hc : b.Contained s) (h : Sep a b) : Sep a s := by
  unfold Rect.Contained at hc
  unfold Sep at *
  omega

theorem Ctx.grown_sep {c : Ctx} (hc : c.Wf) : ∀ (j i : Nat), i < c.n → j < c.n → ¬ c.Up i j →
    ¬ c.Up j i → Sep (c.rect j) (grow (c.rect i) c.gapX c.gapY) := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro i hi hj hij hji
    have hij' : i ≠ j := by
      intro h
      exact hij (h ▸ Ctx.Up.refl)
    by_cases hqs : c.slotOf j = c.slotOf i
    · exact c.rect_grown_sep hc hi hj hij' hqs.symm
    · by_cases hq : c.Up (c.slotOf j) i
      · have hqi : c.slotOf j ≠ i := by
          intro h
          exact hij (by rw [← h]; exact Ctx.up_parent hj)
        obtain ⟨s, hs, hss, hsi⟩ := c.up_sibling hq hqi
        have hsj : s ≠ j := by
          intro h
          subst h
          exact hji hsi
        by_cases hsi' : s = i
        · rw [← hsi']
          exact c.rect_grown_sep hc hs hj hsj hss
        · have hsep := c.rect_sep hc hs hj hsj (by rw [hss])
          have hup : c.Up s (c.slotOf i) := by
            cases hsi with
            | refl => exact absurd rfl hsi'
            | step _ h => exact h
          have hin : c.slotOf i < c.n := by
            rcases c.slotOf_cases hc hi with h1 | ⟨h1, _⟩
            · rw [h1] at hup
              have := hup.root_eq
              omega
            · omega
          have hcs := c.up_contained hc hup hin
          have hne : s ≠ c.n := by omega
          simp only [Ctx.frame, hne, ↓reduceIte] at hcs
          have hgi := c.grown_contained hc hi
          have hne' : c.slotOf i ≠ c.n := by omega
          simp only [Ctx.frame, hne', ↓reduceIte] at hgi
          have := Sep.shrink (Rect.Contained.trans hcs hgi) hsep.comm
          exact this
      · have hqlt : c.slotOf j < j ∧ c.slotOf j < c.n := by
          rcases c.slotOf_cases hc hj with h1 | ⟨h1, _⟩
          · exfalso
            apply hq
            rw [h1]
            exact c.up_root hc i (by omega)
          · exact ⟨h1, by omega⟩
        have hup1 : ¬ c.Up i (c.slotOf j) := by
          intro h
          exact hij (Ctx.Up.step hj h)
        have hsep := ih (c.slotOf j) hqlt.1 i hi hqlt.2 hup1 hq
        have hcj := c.rect_contained hc hj
        have hne : c.slotOf j ≠ c.n := by omega
        simp only [Ctx.frame, hne, ↓reduceIte] at hcj
        exact Sep.mono_left hcj hsep

end Grid
end Elegant

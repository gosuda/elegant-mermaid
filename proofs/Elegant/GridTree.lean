import Elegant.GridFacts

set_option autoImplicit false

/-! The tree structure of the grid layout: ancestry, strict separation of rectangles, and the
free bands around every child rectangle. -/

namespace Elegant
namespace Grid

/-! ### Strict separation -/

abbrev Sep (a b : Rect) : Prop :=
  a.x + a.w ≤ b.x ∨ b.x + b.w ≤ a.x ∨ a.y + a.h ≤ b.y ∨ b.y + b.h ≤ a.y

theorem Sep.comm {a b : Rect} (h : Sep a b) : Sep b a := by
  unfold Sep at *
  omega

theorem Sep.disjoint {a b : Rect} (h : Sep a b) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  unfold Sep at h
  omega

theorem Sep.mono_left {a s b : Rect} (hc : s.Contained a) (h : Sep s b) : Sep a b := by
  unfold Rect.Contained at hc
  unfold Sep at *
  omega

theorem Sep.mono_right {a b s : Rect} (hc : s.Contained b) (h : Sep a s) : Sep a b :=
  (Sep.mono_left hc h.comm).comm

theorem childRect_sep {columns gapX gapY : Int} {F : Rect} {t : Track} {s u : Slot}
    (hw : TrackWf columns gapX gapY t) (hgx : 0 ≤ gapX) (hgy : 0 ≤ gapY) (hs : s ∈ t.slots)
    (hu : u ∈ t.slots) (hlt : linpos columns s + s.eff ≤ linpos columns u) :
    Sep (childRect gapX gapY F t s) (childRect gapX gapY F t u) := by
  have fs := childRect_facts (F := F) hw hgx hgy hs
  have fu := childRect_facts (F := F) hw hgx hgy hu
  have hsep := slot_separated (columns := columns)
    (let ⟨a, b, c, d, e, _⟩ := hw.props s hs; ⟨a, b, c, d, e⟩)
    (let ⟨a, b, c, d, e, _⟩ := hw.props u hu; ⟨a, b, c, d, e⟩) hlt
  have hq : 0 ≤ t.unit + gapX := by have := hw.unitNonneg; omega
  rcases hsep with hrow | ⟨hrow, hcol⟩
  · have h1 := rowTop_le_of_le F.y gapY t.rows (r := s.row.toNat + 1) (r' := u.row.toNat)
      hw.rowsNonneg hgy (by have := (hw.props s hs).2.2.1; omega)
    have := fs.bottom
    have := fu.yEq
    unfold Sep
    omega
  · have hmul : (s.col + s.eff) * (t.unit + gapX) ≤ u.col * (t.unit + gapX) :=
      Int.mul_le_mul_of_nonneg_right hcol hq
    have := fs.right
    have := fu.left
    have : u.col * (t.unit + gapX) ≥ 0 := Int.mul_nonneg (hw.props u hu).2.1 hq
    have := fu.right
    have := fu.top
    have hxu : (childRect gapX gapY F t u).x = F.x + gapX + u.col * (t.unit + gapX) := rfl
    unfold Sep
    omega

theorem Ctx.rect_sep {c : Ctx} (hc : c.Wf) {i j : Nat} (hi : i < c.n) (hj : j < c.n)
    (hne : i ≠ j) (hs : c.slotOf i = c.slotOf j) : Sep (c.rect i) (c.rect j) := by
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
  · exact childRect_sep hw hc.gapX hc.gapY si.1 sj.1 h
  · exact (childRect_sep hw hc.gapX hc.gapY sj.1 si.1 h).comm

/-! ### Ancestry -/

/-- `Up a k`: `a` is `k` or one of its ancestors; the root has index `n`. -/
inductive Ctx.Up (c : Ctx) (a : Nat) : Nat → Prop
  | refl : Ctx.Up c a a
  | step {k : Nat} : k < c.n → Ctx.Up c a (c.slotOf k) → Ctx.Up c a k

theorem Ctx.Up.root_eq {c : Ctx} {a : Nat} (h : c.Up a c.n) : a = c.n := by
  cases h with
  | refl => rfl
  | step hk _ => exact absurd hk (Nat.lt_irrefl _)

theorem Ctx.Up.trans {c : Ctx} {a b k : Nat} (hab : c.Up a b) (hbk : c.Up b k) : c.Up a k := by
  induction hbk with
  | refl => exact hab
  | step hk _ ih => exact Ctx.Up.step hk ih

theorem Ctx.up_parent {c : Ctx} {k : Nat} (hk : k < c.n) : c.Up (c.slotOf k) k :=
  Ctx.Up.step hk Ctx.Up.refl

theorem Ctx.up_root (c : Ctx) (hc : c.Wf) : ∀ k, k ≤ c.n → c.Up c.n k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    by_cases h : k = c.n
    · subst h
      exact Ctx.Up.refl
    · have hlt : k < c.n := by omega
      rcases c.slotOf_cases hc hlt with h1 | ⟨h1, _⟩
      · exact Ctx.Up.step hlt (by rw [h1]; exact Ctx.Up.refl)
      · exact Ctx.Up.step hlt (ih _ h1 (by omega))

theorem Ctx.up_composite {c : Ctx} (hc : c.Wf) {a k : Nat} (h : c.Up a k) :
    a ≠ k → a < c.n → (c.box a).kind = Kind.composite := by
  induction h with
  | refl => intro hne; exact absurd rfl hne
  | @step k hk h ih =>
    intro hne ha
    by_cases hq : a = c.slotOf k
    · rcases c.slotOf_cases hc hk with h1 | ⟨_, h2⟩
      · omega
      · rw [hq]
        exact h2
    · exact ih hq ha

theorem Ctx.up_sibling {c : Ctx} {q p : Nat} (h : c.Up q p) :
    q ≠ p → ∃ s, s < c.n ∧ c.slotOf s = q ∧ c.Up s p := by
  induction h with
  | refl => intro hne; exact absurd rfl hne
  | @step p hp h ih =>
    intro hne
    by_cases hq : q = c.slotOf p
    · exact ⟨p, hp, hq.symm, Ctx.Up.refl⟩
    · obtain ⟨s, hs, hss, hsp⟩ := ih hq
      exact ⟨s, hs, hss, Ctx.Up.step hp hsp⟩

theorem Ctx.up_contained {c : Ctx} (hc : c.Wf) {a k : Nat} (h : c.Up a k) :
    k < c.n → (c.frame a).Contained (c.rect k) := by
  induction h with
  | refl =>
    intro hk
    have hne : a ≠ c.n := by omega
    simp only [Ctx.frame, hne, ↓reduceIte]
    exact Rect.Contained.refl _
  | @step k hk' h ih =>
    intro _
    by_cases hq : c.slotOf k = c.n
    · rw [hq] at h
      have := h.root_eq
      subst this
      have := c.rect_contained hc hk'
      rw [hq] at this
      exact this
    · have hlt : c.slotOf k < c.n := by
        rcases c.slotOf_cases hc hk' with h1 | ⟨h1, _⟩
        · exact absurd h1 hq
        · omega
      have h1 := ih hlt
      have h2 := c.rect_contained hc hk'
      have hne : c.slotOf k ≠ c.n := hq
      simp only [Ctx.frame, hne, ↓reduceIte] at h2
      exact Rect.Contained.trans h1 h2

theorem Ctx.sep_of_up {c : Ctx} (hc : c.Wf) : ∀ (j i : Nat), i < c.n → j < c.n → i ≠ j →
    ¬ c.Up i j → ¬ c.Up j i → Sep (c.rect i) (c.rect j) := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro i hi hj hij hij' hji
    have hcont : ∀ s, c.Up s i → s < c.n → (c.rect s).Contained (c.rect i) := by
      intro s hs hsn
      have := c.up_contained hc hs hi
      have hne : s ≠ c.n := by omega
      simp only [Ctx.frame, hne, ↓reduceIte] at this
      exact this
    by_cases hqs : c.slotOf j = c.slotOf i
    · exact c.rect_sep hc hi hj hij hqs.symm
    · by_cases hq : c.Up (c.slotOf j) i
      · have hqi : c.slotOf j ≠ i := by
          intro h
          exact hij' (by rw [← h]; exact Ctx.up_parent hj)
        obtain ⟨s, hs, hss, hsi⟩ := c.up_sibling hq hqi
        have hsj : s ≠ j := by
          intro h
          subst h
          exact hji hsi
        have hsep := c.rect_sep hc hs hj hsj (by rw [hss])
        exact Sep.mono_left (hcont s hsi hs) hsep
      · have hqlt : c.slotOf j < j ∧ c.slotOf j < c.n := by
          rcases c.slotOf_cases hc hj with h1 | ⟨h1, _⟩
          · exfalso
            apply hq
            rw [h1]
            exact c.up_root hc i (by omega)
          · exact ⟨h1, by omega⟩
        have hiq : i ≠ c.slotOf j := by
          intro h
          exact hq (by rw [← h]; exact Ctx.Up.refl)
        have hup1 : ¬ c.Up i (c.slotOf j) := by
          intro h
          exact hij' (Ctx.Up.step hj h)
        have hsep := ih (c.slotOf j) hqlt.1 i hi hqlt.2 hiq hup1 hq
        have hcj := c.rect_contained hc hj
        have hne : c.slotOf j ≠ c.n := by omega
        simp only [Ctx.frame, hne, ↓reduceIte] at hcj
        exact Sep.mono_right hcj hsep

/-- Leaves cannot be proper ancestors, so the separation theorem applies to every pair
of distinct non-composite boxes, including leaves in different nested groups. -/
theorem Ctx.leaves_sep {c : Ctx} (hc : c.Wf) {i j : Nat}
    (hi : i < c.n) (hj : j < c.n) (hne : i ≠ j)
    (hli : (c.box i).kind ≠ Kind.composite)
    (hlj : (c.box j).kind ≠ Kind.composite) :
    Sep (c.rect i) (c.rect j) := by
  apply c.sep_of_up hc j i hi hj hne
  · intro h
    exact hli (c.up_composite hc h hne hi)
  · intro h
    exact hlj (c.up_composite hc h hne.symm hj)

theorem Ctx.leaves_disjoint {c : Ctx} (hc : c.Wf) {i j : Nat}
    (hi : i < c.n) (hj : j < c.n) (hne : i ≠ j)
    (hli : (c.box i).kind ≠ Kind.composite)
    (hlj : (c.box j).kind ≠ Kind.composite) :
    Disjoint (c.rect i) (c.rect j) :=
  (c.leaves_sep hc hi hj hne hli hlj).disjoint

theorem Ctx.rect_inside_root {c : Ctx} (hc : c.Wf) {i : Nat} (hi : i < c.n) :
    (c.frame c.n).Contained (c.rect i) :=
  c.up_contained hc (c.up_root hc i (Nat.le_of_lt hi)) hi

theorem Ctx.rect_inside_ancestor {c : Ctx} (hc : c.Wf) {a i : Nat}
    (ha : a < c.n) (hi : i < c.n) (h : c.Up a i) :
    (c.rect a).Contained (c.rect i) := by
  have contained := c.up_contained hc h hi
  have hne : a ≠ c.n := Nat.ne_of_lt ha
  simpa only [Ctx.frame, hne, ↓reduceIte] using contained

end Grid
end Elegant

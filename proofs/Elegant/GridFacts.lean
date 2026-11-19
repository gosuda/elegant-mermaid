import Elegant.Grid

set_option autoImplicit false

/-! Proofs about the grid family's block layout: the column tracks, the child rectangles, the
containment and disjointness of the boxes, and the validity of the layout dump. -/

namespace Elegant
namespace Grid

local instance : Inhabited ModelBox := ⟨{ id := "" }⟩

@[simp] theorem except_pure {α ε : Type} (a : α) :
    (pure a : Except ε α) = .ok a := rfl

@[simp] theorem except_bind_ok {α β ε : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem except_bind_error {α β ε : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl

@[simp] theorem except_map_ok {α β ε : Type} (a : α) (f : α → β) :
    f <$> (Except.ok a : Except ε α) = .ok (f a) := rfl

@[simp] theorem except_map_error {α β ε : Type} (e : ε) (f : α → β) :
    f <$> (Except.error e : Except ε α) = .error e := rfl

@[simp] theorem except_throw {α ε : Type} (e : ε) :
    (throw e : Except ε α) = .error e := rfl
/-! ### Division facts -/

theorem fdiv_fmod_nonneg {pos columns : Int} (hp : 0 ≤ pos) (hc : 0 < columns) :
    pos = Int.fdiv pos columns * columns + Int.fmod pos columns ∧ 0 ≤ Int.fmod pos columns ∧
      Int.fmod pos columns < columns ∧ 0 ≤ Int.fdiv pos columns := by
  refine ⟨?_, Int.fmod_nonneg hp (Int.le_of_lt hc), Int.fmod_lt_of_pos _ hc,
    Int.fdiv_nonneg hp (Int.le_of_lt hc)⟩
  have := Int.fmod_def pos columns
  rw [Int.mul_comm] at this
  omega

theorem ceilDiv_mul_ge {a b : Int} (ha : 0 ≤ a) (hb : 1 ≤ b) : a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  have h := fdiv_fmod_nonneg (pos := a + b - 1) (columns := b) (by omega) (by omega)
  omega

theorem ceilDiv_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 1 ≤ b) : 0 ≤ ceilDiv a b := by
  unfold ceilDiv
  exact (fdiv_fmod_nonneg (pos := a + b - 1) (columns := b) (by omega) (by omega)).2.2.2

/-! ### Slots -/

def linpos (columns : Int) (s : Slot) : Int :=
  if 0 < columns then s.row * columns + s.col else s.col

theorem effective_pos (span : Int) : 1 ≤ effective span := by unfold effective; omega

theorem slotHead (columns pos span : Int) (hp : 0 ≤ pos) :
    1 ≤ slotEff columns pos span ∧ 0 ≤ slotCol columns pos ∧ 0 ≤ slotRow columns pos ∧
      (0 < columns → slotCol columns pos + slotEff columns pos span ≤ columns) ∧
      (columns ≤ 0 → slotRow columns pos = 0) ∧
      linpos columns ⟨0, slotCol columns pos, slotRow columns pos, 0, 0, 0⟩ = pos := by
  have hspan := effective_pos span
  by_cases hc : 0 < columns
  · have hd := fdiv_fmod_nonneg hp hc
    have e1 : slotCol columns pos = Int.fmod pos columns := by simp [slotCol, hc]
    have e2 : slotRow columns pos = Int.fdiv pos columns := by simp [slotRow, hc]
    have e3 : slotEff columns pos span = min (effective span) (columns - Int.fmod pos columns) := by
      simp [slotEff, hc, e1]
    have e4 : linpos columns ⟨0, slotCol columns pos, slotRow columns pos, 0, 0, 0⟩ =
        slotRow columns pos * columns + slotCol columns pos := by simp [linpos, hc]
    rw [e4, e1, e2, e3]
    refine ⟨by omega, hd.2.1, hd.2.2.2, fun _ => by omega, fun h => by omega, by omega⟩
  · have e1 : slotCol columns pos = pos := by simp [slotCol, hc]
    have e2 : slotRow columns pos = 0 := by simp [slotRow, hc]
    have e3 : slotEff columns pos span = effective span := by simp [slotEff, hc]
    have e4 : linpos columns ⟨0, slotCol columns pos, slotRow columns pos, 0, 0, 0⟩ =
        slotCol columns pos := by simp [linpos, hc]
    rw [e4, e1, e2, e3]
    refine ⟨hspan, hp, Int.le_refl _, fun h => absurd h hc, fun _ => rfl, rfl⟩

theorem slotsFrom_length (columns : Int) (kids : List Kid) (pos : Int) :
    (slotsFrom columns pos kids).length = kids.length := by
  induction kids generalizing pos with
  | nil => rfl
  | cons k ks ih => simp [slotsFrom, ih]

theorem slotsFrom_props (columns : Int) : ∀ (kids : List Kid) (pos : Int), 0 ≤ pos →
    (∀ k ∈ kids, 0 ≤ k.w ∧ 0 ≤ k.h) →
    ∀ s ∈ slotsFrom columns pos kids,
      1 ≤ s.eff ∧ 0 ≤ s.col ∧ 0 ≤ s.row ∧ (0 < columns → s.col + s.eff ≤ columns) ∧
        (columns ≤ 0 → s.row = 0) ∧ pos ≤ linpos columns s ∧ 0 ≤ s.w ∧ 0 ≤ s.h ∧
        ∃ k ∈ kids, s.child = k.child ∧ s.w = k.w ∧ s.h = k.h := by
  intro kids
  induction kids with
  | nil => intro pos _ _ s hs; simp [slotsFrom] at hs
  | cons k ks ih =>
    intro pos hpos hk s hs
    simp only [slotsFrom, List.mem_cons] at hs
    have hkk := hk k (List.mem_cons_self ..)
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := slotHead columns pos k.span hpos
    rcases hs with rfl | hs
    · refine ⟨h1, h2, h3, h4, h5, ?_, hkk.1, hkk.2, k, List.mem_cons_self .., rfl, rfl, rfl⟩
      simp only [linpos] at h6 ⊢
      omega
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, k', hk', a9⟩ :=
        ih (pos + slotEff columns pos k.span) (by omega)
          (fun k' hk' => hk k' (List.mem_cons_of_mem _ hk')) s hs
      exact ⟨a1, a2, a3, a4, a5, by omega, a7, a8, k', List.mem_cons_of_mem _ hk', a9⟩

theorem slotsFrom_pairwise (columns : Int) : ∀ (kids : List Kid) (pos : Int), 0 ≤ pos →
    (∀ k ∈ kids, 0 ≤ k.w ∧ 0 ≤ k.h) →
    List.Pairwise (fun s t => linpos columns s + s.eff ≤ linpos columns t)
      (slotsFrom columns pos kids) := by
  intro kids
  induction kids with
  | nil => intro pos _ _; exact List.Pairwise.nil
  | cons k ks ih =>
    intro pos hpos hk
    simp only [slotsFrom]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := slotHead columns pos k.span hpos
    refine List.Pairwise.cons ?_ (ih _ (by omega) (fun k' hk' => hk k' (List.mem_cons_of_mem _ hk')))
    intro t ht
    obtain ⟨a1, a2, a3, a4, a5, a6, _⟩ :=
      slotsFrom_props columns ks (pos + slotEff columns pos k.span) (by omega)
        (fun k' hk' => hk k' (List.mem_cons_of_mem _ hk')) t ht
    simp only [linpos] at h6 ⊢
    simp only [linpos] at a6
    omega

/-! ### Folds -/

theorem foldl_max_init (f : Slot → Int) (l : List Slot) (a : Int) :
    a ≤ l.foldl (fun m s => max m (f s)) a := by
  induction l generalizing a with
  | nil => exact Int.le_refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have := ih (max a (f x))
    omega

theorem foldl_max_mem (f : Slot → Int) (l : List Slot) (a : Int) {s : Slot} (hs : s ∈ l) :
    f s ≤ l.foldl (fun m s => max m (f s)) a := by
  induction l generalizing a with
  | nil => cases hs
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hs with rfl | h
    · have := foldl_max_init f xs (max a (f s))
      omega
    · exact ih _ h

theorem foldl_row_init (r : Int) (l : List Slot) (a : Int) :
    a ≤ l.foldl (fun m s => if s.row = r then max m s.h else m) a := by
  induction l generalizing a with
  | nil => exact Int.le_refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    by_cases h : x.row = r
    · simp only [h, ↓reduceIte]
      have := ih (max a x.h)
      omega
    · simp only [h, ↓reduceIte]
      exact ih a

theorem foldl_row_mem (r : Int) (l : List Slot) (a : Int) {s : Slot} (hs : s ∈ l) (hr : s.row = r) :
    s.h ≤ l.foldl (fun m s => if s.row = r then max m s.h else m) a := by
  induction l generalizing a with
  | nil => cases hs
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hs with rfl | h
    · simp only [hr, ↓reduceIte]
      have := foldl_row_init r xs (max a s.h)
      omega
    · by_cases hx : x.row = r
      · simp only [hx, ↓reduceIte]
        exact ih _ h
      · simp only [hx, ↓reduceIte]
        exact ih a h

theorem foldl_row_nonneg (r : Int) (l : List Slot) : 0 ≤ l.foldl (fun m s => if s.row = r then max m s.h else m) 0 :=
  foldl_row_init r l 0

/-! ### The tracks of a composite -/

structure TrackWf (columns gapX gapY : Int) (t : Track) : Prop where
  pairwise : List.Pairwise (fun s u => linpos columns s + s.eff ≤ linpos columns u) t.slots
  props : ∀ s ∈ t.slots, 1 ≤ s.eff ∧ 0 ≤ s.col ∧ 0 ≤ s.row ∧ (0 < columns → s.col + s.eff ≤ columns) ∧
    (columns ≤ 0 → s.row = 0) ∧ 0 ≤ s.w ∧ 0 ≤ s.h
  ncols : ∀ s ∈ t.slots, s.col + s.eff ≤ t.ncols
  nrows : ∀ s ∈ t.slots, s.row + 1 ≤ t.nrows
  ncolsNonneg : 0 ≤ t.ncols
  nrowsNonneg : 0 ≤ t.nrows
  unitNonneg : 0 ≤ t.unit
  unit : ∀ s ∈ t.slots, s.w ≤ t.unit * s.eff
  rowsLength : t.rows.length = t.nrows.toNat
  rowsNonneg : ∀ h ∈ t.rows, 0 ≤ h
  rowH : ∀ s ∈ t.slots, s.h ≤ t.rows.getD s.row.toNat 0
  width : t.width = t.ncols * t.unit + (t.ncols + 1) * gapX
  height : t.height = t.rows.sum + (t.nrows + 1) * gapY

theorem trackOf_wf (gapX gapY columns : Int) (kids : List Kid)
    (hk : ∀ k ∈ kids, 0 ≤ k.w ∧ 0 ≤ k.h) :
    TrackWf columns gapX gapY (trackOf gapX gapY columns kids) := by
  have hp := slotsFrom_props columns kids 0 (Int.le_refl 0) hk
  have hpw := slotsFrom_pairwise columns kids 0 (Int.le_refl 0) hk
  have props : ∀ s ∈ slotsFrom columns 0 kids, 1 ≤ s.eff ∧ 0 ≤ s.col ∧ 0 ≤ s.row ∧
      (0 < columns → s.col + s.eff ≤ columns) ∧ (columns ≤ 0 → s.row = 0) ∧ 0 ≤ s.w ∧ 0 ≤ s.h :=
    fun s hs => by
      obtain ⟨a1, a2, a3, a4, a5, _, a7, a8, _⟩ := hp s hs
      exact ⟨a1, a2, a3, a4, a5, a7, a8⟩
  have hncols : 0 ≤ ncolsOf (slotsFrom columns 0 kids) := foldl_max_init (fun s => s.col + s.eff) _ 0
  have hnrows : 0 ≤ nrowsOf (slotsFrom columns 0 kids) := foldl_max_init (fun s => s.row + 1) _ 0
  have hunit : 0 ≤ unitOf (slotsFrom columns 0 kids) :=
    foldl_max_init (fun s => ceilDiv s.w s.eff) _ 0
  have hrowsLen : (rowsOf (slotsFrom columns 0 kids) (nrowsOf (slotsFrom columns 0 kids))).length =
      (nrowsOf (slotsFrom columns 0 kids)).toNat := by simp [rowsOf]
  refine ⟨hpw, props, ?_, ?_, hncols, hnrows, hunit, ?_, hrowsLen, ?_, ?_, rfl, rfl⟩
  · intro s hs
    exact foldl_max_mem (fun s => s.col + s.eff) _ 0 hs
  · intro s hs
    exact foldl_max_mem (fun s => s.row + 1) _ 0 hs
  · intro s hs
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := props s hs
    have hce : ceilDiv s.w s.eff ≤ unitOf (slotsFrom columns 0 kids) :=
      foldl_max_mem (fun s => ceilDiv s.w s.eff) _ 0 hs
    have := ceilDiv_mul_ge a6 a1
    have := Int.mul_le_mul_of_nonneg_right hce (Int.le_trans (by omega) a1)
    show s.w ≤ unitOf (slotsFrom columns 0 kids) * s.eff
    omega
  · intro h hh
    unfold rowsOf at hh
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hh
    exact foldl_row_nonneg _ _
  · intro s hs
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := props s hs
    have hnr : s.row + 1 ≤ nrowsOf (slotsFrom columns 0 kids) :=
      foldl_max_mem (fun s => s.row + 1) _ 0 hs
    have hlt : s.row.toNat < (nrowsOf (slotsFrom columns 0 kids)).toNat := by omega
    show s.h ≤ (rowsOf (slotsFrom columns 0 kids) (nrowsOf (slotsFrom columns 0 kids))).getD s.row.toNat 0
    unfold rowsOf
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
    simp only [Option.map_some, Option.getD_some]
    exact foldl_row_mem (s.row.toNat : Int) (slotsFrom columns 0 kids) 0 hs (by omega)

/-! ### Row tops -/

theorem sum_map_add (rows : List Int) (g : Int) :
    (rows.map fun h => h + g).sum = rows.sum + (rows.length : Int) * g := by
  induction rows with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [Int.natCast_add, Int.add_mul]
    omega

theorem rowTop_succ (frameY gapY : Int) (rows : List Int) (r : Nat) :
    rowTop frameY gapY rows (r + 1) =
      rowTop frameY gapY rows r + (match rows[r]? with | some h => h + gapY | none => 0) := by
  unfold rowTop
  rw [List.take_add_one]
  cases hr : rows[r]? with
  | none => simp
  | some h => simp; omega

theorem rowTop_zero (frameY gapY : Int) (rows : List Int) : rowTop frameY gapY rows 0 = frameY := by
  simp [rowTop]

theorem rowTop_step_le (frameY gapY : Int) (rows : List Int) (r : Nat) (hrows : ∀ h ∈ rows, 0 ≤ h)
    (hg : 0 ≤ gapY) : rowTop frameY gapY rows r ≤ rowTop frameY gapY rows (r + 1) := by
  rw [rowTop_succ]
  cases hr : rows[r]? with
  | none => simp
  | some h =>
    have := hrows h (List.mem_of_getElem? hr)
    show _ ≤ _ + (h + gapY)
    omega

theorem rowTop_mono (frameY gapY : Int) (rows : List Int) (r : Nat) (hrows : ∀ h ∈ rows, 0 ≤ h)
    (hg : 0 ≤ gapY) : ∀ k : Nat, rowTop frameY gapY rows r ≤ rowTop frameY gapY rows (r + k) := by
  intro k
  induction k with
  | zero => exact Int.le_refl _
  | succ k ih => exact Int.le_trans ih (rowTop_step_le frameY gapY rows (r + k) hrows hg)

theorem rowTop_le_of_le (frameY gapY : Int) (rows : List Int) {r r' : Nat}
    (hrows : ∀ h ∈ rows, 0 ≤ h) (hg : 0 ≤ gapY) (h : r ≤ r') :
    rowTop frameY gapY rows r ≤ rowTop frameY gapY rows r' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact rowTop_mono frameY gapY rows r hrows hg k

theorem frame_le_rowTop (frameY gapY : Int) (rows : List Int) (r : Nat) (hrows : ∀ h ∈ rows, 0 ≤ h)
    (hg : 0 ≤ gapY) : frameY ≤ rowTop frameY gapY rows r := by
  have := rowTop_le_of_le frameY gapY rows hrows hg (Nat.zero_le r)
  rw [rowTop_zero] at this
  exact this

theorem rowTop_full (frameY gapY : Int) (rows : List Int) :
    rowTop frameY gapY rows rows.length = frameY + rows.sum + (rows.length : Int) * gapY := by
  unfold rowTop
  rw [List.take_length, sum_map_add]
  omega

/-! ### Child rectangles -/

theorem slot_separated {columns : Int} {s u : Slot}
    (hs : 1 ≤ s.eff ∧ 0 ≤ s.col ∧ 0 ≤ s.row ∧ (0 < columns → s.col + s.eff ≤ columns) ∧
      (columns ≤ 0 → s.row = 0))
    (hu : 1 ≤ u.eff ∧ 0 ≤ u.col ∧ 0 ≤ u.row ∧ (0 < columns → u.col + u.eff ≤ columns) ∧
      (columns ≤ 0 → u.row = 0))
    (h : linpos columns s + s.eff ≤ linpos columns u) :
    s.row < u.row ∨ (s.row = u.row ∧ s.col + s.eff ≤ u.col) := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := hs
  obtain ⟨u1, u2, u3, u4, u5⟩ := hu
  by_cases hc : 0 < columns
  · have es : linpos columns s = s.row * columns + s.col := by simp [linpos, hc]
    have eu : linpos columns u = u.row * columns + u.col := by simp [linpos, hc]
    rw [es, eu] at h
    have hu4 := u4 hc
    rcases Int.lt_trichotomy s.row u.row with hlt | heq | hgt
    · exact Or.inl hlt
    · rw [heq] at h
      exact Or.inr ⟨heq, by omega⟩
    · have hmul : (u.row + 1) * columns ≤ s.row * columns :=
        Int.mul_le_mul_of_nonneg_right (by omega) (Int.le_of_lt hc)
      rw [Int.add_mul, Int.one_mul] at hmul
      omega
  · have es : linpos columns s = s.col := by simp [linpos, hc]
    have eu : linpos columns u = u.col := by simp [linpos, hc]
    rw [es, eu] at h
    have := s5 (by omega)
    have := u5 (by omega)
    exact Or.inr ⟨by omega, h⟩

structure ChildFacts (F r : Rect) (t : Track) (gapX gapY : Int) (s : Slot) : Prop where
  left : F.x + gapX ≤ r.x
  right : r.x + r.w = F.x + (s.col + s.eff) * (t.unit + gapX)
  top : F.y + gapY ≤ r.y
  yEq : r.y = rowTop F.y gapY t.rows s.row.toNat + gapY
  bottom : r.y + r.h = rowTop F.y gapY t.rows (s.row.toNat + 1)
  wFits : s.w ≤ r.w
  hFits : s.h ≤ r.h
  wNonneg : 0 ≤ r.w
  hNonneg : 0 ≤ r.h

theorem x_end_eq (fx g unit col eff : Int) :
    (fx + g + col * (unit + g)) + (unit * eff + g * (eff - 1)) = fx + (col + eff) * (unit + g) := by
  simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.mul_one]
  rw [Int.mul_comm eff unit, Int.mul_comm eff g]
  omega

theorem childRect_facts {columns gapX gapY : Int} {F : Rect} {t : Track} {s : Slot}
    (hw : TrackWf columns gapX gapY t) (hgx : 0 ≤ gapX) (hgy : 0 ≤ gapY) (hs : s ∈ t.slots) :
    ChildFacts F (childRect gapX gapY F t s) t gapX gapY s := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hw.props s hs
  have hrow : s.row.toNat < t.rows.length := by
    have := hw.nrows s hs
    have := hw.rowsLength
    omega
  have hget : t.rows[s.row.toNat]? = some (t.rows.getD s.row.toNat 0) := by
    rw [List.getElem?_eq_getElem hrow, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrow]
    rfl
  have hy : rowTop F.y gapY t.rows (s.row.toNat + 1) =
      rowTop F.y gapY t.rows s.row.toNat + (t.rows.getD s.row.toNat 0 + gapY) := by
    rw [rowTop_succ, hget]
  have hf := frame_le_rowTop F.y gapY t.rows s.row.toNat hw.rowsNonneg hgy
  have hrowH := hw.rowH s hs
  have hgm : 0 ≤ gapX * (s.eff - 1) := Int.mul_nonneg hgx (by omega)
  have hunit := hw.unit s hs
  have hx : (childRect gapX gapY F t s).x + (childRect gapX gapY F t s).w =
      F.x + (s.col + s.eff) * (t.unit + gapX) := by
    show (F.x + gapX + s.col * (t.unit + gapX)) + (t.unit * s.eff + gapX * (s.eff - 1)) = _
    exact x_end_eq F.x gapX t.unit s.col s.eff
  refine ⟨?_, hx, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show F.x + gapX ≤ F.x + gapX + s.col * (t.unit + gapX)
    have : 0 ≤ s.col * (t.unit + gapX) := Int.mul_nonneg p2 (by have := hw.unitNonneg; omega)
    omega
  · show F.y + gapY ≤ rowTop F.y gapY t.rows s.row.toNat + gapY
    omega
  · show rowTop F.y gapY t.rows s.row.toNat + gapY + t.rows.getD s.row.toNat 0 = _
    omega
  · show s.w ≤ t.unit * s.eff + gapX * (s.eff - 1)
    omega
  · show s.h ≤ t.rows.getD s.row.toNat 0
    exact hrowH
  · show 0 ≤ t.unit * s.eff + gapX * (s.eff - 1)
    omega
  · show 0 ≤ t.rows.getD s.row.toNat 0
    omega

theorem childRect_contained {columns gapX gapY : Int} {F : Rect} {t : Track} {s : Slot}
    (hw : TrackWf columns gapX gapY t) (hgx : 0 ≤ gapX) (hgy : 0 ≤ gapY) (hs : s ∈ t.slots)
    (hW : t.width ≤ F.w) (hH : t.height ≤ F.h) :
    F.Contained (childRect gapX gapY F t s) := by
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hf.left
    omega
  · have := hf.right
    omega
  · have := hf.top
    omega
  · have := hf.bottom
    omega

theorem childRect_disjoint {columns gapX gapY : Int} {F : Rect} {t : Track} {s u : Slot}
    (hw : TrackWf columns gapX gapY t) (hgx : 0 ≤ gapX) (hgy : 0 ≤ gapY) (hs : s ∈ t.slots)
    (hu : u ∈ t.slots) (hlt : linpos columns s + s.eff ≤ linpos columns u) :
    Disjoint (childRect gapX gapY F t s) (childRect gapX gapY F t u) := by
  have fs := childRect_facts (F := F) hw hgx hgy hs
  have fu := childRect_facts (F := F) hw hgx hgy hu
  have hsep := slot_separated (columns := columns)
    (let ⟨a, b, c, d, e, _⟩ := hw.props s hs; ⟨a, b, c, d, e⟩)
    (let ⟨a, b, c, d, e, _⟩ := hw.props u hu; ⟨a, b, c, d, e⟩) hlt
  have hq : 0 ≤ t.unit + gapX := by have := hw.unitNonneg; omega
  intro hm
  unfold Rect.meetsInterior at hm
  rcases hsep with hrow | ⟨hrow, hcol⟩
  · have h1 := rowTop_le_of_le F.y gapY t.rows (r := s.row.toNat + 1) (r' := u.row.toNat)
      hw.rowsNonneg hgy (by have := (hw.props s hs).2.2.1; omega)
    have := fs.bottom
    have := fu.yEq
    omega
  · have hmul : (s.col + s.eff) * (t.unit + gapX) ≤ u.col * (t.unit + gapX) :=
      Int.mul_le_mul_of_nonneg_right hcol hq
    have := fs.right
    have := fu.left
    have : u.col * (t.unit + gapX) ≥ 0 := Int.mul_nonneg (hw.props u hu).2.1 hq
    have := fu.right
    have := fu.top
    have hxu : (childRect gapX gapY F t u).x = F.x + gapX + u.col * (t.unit + gapX) := rfl
    omega

/-! ### Plans of the tree -/

theorem sum_nonneg_int (l : List Int) (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.sum_cons]
    have := h a (List.mem_cons_self ..)
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem TrackWf.dims_nonneg {columns gapX gapY : Int} {t : Track}
    (hw : TrackWf columns gapX gapY t) (hgx : 0 ≤ gapX) (hgy : 0 ≤ gapY) :
    0 ≤ t.width ∧ 0 ≤ t.height := by
  have h1 := hw.width
  have h2 := hw.height
  have h3 : 0 ≤ t.ncols * t.unit := Int.mul_nonneg hw.ncolsNonneg hw.unitNonneg
  have h4 : 0 ≤ (t.ncols + 1) * gapX := Int.mul_nonneg (by have := hw.ncolsNonneg; omega) hgx
  have h5 : 0 ≤ (t.nrows + 1) * gapY := Int.mul_nonneg (by have := hw.nrowsNonneg; omega) hgy
  have h6 := sum_nonneg_int t.rows hw.rowsNonneg
  omega

/-- The facts about a context that `GInput.valid` and `gapsOf` give. -/
structure Ctx.Wf (c : Ctx) : Prop where
  gapX : 0 ≤ c.gapX
  gapY : 0 ≤ c.gapY
  parentLt : ∀ i, i < c.n → -1 ≤ (c.box i).parent ∧ (c.box i).parent < (i : Int)
  parentComposite : ∀ i, i < c.n → 0 ≤ (c.box i).parent →
    (c.box (c.box i).parent.toNat).kind = Kind.composite
  size : ∀ i, i < c.n → 0 ≤ (c.box i).size.w ∧ 0 ≤ (c.box i).size.h

theorem GInput.valid_box {inp : GInput} {pad : Int} (h : inp.valid pad = true)
    {i : Nat} (hi : i < inp.boxes.length) :
    let b := inp.boxes.getD i default
    0 ≤ b.size.w ∧ 0 ≤ b.size.h ∧ -1 ≤ b.parent ∧ b.parent < (i : Int) ∧
      (b.parent < 0 ∨ (inp.boxes.getD b.parent.toNat default).kind = Kind.composite) := by
  have hb : (inp.boxes.getD i default, i) ∈ inp.boxes.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp only [GInput.valid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  have hp := List.all_eq_true.mp h.2.1 _ hb
  simpa only [GBox.sizeOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    and_assoc] using hp

theorem GInput.valid_edge {inp : GInput} {pad : Int} {e : Edge}
    (h : inp.valid pad = true) (he : e ∈ inp.edges) :
    e.fromBox < inp.boxes.length ∧ e.toBox < inp.boxes.length ∧
      0 ≤ e.label.w ∧ 0 ≤ e.label.h := by
  simp only [GInput.valid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  have hp := List.all_eq_true.mp h.2.2 e he
  simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hp

theorem GInput.valid_padding {inp : GInput} {pad : Int} (h : inp.valid pad = true) :
    0 ≤ pad := by
  simp only [GInput.valid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  exact h.1

theorem gapsOf_nonneg {inp : GInput} {pad : Int} (hpad : 0 ≤ pad) :
    0 ≤ (gapsOf inp pad).1 ∧ 0 ≤ (gapsOf inp pad).2 := by
  have hfold : ∀ (es : List Edge) (a : Int), 0 ≤ a →
      0 ≤ es.foldl (fun m e => max m e.label.w) a ∧
      0 ≤ es.foldl (fun m e => max m e.label.h) a := by
    intro es
    induction es with
    | nil => intro a ha; exact ⟨ha, ha⟩
    | cons e es ih =>
      intro a ha
      exact ⟨(ih (max a e.label.w) (by omega)).1,
        (ih (max a e.label.h) (by omega)).2⟩
  have hw := (hfold inp.edges 0 (by omega)).1
  have hh := (hfold inp.edges 0 (by omega)).2
  unfold gapsOf
  dsimp only
  split <;> constructor <;> omega

theorem gapsOf_ge_padding {inp : GInput} {pad : Int} (hpad : 0 ≤ pad) :
    pad ≤ (gapsOf inp pad).1 ∧ pad ≤ (gapsOf inp pad).2 := by
  have hz := gapsOf_nonneg (inp := inp) (pad := 0) (by omega)
  simp [gapsOf] at hz
  unfold gapsOf
  dsimp only
  split <;> constructor <;> omega

theorem Ctx.wf_of_valid {inp : GInput} {pad : Int} (h : inp.valid pad = true) :
    (⟨inp, (gapsOf inp pad).1, (gapsOf inp pad).2⟩ : Ctx).Wf := by
  have hg := gapsOf_nonneg (inp := inp) (GInput.valid_padding h)
  refine ⟨hg.1, hg.2, ?_, ?_, ?_⟩
  · intro i hi
    have hp := GInput.valid_box h hi
    exact ⟨hp.2.2.1, hp.2.2.2.1⟩
  · intro i hi hnonneg
    change 0 ≤ (inp.boxes.getD i default).parent at hnonneg
    have hp := GInput.valid_box h hi
    rcases hp.2.2.2.2 with hneg | hkind
    · omega
    · exact hkind
  · intro i hi
    have hp := GInput.valid_box h hi
    exact ⟨hp.1, hp.2.1⟩

theorem Ctx.plan_eq (c : Ctx) (i : Nat) :
    c.plan i = trackOf c.gapX c.gapY (max (c.box i).columns 0)
      ((c.kidsOf i).map fun k => c.kidOf (c.size k) k) := by
  rw [Ctx.plan]
  congr 1
  exact List.attach_map_val (f := fun k => c.kidOf (c.size k) k)

theorem Ctx.kidOf_child (c : Ctx) (sz : Int × Int) (k : Nat) : (c.kidOf sz k).child = k := by
  unfold Ctx.kidOf
  cases (c.box k).kind <;> rfl

theorem Ctx.kidOf_nonneg {c : Ctx} (hc : c.Wf) {k : Nat} (hk : k < c.n)
    (hp : (c.box k).kind = Kind.composite → 0 ≤ (c.plan k).width ∧ 0 ≤ (c.plan k).height) :
    0 ≤ (c.kidOf (c.size k) k).w ∧ 0 ≤ (c.kidOf (c.size k) k).h := by
  unfold Ctx.kidOf Ctx.size
  have hs := hc.size k hk
  cases hkind : (c.box k).kind with
  | space => simp
  | leaf => exact hs
  | composite => exact hp hkind

theorem Ctx.plan_wf (c : Ctx) (hc : c.Wf) :
    ∀ (m i : Nat), c.n - i = m → TrackWf (max (c.box i).columns 0) c.gapX c.gapY (c.plan i) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro i hm
    rw [Ctx.plan_eq]
    apply trackOf_wf
    intro kd hkd
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hkd
    have hk' := Ctx.kidsOf_mem hk
    apply Ctx.kidOf_nonneg hc hk'.2
    intro _
    exact (ih (c.n - k) (by omega) k rfl).dims_nonneg hc.gapX hc.gapY

theorem Ctx.rootKids_lt {c : Ctx} {k : Nat} (hk : k ∈ c.rootKids) : k < c.n := by
  unfold Ctx.rootKids at hk
  rw [List.mem_filter, List.mem_range] at hk
  exact hk.1

theorem Ctx.rootPlan_wf (c : Ctx) (hc : c.Wf) :
    TrackWf (max c.inp.columns 0) c.gapX c.gapY c.rootPlan := by
  unfold Ctx.rootPlan
  apply trackOf_wf
  intro kd hkd
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hkd
  exact Ctx.kidOf_nonneg hc (Ctx.rootKids_lt hk)
    (fun _ => (c.plan_wf hc _ k rfl).dims_nonneg hc.gapX hc.gapY)

/-- The children of a slot of the tree: the root (index `n`) or a composite box. -/
def Ctx.children (c : Ctx) (p : Nat) : List Nat := if p = c.n then c.rootKids else c.kidsOf p

def Ctx.parentTrack (c : Ctx) (p : Nat) : Track := if p = c.n then c.rootPlan else c.plan p

def Ctx.frame (c : Ctx) (p : Nat) : Rect := if p = c.n then c.rootFrame else c.rect p

def Ctx.columnsOf (c : Ctx) (p : Nat) : Int :=
  if p = c.n then max c.inp.columns 0 else max (c.box p).columns 0

theorem Ctx.parentTrack_wf (c : Ctx) (hc : c.Wf) (p : Nat) :
    TrackWf (c.columnsOf p) c.gapX c.gapY (c.parentTrack p) := by
  unfold Ctx.columnsOf Ctx.parentTrack
  by_cases h : p = c.n
  · simp only [h, ↓reduceIte]
    exact c.rootPlan_wf hc
  · simp only [h, ↓reduceIte]
    exact c.plan_wf hc _ p rfl

theorem Ctx.parentTrack_eq (c : Ctx) (p : Nat) :
    c.parentTrack p = trackOf c.gapX c.gapY (c.columnsOf p)
      ((c.children p).map fun k => c.kidOf (c.size k) k) := by
  unfold Ctx.parentTrack Ctx.columnsOf Ctx.children
  by_cases h : p = c.n
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte]
    exact c.plan_eq p

theorem slotsFrom_child (columns : Int) (kids : List Kid) (pos : Int) :
    (slotsFrom columns pos kids).map Slot.child = kids.map Kid.child := by
  induction kids generalizing pos with
  | nil => rfl
  | cons k ks ih => simp [slotsFrom, ih]

theorem Ctx.slotFor_spec (c : Ctx) {p k : Nat} (hk : k ∈ c.children p) :
    slotFor (c.parentTrack p) k ∈ (c.parentTrack p).slots ∧
      (slotFor (c.parentTrack p) k).child = k ∧
      (slotFor (c.parentTrack p) k).w = (c.kidOf (c.size k) k).w ∧
      (slotFor (c.parentTrack p) k).h = (c.kidOf (c.size k) k).h := by
  have hdef : ∀ (cols : Int) (kids : List Kid) (k : Nat), k ∈ kids.map Kid.child →
      ∃ s ∈ slotsFrom cols 0 kids, s.child = k := by
    intro cols kids k hk
    rw [← slotsFrom_child cols kids 0] at hk
    obtain ⟨s, hs, hsk⟩ := List.mem_map.mp hk
    exact ⟨s, hs, hsk⟩
  rw [Ctx.parentTrack_eq]
  have hmem : k ∈ ((c.children p).map fun k => c.kidOf (c.size k) k).map Kid.child := by
    rw [List.map_map]
    exact List.mem_map.mpr ⟨k, hk, Ctx.kidOf_child c _ k⟩
  obtain ⟨s0, hs0, hs0k⟩ := hdef (c.columnsOf p) _ k hmem
  have hfind : (trackOf c.gapX c.gapY (c.columnsOf p)
      ((c.children p).map fun k => c.kidOf (c.size k) k)).slots.find? (fun s => s.child = k) ≠ none := by
    intro hnone
    have := List.find?_eq_none.mp hnone s0 hs0
    simp [hs0k] at this
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hfind
  have hsmem := List.mem_of_find?_eq_some hs
  have hsc : s.child = k := by
    have := List.find?_some hs
    simpa using this
  have hslot : slotFor (trackOf c.gapX c.gapY (c.columnsOf p)
      ((c.children p).map fun k => c.kidOf (c.size k) k)) k = s := by
    unfold slotFor
    rw [hs]
    rfl
  rw [hslot]
  refine ⟨hsmem, hsc, ?_⟩
  have hkids : ∀ kd ∈ (c.children p).map (fun k => c.kidOf (c.size k) k), 0 ≤ kd.w ∨ True :=
    fun _ _ => Or.inr trivial
  have hslots : s ∈ slotsFrom (c.columnsOf p) 0 ((c.children p).map fun k => c.kidOf (c.size k) k) :=
    hsmem
  have hprop : ∃ kd ∈ (c.children p).map (fun k => c.kidOf (c.size k) k),
      s.child = kd.child ∧ s.w = kd.w ∧ s.h = kd.h := by
    clear hs hslot hfind hsmem hdef hmem
    generalize (c.children p).map (fun k => c.kidOf (c.size k) k) = kids at hslots
    generalize c.columnsOf p = cols at hslots
    revert hslots
    suffices ∀ (pos : Int) (ks : List Kid), s ∈ slotsFrom cols pos ks →
        ∃ kd ∈ ks, s.child = kd.child ∧ s.w = kd.w ∧ s.h = kd.h from fun h => this 0 kids h
    intro pos ks
    induction ks generalizing pos with
    | nil => intro h; simp [slotsFrom] at h
    | cons kd rest ih =>
      intro h
      simp only [slotsFrom, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨kd, List.mem_cons_self .., rfl, rfl, rfl⟩
      · obtain ⟨kd', hkd', hh⟩ := ih _ h
        exact ⟨kd', List.mem_cons_of_mem _ hkd', hh⟩
  obtain ⟨kd, hkd, hch, hw, hh⟩ := hprop
  obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hkd
  rw [Ctx.kidOf_child] at hch
  have : k' = k := by rw [← hch, ← hsc]
  subst this
  exact ⟨hw, hh⟩

/-! ### Rectangles of the tree -/

theorem pairwise_total {α : Type} {R : α → α → Prop} {l : List α} (hp : List.Pairwise R l) :
    ∀ x ∈ l, ∀ y ∈ l, x ≠ y → R x y ∨ R y x := by
  induction hp with
  | nil => intro x hx; cases hx
  | @cons a t h _ ih =>
    intro x hx y hy hne
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd rfl hne
      · exact Or.inl (h y hy')
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact Or.inr (h x hx')
      · exact ih x hx' y hy' hne

theorem Ctx.slotOf_cases {c : Ctx} (hc : c.Wf) {i : Nat} (hi : i < c.n) :
    c.slotOf i = c.n ∨ (c.slotOf i < i ∧ (c.box (c.slotOf i)).kind = Kind.composite) := by
  have h1 := hc.parentLt i hi
  unfold Ctx.slotOf
  by_cases hp : (c.box i).parent < 0
  · simp [hp]
  · have := hc.parentComposite i hi (by omega)
    right
    simp only [hp, ↓reduceIte]
    exact ⟨by omega, this⟩

theorem Ctx.mem_children {c : Ctx} (hc : c.Wf) {i : Nat} (hi : i < c.n) :
    i ∈ c.children (c.slotOf i) := by
  unfold Ctx.children
  rcases c.slotOf_cases hc hi with h | ⟨hlt, _⟩
  · simp only [h, ↓reduceIte]
    unfold Ctx.rootKids
    rw [List.mem_filter, List.mem_range]
    exact ⟨hi, by simp [h]⟩
  · have hne : c.slotOf i ≠ c.n := by omega
    simp only [hne, ↓reduceIte]
    unfold Ctx.kidsOf
    rw [List.mem_filter, List.mem_range'_1]
    have h2 : c.slotOf i + 1 + (c.n - (c.slotOf i + 1)) = c.n := Nat.add_sub_cancel' (by omega)
    exact ⟨⟨by omega, by rw [h2]; exact hi⟩, by simp⟩

theorem Ctx.rect_eq {c : Ctx} (hc : c.Wf) {i : Nat} (hi : i < c.n) :
    c.rect i = childRect c.gapX c.gapY (c.frame (c.slotOf i)) (c.parentTrack (c.slotOf i))
      (slotFor (c.parentTrack (c.slotOf i)) i) := by
  rw [Ctx.rect]
  rcases c.slotOf_cases hc hi with h | ⟨hlt, _⟩
  · simp only [h, ↓reduceIte]
    simp [Ctx.frame, Ctx.parentTrack]
  · have hne : c.slotOf i ≠ c.n := by omega
    simp only [hne, ↓reduceIte, hlt, dite_true]
    simp [Ctx.frame, Ctx.parentTrack, hne]

theorem Ctx.rect_facts {c : Ctx} (hc : c.Wf) {i : Nat} (hi : i < c.n) :
    ChildFacts (c.frame (c.slotOf i)) (c.rect i) (c.parentTrack (c.slotOf i)) c.gapX c.gapY
      (slotFor (c.parentTrack (c.slotOf i)) i) := by
  rw [c.rect_eq hc hi]
  exact childRect_facts (c.parentTrack_wf hc _) hc.gapX hc.gapY
    (c.slotFor_spec (c.mem_children hc hi)).1

theorem Ctx.plan_fits {c : Ctx} (hc : c.Wf) {j : Nat} (hj : j < c.n)
    (hk : (c.box j).kind = Kind.composite) :
    (c.plan j).width ≤ (c.rect j).w ∧ (c.plan j).height ≤ (c.rect j).h := by
  have hf := c.rect_facts hc hj
  have hs := c.slotFor_spec (c.mem_children hc hj)
  have e1 : (c.kidOf (c.size j) j).w = (c.plan j).width := by simp [Ctx.kidOf, Ctx.size, hk]
  have e2 : (c.kidOf (c.size j) j).h = (c.plan j).height := by simp [Ctx.kidOf, Ctx.size, hk]
  have w1 := hf.wFits
  have h1 := hf.hFits
  rw [hs.2.2.1, e1] at w1
  rw [hs.2.2.2, e2] at h1
  exact ⟨w1, h1⟩

theorem Ctx.frame_fits {c : Ctx} (hc : c.Wf) {p : Nat}
    (hp : p = c.n ∨ (p < c.n ∧ (c.box p).kind = Kind.composite)) :
    (c.parentTrack p).width ≤ (c.frame p).w ∧ (c.parentTrack p).height ≤ (c.frame p).h := by
  rcases hp with h | ⟨hlt, hk⟩
  · simp [Ctx.parentTrack, Ctx.frame, h, Ctx.rootFrame]
  · have hne : p ≠ c.n := by omega
    simp only [Ctx.parentTrack, Ctx.frame, hne, ↓reduceIte]
    exact c.plan_fits hc hlt hk

theorem Ctx.rect_contained {c : Ctx} (hc : c.Wf) {i : Nat} (hi : i < c.n) :
    (c.frame (c.slotOf i)).Contained (c.rect i) := by
  have hp : c.slotOf i = c.n ∨ (c.slotOf i < c.n ∧ (c.box (c.slotOf i)).kind = Kind.composite) := by
    rcases c.slotOf_cases hc hi with h | ⟨hlt, hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hk⟩
  have hfit := c.frame_fits hc hp
  rw [c.rect_eq hc hi]
  exact childRect_contained (c.parentTrack_wf hc _) hc.gapX hc.gapY
    (c.slotFor_spec (c.mem_children hc hi)).1 hfit.1 hfit.2

theorem Ctx.rect_disjoint {c : Ctx} (hc : c.Wf) {i j : Nat} (hi : i < c.n) (hj : j < c.n)
    (hne : i ≠ j) (hs : c.slotOf i = c.slotOf j) : Disjoint (c.rect i) (c.rect j) := by
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
  · exact childRect_disjoint hw hc.gapX hc.gapY si.1 sj.1 h
  · exact (Disjoint.comm _ _).mp (childRect_disjoint hw hc.gapX hc.gapY sj.1 si.1 h)

/-- The cells of one group are pairwise disjoint (`block_cells_disjoint`). -/
theorem block_cells_disjoint {c : Ctx} (hc : c.Wf) {i j : Nat} (hi : i < c.n) (hj : j < c.n)
    (hne : i ≠ j) (hs : c.slotOf i = c.slotOf j) : Disjoint (c.rect i) (c.rect j) :=
  Ctx.rect_disjoint hc hi hj hne hs

/-- A child of span `s` is `U * s + gap * (s - 1)` wide (`block_span_honoured`); the gap is
`padding` when the diagram has no edge (grid-10, grid-61). -/
theorem block_span_honoured {c : Ctx} (hc : c.Wf) {i : Nat} (hi : i < c.n) :
    (c.rect i).w = (c.parentTrack (c.slotOf i)).unit * (slotFor (c.parentTrack (c.slotOf i)) i).eff +
      c.gapX * ((slotFor (c.parentTrack (c.slotOf i)) i).eff - 1) := by
  rw [c.rect_eq hc hi]
  rfl

/-- Every placed child lies within the columns of its group (`block_within_columns`). -/
theorem block_within_columns {c : Ctx} (hc : c.Wf) {i : Nat} (hi : i < c.n) :
    (slotFor (c.parentTrack (c.slotOf i)) i).col + (slotFor (c.parentTrack (c.slotOf i)) i).eff ≤
        (c.parentTrack (c.slotOf i)).ncols ∧
      (0 < c.columnsOf (c.slotOf i) →
        (slotFor (c.parentTrack (c.slotOf i)) i).col + (slotFor (c.parentTrack (c.slotOf i)) i).eff ≤
          c.columnsOf (c.slotOf i)) := by
  have hw := c.parentTrack_wf hc (c.slotOf i)
  have hs := (c.slotFor_spec (c.mem_children hc hi)).1
  exact ⟨hw.ncols _ hs, (hw.props _ hs).2.2.2.1⟩

/-- The children of a group lie inside it, at every nesting level (`block_children_inside_group`). -/
theorem block_children_inside_group {c : Ctx} (hc : c.Wf) {i : Nat} (hi : i < c.n) :
    (c.frame (c.slotOf i)).Contained (c.rect i) :=
  Ctx.rect_contained hc hi

/-- A successful family result keeps precisely the rectangles constructed by the
well-formed track context; routing and label placement do not rewrite them. -/
theorem block_rects {inp : GInput} {p : GParams} {res : GLayout}
    (h : block inp p = .ok res) :
    let c : Ctx := ⟨inp, (gapsOf inp p.padding).1, (gapsOf inp p.padding).2⟩
    c.Wf ∧ res.rects = (List.range c.n).map c.rect := by
  by_cases hv : inp.valid p.padding = true
  · refine ⟨Ctx.wf_of_valid hv, ?_⟩
    simp only [block, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · injection h with he
              subst res
              rfl
  · have hf : inp.valid p.padding = false := by
      cases he : inp.valid p.padding
      · rfl
      · exact False.elim (hv he)
    simp [block, hf] at h

theorem mapM_ok_pairs {α β ε : Type} {f : α → Except ε β} :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      xs.length = ys.length ∧ ∀ a b, (a, b) ∈ xs.zip ys → f a = .ok b := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    simp only [List.mapM_nil, except_pure, Except.ok.injEq] at h
    subst ys
    exact ⟨rfl, by simp⟩
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons] at h
    cases hf : f x with
    | error err => simp [hf] at h
    | ok y =>
      cases ht : xs.mapM f with
      | error err => simp [hf, ht] at h
      | ok tail =>
        simp [hf, ht] at h
        subst ys
        have hp := ih tail ht
        refine ⟨by simp only [List.length_cons, hp.1], ?_⟩
        intro a b hab
        simp only [List.zip_cons_cons, List.mem_cons] at hab
        rcases hab with heq | hmem
        · have heq' := Prod.mk.inj heq
          cases heq'.1
          cases heq'.2
          exact hf
        · exact hp.2 a b hmem

theorem spaceBoxesNonexclusive_spec {m : Model} (h : spaceBoxesNonexclusive m = true)
    {b : ModelBox} (hb : b ∈ m.boxes) (hrole : b.role = .node)
    (hshape : (Spec.parse b.shape).type = "space") : b.exclusive = false := by
  have hrow := List.all_eq_true.mp h b hb
  simpa [hrole, hshape] using hrow

theorem BlockPlan.rejects_exclusive_space {m : Model}
    (h : spaceBoxesNonexclusive m = false) : BlockPlan.build m = .error .domain := by
  unfold BlockPlan.build
  cases rootOk m <;> simp [h]

theorem BlockPlan.success_spaces {m : Model} {pl : BlockPlan}
    (h : BlockPlan.build m = .ok pl) : spaceBoxesNonexclusive m = true := by
  cases hs : spaceBoxesNonexclusive m with
  | false =>
    rw [BlockPlan.rejects_exclusive_space hs] at h
    cases h
  | true => rfl

theorem BlockPlan.success_model {m : Model} {pl : BlockPlan}
    (h : BlockPlan.build m = .ok pl) : pl.m = m := by
  unfold BlockPlan.build at h
  dsimp only [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map,
    MonadExceptOf.throw] at h
  repeat' first
    | (split at h)
    | (cases h)
  all_goals rfl

theorem BlockPlan.success_specs {m : Model} {pl : BlockPlan}
    (h : BlockPlan.build m = .ok pl) :
    pl.specs = m.boxes.map (fun b => Spec.parse b.shape) := by
  unfold BlockPlan.build at h
  dsimp only [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map,
    MonadExceptOf.throw] at h
  repeat' first
    | (split at h)
    | (cases h)
  all_goals rfl

theorem BlockPlan.success_boxes {m : Model} {pl : BlockPlan}
    (h : BlockPlan.build m = .ok pl) :
    (List.range (m.boxes.length - 1)).mapM
      (fun k => gridBox m pl.consts pl.padding pl.specs pl.boxLines (k + 1)) =
        .ok pl.input.boxes := by
  unfold BlockPlan.build at h
  dsimp only [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map,
    MonadExceptOf.throw] at h
  repeat' first
    | (split at h)
    | (cases h)
  all_goals assumption

theorem BlockPlan.success_edges {m : Model} {pl : BlockPlan}
    (h : BlockPlan.build m = .ok pl) :
    m.routes.mapM (gridEdge m pl.consts pl.labelLines) = .ok pl.input.edges := by
  unfold BlockPlan.build at h
  dsimp only [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map,
    MonadExceptOf.throw] at h
  repeat' first
    | (split at h)
    | (cases h)
  all_goals assumption

theorem BlockPlan.success_box_count {m : Model} {pl : BlockPlan}
    (h : BlockPlan.build m = .ok pl) : pl.input.boxes.length = m.boxes.length - 1 := by
  have hp := (mapM_ok_pairs _ _ (BlockPlan.success_boxes h)).1
  simpa only [List.length_range] using hp.symm

theorem BlockPlan.success_edge_count {m : Model} {pl : BlockPlan}
    (h : BlockPlan.build m = .ok pl) : pl.input.edges.length = m.routes.length :=
  (mapM_ok_pairs _ _ (BlockPlan.success_edges h)).1.symm

theorem BlockPlan.success_root {m : Model} {pl : BlockPlan}
    (h : BlockPlan.build m = .ok pl) : rootOk m = true := by
  cases hr : rootOk m with
  | false => simp [BlockPlan.build, hr] at h
  | true => rfl

theorem BlockPlan.success_nonempty {m : Model} {pl : BlockPlan}
    (h : BlockPlan.build m = .ok pl) : 0 < m.boxes.length := by
  have hr := BlockPlan.success_root h
  cases hb : m.boxes with
  | nil => simp [rootOk, hb] at hr
  | cons b rest => simp

theorem foldlM_preserves {α β ε : Type} (step : β → α → Except ε β) (P : β → Prop)
    (hstep : ∀ st a next, P st → step st a = .ok next → P next) :
    ∀ (xs : List α) (st out : β), P st → xs.foldlM step st = .ok out → P out := by
  intro xs
  induction xs with
  | nil =>
    intro st out hp h
    simp only [List.foldlM_nil, except_pure, Except.ok.injEq] at h
    subst out
    exact hp
  | cons a xs ih =>
    intro st out hp h
    simp only [List.foldlM_cons] at h
    cases hs : step st a with
    | error err => simp [hs] at h
    | ok next =>
      simp only [hs, except_bind_ok] at h
      exact ih next out (hstep st a next hp hs) h

theorem gridBox_kind {m : Model} {consts : BlockConsts} {padding : Int}
    {specs : List Spec} {lines : List (List Measure.Line)} {i : Nat} {out : GBox}
    (h : gridBox m consts padding specs lines i = .ok out) :
    ∃ b, m.boxes[i]? = some b ∧ out.kind =
      (if b.role == .group then Kind.composite
       else if (specs.getD i default).type == "space" then Kind.space else Kind.leaf) := by
  cases hb : m.boxes[i]? with
  | none => simp [gridBox, hb] at h
  | some b =>
    refine ⟨b, rfl, ?_⟩
    cases hp : indexOf m.boxes b.parent with
    | none => simp [gridBox, hb, hp] at h
    | some parent =>
      by_cases he : b.parent = ""
      · have hp' : indexOf m.boxes "" = some parent := by simpa only [he] using hp
        simp only [gridBox, hb, hp', he, beq_self_eq_true, ↓reduceIte,
          except_pure, except_throw, except_bind_ok, except_bind_error] at h
        cases h
      · have hout : out = ⟨(parent : Int) - 1,
            (if b.role == .group then Kind.composite
             else if (specs.getD i default).type == "space" then Kind.space else Kind.leaf),
            (specs.getD i default).span, (specs.getD i default).columns,
            (if (if b.role == .group then Kind.composite
                 else if (specs.getD i default).type == "space" then Kind.space else Kind.leaf) == Kind.leaf then
              ⟨min ((extentOf consts.lineHeight (lines.getD i [])).w + 2 * padding) COORD_LIMIT,
               min ((extentOf consts.lineHeight (lines.getD i [])).h + 2 * padding) COORD_LIMIT⟩
             else default)⟩ := by
          simpa only [gridBox, hb, hp, he, beq_iff_eq, ite_false,
            except_pure, except_bind_ok, except_map_ok, Except.ok.injEq] using h.symm
        rw [hout]

theorem indexOf_mem {boxes : List ModelBox} {id : String} {i : Nat}
    (h : indexOf boxes id = some i) :
    ∃ b, (b, i) ∈ boxes.zipIdx ∧ b.id = id := by
  unfold indexOf at h
  cases hf : boxes.zipIdx.reverse.find? (fun (b, _) => b.id == id) with
  | none => simp [hf] at h
  | some pair =>
    obtain ⟨b, j⟩ := pair
    have hj : j = i := Option.some.inj (by simpa [hf] using h)
    subst j
    have hmem := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    exact ⟨b, List.mem_reverse.mp hmem, by simpa using hpred⟩

theorem indexOf_lt {boxes : List ModelBox} {id : String} {i : Nat}
    (h : indexOf boxes id = some i) : i < boxes.length := by
  obtain ⟨b, hb, _⟩ := indexOf_mem h
  exact (List.mem_zipIdx' hb).1

theorem gridBox_parent {m : Model} {consts : BlockConsts} {padding : Int}
    {specs : List Spec} {lines : List (List Measure.Line)} {i : Nat} {out : GBox}
    (h : gridBox m consts padding specs lines i = .ok out) :
    ∃ b parent, m.boxes[i]? = some b ∧ indexOf m.boxes b.parent = some parent ∧
      b.parent ≠ "" ∧ out.parent = (parent : Int) - 1 := by
  cases hb : m.boxes[i]? with
  | none => simp [gridBox, hb] at h
  | some b =>
    cases hp : indexOf m.boxes b.parent with
    | none => simp [gridBox, hb, hp] at h
    | some parent =>
      by_cases he : b.parent = ""
      · have hp' : indexOf m.boxes "" = some parent := by simpa only [he] using hp
        simp only [gridBox, hb, hp', he, beq_self_eq_true, ↓reduceIte,
          except_pure, except_throw, except_bind_ok, except_bind_error] at h
        cases h
      · refine ⟨b, parent, rfl, hp, he, ?_⟩
        simp [gridBox, hb, hp, he] at h
        subst out
        rfl

theorem zip_getD {α β : Type} (xs : List α) (ys : List β) (a : α) (b : β)
    {i : Nat} (hx : i < xs.length) (hy : i < ys.length) :
    (xs.getD i a, ys.getD i b) ∈ xs.zip ys := by
  apply List.mem_iff_getElem?.mpr
  refine ⟨i, ?_⟩
  apply List.getElem?_zip_eq_some.mpr
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx,
    List.getElem?_eq_getElem hy, Option.getD_some]
  exact ⟨True.intro, True.intro⟩

theorem BlockPlan.gridBox_at {m : Model} {pl : BlockPlan}
    (h : BlockPlan.build m = .ok pl) {i : Nat} (hi : i < pl.input.boxes.length) :
    gridBox m pl.consts pl.padding pl.specs pl.boxLines (i + 1) =
      .ok (pl.input.boxes.getD i default) := by
  have hcount := BlockPlan.success_box_count h
  have hmap := BlockPlan.success_boxes h
  have hpair := zip_getD (List.range (m.boxes.length - 1)) pl.input.boxes 0 default
    (by simpa only [List.length_range, ← hcount] using hi) hi
  have hrow := (mapM_ok_pairs _ _ hmap).2 _ _ hpair
  have hindex : (List.range (m.boxes.length - 1)).getD i 0 = i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_range (by omega)]
    rfl
  simpa only [hindex] using hrow

theorem BlockPlan.exclusive_leaf {m : Model} {pl : BlockPlan}
    (h : BlockPlan.build m = .ok pl) (hwf : WellFormed m)
    {i : Nat} (hi : i < pl.input.boxes.length)
    (hex : (m.boxes.getD (i + 1) default).exclusive = true) :
    (pl.input.boxes.getD i default).kind = Kind.leaf := by
  obtain ⟨b, hb, hkind⟩ := gridBox_kind (BlockPlan.gridBox_at h hi)
  have hb' : m.boxes.getD (i + 1) default = b := by
    rw [List.getD_eq_getElem?_getD, hb]
    rfl
  have hbmem : b ∈ m.boxes := List.mem_of_getElem? hb
  have hgroup : b.role ≠ .group := by
    intro hg
    have hall : (m.boxes.all fun b => b.role != .group || !b.exclusive) = true := by
      unfold WellFormed modelWellFormed at hwf
      simp only [Bool.and_eq_true] at hwf
      exact hwf.2
    have hp := List.all_eq_true.mp hall b hbmem
    have hexb : b.exclusive = true := by rw [← hb']; exact hex
    simp [hg, hexb] at hp
  have hnode : b.role = .node := by
    cases hr : b.role with
    | node => rfl
    | group => exact False.elim (hgroup hr)
  have hspace : (Spec.parse b.shape).type ≠ "space" := by
    intro hs
    have hn := spaceBoxesNonexclusive_spec (BlockPlan.success_spaces h) hbmem hnode hs
    rw [← hb', hex] at hn
    contradiction
  have hspec : pl.specs.getD (i + 1) default = Spec.parse b.shape := by
    rw [BlockPlan.success_specs h, List.getD_eq_getElem?_getD, List.getElem?_map, hb]
    rfl
  rw [hspec] at hkind
  simpa only [beq_iff_eq, hgroup, hspace, ↓reduceIte] using hkind

theorem BlockPlan.gridEdge_pair {m : Model} {pl : BlockPlan}
    (h : BlockPlan.build m = .ok pl) {r : ModelRoute} {e : Edge}
    (hp : (r, e) ∈ m.routes.zip pl.input.edges) :
    gridEdge m pl.consts pl.labelLines r = .ok e :=
  (mapM_ok_pairs _ _ (BlockPlan.success_edges h)).2 r e hp

theorem gridEdge_endpoints {m : Model} {consts : BlockConsts}
    {lines : List (List Measure.Line)} {r : ModelRoute} {e : Edge}
    (h : gridEdge m consts lines r = .ok e) :
    ∃ src dst, indexOf m.boxes r.fromId = some src ∧
      indexOf m.boxes r.toId = some dst ∧ src ≠ 0 ∧ dst ≠ 0 ∧
      e.fromBox = src - 1 ∧ e.toBox = dst - 1 := by
  cases hs : indexOf m.boxes r.fromId with
  | none => simp [gridEdge, hs] at h
  | some src =>
    cases ht : indexOf m.boxes r.toId with
    | none => simp [gridEdge, hs, ht] at h
    | some dst =>
      by_cases hs0 : src = 0
      · simp [gridEdge, hs, hs0] at h
      · by_cases ht0 : dst = 0
        · simp [gridEdge, hs, ht, ht0] at h
        · refine ⟨src, dst, rfl, rfl, hs0, ht0, ?_, ?_⟩
          · simp [gridEdge, hs, ht, hs0, ht0] at h
            subst e
            rfl
          · simp [gridEdge, hs, ht, hs0, ht0] at h
            subst e
            rfl

theorem gridBox_same_parent {m : Model} {consts : BlockConsts} {padding : Int}
    {specs : List Spec} {lines : List (List Measure.Line)} {i j : Nat} {a b : GBox}
    (ha : gridBox m consts padding specs lines i = .ok a)
    (hb : gridBox m consts padding specs lines j = .ok b)
    (hparent : (m.boxes.getD i default).parent = (m.boxes.getD j default).parent) :
    a.parent = b.parent := by
  obtain ⟨ma, pa, hma, hpa, _hna, hara⟩ := gridBox_parent ha
  obtain ⟨mb, pb, hmb, hpb, _hnb, hbrb⟩ := gridBox_parent hb
  have heqa : m.boxes.getD i default = ma := by
    rw [List.getD_eq_getElem?_getD, hma]
    rfl
  have heqb : m.boxes.getD j default = mb := by
    rw [List.getD_eq_getElem?_getD, hmb]
    rfl
  rw [heqa, heqb] at hparent
  rw [hparent, hpb] at hpa
  have hp : pb = pa := Option.some.inj hpa
  rw [hara, hbrb, hp]

theorem BlockPlan.root_nonexclusive {m : Model} {pl : BlockPlan}
    (hb : BlockPlan.build m = .ok pl) (hwf : WellFormed m) :
    (m.boxes.getD 0 default).exclusive = false := by
  have hr := BlockPlan.success_root hb
  cases hm : m.boxes with
  | nil => simp [rootOk, hm] at hr
  | cons b rest =>
    have hrole : b.role = .group := by
      simp only [rootOk, hm, List.head?_cons, Bool.and_eq_true, beq_iff_eq] at hr
      exact hr.1.1
    have hall : (m.boxes.all fun b => b.role != .group || !b.exclusive) = true := by
      unfold WellFormed modelWellFormed at hwf
      simp only [Bool.and_eq_true] at hwf
      exact hwf.2
    have hp := List.all_eq_true.mp hall b (by rw [hm]; simp)
    simpa [hm, hrole] using hp
theorem BlockPlan.parent_slot {m : Model} {pl : BlockPlan}
    (hb : BlockPlan.build m = .ok pl) {i : Nat}
    (hi : i < pl.input.boxes.length) :
    ∃ b parent, m.boxes[i + 1]? = some b ∧
      indexOf m.boxes b.parent = some parent ∧ b.parent ≠ "" ∧
      (∀ c : Ctx, c.inp = pl.input →
        c.slotOf i = if parent = 0 then c.n else parent - 1) := by
  obtain ⟨b, parent, hm, hp, hn, hparent⟩ :=
    gridBox_parent (BlockPlan.gridBox_at hb hi)
  refine ⟨b, parent, hm, hp, hn, ?_⟩
  intro c hc
  have he : (c.box i).parent = (parent : Int) - 1 := by
    simpa only [Ctx.box, hc] using hparent
  unfold Ctx.slotOf
  rw [he]
  by_cases hz : parent = 0
  · simp [hz]
  · have hn : ¬ (parent : Int) - 1 < 0 := by omega
    simp only [hn, ↓reduceIte, hz]
    omega

private theorem dedup_length_le : ∀ l : List String, l.eraseDups.length ≤ l.length
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    have h1 := dedup_length_le (as.filter fun b => !b == a)
    have h2 := List.length_filter_le (fun b => !b == a) as
    simp only [List.length_cons]
    omega
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private theorem nodup_of_dedup_length :
    ∀ l : List String, l.eraseDups.length = l.length → l.Nodup
  | [] => fun _ => List.nodup_nil
  | a :: as => by
    intro h
    rw [List.eraseDups_cons] at h
    simp only [List.length_cons] at h
    have h1 := dedup_length_le (as.filter fun b => !b == a)
    have h2 := List.length_filter_le (fun b => !b == a) as
    have hf : (as.filter fun b => !b == a).length = as.length := by omega
    have hall : ∀ b ∈ as, (!b == a) = true := List.length_filter_eq_length_iff.mp hf
    have hfe : (as.filter fun b => !b == a) = as := List.filter_eq_self.mpr hall
    have hn := nodup_of_dedup_length (as.filter fun b => !b == a) (by omega)
    rw [hfe] at hn
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, hn⟩
    have := hall a hmem
    simp at this
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem model_box_ids_nodup {m : Model} (h : WellFormed m) :
    (m.boxes.map (·.id)).Nodup := by
  unfold WellFormed modelWellFormed at h
  simp only [Bool.and_eq_true] at h
  have hu := h.1.1.1.1.1.1
  change ((m.boxes.map (·.id)).eraseDups.length == (m.boxes.map (·.id)).length) = true at hu
  exact nodup_of_dedup_length _ (beq_iff_eq.mp hu)

theorem model_box_index_unique {m : Model} (hwf : WellFormed m) {i j : Nat}
    (hi : i < m.boxes.length) (hj : j < m.boxes.length)
    (he : (m.boxes.getD i default).id = (m.boxes.getD j default).id) : i = j := by
  apply (model_box_ids_nodup hwf).eq_of_getElem_eq
    (by simpa only [List.length_map] using hi)
    (by simpa only [List.length_map] using hj)
  simpa only [List.getElem_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.getD_some] using he

theorem indexOf_id {boxes : List ModelBox} {id : String} {i : Nat}
    (h : indexOf boxes id = some i) : (boxes.getD i default).id = id := by
  obtain ⟨b, hb, hid⟩ := indexOf_mem h
  obtain ⟨hi, he⟩ := List.mem_zipIdx' hb
  have hd : boxes.getD i default = b := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact he.symm
  rw [hd]
  exact hid

theorem BlockPlan.root_parent {m : Model} {pl : BlockPlan}
    (hb : BlockPlan.build m = .ok pl) : (m.boxes.getD 0 default).parent = "" := by
  have hr := BlockPlan.success_root hb
  cases hm : m.boxes with
  | nil => simp [rootOk, hm] at hr
  | cons b bs =>
    simp only [rootOk, hm, List.head?_cons, Bool.and_eq_true, beq_iff_eq] at hr
    simpa only [hm, List.getD_cons_zero] using hr.1.2

end Grid
end Elegant

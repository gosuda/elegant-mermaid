import Elegant.Kinds.Kanban
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant.GridKanban

/-- Section frames use a fixed width and the native section-gap pitch. -/
def column (padding width gap height : Int) (index : Nat) : Rect :=
  ⟨padding + Int.ofNat index * (width + gap), padding, width, height⟩

/-- Cards advance their section cursor by their height and the card gap. -/
def nextCard (r : Rect) (gap height : Int) : Rect :=
  ⟨r.x, r.y + r.h + gap, r.w, height⟩

theorem nextCard_y (r : Rect) (gap height : Int) :
    (nextCard r gap height).y = r.y + r.h + gap := rfl

theorem kanban_columns_disjoint (padding width gap height : Int) (i j : Nat)
    (hw : 0 ≤ width) (hg : 0 ≤ gap) (hij : i < j) :
    Disjoint (column padding width gap height i) (column padding width gap height j) := by
  have hn : (i : Int) + 1 ≤ (j : Int) := by omega
  have hp : 0 ≤ width + gap := by omega
  have hm := Int.mul_le_mul_of_nonneg_right hn hp
  have hsep : padding + Int.ofNat i * (width + gap) + width ≤
      padding + Int.ofNat j * (width + gap) := by
    rw [Int.add_mul, Int.one_mul] at hm
    change padding + (i : Int) * (width + gap) + width ≤
      padding + (j : Int) * (width + gap)
    omega
  intro h
  have hx := h.1
  change max (padding + Int.ofNat i * (width + gap))
      (padding + Int.ofNat j * (width + gap)) <
    min (padding + Int.ofNat i * (width + gap) + width)
      (padding + Int.ofNat j * (width + gap) + width) at hx
  have hl := Int.le_max_right (padding + Int.ofNat i * (width + gap))
    (padding + Int.ofNat j * (width + gap))
  have hr := Int.min_le_left (padding + Int.ofNat i * (width + gap) + width)
    (padding + Int.ofNat j * (width + gap) + width)
  omega

/-- The native frame formula contains the last card whenever its fixed residual
clearance covers the header minimum. Earlier cards have smaller cursor ends. -/
theorem column_contains_card_bounds (pad width inset cardWidth band minimum gutter
    minHeight cursor cardHeight : Int)
    (hi : 0 ≤ inset) (hw : inset + cardWidth ≤ width)
    (hc : 0 ≤ cursor) (hh : 0 ≤ band)
    (clearance : minimum ≤ Int.fdiv gutter 2 + 3 * gutter) :
    Rect.Contained
      ⟨pad, pad, width,
        max (cursor + cardHeight + Int.fdiv gutter 2 + 3 * gutter) minHeight +
          band - minimum⟩
      ⟨pad + inset, pad + band + cursor, cardWidth, cardHeight⟩ := by
  unfold Rect.Contained
  simp only
  have hm := Int.le_max_left
    (cursor + cardHeight + Int.fdiv gutter 2 + 3 * gutter) minHeight
  omega

theorem cursor_get_after (cursors : List Int) (i j : Nat) (height gap band : Int) :
    (Kinds.Kanban.advanceCursor cursors i height gap band).getD j band =
      if i = j ∧ i < cursors.length then cursors.getD i band + height + gap
      else cursors.getD j band := by
  unfold Kinds.Kanban.advanceCursor
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases heq : i = j
  · subst j
    by_cases hi : i < cursors.length <;> simp [hi]
  · simp [heq]

theorem cursor_length_preserved (cursors : List Int) (i : Nat) (height gap band : Int) :
    (Kinds.Kanban.advanceCursor cursors i height gap band).length = cursors.length := by
  simp [Kinds.Kanban.advanceCursor]

/-- Once a card has been placed, subsequent cards cannot move its column cursor
back through its bottom edge. This includes interleaved cards of other columns. -/
theorem cursor_monotone (cursors : List Int) (i j : Nat) (height gap band : Int)
    (hh : 0 ≤ height) (hg : 0 ≤ gap) :
    cursors.getD j band ≤
      (Kinds.Kanban.advanceCursor cursors i height gap band).getD j band := by
  rw [cursor_get_after]
  split
  · rename_i h
    rcases h with ⟨rfl, _⟩
    omega
  · exact Int.le_refl _

theorem cursor_lower_bound (cursors : List Int) (i : Nat) (height gap band : Int)
    (hinv : ∀ j, band ≤ cursors.getD j band)
    (hh : 0 ≤ height) (hg : 0 ≤ gap) :
    ∀ j, band ≤ (Kinds.Kanban.advanceCursor cursors i height gap band).getD j band := by
  intro j
  exact Int.le_trans (hinv j) (cursor_monotone cursors i j height gap band hh hg)

theorem cursor_owner_step (cursors : List Int) (i : Nat) (height gap band : Int)
    (hi : i < cursors.length) :
    (Kinds.Kanban.advanceCursor cursors i height gap band).getD i band =
      cursors.getD i band + height + gap := by
  rw [cursor_get_after]
  simp [hi]

def advanceCards (cards : List (Nat × Int)) (gap band : Int) (cursors : List Int) : List Int :=
  cards.foldl (fun cs card => Kinds.Kanban.advanceCursor cs card.1 card.2 gap band) cursors

theorem cursor_fold_monotone (cards : List (Nat × Int)) (gap band : Int)
    (cursors : List Int) (hg : 0 ≤ gap)
    (hh : ∀ card ∈ cards, 0 ≤ card.2) (j : Nat) :
    cursors.getD j band ≤ (advanceCards cards gap band cursors).getD j band := by
  induction cards generalizing cursors with
  | nil => exact Int.le_refl _
  | cons card cards ih =>
    have hcard := hh card (by simp)
    have hrest : ∀ c ∈ cards, 0 ≤ c.2 := by
      intro c hc
      exact hh c (by simp [hc])
    exact Int.le_trans
      (cursor_monotone cursors card.1 j card.2 gap band hcard hg)
      (ih (Kinds.Kanban.advanceCursor cursors card.1 card.2 gap band) hrest)

theorem cursor_fold_length (cards : List (Nat × Int)) (gap band : Int)
    (cursors : List Int) :
    (advanceCards cards gap band cursors).length = cursors.length := by
  induction cards generalizing cursors with
  | nil => rfl
  | cons card cards ih =>
    simpa [advanceCards, List.foldl_cons, Kinds.Kanban.advanceCursor] using
      ih (Kinds.Kanban.advanceCursor cursors card.1 card.2 gap band)

theorem kanban_cards_disjoint_after_fold (between : List (Nat × Int))
    (cursors : List Int) (pad width gap cardWidth band firstHeight nextHeight : Int)
    (owner : Nat) (ho : owner < cursors.length)
    (hg : 0 ≤ gap) (_hh : 0 ≤ firstHeight)
    (hbetween : ∀ card ∈ between, 0 ≤ card.2) :
    Disjoint
      (Kinds.Kanban.cardRect pad width gap cardWidth owner
        (cursors.getD owner band) firstHeight)
      (Kinds.Kanban.cardRect pad width gap cardWidth owner
        ((advanceCards between gap band
          (Kinds.Kanban.advanceCursor cursors owner firstHeight gap band)).getD owner band)
        nextHeight) := by
  have hstep := cursor_owner_step cursors owner firstHeight gap band ho
  have hmono := cursor_fold_monotone between gap band
    (Kinds.Kanban.advanceCursor cursors owner firstHeight gap band) hg hbetween owner
  intro h
  have hy := h.2
  let after := (advanceCards between gap band
    (Kinds.Kanban.advanceCursor cursors owner firstHeight gap band)).getD owner band
  change max (pad + cursors.getD owner band) (pad + after) <
    min (pad + cursors.getD owner band + firstHeight) (pad + after + nextHeight) at hy
  have hl := Int.le_max_right (pad + cursors.getD owner band) (pad + after)
  have hr := Int.min_le_left (pad + cursors.getD owner band + firstHeight) (pad + after + nextHeight)
  dsimp [after] at *
  omega

theorem cursor_fold_lower_bound (cards : List (Nat × Int)) (gap band : Int)
    (cursors : List Int) (hg : 0 ≤ gap)
    (hh : ∀ card ∈ cards, 0 ≤ card.2)
    (hinv : ∀ j, band ≤ cursors.getD j band) :
    ∀ j, band ≤ (advanceCards cards gap band cursors).getD j band := by
  intro j
  exact Int.le_trans (hinv j) (cursor_fold_monotone cards gap band cursors hg hh j)

theorem kanban_card_inside_column_horizontal (pad width gap cardWidth cursor height frameHeight : Int)
    (owner : Nat) (_hw : 0 ≤ cardWidth) (hwidth : cardWidth ≤ width) :
    let r := Kinds.Kanban.cardRect pad width gap cardWidth owner cursor height
    let frame := column pad width gap frameHeight owner
    frame.x ≤ r.x ∧ r.x + r.w ≤ frame.x + frame.w := by
  dsimp [Kinds.Kanban.cardRect, column]
  have hd : 0 ≤ width - cardWidth := by omega
  have hn : 0 ≤ Int.fdiv (width - cardWidth) 2 :=
    Int.fdiv_nonneg hd (by decide)
  have hdiv : Int.fdiv (width - cardWidth) 2 ≤ width - cardWidth := by
    have hq := Int.mul_fdiv_add_fmod (width - cardWidth) 2
    have hr := Int.fmod_nonneg_of_pos (width - cardWidth) (by decide : (0 : Int) < 2)
    omega
  omega

theorem kanban_card_inside_final_column (pad width gap cardWidth gutter band minimum
    minHeight oldCursor finalCursor height : Int) (owner : Nat)
    (hw : 0 ≤ cardWidth) (hwidth : cardWidth ≤ width)
    (htop : 0 ≤ oldCursor)
    (hend : oldCursor + height + gap ≤ finalCursor)
    (hclear : minimum ≤ Int.fdiv gutter 2 + 3 * gutter) :
    Rect.Contained
      (Kinds.Kanban.sectionRect pad width gap gutter band minimum minHeight finalCursor owner)
      (Kinds.Kanban.cardRect pad width gap cardWidth owner oldCursor height) := by
  have hhoriz := kanban_card_inside_column_horizontal pad width gap cardWidth
    oldCursor height 0 owner hw hwidth
  have hm := Int.le_max_left
    (finalCursor - band - gap + Int.fdiv gutter 2 + 3 * gutter) minHeight
  dsimp [column, Kinds.Kanban.cardRect] at hhoriz
  dsimp [Rect.Contained, Kinds.Kanban.sectionRect, Kinds.Kanban.cardRect]
  omega

theorem kanban_native_header_clearance (p : Profile) :
    LayoutConst.kanban_label_band_min.get p ≤
      Int.fdiv (LayoutConst.kanban_gutter.get p) 2 +
        3 * LayoutConst.kanban_gutter.get p := by
  cases p <;> decide

theorem kanban_columns_disjoint_final (pad width gap gutter band minimum minHeight
    cursorI cursorJ : Int) (i j : Nat)
    (hw : 0 ≤ width) (hg : 0 ≤ gap) (hij : i < j) :
    Disjoint
      (Kinds.Kanban.sectionRect pad width gap gutter band minimum minHeight cursorI i)
      (Kinds.Kanban.sectionRect pad width gap gutter band minimum minHeight cursorJ j) := by
  have hn : (i : Int) + 1 ≤ (j : Int) := by omega
  have hp : 0 ≤ width + gap := by omega
  have hm := Int.mul_le_mul_of_nonneg_right hn hp
  have hsep : pad + Int.ofNat i * (width + gap) + width ≤
      pad + Int.ofNat j * (width + gap) := by
    rw [Int.add_mul, Int.one_mul] at hm
    change pad + (i : Int) * (width + gap) + width ≤
      pad + (j : Int) * (width + gap)
    omega
  intro h
  have hx := h.1
  change max (pad + Int.ofNat i * (width + gap))
      (pad + Int.ofNat j * (width + gap)) <
    min (pad + Int.ofNat i * (width + gap) + width)
      (pad + Int.ofNat j * (width + gap) + width) at hx
  have hl := Int.le_max_right (pad + Int.ofNat i * (width + gap))
    (pad + Int.ofNat j * (width + gap))
  have hr := Int.min_le_left (pad + Int.ofNat i * (width + gap) + width)
    (pad + Int.ofNat j * (width + gap) + width)
  omega

theorem disjoint_contained_right (a b inner : Rect)
    (hd : Disjoint a b) (hc : b.Contained inner) : Disjoint a inner := by
  unfold Disjoint Rect.meetsInterior Rect.Contained at *
  omega

theorem kanban_foreign_card_clearance (pad width gap gutter band minimum minHeight
    cursorI cursorJ : Int) (i j : Nat) (card : Rect)
    (hw : 0 ≤ width) (hg : 0 ≤ gap) (hij : i < j)
    (hc : (Kinds.Kanban.sectionRect pad width gap gutter band minimum minHeight cursorJ j).Contained card) :
    Disjoint
      (Kinds.Kanban.sectionRect pad width gap gutter band minimum minHeight cursorI i) card :=
  disjoint_contained_right _ _ _ (kanban_columns_disjoint_final
    pad width gap gutter band minimum minHeight cursorI cursorJ i j hw hg hij) hc

theorem assemble_routes_empty (m : Model) (canvas : Size) (placed : List (String × Rect))
    (groups : List Group) :
    (Kinds.Kanban.assemble m canvas placed groups).routes = [] := rfl

theorem assemble_labels_empty (m : Model) (canvas : Size) (placed : List (String × Rect))
    (groups : List Group) :
    (Kinds.Kanban.assemble m canvas placed groups).labels = [] := rfl

theorem assemble_relational_clauses (m : Model) (canvas : Size)
    (placed : List (String × Rect)) (groups : List Group) :
    let d := (Kinds.Kanban.assemble m canvas placed groups).layoutDump
    Validator.C4 d ∧ Validator.C5 d ∧ Validator.C6 d ∧ Validator.C7 d ∧ Validator.C8b d := by
  simp [Kinds.Kanban.assemble, Scene.layoutDump, Validator.C4, Validator.C5,
    Validator.C6, Validator.C7, Validator.C8b]

theorem assemble_valid (m : Model) (canvas : Size)
    (placed : List (String × Rect)) (groups : List Group)
    (hcanvas : Validator.C1 (Kinds.Kanban.assemble m canvas placed groups).layoutDump)
    (hsiblings : Validator.C2 (Kinds.Kanban.assemble m canvas placed groups).layoutDump)
    (hparent : Validator.C3 (Kinds.Kanban.assemble m canvas placed groups).layoutDump)
    (hforeign : Validator.C8a (Kinds.Kanban.assemble m canvas placed groups).layoutDump) :
    HardConstraints (Kinds.Kanban.assemble m canvas placed groups).layoutDump := by
  obtain ⟨h4, h5, h6, h7, h8b⟩ := assemble_relational_clauses m canvas placed groups
  exact ⟨hcanvas, hsiblings, hparent, h4, h5, h6, h7, hforeign, h8b⟩

structure CardWalk where
  cursors : List Int
  placed : List (Nat × Rect)

def CardWalk.step (w : CardWalk) (pad width gap cardWidth band : Int)
    (owner : Nat) (height : Int) : CardWalk :=
  { cursors := Kinds.Kanban.advanceCursor w.cursors owner height gap band
    placed := (owner, Kinds.Kanban.cardRect pad width gap cardWidth owner
      (w.cursors.getD owner band) height) :: w.placed }

def CardInvariant (pad gap band : Int) (w : CardWalk) : Prop :=
  (∀ j, band ≤ w.cursors.getD j band) ∧
  (∀ old ∈ w.placed, old.1 < w.cursors.length ∧
    pad + band ≤ old.2.y ∧
    old.2.y + old.2.h + gap ≤ pad + w.cursors.getD old.1 band) ∧
  w.placed.Pairwise (fun a b => a.1 = b.1 → Disjoint a.2 b.2)

theorem card_walk_step_preserves (w : CardWalk) (pad width gap cardWidth band : Int)
    (owner : Nat) (height : Int)
    (hinv : CardInvariant pad gap band w)
    (ho : owner < w.cursors.length) (hh : 0 ≤ height) (hg : 0 ≤ gap) :
    CardInvariant pad gap band (w.step pad width gap cardWidth band owner height) := by
  rcases hinv with ⟨hcursor, hold, hpairs⟩
  refine ⟨cursor_lower_bound w.cursors owner height gap band hcursor hh hg, ?_, ?_⟩
  · intro old hmem
    simp only [CardWalk.step, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · refine ⟨?_, ?_, ?_⟩
      · simpa [CardWalk.step, cursor_length_preserved] using ho
      · have hc := hcursor owner
        dsimp [CardWalk.step, Kinds.Kanban.cardRect]
        omega
      · dsimp [CardWalk.step, Kinds.Kanban.cardRect]
        rw [cursor_owner_step _ _ _ _ _ ho]
        omega
    · obtain ⟨hindex, htop, hbottom⟩ := hold old hmem
      refine ⟨?_, htop, ?_⟩
      · simpa [CardWalk.step, cursor_length_preserved] using hindex
      · have hm := cursor_monotone w.cursors owner old.1 height gap band hh hg
        dsimp [CardWalk.step]
        omega
  · apply List.Pairwise.cons
    · intro old hmem heq
      have hbottom := (hold old hmem).2.2
      have howner : old.1 = owner := heq.symm
      rw [howner] at hbottom
      intro h
      have hy := h.2
      change max (pad + w.cursors.getD owner band) old.2.y <
        min (pad + w.cursors.getD owner band + height) (old.2.y + old.2.h) at hy
      have hl := Int.le_max_left (pad + w.cursors.getD owner band) old.2.y
      have hr := Int.min_le_right (pad + w.cursors.getD owner band + height) (old.2.y + old.2.h)
      omega
    · exact hpairs

theorem card_walk_init (count : Nat) (pad gap band : Int) :
    CardInvariant pad gap band ⟨List.replicate count band, []⟩ := by
  refine ⟨?_, ?_, List.Pairwise.nil⟩
  · intro j
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> simp
  · simp

def CardWalk.run (cards : List (Nat × Int)) (pad width gap cardWidth band : Int)
    (w : CardWalk) : CardWalk :=
  cards.foldl (fun state card => state.step pad width gap cardWidth band card.1 card.2) w

theorem card_walk_run_preserves (cards : List (Nat × Int)) (pad width gap cardWidth band : Int)
    (w : CardWalk) (hinv : CardInvariant pad gap band w) (hg : 0 ≤ gap)
    (hcards : ∀ card ∈ cards, card.1 < w.cursors.length ∧ 0 ≤ card.2) :
    CardInvariant pad gap band (w.run cards pad width gap cardWidth band) := by
  induction cards generalizing w with
  | nil => exact hinv
  | cons card cards ih =>
    obtain ⟨ho, hh⟩ := hcards card (by simp)
    have hstep := card_walk_step_preserves w pad width gap cardWidth band card.1 card.2 hinv ho hh hg
    have hrest : ∀ c ∈ cards,
        c.1 < (w.step pad width gap cardWidth band card.1 card.2).cursors.length ∧ 0 ≤ c.2 := by
      intro c hc
      simpa [CardWalk.step, cursor_length_preserved] using hcards c (by simp [hc])
    exact ih (w.step pad width gap cardWidth band card.1 card.2) hstep hrest

def CardHorizontal (pad width gap cardWidth : Int) (w : CardWalk) : Prop :=
  ∀ old ∈ w.placed,
    old.2.x = pad + Int.ofNat old.1 * (width + gap) + Int.fdiv (width - cardWidth) 2 ∧
    old.2.w = cardWidth

theorem card_horizontal_step (w : CardWalk) (pad width gap cardWidth band : Int)
    (owner : Nat) (height : Int) (hinv : CardHorizontal pad width gap cardWidth w) :
    CardHorizontal pad width gap cardWidth (w.step pad width gap cardWidth band owner height) := by
  intro old hmem
  simp only [CardWalk.step, List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  · exact ⟨rfl, rfl⟩
  · exact hinv old hmem

theorem card_horizontal_run (cards : List (Nat × Int)) (pad width gap cardWidth band : Int)
    (w : CardWalk) (hinv : CardHorizontal pad width gap cardWidth w) :
    CardHorizontal pad width gap cardWidth (w.run cards pad width gap cardWidth band) := by
  induction cards generalizing w with
  | nil => exact hinv
  | cons card cards ih =>
    exact ih (w.step pad width gap cardWidth band card.1 card.2)
      (card_horizontal_step w pad width gap cardWidth band card.1 card.2 hinv)

theorem card_walk_all_inside_final_columns (w : CardWalk)
    (pad width gap cardWidth gutter band minimum minHeight : Int)
    (hv : CardInvariant pad gap band w)
    (hx : CardHorizontal pad width gap cardWidth w)
    (hband : 0 ≤ band) (hcw : cardWidth ≤ width)
    (hclear : minimum ≤ Int.fdiv gutter 2 + 3 * gutter) :
    ∀ old ∈ w.placed,
      (Kinds.Kanban.sectionRect pad width gap gutter band minimum minHeight
        (w.cursors.getD old.1 band) old.1).Contained old.2 := by
  intro old hmem
  obtain ⟨_, htop, hbottom⟩ := hv.2.1 old hmem
  obtain ⟨hleft, hwidth⟩ := hx old hmem
  have hd : 0 ≤ width - cardWidth := by omega
  have hn := Int.fdiv_nonneg hd (by decide : (0 : Int) ≤ 2)
  have hq := Int.mul_fdiv_add_fmod (width - cardWidth) 2
  have hr := Int.fmod_nonneg_of_pos (width - cardWidth) (by decide : (0 : Int) < 2)
  have hm := Int.le_max_left
    (w.cursors.getD old.1 band - band - gap + Int.fdiv gutter 2 + 3 * gutter) minHeight
  dsimp [Rect.Contained, Kinds.Kanban.sectionRect]
  change old.2.x = pad + (old.1 : Int) * (width + gap) +
    Int.fdiv (width - cardWidth) 2 at hleft
  omega

theorem kanban_cards_stacked (cards : List (Nat × Int)) (count : Nat)
    (pad width gap cardWidth band : Int) (hg : 0 ≤ gap)
    (hcards : ∀ card ∈ cards, card.1 < count ∧ 0 ≤ card.2) :
    ((CardWalk.run cards pad width gap cardWidth band
      ⟨List.replicate count band, []⟩).placed).Pairwise
        (fun a b => a.1 = b.1 → Disjoint a.2 b.2) := by
  have hs : ∀ card ∈ cards,
      card.1 < (List.replicate count band).length ∧ 0 ≤ card.2 := by
    simpa using hcards
  exact (card_walk_run_preserves cards pad width gap cardWidth band
    ⟨List.replicate count band, []⟩ (card_walk_init count pad gap band) hg hs).2.2

theorem kanban_column_contains_cards (cards : List (Nat × Int)) (count : Nat)
    (pad width gap cardWidth gutter band minimum minHeight : Int)
    (hg : 0 ≤ gap) (hband : 0 ≤ band) (hcw : cardWidth ≤ width)
    (hclear : minimum ≤ Int.fdiv gutter 2 + 3 * gutter)
    (hcards : ∀ card ∈ cards, card.1 < count ∧ 0 ≤ card.2) :
    let final := CardWalk.run cards pad width gap cardWidth band
      ⟨List.replicate count band, []⟩
    ∀ old ∈ final.placed,
      (Kinds.Kanban.sectionRect pad width gap gutter band minimum minHeight
        (final.cursors.getD old.1 band) old.1).Contained old.2 := by
  have hs : ∀ card ∈ cards,
      card.1 < (List.replicate count band).length ∧ 0 ≤ card.2 := by
    simpa using hcards
  have hv := card_walk_run_preserves cards pad width gap cardWidth band
    ⟨List.replicate count band, []⟩ (card_walk_init count pad gap band) hg hs
  have hx : CardHorizontal pad width gap cardWidth
      (CardWalk.run cards pad width gap cardWidth band ⟨List.replicate count band, []⟩) :=
    card_horizontal_run cards pad width gap cardWidth band
      ⟨List.replicate count band, []⟩ (by intro old h; simp at h)
  exact card_walk_all_inside_final_columns _ pad width gap cardWidth gutter band minimum
    minHeight hv hx hband hcw hclear

theorem max_fold_ge_init (values : List Int) (initial : Int) :
    initial ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => exact Int.le_refl _
  | cons value values ih =>
    exact Int.le_trans (Int.le_max_left initial value) (ih (max initial value))

theorem max_fold_ge_member (values : List Int) (initial value : Int) (hmem : value ∈ values) :
    value ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => simp at hmem
  | cons first rest ih =>
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact Int.le_trans (Int.le_max_right initial value)
        (max_fold_ge_init rest (max initial value))
    · exact ih (max initial first) hmem

def canvasFor (frames : List Rect) (padding : Int) : Rect :=
  ⟨0, 0, (frames.map (fun r => r.x + r.w)).foldl max padding + padding,
    (frames.map (fun r => r.y + r.h)).foldl max padding + padding⟩

theorem frames_inside_canvas (frames : List Rect) (padding : Int) (hp : 0 ≤ padding)
    (hn : ∀ frame ∈ frames, 0 ≤ frame.x ∧ 0 ≤ frame.y) :
    ∀ frame ∈ frames, (canvasFor frames padding).Contained frame := by
  intro frame hmem
  have hx := max_fold_ge_member (frames.map (fun r => r.x + r.w)) padding
    (frame.x + frame.w) (List.mem_map.mpr ⟨frame, hmem, rfl⟩)
  have hy := max_fold_ge_member (frames.map (fun r => r.y + r.h)) padding
    (frame.y + frame.h) (List.mem_map.mpr ⟨frame, hmem, rfl⟩)
  obtain ⟨hx0, hy0⟩ := hn frame hmem
  dsimp [canvasFor, Rect.Contained]
  omega

theorem cards_inside_canvas_of_columns (frames : List Rect) (padding : Int) (card frame : Rect)
    (hp : 0 ≤ padding) (hn : ∀ r ∈ frames, 0 ≤ r.x ∧ 0 ≤ r.y)
    (hframe : frame ∈ frames) (hcard : frame.Contained card) :
    (canvasFor frames padding).Contained card :=
  Rect.Contained.trans (frames_inside_canvas frames padding hp hn frame hframe) hcard

theorem assemble_canvas_transfer (m : Model) (canvas : Size)
    (placed : List (String × Rect)) (groups : List Group)
    (hrect : ∀ b ∈ m.boxes, (⟨0, 0, canvas.w, canvas.h⟩ : Rect).Contained
      (Kinds.Kanban.placedRect placed b.id)) :
    Validator.C1 (Kinds.Kanban.assemble m canvas placed groups).layoutDump := by
  intro b hb
  change b ∈ m.boxes.map (Kinds.Kanban.sceneBox placed) at hb
  obtain ⟨original, hm, rfl⟩ := List.mem_map.mp hb
  exact hrect original hm

theorem assemble_siblings_transfer (m : Model) (canvas : Size)
    (placed : List (String × Rect)) (groups : List Group)
    (hrect : ∀ a ∈ m.boxes, ∀ b ∈ m.boxes,
      a.id ≠ b.id → a.exclusive = true → b.exclusive = true → a.parent = b.parent →
      Disjoint (Kinds.Kanban.placedRect placed a.id) (Kinds.Kanban.placedRect placed b.id)) :
    Validator.C2 (Kinds.Kanban.assemble m canvas placed groups).layoutDump := by
  intro a ha b hb hne hae hbe hparent
  change a ∈ m.boxes.map (Kinds.Kanban.sceneBox placed) at ha
  change b ∈ m.boxes.map (Kinds.Kanban.sceneBox placed) at hb
  obtain ⟨originalA, ham, rfl⟩ := List.mem_map.mp ha
  obtain ⟨originalB, hbm, rfl⟩ := List.mem_map.mp hb
  exact hrect originalA ham originalB hbm hne hae hbe hparent

theorem assemble_parent_transfer (m : Model) (canvas : Size)
    (placed : List (String × Rect)) (groups : List Group)
    (hrect : ∀ b ∈ m.boxes, b.parent ≠ "" → ∀ p ∈ m.boxes, p.id = b.parent →
      (Kinds.Kanban.placedRect placed p.id).Contained (Kinds.Kanban.placedRect placed b.id)) :
    Validator.C3 (Kinds.Kanban.assemble m canvas placed groups).layoutDump := by
  intro b hb hparent p hp
  have hpmem := List.mem_of_find?_eq_some hp
  have hpid := List.find?_some hp
  change b ∈ m.boxes.map (Kinds.Kanban.sceneBox placed) at hb
  change p ∈ m.boxes.map (Kinds.Kanban.sceneBox placed) at hpmem
  obtain ⟨originalB, hbm, rfl⟩ := List.mem_map.mp hb
  obtain ⟨originalP, hpm, rfl⟩ := List.mem_map.mp hpmem
  have heq : originalP.id = originalB.parent := by
    simpa [Kinds.Kanban.sceneBox] using hpid
  exact hrect originalB hbm hparent originalP hpm heq

end Elegant.GridKanban

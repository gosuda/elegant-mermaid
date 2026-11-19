import Elegant.SequenceStep2

set_option autoImplicit false

namespace Elegant
namespace Sequence

def noteRect (pl : Plan) (cs : List Int) (w : Walk) (placement a b box : Nat) : Rect :=
  ⟨(noteSpan pl cs placement a b box).1, w.cursor + pl.c.boxMargin, (noteSpan pl cs placement a b box).2,
    noteTextHeight pl box + 2 * pl.c.noteMargin⟩

def noteLabelRect (pl : Plan) (cs : List Int) (w : Walk) (placement a b box : Nat) : Rect :=
  ⟨(noteSpan pl cs placement a b box).1 + pl.c.noteMargin, w.cursor + pl.c.boxMargin + pl.c.noteMargin,
    max ((noteSpan pl cs placement a b box).2 - 2 * pl.c.noteMargin) 0, noteTextHeight pl box⟩

theorem stepNote_cursor_eq (pl : Plan) (cs : List Int) (w : Walk) (placement a b box : Nat) :
    (stepNote pl cs w placement a b box).cursor =
      w.cursor + (pl.c.boxMargin + (noteTextHeight pl box + 2 * pl.c.noteMargin)) := by
  unfold stepNote
  simp only [Walk.advance, addMember_cursor, placeLabel_cursor]

theorem stepNote_boxRects_eq (pl : Plan) (cs : List Int) (w : Walk) (placement a b box : Nat) :
    (stepNote pl cs w placement a b box).boxRects =
      w.boxRects.set box (noteRect pl cs w placement a b box) := by
  unfold stepNote
  simp only [Walk.advance, addMember_boxRects, placeLabel_boxRects]
  rfl

theorem stepNote_labelRects_eq (pl : Plan) (cs : List Int) (w : Walk) (placement a b box : Nat) :
    (stepNote pl cs w placement a b box).labelRects =
      match ownedLabelPos pl.m (boxId pl.m box) with
      | some p => w.labelRects.set p (noteLabelRect pl cs w placement a b box)
      | none => w.labelRects := by
  unfold stepNote
  simp only [Walk.advance, addMember_labelRects, placeLabel_labelRects]
  rfl

theorem stepNote_fragments_eq (pl : Plan) (cs : List Int) (w : Walk) (placement a b box : Nat) :
    (stepNote pl cs w placement a b box).fragments =
      fragsAddAll w.fragments [noteRect pl cs w placement a b box] := by
  unfold stepNote
  simp only [Walk.advance, addMember_fragments, placeLabel_fragments]
  rw [fragsAdd_eq_all]
  rfl

theorem noteSpan_width_ge {pl : Plan} (hpl : pl.Wf) (cs : List Int) (placement a b box : Nat) :
    2 * pl.c.noteMargin ≤ (noteSpan pl cs placement a b box).2 := by
  unfold noteSpan
  have h0 := widest_nonneg (pl.titleLines box)
  have h1 := hpl.pos.noteMargin
  dsimp only
  split
  · (try dsimp only); omega
  · split
    · (try dsimp only); omega
    · split
      · (try dsimp only); omega
      · (try dsimp only); omega

theorem inv_note {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w : Walk}
    {E : List Ent} {cs : List Int} (hpl : pl.Wf) (hfm : ModelFacts pl.m)
    (hI : Inv pl hdr lab0 stack placed w E) {placement a b box : Nat}
    (hbox : box < pl.m.boxes.length) (hnp : box ∉ placed)
    (hpar : boxParent pl.m box = topId pl.m stack) (hng : ¬ IsGroupAt pl.m box) :
    ∃ E', Inv pl hdr lab0 stack (box :: placed) (stepNote pl cs w placement a b box) E' := by
  have hbm := hpl.pos.boxMargin
  have hnm := hpl.pos.noteMargin
  have hth := noteTextHeight_nonneg pl hpl box
  have hw0 := noteSpan_width_ge hpl cs placement a b box
  refine inv_leaf hfm hI (w' := stepNote pl cs w placement a b box)
    (some (box, noteRect pl cs w placement a b box))
    ((ownedLabelPos pl.m (boxId pl.m box)).map fun p => (p, noteLabelRect pl cs w placement a b box))
    [noteRect pl cs w placement a b box]
    (w.cursor + (pl.c.boxMargin + (noteTextHeight pl box + 2 * pl.c.noteMargin)))
    (stepNote_boxRects_eq pl cs w placement a b box) ?_
    (stepNote_fragments_eq pl cs w placement a b box)
    (stepNote_cursor_eq pl cs w placement a b box) (by omega) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stepNote_labelRects_eq]
    cases ownedLabelPos pl.m (boxId pl.m box) <;> rfl
  · intro n r h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨hbox, hnp, hpar, ?_, ?_, ?_, ?_⟩
    · show w.cursor ≤ w.cursor + pl.c.boxMargin; omega
    · show 0 ≤ (noteSpan pl cs placement a b box).2; omega
    · show 0 ≤ noteTextHeight pl box + 2 * pl.c.noteMargin; omega
    · show w.cursor + pl.c.boxMargin + (noteTextHeight pl box + 2 * pl.c.noteMargin) ≤
        w.cursor + (pl.c.boxMargin + (noteTextHeight pl box + 2 * pl.c.noteMargin))
      omega
  · intro p r h
    cases hm : ownedLabelPos pl.m (boxId pl.m box) with
    | none => simp [hm] at h
    | some q =>
      simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      show w.cursor ≤ w.cursor + pl.c.boxMargin + pl.c.noteMargin ∧
        0 ≤ max ((noteSpan pl cs placement a b box).2 - 2 * pl.c.noteMargin) 0 ∧ 0 ≤ noteTextHeight pl box ∧
          w.cursor + pl.c.boxMargin + pl.c.noteMargin + noteTextHeight pl box ≤
            w.cursor + (pl.c.boxMargin + (noteTextHeight pl box + 2 * pl.c.noteMargin))
      omega
  · intro r hr
    have hr' : r = noteRect pl cs w placement a b box := by simpa using hr
    subst hr'
    show w.cursor ≤ w.cursor + pl.c.boxMargin ∧ 0 ≤ (noteSpan pl cs placement a b box).2 ∧
      0 ≤ noteTextHeight pl box + 2 * pl.c.noteMargin ∧
        w.cursor + pl.c.boxMargin + (noteTextHeight pl box + 2 * pl.c.noteMargin) ≤
          w.cursor + (pl.c.boxMargin + (noteTextHeight pl box + 2 * pl.c.noteMargin))
    omega
  · intro n r h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp
  · intro p r h
    refine ⟨noteRect pl cs w placement a b box, List.mem_singleton.mpr rfl, ?_⟩
    cases hm : ownedLabelPos pl.m (boxId pl.m box) with
    | none => simp [hm] at h
    | some q =>
      simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      show (noteSpan pl cs placement a b box).1 ≤ (noteSpan pl cs placement a b box).1 + pl.c.noteMargin ∧
        (noteSpan pl cs placement a b box).1 + pl.c.noteMargin +
            max ((noteSpan pl cs placement a b box).2 - 2 * pl.c.noteMargin) 0 ≤
          (noteSpan pl cs placement a b box).1 + (noteSpan pl cs placement a b box).2 ∧
        w.cursor + pl.c.boxMargin ≤ w.cursor + pl.c.boxMargin + pl.c.noteMargin ∧
        w.cursor + pl.c.boxMargin + pl.c.noteMargin + noteTextHeight pl box ≤
          w.cursor + pl.c.boxMargin + (noteTextHeight pl box + 2 * pl.c.noteMargin)
      omega
  · intro n r h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hng

end Sequence
end Elegant

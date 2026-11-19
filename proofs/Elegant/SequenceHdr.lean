import Elegant.SequenceFinal2

set_option autoImplicit false

/-! The headers of a sequence layout: the checked clearance of the participant frames, and the facts
about the header rectangles and header labels that the validity proof reads
(`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

theorem headersOk_spec {pl : Plan} {cs : List Int} (h : headersOk pl cs = true) {i j : Nat}
    {b b' : ModelBox} (hb : pl.m.boxes[i]? = some b) (hb' : pl.m.boxes[j]? = some b')
    (hp : isParticipantBox b = true) (hij : j ≠ i) :
    (b'.parent = b.id →
      Rect.Contained ((headerRects pl cs).getD i rectZero) ((headerRects pl cs).getD j rectZero)) ∧
    (b'.parent ≠ b.id → (isParticipantBox b' = true ∨ isActorBox b' = true) →
      Disjoint ((headerRects pl cs).getD i rectZero) ((headerRects pl cs).getD j rectZero)) := by
  unfold headersOk at h
  simp only [List.all_eq_true] at h
  have hi : (b, i) ∈ pl.m.boxes.zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?]; exact hb
  have hj : (b', j) ∈ pl.m.boxes.zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?]; exact hb'
  have h1 := h (b, i) hi
  simp only [hp, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  have h2 := h1 (b', j) hj
  have hne : (j == i) = false := by simpa using hij
  simp only [hne, Bool.false_or] at h2
  constructor
  · intro hpar
    have hq : (b'.parent == b.id) = true := by simpa using hpar
    simp only [hq, ↓reduceIte, decide_eq_true_eq] at h2
    exact h2
  · intro hpar hcls
    have hq : (b'.parent == b.id) = false := by simpa using hpar
    simp only [hq, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at h2
    rcases h2 with h2 | h2
    · exfalso
      rcases hcls with hc | hc <;> simp [hc] at h2
    · exact h2

theorem layoutOk_modelOk {model : Model} (h : layoutOk model = true) : modelOk model = true := by
  unfold layoutOk at h
  unfold modelOk
  cases hp : Plan.build (restoreFragmentShapes model) with
  | error e => simp [hp] at h
  | ok pl =>
    simp only [hp] at h ⊢
    cases hc : (decodeSteps (restoreFragmentShapes model).regionSets).foldlM (stepCheck pl)
        { stack := [], placed := [], routes := 0 } with
    | none => simp [hc] at h
    | some ck =>
      simp only [hc, Bool.and_eq_true] at h ⊢
      exact h.1

/-! ### Header rectangles -/

theorem hdr_part {pl : Plan} (cs : List Int) {i : Nat} {b : ModelBox} (hb : pl.m.boxes[i]? = some b)
    (hp : isParticipantBox b = true) :
    (headerRects pl cs).getD i rectZero = participantRect pl (actorRects pl cs) b i := by
  unfold headerRects
  simp only []
  rw [getD_zipIdx_map _ _ _ _ b hb]
  simp only [hp, ↓reduceIte]

/-- The facts about a participant frame that the header labels and the clauses read. -/
structure FrameOk (pl : Plan) (i : Nat) (fr : Rect) : Prop where
  y : fr.y = pl.bandTop - (((pl.titleLines i).length : Int) * pl.c.lineHeight + pl.c.boxMargin)
  h : fr.h = ((pl.titleLines i).length : Int) * pl.c.lineHeight + pl.c.boxMargin + pl.bandHeight +
    pl.c.boxMargin
  w : widest (pl.titleLines i) + 2 * pl.c.wrapPadding ≤ fr.w

theorem participantRect_ok (pl : Plan) (actors : List Rect) (b : ModelBox) (i : Nat) :
    FrameOk pl i (participantRect pl actors b i) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold participantRect
    rfl
  · unfold participantRect
    rfl
  · unfold participantRect
    dsimp only
    omega

def Lab0Cls (pl : Plan) (rects : List Rect) (l : Rect) : Prop :=
  l = rectZero ∨ ∃ i b, pl.m.boxes[i]? = some b ∧ isParticipantBox b = true ∧
    Rect.StrictInside (rects.getD i rectZero) l ∧ l.y + l.h ≤ pl.bandTop ∧ 0 ≤ l.w ∧ 0 ≤ l.h

theorem centreLabel_cls {pl : Plan} (hpl : pl.Wf) (hpf : PlanFacts pl) (rects : List Rect)
    {ls : List Rect} {i : Nat}
    {b : ModelBox} (hb : pl.m.boxes[i]? = some b) (hp : isParticipantBox b = true)
    (hfr : FrameOk pl i (rects.getD i rectZero))
    (htitle : titlePos pl.m i = labelPosById pl.m (b.id ++ ".label"))
    (hls : ∀ j, Lab0Cls pl rects (ls.getD j rectZero)) :
    ∀ j, Lab0Cls pl rects
      ((centreLabel pl ls (labelPosById pl.m (b.id ++ ".label")) (rects.getD i rectZero)
        ((rects.getD i rectZero).y + pl.c.boxTextMargin)).getD j rectZero) := by
  intro j
  unfold centreLabel
  cases hlp : labelPosById pl.m (b.id ++ ".label") with
  | none => exact hls j
  | some p =>
    simp only []
    by_cases hpl' : p < pl.labelLines.length
    · simp only [hpl', ↓reduceIte]
      rw [getD_set_gen]
      by_cases hj : p = j ∧ p < ls.length
      · rw [ite_eq_left hj]
        right
        have hT : pl.titleLines i = pl.labelLines.getD p [] := by
          unfold Plan.titleLines
          rw [htitle, hlp]
          rfl
        have hw := widest_nonneg (pl.labelLines.getD p [])
        have hlh := hpl.pos.lineHeight
        have hL : 0 ≤ ((pl.labelLines.getD p []).length : Int) * pl.c.lineHeight :=
          Int.mul_nonneg (Int.natCast_nonneg _) hlh
        have hbm := hpl.pos.boxMargin
        have htm := hpl.pos.textMargin
        have htp := hpl.pos.boxTextMarginPos
        have hwp := hpl.pos.wrapPaddingPos
        have hy := hfr.y
        have hh := hfr.h
        have hww := hfr.w
        rw [hT] at hy hh hww
        have hbh := hpf.bandH0
        have hd : 2 ≤ (rects.getD i rectZero).w - widest (pl.labelLines.getD p []) := by omega
        have hhalf := half_eq _ (by omega : 0 ≤ (rects.getD i rectZero).w - widest (pl.labelLines.getD p []))
        refine ⟨i, b, hb, hp, ?_, ?_, ?_, ?_⟩
        · unfold Rect.StrictInside
          refine ⟨?_, ?_, ?_, ?_⟩ <;> (try dsimp only) <;> omega
        · (try dsimp only)
          omega
        · exact hw
        · exact hL
      · rw [ite_eq_right hj]
        exact hls j
    · simpa [hpl'] using hls j

theorem headerLabels_cls {pl : Plan} (hpl : pl.Wf) (hpf : PlanFacts pl) (rects : List Rect)
    (hfr : ∀ i b, pl.m.boxes[i]? = some b → isParticipantBox b = true →
      FrameOk pl i (rects.getD i rectZero))
    (htitle : ∀ i b, pl.m.boxes[i]? = some b → isParticipantBox b = true →
      titlePos pl.m i = labelPosById pl.m (b.id ++ ".label")) :
    ∀ j, Lab0Cls pl rects ((headerLabels pl rects).getD j rectZero) := by
  unfold headerLabels
  have key : ∀ (l : List (ModelBox × Nat)), (∀ x ∈ l, pl.m.boxes[x.2]? = some x.1) →
      ∀ ls : List Rect, (∀ j, Lab0Cls pl rects (ls.getD j rectZero)) →
        ∀ j, Lab0Cls pl rects ((l.foldl (fun ls (bi : ModelBox × Nat) =>
          if isParticipantBox bi.1 then
            centreLabel pl ls (labelPosById pl.m (bi.1.id ++ ".label")) (rects.getD bi.2 rectZero)
              ((rects.getD bi.2 rectZero).y + pl.c.boxTextMargin)
          else ls) ls).getD j rectZero) := by
    intro l
    induction l with
    | nil =>
      intro _ ls h j
      exact h j
    | cons x t ih =>
      intro hx ls hls
      simp only [List.foldl_cons]
      apply ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
      have hx0 := hx x List.mem_cons_self
      by_cases hp : isParticipantBox x.1 = true
      · simp only [hp, ↓reduceIte]
        exact centreLabel_cls hpl hpf rects hx0 hp (hfr _ _ hx0 hp) (htitle _ _ hx0 hp) hls
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]
        exact hls
  refine key _ ?_ _ (fun j => Or.inl ?_)
  · intro x hx
    obtain ⟨b, i⟩ := x
    exact List.mk_mem_zipIdx_iff_getElem?.mp hx
  · simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl

end Sequence
end Elegant

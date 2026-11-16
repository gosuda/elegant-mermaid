import Elegant.SequenceLeaf

set_option autoImplicit false

/-! The invariant step for a fragment that closes: the frame takes its place, the title and the
divider labels are centred in it, and the frame joins the enclosing fragment. -/

namespace Elegant
namespace Sequence

theorem fragmentWidth_covers (pl : Plan) (run : FragRun) (natural width : Int)
    (h : fragmentWidth pl run natural = .ok width) (hk : (run.kind == fragmentKindRect) = false) :
    pl.labelWidth (labelPosById pl.m (boxId pl.m run.box ++ ".label")) + 2 * pl.c.boxMargin ≤ width ∧
      ∀ d ∈ run.dividers, pl.labelWidth d.label + 2 * pl.c.boxMargin ≤ width := by
  unfold fragmentWidth at h
  simp only [hk, Bool.false_eq_true, ↓reduceIte] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    refine ⟨Int.le_trans ?_ (foldl_max_ge_init (fun d : Divider => pl.labelWidth d.label + 2 * pl.c.boxMargin)
      run.dividers _), fun d hd => foldl_max_ge_mem _ _ _ d hd⟩
    exact Int.le_trans (Int.add_le_add_right (Int.le_max_right _ _) _) (Int.le_max_right _ _)

theorem closeFragment_spec (pl : Plan) (w : Walk) (run : FragRun) (w' : Walk)
    (h : closeFragment pl w run = .ok w') :
    ∃ width, (rectSpan run.members).2 - (rectSpan run.members).1 + 2 * pl.c.boxMargin ≤ width ∧
      ((run.kind == fragmentKindRect) = false →
        pl.labelWidth (labelPosById pl.m (boxId pl.m run.box ++ ".label")) + 2 * pl.c.boxMargin ≤ width ∧
          ∀ d ∈ run.dividers, pl.labelWidth d.label + 2 * pl.c.boxMargin ≤ width) ∧
      w' = closeWith pl w run width := by
  unfold closeFragment at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i width hw
    cases h
    exact ⟨width, fragmentWidth_ge _ _ _ _ hw, fun hk => fragmentWidth_covers _ _ _ _ hw hk, rfl⟩

/-- The rectangle of a label that is centred in `frame` with its top at `top`. -/
def centredRect (pl : Plan) (p : Nat) (frame : Rect) (top : Int) : Rect :=
  ⟨frame.x + half (frame.w - widest (pl.labelLines.getD p [])), top, widest (pl.labelLines.getD p []),
    ((pl.labelLines.getD p []).length : Int) * pl.c.lineHeight⟩

theorem centreLabel_getD (pl : Plan) (ls : List Rect) (label : Option Nat) (frame : Rect) (top : Int)
    (q : Nat) :
    (centreLabel pl ls label frame top).getD q rectZero = ls.getD q rectZero ∨
      ∃ p, label = some p ∧ p < pl.labelLines.length ∧
        (centreLabel pl ls label frame top).getD q rectZero = centredRect pl p frame top := by
  unfold centreLabel
  cases label with
  | none => exact Or.inl rfl
  | some p =>
    simp only []
    by_cases hp : p < pl.labelLines.length
    · simp only [hp, ↓reduceIte, getD_set_gen]
      by_cases hc : p = q ∧ p < ls.length
      · right
        exact ⟨p, rfl, hp, by simp only [show (p = q ∧ p < ls.length) = True from eq_true hc, ↓reduceIte]; rfl⟩
      · left
        simp only [show (p = q ∧ p < ls.length) = False from eq_false hc, ↓reduceIte]
    · simp [hp]

/-- A rectangle that the closing of fragment `f` with frame `F` gave to a label. -/
def NewLab (pl : Plan) (f : FragRun) (F : Rect) (r : Rect) : Prop :=
  (∃ p, labelPosById pl.m (boxId pl.m f.box ++ ".label") = some p ∧ p < pl.labelLines.length ∧
      r = centredRect pl p F (f.top + (pl.c.boxMargin + pl.c.boxTextMargin))) ∨
    (∃ d ∈ f.dividers, ∃ p, d.label = some p ∧ p < pl.labelLines.length ∧
      r = centredRect pl p F (d.row + (pl.c.boxMargin + pl.c.boxTextMargin)))

theorem closeLabels_getD (pl : Plan) (ls : List Rect) (f : FragRun) (F : Rect) (q : Nat) :
    (f.dividers.foldl (fun ls d => centreLabel pl ls d.label F (d.row + (pl.c.boxMargin + pl.c.boxTextMargin)))
      (centreLabel pl ls (labelPosById pl.m (boxId pl.m f.box ++ ".label")) F
        (f.top + (pl.c.boxMargin + pl.c.boxTextMargin)))).getD q rectZero = ls.getD q rectZero ∨
    NewLab pl f F ((f.dividers.foldl (fun ls d => centreLabel pl ls d.label F (d.row + (pl.c.boxMargin + pl.c.boxTextMargin)))
      (centreLabel pl ls (labelPosById pl.m (boxId pl.m f.box ++ ".label")) F
        (f.top + (pl.c.boxMargin + pl.c.boxTextMargin)))).getD q rectZero) := by
  have key : ∀ (ds : List Divider) (l0 : List Rect), (∀ d ∈ ds, d ∈ f.dividers) →
      (ds.foldl (fun ls d => centreLabel pl ls d.label F (d.row + (pl.c.boxMargin + pl.c.boxTextMargin))) l0).getD q rectZero
        = l0.getD q rectZero ∨
      ∃ d ∈ f.dividers, ∃ p, d.label = some p ∧ p < pl.labelLines.length ∧
        (ds.foldl (fun ls d => centreLabel pl ls d.label F (d.row + (pl.c.boxMargin + pl.c.boxTextMargin))) l0).getD q rectZero
          = centredRect pl p F (d.row + (pl.c.boxMargin + pl.c.boxTextMargin)) := by
    intro ds
    induction ds with
    | nil => intro l0 _; exact Or.inl rfl
    | cons d t ih =>
      intro l0 hd
      simp only [List.foldl_cons]
      have hdf : d ∈ f.dividers := hd d List.mem_cons_self
      have ht : ∀ d' ∈ t, d' ∈ f.dividers := fun d' h => hd d' (List.mem_cons_of_mem _ h)
      rcases ih (centreLabel pl l0 d.label F (d.row + (pl.c.boxMargin + pl.c.boxTextMargin))) ht with h | h
      · rcases centreLabel_getD pl l0 d.label F (d.row + (pl.c.boxMargin + pl.c.boxTextMargin)) q with h' | ⟨p, hp, hlt, h'⟩
        · exact Or.inl (h.trans h')
        · exact Or.inr ⟨d, hdf, p, hp, hlt, h.trans h'⟩
      · exact Or.inr h
  rcases key f.dividers (centreLabel pl ls (labelPosById pl.m (boxId pl.m f.box ++ ".label")) F
      (f.top + (pl.c.boxMargin + pl.c.boxTextMargin))) (fun d hd => hd) with h | ⟨d, hd, p, hp, hlt, h⟩
  · rcases centreLabel_getD pl ls (labelPosById pl.m (boxId pl.m f.box ++ ".label")) F
        (f.top + (pl.c.boxMargin + pl.c.boxTextMargin)) q with h' | ⟨p, hp, hlt, h'⟩
    · exact Or.inl (h.trans h')
    · exact Or.inr (Or.inl ⟨p, hp, hlt, h.trans h'⟩)
  · exact Or.inr (Or.inr ⟨d, hd, p, hp, hlt, h⟩)

end Sequence
end Elegant

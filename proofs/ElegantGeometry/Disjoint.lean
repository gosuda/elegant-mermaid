import ElegantGeometry.Basic

/-! Disjointness of rectangles: the predicate, its commutativity, its invariance under
translation, and the placement rule. -/

set_option autoImplicit false

/-- Two rectangles are disjoint when their open interiors share no point. -/
abbrev Disjoint (a b : Rect) : Prop := ¬ a.meetsInterior b

theorem Disjoint.comm (a b : Rect) : Disjoint a b ↔ Disjoint b a := by
  unfold Disjoint Rect.meetsInterior
  constructor <;> intro h <;> omega

theorem Rect.disjoint_comm (a b : Rect) : Disjoint a b ↔ Disjoint b a :=
  Disjoint.comm a b

theorem Rect.disjoint_translate {a b a' b' : Rect} {dx dy : Int}
    (ha : a.translate dx dy = .ok a') (hb : b.translate dx dy = .ok b') :
    Disjoint a b ↔ Disjoint a' b' := by
  obtain ⟨_, hae, _⟩ := Rect.translate_ok ha
  obtain ⟨_, hbe, _⟩ := Rect.translate_ok hb
  subst hae hbe
  unfold Disjoint Rect.meetsInterior Rect.translateRaw
  constructor <;> intro h <;> simp only at * <;> omega

/-- Placing a size after the far edge of a rectangle with a non-negative gap yields a
disjoint rectangle. -/
theorem placeAfter_disjoint {axis : Axis} {a p : Rect} {gap : Int} {s : Size}
    (hg : 0 ≤ gap) (h : a.placeAfter axis gap s = .ok p) : Disjoint a p := by
  obtain ⟨_, _, _, hpr, _⟩ := Rect.placeAfter_ok h
  subst hpr
  unfold Disjoint Rect.meetsInterior Rect.placeAfterRaw
  cases axis with
  | X => simp only; omega
  | Y => simp only; omega

import Elegant.SequenceFinal

set_option autoImplicit false

/-! What a passing `finalOk` and the event check say about every box (`spec/layout/sequence.md`,
sequence-54). -/

namespace Elegant
namespace Sequence

theorem finalOk_box {pl : Plan} {ck : CheckState} (h : finalOk pl ck = true) (i : Nat) (b : ModelBox)
    (hb : pl.m.boxes[i]? = some b) : boxFinalOk pl ck b i = true := by
  unfold finalOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hmem : (b, i) ∈ pl.m.boxes.zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?]
    exact hb
  exact h.2 (b, i) hmem

theorem finalOk_routes {pl : Plan} {ck : CheckState} (h : finalOk pl ck = true) :
    ck.routes = pl.m.routes.length := by
  unfold finalOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem mem_of_contains_true {l : List Nat} {a : Nat} (h : l.contains a = true) : a ∈ l :=
  List.contains_iff_mem.mp h

/-- The kinds of box that a passing final check allows. -/
theorem boxFinalOk_cls {pl : Plan} {ck : CheckState} {b : ModelBox} {i : Nat}
    (h : boxFinalOk pl ck b i = true) :
    b.id ≠ "" ∧
      ((isActorBox b = true ∧ b.exclusive = true ∧ i ∉ ck.placed ∧
          (b.parent = "" ∨ isParticipantId pl.m b.parent = true)) ∨
        (isActorBox b = true ∧ b.exclusive = false ∧ i ∈ ck.placed) ∨
        (isNoteBox b = true ∧ b.exclusive = false ∧ i ∈ ck.placed) ∨
        (isParticipantBox b = true ∧ b.exclusive = false ∧ b.parent = "") ∨
        (isFragmentBox b = true ∧ b.exclusive = false ∧ i ∈ ck.placed)) := by
  unfold boxFinalOk at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hid, h⟩ := h
  refine ⟨hid, ?_⟩
  by_cases ha : isActorBox b = true
  · simp only [ha, ↓reduceIte] at h
    by_cases he : b.exclusive = true
    · simp only [he, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true,
        beq_iff_eq] at h
      refine Or.inl ⟨ha, he, not_mem_of_contains_false h.1, h.2⟩
    · have he' : b.exclusive = false := by simpa using he
      simp only [he', Bool.false_eq_true, ↓reduceIte] at h
      exact Or.inr (Or.inl ⟨ha, he', mem_of_contains_true h⟩)
  · simp only [ha, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hn : isNoteBox b = true
    · simp only [hn, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact Or.inr (Or.inr (Or.inl ⟨hn, h.1, mem_of_contains_true h.2⟩))
    · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hp : isParticipantBox b = true
      · simp only [hp, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, h.1.1.1, h.1.1.2⟩)))
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hf : isFragmentBox b = true
        · simp only [hf, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at h
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hf, h.1, mem_of_contains_true h.2⟩)))
        · simp only [hf, Bool.false_eq_true, ↓reduceIte] at h

/-- The boxes that an event places are actors, notes, and fragments. -/
def PlacedCls (pl : Plan) (placed : List Nat) : Prop :=
  ∀ i ∈ placed, ∃ b, pl.m.boxes[i]? = some b ∧
    (isActorBox b = true ∨ isNoteBox b = true ∨ isFragmentBox b = true)

theorem stepCheck_placedCls {pl : Plan} (hpf : PlanFacts pl) {ck ck' : CheckState} (s : Step)
    (h : stepCheck pl ck s = some ck') (hc : PlacedCls pl ck.placed) : PlacedCls pl ck'.placed := by
  cases s with
  | message bits src dst route destroyed =>
    simp only [stepCheck] at h
    split at h
    · rename_i hcond
      split at h
      · split at h
        · rename_i bi hcr
          have h' := Option.some.inj h
          subst h'
          obtain ⟨hab, b, hb, -, -⟩ := createOk_spec pl ck dst bi hcr
          intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · obtain ⟨-, hdst⟩ : (_ ∧ dst < pl.actorBoxes.length) := by
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
              exact ⟨trivial, hcond.1.1.2⟩
            obtain ⟨b3, hb3, hact⟩ := hpf.ab_actor dst hdst
            have e : pl.actorBoxes[dst] = i := by
              have := hab
              simp [List.getElem?_eq_getElem hdst] at this
              exact this
            rw [e] at hb3
            exact ⟨b3, hb3, Or.inl hact⟩
          · exact hc i hi
        · cases h
      · have h' := Option.some.inj h
        subst h'
        exact hc
    · cases h
  | note placement a b box =>
    simp only [stepCheck] at h
    cases hbx : pl.m.boxes[box]? with
    | none => simp [hbx] at h
    | some b' =>
      simp only [hbx] at h
      split at h
      · rename_i hcond
        have h' := Option.some.inj h
        subst h'
        simp only [Bool.and_eq_true] at hcond
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact ⟨b', hbx, Or.inr (Or.inl hcond.1.1.1)⟩
        · exact hc i hi
      · cases h
  | fragmentStart kind box =>
    simp only [stepCheck] at h
    cases hbx : pl.m.boxes[box]? with
    | none => simp [hbx] at h
    | some b' =>
      simp only [hbx] at h
      split at h
      · rename_i hcond
        have h' := Option.some.inj h
        subst h'
        simp only [Bool.and_eq_true] at hcond
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact ⟨b', hbx, Or.inr (Or.inr hcond.1.1.1)⟩
        · exact hc i hi
      · cases h
  | fragmentElse box sect =>
    simp only [stepCheck] at h
    cases hst : ck.stack with
    | nil => rw [hst] at h; cases h
    | cons top rest =>
      rw [hst] at h
      dsimp only at h
      split at h
      · have h' := Option.some.inj h
        subst h'
        exact hc
      · cases h
  | fragmentEnd =>
    simp only [stepCheck] at h
    cases hst : ck.stack with
    | nil => rw [hst] at h; cases h
    | cons top rest =>
      rw [hst] at h
      have h' := Option.some.inj h
      subst h'
      exact hc
  | activateStart actor =>
    simp only [stepCheck] at h
    have h' := Option.some.inj h
    subst h'
    exact hc
  | activateEnd actor =>
    simp only [stepCheck] at h
    have h' := Option.some.inj h
    subst h'
    exact hc

theorem foldCheck_placedCls {pl : Plan} (hpf : PlanFacts pl) :
    ∀ (l : List Step) (ck ck' : CheckState), l.foldlM (stepCheck pl) ck = some ck' →
      PlacedCls pl ck.placed → PlacedCls pl ck'.placed := by
  intro l
  induction l with
  | nil =>
    intro ck ck' h hc
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    subst h
    exact hc
  | cons s t ih =>
    intro ck ck' h hc
    simp only [List.foldlM_cons, bind, Option.bind] at h
    cases h1 : stepCheck pl ck s with
    | none => rw [h1] at h; cases h
    | some ck2 =>
      rw [h1] at h
      exact ih ck2 ck' h (stepCheck_placedCls hpf s h1 hc)

end Sequence
end Elegant

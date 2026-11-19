import Elegant.SequenceStep3

set_option autoImplicit false

/-! What the plan of a sequence layout says about its actor boxes and its header band
(`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

theorem mapM_ok_length {α β ε : Type} (f : α → Except ε β) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → r.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro r h
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | cons a t ih =>
    intro r h
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hf : f a with
    | error e => simp [hf] at h
    | ok b =>
      simp only [hf] at h
      cases ht : t.mapM f with
      | error e => simp [ht] at h
      | ok rs =>
        simp only [ht, Except.ok.injEq] at h
        subst h
        simp [ih rs ht]

theorem actorIdx_mem :
    ∀ (l : List ModelBox) (k x : Nat),
      x ∈ (l.zipIdx k).filterMap (fun (b, i) => if isActorBox b then some i else none) →
        k ≤ x ∧ x < k + l.length ∧ ∃ b, l[x - k]? = some b ∧ isActorBox b = true := by
  intro l
  induction l with
  | nil => intro k x hx; simp [List.zipIdx] at hx
  | cons a t ih =>
    intro k x hx
    rw [List.zipIdx_cons, List.filterMap_cons] at hx
    by_cases ha : isActorBox a = true
    · simp only [ha, ↓reduceIte, List.mem_cons] at hx
      rcases hx with rfl | hx
      · refine ⟨Nat.le_refl _, by simp, a, by simp, ha⟩
      · obtain ⟨h1, h2, b, hb, hbb⟩ := ih (k + 1) x hx
        refine ⟨by omega, by simp only [List.length_cons]; omega, b, ?_, hbb⟩
        have : x - k = (x - (k + 1)) + 1 := by omega
        rw [this]
        exact hb
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hx
      obtain ⟨h1, h2, b, hb, hbb⟩ := ih (k + 1) x hx
      refine ⟨by omega, by simp only [List.length_cons]; omega, b, ?_, hbb⟩
      have : x - k = (x - (k + 1)) + 1 := by omega
      rw [this]
      exact hb

theorem actorIdx_nodup :
    ∀ (l : List ModelBox) (k : Nat),
      ((l.zipIdx k).filterMap (fun (b, i) => if isActorBox b then some i else none)).Nodup := by
  intro l
  induction l with
  | nil => intro k; simp [List.zipIdx]
  | cons a t ih =>
    intro k
    rw [List.zipIdx_cons, List.filterMap_cons]
    by_cases ha : isActorBox a = true
    · simp only [ha, ↓reduceIte]
      refine List.nodup_cons.mpr ⟨fun hk => ?_, ih (k + 1)⟩
      have := (actorIdx_mem t (k + 1) k hk).1
      omega
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      exact ih (k + 1)

theorem actorIdx_complete :
    ∀ (l : List ModelBox) (k i : Nat) (b : ModelBox), l[i]? = some b → isActorBox b = true →
      (k + i) ∈ (l.zipIdx k).filterMap (fun (b, i) => if isActorBox b then some i else none) := by
  intro l
  induction l with
  | nil => intro k i b h; simp at h
  | cons a t ih =>
    intro k i b h hb
    rw [List.zipIdx_cons, List.filterMap_cons]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [hb]
    | succ i' =>
      simp only [List.getElem?_cons_succ] at h
      have := ih (k + 1) i' b h hb
      have e : k + (i' + 1) = k + 1 + i' := by omega
      rw [e]
      by_cases ha : isActorBox a = true
      · simp only [ha, ↓reduceIte, List.mem_cons]
        exact Or.inr this
      · simp only [ha, Bool.false_eq_true, ↓reduceIte]
        exact this

theorem actorIdx_length :
    ∀ (l : List ModelBox) (k : Nat),
      ((l.zipIdx k).filterMap (fun (b, i) => if isActorBox b then some i else none)).length =
        (l.filter isActorBox).length := by
  intro l
  induction l with
  | nil => intro k; simp [List.zipIdx]
  | cons a t ih =>
    intro k
    rw [List.zipIdx_cons, List.filterMap_cons, List.filter_cons]
    by_cases ha : isActorBox a = true
    · simp only [ha, ↓reduceIte, List.length_cons]
      rw [ih]
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      rw [ih]

theorem findIdx_of_nodup (l : List Nat) (hnd : l.Nodup) :
    ∀ (o : Nat) (h : o < l.length), l.findIdx? (· == l[o]) = some o := by
  induction l with
  | nil => intro o h; simp at h
  | cons a t ih =>
    intro o h
    cases o with
    | zero => simp [List.findIdx?_cons, List.getElem_cons_zero]
    | succ o' =>
      have hnd' := List.nodup_cons.mp hnd
      have ht : o' < t.length := by simpa using h
      have hne : (a == t[o']) = false := by
        have : a ≠ t[o'] := fun hh => hnd'.1 (hh ▸ List.getElem_mem ht)
        simpa using this
      simp only [List.findIdx?_cons, List.getElem_cons_succ, hne]
      simp [ih hnd'.2 o' ht]

theorem foldl_infl {α : Type} (F : Int → α → Int) (hF : ∀ acc a, acc ≤ F acc a) :
    ∀ (l : List α) (init : Int), init ≤ l.foldl F init := by
  intro l
  induction l with
  | nil => intro init; exact Int.le_refl _
  | cons a t ih =>
    intro init
    simp only [List.foldl_cons]
    exact Int.le_trans (hF init a) (ih _)

theorem foldl_mem_ge {α : Type} (F : Int → α → Int) (hF : ∀ acc a, acc ≤ F acc a) :
    ∀ (l : List α) (init v : Int) (a : α), a ∈ l → (∀ acc, v ≤ F acc a) → v ≤ l.foldl F init := by
  intro l
  induction l with
  | nil => intro init v a h; simp at h
  | cons x t ih =>
    intro init v a h hv
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Int.le_trans (hv init) (foldl_infl F hF t _)
    · exact ih _ v a h hv

theorem foldl_nonneg_max (l : List Int) : 0 ≤ l.foldl max 0 :=
  foldl_max_ge_init (fun x => x) l 0

theorem getD_le_foldl_max (l : List Int) (o : Nat) : l.getD o 0 ≤ l.foldl max 0 := by
  by_cases ho : o < l.length
  · have h1 : l.getD o 0 = l[o] := by simp [List.getD_eq_getElem?_getD, ho]
    rw [h1]
    exact foldl_max_ge_mem (fun x => x) l 0 l[o] (List.getElem_mem ho)
  · have h1 : l.getD o 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : l.length ≤ o)]
    rw [h1]
    exact foldl_nonneg_max l

/-- What the plan of a layout says about its actor boxes and its header band. -/
structure PlanFacts (pl : Plan) : Prop where
  ab_actor : ∀ o (h : o < pl.actorBoxes.length),
    ∃ b, pl.m.boxes[pl.actorBoxes[o]]? = some b ∧ isActorBox b = true
  ab_nodup : pl.actorBoxes.Nodup
  ab_complete : ∀ i b, pl.m.boxes[i]? = some b → isActorBox b = true → i ∈ pl.actorBoxes
  lenW : pl.widths.length = pl.actorBoxes.length
  lenH : pl.heights.length = pl.actorBoxes.length
  bandH : ∀ o, pl.heights.getD o 0 ≤ pl.bandHeight
  bandH0 : 0 ≤ pl.bandHeight
  bandT0 : 0 ≤ pl.bandTop
  bandT : ∀ i b, pl.m.boxes[i]? = some b → isParticipantBox b = true →
    ((pl.titleLines i).length : Int) * pl.c.lineHeight + pl.c.boxMargin ≤ pl.bandTop

theorem Plan.build_facts (m : Model) (pl : Plan) (h : Plan.build m = .ok pl) : PlanFacts pl := by
  unfold Plan.build at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i c hc
    split at h
    · cases h
    · rename_i actorLines hAL
      split at h
      · cases h
      · rename_i labelLines hLL
        cases h
        have hlen := mapM_ok_length _ _ _ hAL
        have hA := actorIdx_length m.boxes 0
        have hz : ((m.boxes.filter isActorBox).zip actorLines).length = (m.boxes.filter isActorBox).length := by
          rw [List.length_zip, hlen]; exact Nat.min_self _
        refine ⟨?_, actorIdx_nodup m.boxes 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro o ho
          have hmem := List.getElem_mem ho
          obtain ⟨-, -, b, hb, hbb⟩ := actorIdx_mem m.boxes 0 _ hmem
          exact ⟨b, by simpa using hb, hbb⟩
        · intro i b hb hbb
          have := actorIdx_complete m.boxes 0 i b hb hbb
          simpa using this
        · simp only [List.length_map]
          rw [hz, ← hA]
        · simp only [List.length_map]
          rw [hz, ← hA]
        · intro o
          exact getD_le_foldl_max _ o
        · exact foldl_nonneg_max _
        · refine foldl_infl _ (fun acc p => ?_) _ 0
          (try dsimp only)
          split
          · exact Int.le_max_left _ _
          · exact Int.le_refl _
        · intro i b hb hbb
          have hmem : (b, i) ∈ m.boxes.zipIdx := by
            rw [List.mk_mem_zipIdx_iff_getElem?]
            exact hb
          refine foldl_mem_ge _ (fun acc p => ?_) _ _ _ (b, i) hmem (fun acc => ?_)
          · (try dsimp only)
            split
            · exact Int.le_max_left _ _
            · exact Int.le_refl _
          · dsimp only
            simp only [hbb, ↓reduceIte]
            exact Int.le_max_right _ _

end Sequence
end Elegant

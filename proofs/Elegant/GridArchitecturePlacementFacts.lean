import Elegant.GridArchitecturePlacement

set_option autoImplicit false

namespace Elegant.Grid.Architecture

def Marked (l : Level) (i : Nat) : Prop := l.placed[i]? = some true

theorem put_marked (p : Params) (l : Level) (i : Nat) (c : Cell)
    (hi : i < l.placed.length) : Marked (put p l i c) i := by
  simp [Marked,put,List.getElem?_set_self hi]

theorem put_preserves_marked (p : Params) (l : Level) (i j : Nat) (c : Cell)
    (hj : Marked l j) : Marked (put p l i c) j := by
  by_cases h : i = j
  · subst i
    have bound : j < l.placed.length := by
      by_cases hn : j < l.placed.length
      · exact hn
      · have hnone : l.placed[j]? = none := List.getElem?_eq_none (by omega)
        simp [Marked,hnone] at hj
    exact put_marked p l j c bound
  · simpa [Marked,put,List.getElem?_set_ne h] using hj

theorem put_placed_length (p : Params) (l : Level) (i : Nat) (c : Cell) :
    (put p l i c).placed.length = l.placed.length := by simp [put]

theorem expand_preserves_marked (p : Params) (u : Nat) (l : Level) (queue : List Nat)
    (i : Nat) (hi : Marked l i) : Marked (expand p u l queue).1 i := by
  unfold expand
  have fold : ∀ (edges : List Edge) (state : Level × List Nat), Marked state.1 i →
      Marked (edges.foldl (fun state e =>
        if e.a != u && e.b != u then state else
        let v := if e.b = u then e.a else e.b
        let side := if e.b = u then e.sideB else e.sideA
        if state.1.placed.getD v false then state
        else (put p state.1 v (choose p state.1 v u side), state.2 ++ [v])) state).1 i := by
    intro edges
    induction edges with
    | nil => intro state h; exact h
    | cons e rest ih =>
      intro state h
      simp only [List.foldl_cons]
      apply ih
      split
      · exact h
      · split <;> split
        all_goals first | exact h | exact put_preserves_marked _ _ _ _ _ h
  exact fold _ _ hi

theorem drain_preserves_marked (p : Params) (fuel : Nat) (l : Level) (queue : List Nat)
    (i : Nat) (hi : Marked l i) : Marked (drain p fuel l queue).1 i := by
  induction fuel generalizing l queue with
  | zero => cases queue <;> exact hi
  | succ fuel ih =>
    cases queue with
    | nil => exact hi
    | cons u rest =>
      simp only [drain]
      exact ih _ _ (expand_preserves_marked p u l rest i hi)

theorem expand_placed_length (p : Params) (u : Nat) (l : Level) (queue : List Nat) :
    (expand p u l queue).1.placed.length = l.placed.length := by
  unfold expand
  have fold : ∀ (edges : List Edge) (state : Level × List Nat),
      (edges.foldl (fun state e =>
        if e.a != u && e.b != u then state else
        let v := if e.b = u then e.a else e.b
        let side := if e.b = u then e.sideB else e.sideA
        if state.1.placed.getD v false then state
        else (put p state.1 v (choose p state.1 v u side), state.2 ++ [v])) state).1.placed.length =
          state.1.placed.length := by
    intro edges
    induction edges with
    | nil => intro state; rfl
    | cons e rest ih =>
      intro state
      simp only [List.foldl_cons]
      rw [ih]
      split
      · rfl
      · split <;> split
        all_goals first | rfl | exact put_placed_length _ _ _ _
  exact fold _ _

theorem drain_placed_length (p : Params) (fuel : Nat) (l : Level) (queue : List Nat) :
    (drain p fuel l queue).1.placed.length = l.placed.length := by
  induction fuel generalizing l queue with
  | zero => cases queue <;> rfl
  | succ fuel ih =>
    cases queue with
    | nil => rfl
    | cons u rest =>
      simp only [drain]
      rw [ih]
      exact expand_placed_length _ _ _ _

def visit (p : Params) (state : Level × Nat) (first : Nat) : Level × Nat :=
  if state.1.placed.getD first false then state
  else drain p state.2 (put p state.1 first (seedCell p state.1 first)) [first]

theorem visit_preserves_marked (p : Params) (state : Level × Nat) (first i : Nat)
    (hi : Marked state.1 i) : Marked (visit p state first).1 i := by
  unfold visit
  split
  · exact hi
  · exact drain_preserves_marked _ _ _ _ _ (put_preserves_marked _ _ _ _ _ hi)

theorem visit_placed_length (p : Params) (state : Level × Nat) (first : Nat) :
    (visit p state first).1.placed.length = state.1.placed.length := by
  unfold visit
  split
  · rfl
  · rw [drain_placed_length,put_placed_length]

theorem visit_marks (p : Params) (state : Level × Nat) (first : Nat)
    (h : first < state.1.placed.length) : Marked (visit p state first).1 first := by
  unfold visit
  split
  · rename_i marked
    simpa [Marked,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h] using marked
  · exact drain_preserves_marked _ _ _ _ _ (put_marked _ _ _ _ h)

theorem visit_fold_preserves (p : Params) (indices : List Nat) (state : Level × Nat)
    (i : Nat) (hi : Marked state.1 i) :
    Marked (indices.foldl (visit p) state).1 i := by
  induction indices generalizing state with
  | nil => exact hi
  | cons first rest ih =>
    exact ih _ (visit_preserves_marked _ _ _ _ hi)

theorem visit_fold_marks (p : Params) (indices : List Nat) (state : Level × Nat)
    (i : Nat) (hi : i ∈ indices) (bound : i < state.1.placed.length) :
    Marked (indices.foldl (visit p) state).1 i := by
  induction indices generalizing state with
  | nil => simp at hi
  | cons first rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hi with heq | hmem
    · subst i
      exact visit_fold_preserves _ _ _ _ (visit_marks _ _ _ bound)
    · apply ih _ hmem
      simpa only [visit_placed_length] using bound

/-- The native outer component loop seeds every unvisited unit even after BFS
fuel is exhausted; therefore all units are placed, independently of the cap. -/
theorem arrange_all_marked (p : Params) (fuel : Nat) (l : Level)
    (lengths : l.placed.length = l.units.length) (i : Nat) (hi : i < l.units.length) :
    Marked (arrange p fuel l).1 i := by
  change Marked ((List.range l.units.length).foldl (visit p) (l,fuel)).1 i
  exact visit_fold_marks p _ _ i (List.mem_range.mpr hi) (by change i < l.placed.length; omega)

theorem arch_all_placed (p : Params) (fuel : Nat) (l : Level)
    (lengths : l.placed.length = l.units.length) (i : Nat) (hi : i < l.units.length) :
    Marked (arrange p fuel l).1 i :=
  arrange_all_marked p fuel l lengths i hi

end Elegant.Grid.Architecture

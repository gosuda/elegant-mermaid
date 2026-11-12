import Elegant.Scene

set_option autoImplicit false

namespace Elegant.Layered.Portfolio

structure Candidate (α : Type) where
  value : α
  scene : Scene
  budgetExhausted : Bool := false

structure Scored (α : Type) where
  candidate : Candidate α
  cost : Int
  cost_eq : softCost candidate.scene = .ok cost

def score {α : Type} (candidate : Candidate α) : Except LayoutError (Scored α) :=
  match h : softCost candidate.scene with
  | .error e => .error e
  | .ok cost =>
    .ok ⟨candidate, cost, h⟩

def improves (incumbent trial : Int) : Except LayoutError Bool :=
  let lhs := 100 * trial
  let rhs := 97 * incumbent
  if lhs < -9223372036854775808 ∨ 9223372036854775807 < lhs then .error .overflow
  else if rhs < -9223372036854775808 ∨ 9223372036854775807 < rhs then .error .overflow
  else .ok (decide (lhs < rhs))

def consider {α : Type} (incumbent trial : Scored α) : Except LayoutError (Scored α) :=
  match improves incumbent.cost trial.cost with
  | .error e => .error e
  | .ok better =>
    let chosen := if better then trial else incumbent
    .ok { chosen with candidate := { chosen.candidate with
      budgetExhausted := incumbent.candidate.budgetExhausted || trial.candidate.budgetExhausted } }

theorem consider_cost_le {α : Type} {incumbent trial out : Scored α}
    (h : consider incumbent trial = .ok out) : out.cost ≤ incumbent.cost := by
  unfold consider at h
  cases hi : improves incumbent.cost trial.cost with
  | error e => simp [hi] at h
  | ok better =>
    rw [hi] at h
    dsimp only at h
    cases better with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
      subst out
      exact Int.le_refl _
    | true =>
      simp only [↓reduceIte, Except.ok.injEq] at h
      subst out
      change trial.cost ≤ incumbent.cost
      have hn := softCost_nonneg trial.cost_eq
      unfold improves at hi
      dsimp only at hi
      split at hi
      · cases hi
      · split at hi
        · cases hi
        · simp only [Except.ok.injEq, decide_eq_true_eq] at hi
          omega

def run {α : Type} (candidate : Nat → Except LayoutError (Candidate α)) :
    Nat → Nat → Scored α → Except LayoutError (Scored α)
  | 0, _, incumbent => .ok incumbent
  | fuel + 1, index, incumbent =>
    match candidate index with
    | .error e => .error e
    | .ok trial =>
      match score trial with
      | .error e => .error e
      | .ok scored =>
        match consider incumbent scored with
        | .error e => .error e
        | .ok next => run candidate fuel (index + 1) next

theorem run_cost_le {α : Type} (candidate : Nat → Except LayoutError (Candidate α))
    (fuel index : Nat) (incumbent out : Scored α)
    (h : run candidate fuel index incumbent = .ok out) : out.cost ≤ incumbent.cost := by
  induction fuel generalizing index incumbent with
  | zero =>
    simp only [run, Except.ok.injEq] at h
    subst out
    exact Int.le_refl _
  | succ fuel ih =>
    simp only [run] at h
    cases hc : candidate index with
    | error e => simp only [hc] at h; cases h
    | ok trial =>
      simp only [hc] at h
      cases hs : score trial with
      | error e => simp only [hs] at h; cases h
      | ok scored =>
        simp only [hs] at h
        cases hn : consider incumbent scored with
        | error e => simp only [hn] at h; cases h
        | ok next =>
          simp only [hn] at h
          exact Int.le_trans (ih (index + 1) next h) (consider_cost_le hn)

def portfolio {α : Type} (thoroughness : Nat) (candidate : Nat → Except LayoutError (Candidate α)) :
    Except LayoutError (Candidate α) :=
  let count := if thoroughness = 0 then 3 else thoroughness
  if 5 < count then .error .domain
  else
    match candidate 0 with
    | .error e => .error e
    | .ok first =>
      match score first with
      | .error e => .error e
      | .ok initial =>
        match run candidate ((min count 5) - 1) 1 initial with
        | .error e => .error e
        | .ok selected => .ok selected.candidate

theorem portfolio_cost_le_default {α : Type} {thoroughness : Nat}
    {candidate : Nat → Except LayoutError (Candidate α)} {out : Candidate α}
    (h : portfolio thoroughness candidate = .ok out) :
    ∃ first initial final,
      candidate 0 = .ok first ∧ softCost first.scene = .ok initial ∧
      softCost out.scene = .ok final ∧ final ≤ initial := by
  unfold portfolio at h
  generalize (if thoroughness = 0 then 3 else thoroughness) = count at h
  by_cases hh : 5 < count
  · simp only [hh, ↓reduceIte, reduceCtorEq] at h
  · simp only [hh, ↓reduceIte] at h
    cases hc : candidate 0 with
    | error e => simp only [hc] at h; cases h
    | ok first =>
      simp only [hc] at h
      cases hs : score first with
      | error e => simp only [hs] at h; cases h
      | ok initial =>
        simp only [hs] at h
        cases hr : run candidate (min count 5 - 1) 1 initial with
        | error e => simp only [hr] at h; cases h
        | ok selected =>
          simp only [hr, Except.ok.injEq] at h
          subst out
          have hi : softCost first.scene = .ok initial.cost := by
            unfold score at hs
            split at hs
            · cases hs
            · cases hs
              assumption
          exact ⟨first, initial.cost, selected.cost, rfl, hi,
            selected.cost_eq, run_cost_le candidate _ 1 initial selected hr⟩

def SameSelection {α : Type} (a b : Candidate α) : Prop :=
  a.value = b.value ∧ a.scene = b.scene

theorem consider_selected {α : Type} {a b out : Scored α}
    (h : consider a b = .ok out) :
    SameSelection out.candidate a.candidate ∨ SameSelection out.candidate b.candidate := by
  unfold consider at h
  cases hi : improves a.cost b.cost with
  | error e => simp [hi] at h
  | ok better =>
    rw [hi] at h
    cases better <;> simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    · subst out; exact Or.inl ⟨rfl, rfl⟩
    · subst out; exact Or.inr ⟨rfl, rfl⟩

private theorem score_selected {α : Type} {a : Candidate α} {out : Scored α}
    (h : score a = .ok out) : SameSelection out.candidate a := by
  unfold score at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

theorem run_selected {α : Type} (callback : Nat → Except LayoutError (Candidate α))
    (fuel index : Nat) (initial out : Scored α)
    (h : run callback fuel index initial = .ok out) :
    SameSelection out.candidate initial.candidate ∨
      ∃ i trial, index ≤ i ∧ i < index + fuel ∧ callback i = .ok trial ∧
        SameSelection out.candidate trial := by
  induction fuel generalizing index initial with
  | zero =>
    simp only [run, Except.ok.injEq] at h
    subst out
    exact Or.inl ⟨rfl, rfl⟩
  | succ fuel ih =>
    simp only [run] at h
    cases hc : callback index with
    | error e => simp [hc] at h
    | ok trial =>
      simp only [hc] at h
      cases hs : score trial with
      | error e => simp [hs] at h
      | ok scored =>
        simp only [hs] at h
        cases hn : consider initial scored with
        | error e => simp [hn] at h
        | ok next =>
          simp only [hn] at h
          rcases ih (index + 1) next h with hold | ⟨i, t, hlo, hhi, ht, same⟩
          · rcases consider_selected hn with old | fresh
            · exact Or.inl ⟨hold.1.trans old.1, hold.2.trans old.2⟩
            · have st := score_selected hs
              exact Or.inr ⟨index, trial, Nat.le_refl _, by omega, hc,
                ⟨hold.1.trans (fresh.1.trans st.1), hold.2.trans (fresh.2.trans st.2)⟩⟩
          · exact Or.inr ⟨i, t, by omega, by omega, ht, same⟩

theorem portfolio_selected {α : Type} {thoroughness : Nat}
    {callback : Nat → Except LayoutError (Candidate α)} {out : Candidate α}
    (h : portfolio thoroughness callback = .ok out) :
    ∃ index trial, index < 5 ∧ callback index = .ok trial ∧
      out.value = trial.value ∧ out.scene = trial.scene := by
  unfold portfolio at h
  generalize (if thoroughness = 0 then 3 else thoroughness) = count at h
  by_cases hh : 5 < count
  · simp only [hh, ↓reduceIte, reduceCtorEq] at h
  · simp only [hh, ↓reduceIte] at h
    cases hc : callback 0 with
    | error e => simp [hc] at h
    | ok first =>
      simp only [hc] at h
      cases hs : score first with
      | error e => simp [hs] at h
      | ok initial =>
        simp only [hs] at h
        cases hr : run callback (min count 5 - 1) 1 initial with
        | error e => simp [hr] at h
        | ok selected =>
          simp only [hr, Except.ok.injEq] at h
          subst out
          rcases run_selected callback (min count 5 - 1) 1 initial selected hr with
            same | ⟨i, t, _, hi, ht, same⟩
          · have st := score_selected hs
            exact ⟨0, first, by decide, hc, same.1.trans st.1, same.2.trans st.2⟩
          · exact ⟨i, t, by omega, ht, same.1, same.2⟩

end Elegant.Layered.Portfolio

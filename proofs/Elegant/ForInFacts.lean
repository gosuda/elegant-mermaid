import Std

set_option autoImplicit false

namespace Elegant

theorem forIn_processed {ε α β : Type}
    (processed remaining : List α) (initial output : β)
    (step : α → β → Except ε (ForInStep β))
    (P : List α → β → Prop) (hinit : P processed initial)
    (hstep : ∀ done a rest state next,
      processed ++ remaining = done ++ a :: rest →
      P done state → step a state = .ok next →
      ∃ state', next = .yield state' ∧ P (done ++ [a]) state')
    (h : ForIn.forIn remaining initial step = .ok output) :
    P (processed ++ remaining) output := by
  induction remaining generalizing processed initial with
  | nil =>
    change Except.ok initial = Except.ok output at h
    cases h
    simpa using hinit
  | cons a rest ih =>
    rw [List.forIn_cons] at h
    cases hs : step a initial with
    | error e => simp [hs, Bind.bind, Except.bind] at h
    | ok next =>
      obtain ⟨state', he, hp⟩ :=
        hstep processed a rest initial next rfl hinit hs
      subst next
      simp only [hs, Bind.bind, Except.bind] at h
      have htail := ih (processed ++ [a]) state' hp (by
        intro done b tail state next heq hstate hnext
        apply hstep done b tail state next
        · simpa only [List.append_assoc, List.singleton_append] using heq
        · exact hstate
        · exact hnext) h
      simpa only [List.append_assoc, List.singleton_append] using htail

end Elegant

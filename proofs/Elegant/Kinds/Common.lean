theorem guarded_ok {ε α : Type} {c : Prop} [Decidable c] {e : ε}
    {x : Except ε α} {y : α}
    (h : (if c then (throw e : Except ε PUnit) >>= (fun _ => x) else x) = .ok y) :
    x = .ok y := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    cases h
  · rwa [ite_eq_right hc] at h

theorem guarded_error {ε α : Type} {c : Prop} [Decidable c] {e : ε}
    {x : Except ε α} {y : α} (hc : c)
    (h : (if c then (throw e : Except ε PUnit) >>= (fun _ => x) else x) = .ok y) :
    False := by
  rw [ite_eq_left hc] at h
  cases h

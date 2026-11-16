private theorem startRow_sum (values : List Int) :
    (startRow values).1.sum = (startRow values).2.2 := by
  induction values with
  | nil => rfl
  | cons v vs ih =>
    by_cases hv : v = 0
    · simp [startRow, hv, ih]
    · simp [startRow, hv]

private theorem growRow_sum (alpha : Int) (row : List Int)
    (smallest largest total best : Int) (values : List Int)
    (hs : row.sum = total) :
    (growRow alpha row smallest largest total best values).1.sum =
      (growRow alpha row smallest largest total best values).2.2 := by
  induction values generalizing row smallest largest total best with
  | nil => exact hs
  | cons v vs ih =>
    simp only [growRow]
    split
    · exact hs
    · apply ih
      simp [List.sum_append, hs]

theorem nextRow_sum (values : List Int) (r : Tile) (remaining rho : Int)
    (hs : values.sum = remaining) :
    (nextRow values r remaining rho).1.sum =
      (nextRow values r remaining rho).2.2 := by
  have hstart := startRow_sum values
  cases he : startRow values with
  | mk row tail =>
    cases tail with
    | mk rest total =>
      simp only [he] at hstart
      simp only [nextRow, he]
      split
      · have hz : total = 0 := by simpa using ‹(total == 0) = true›
        simpa [hz] using hstart
      · split
        · exact hs
        · exact growRow_sum _ _ _ _ _ _ _ hstart

theorem nextRow_remaining_sum (values : List Int) (r : Tile) (remaining rho : Int)
    (hs : values.sum = remaining) :
    (nextRow values r remaining rho).2.1.sum =
      remaining - (nextRow values r remaining rho).2.2 := by
  have hp := congrArg List.sum (nextRow_partition values r remaining rho)
  rw [List.sum_append, nextRow_sum values r remaining rho hs, hs] at hp
  omega

private theorem startRow_zero (values : List Int)
    (hz : ∀ v ∈ values, v = 0) :
    startRow values = (values, [], 0) := by
  induction values with
  | nil => rfl
  | cons v vs ih =>
    have hv := hz v (by simp)
    have hvs : ∀ w ∈ vs, w = 0 := by
      intro w hw
      exact hz w (by simp [hw])
    simp [startRow, hv, ih hvs]

theorem nextRow_zero (values : List Int) (r : Tile) (rho : Int)
    (hz : ∀ v ∈ values, v = 0) :
    nextRow values r 0 rho = (values, [], 0) := by
  simp [nextRow, startRow_zero values hz]

theorem tileRows_nil (steps fuel : Nat) (r : Tile) (remaining rho : Int) :
    tileRows steps fuel [] r remaining rho = ([], false) := by
  cases steps <;> rfl

theorem tileRows_zero (steps fuel : Nat) (values : List Int) (r : Tile) (rho : Int)
    (hz : ∀ v ∈ values, v = 0) :
    (tileRows steps fuel values r 0 rho).1 = (placeRow values r 0 0).1 := by
  cases steps with
  | zero => rfl
  | succ steps =>
    cases values with
    | nil => rfl
    | cons v vs =>
      by_cases hf : fuel = 0
      · simp [tileRows, hf, tileRows_nil]
      · simp [tileRows, hf, nextRow_zero (v :: vs) r rho hz, tileRows_nil]

private theorem startRow_positive (values : List Int)
    (hn : ∀ v ∈ values, 0 ≤ v) (hs : 0 < values.sum) :
    0 < (startRow values).2.2 := by
  induction values with
  | nil => simp at hs
  | cons v vs ih =>
    have hv := hn v (by simp)
    have hvs : ∀ w ∈ vs, 0 ≤ w := fun w hw => hn w (by simp [hw])
    by_cases hz : v = 0
    · have hsum : 0 < vs.sum := by simpa [hz] using hs
      simpa [startRow, hz] using ih hvs hsum
    · have hp : 0 < v := by omega
      simpa [startRow, hz] using hp

private theorem growRow_positive (alpha : Int) (row : List Int)
    (smallest largest total best : Int) (values : List Int)
    (hn : ∀ v ∈ values, 0 ≤ v) (ht : 0 < total) :
    0 < (growRow alpha row smallest largest total best values).2.2 := by
  induction values generalizing row smallest largest total best with
  | nil => exact ht
  | cons v vs ih =>
    have hv := hn v (by simp)
    have hvs : ∀ w ∈ vs, 0 ≤ w := fun w hw => hn w (by simp [hw])
    simp only [growRow]
    split
    · exact ht
    · exact ih _ _ _ _ _ hvs (by omega)

theorem nextRow_positive (values : List Int) (r : Tile) (remaining rho : Int)
    (hn : ∀ v ∈ values, 0 ≤ v)
    (hs : values.sum = remaining) (hr : 0 < remaining) :
    0 < (nextRow values r remaining rho).2.2 := by
  have hstart := startRow_positive values hn (by omega)
  have hpartition := startRow_partition values
  cases he : startRow values with
  | mk row tail =>
    cases tail with
    | mk rest total =>
      simp only [he] at hstart hpartition
      have hrest : ∀ v ∈ rest, 0 ≤ v := by
        intro v hv
        apply hn v
        rw [← hpartition]
        exact List.mem_append.mpr (Or.inr hv)
      simp only [nextRow, he]
      split
      · have hz : total = 0 := by simpa using ‹(total == 0) = true›
        omega
      · split
        · exact hr
        · exact growRow_positive _ _ _ _ _ _ _ hrest hstart

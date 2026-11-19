import ElegantGeometry.Basic

namespace Elegant.Treemap

structure Tile where
  x0 : Int
  y0 : Int
  x1 : Int
  y1 : Int
  deriving DecidableEq, Repr

def roundDiv (a b : Int) : Int := Int.fdiv (2 * a + b) (2 * b)

def area (t : Tile) : Int := (t.x1 - t.x0) * (t.y1 - t.y0)

def collapseSpan (lo hi : Int) : Int × Int :=
  if hi < lo then
    let mid := Int.fdiv (lo + hi) 2
    (mid, mid)
  else (lo, hi)

def containedSpan (lo hi parentLo parentHi : Int) : Int × Int :=
  let span := collapseSpan lo hi
  (max parentLo (min parentHi span.1), max parentLo (min parentHi span.2))

def childArea (r : Tile) (padX padY header innerX innerY : Int) : Tile :=
  let hx := Int.fdiv innerX 2
  let hy := Int.fdiv innerY 2
  let xs := containedSpan (r.x0 + padX - hx) (r.x1 - (padX - hx)) r.x0 r.x1
  let ys := containedSpan (r.y0 + header + padY - hy) (r.y1 - (padY - hy)) r.y0 r.y1
  ⟨xs.1, ys.1, xs.2, ys.2⟩

def insetCell (r : Tile) (innerX innerY : Int) : Tile :=
  let hx := Int.fdiv innerX 2
  let hy := Int.fdiv innerY 2
  let xs := containedSpan (r.x0 + hx) (r.x1 - hx) r.x0 r.x1
  let ys := containedSpan (r.y0 + hy) (r.y1 - hy) r.y0 r.y1
  ⟨xs.1, ys.1, xs.2, ys.2⟩

def rowAspect (largest smallest total alpha : Int) : Int :=
  let beta := alpha * total * total
  max (Int.fdiv (largest * 2^80) beta) (Int.fdiv beta smallest)

def rowAlpha (r : Tile) (remaining rho : Int) : Int :=
  let dx := r.x1 - r.x0
  let dy := r.y1 - r.y0
  Int.fdiv (max dx dy * 2^70) (min dx dy * remaining * rho)

private def startRow : List Int → List Int × List Int × Int
  | [] => ([], [], 0)
  | v :: vs =>
    if v != 0 then ([v], vs, v)
    else
      let (row, rest, total) := startRow vs
      (v :: row, rest, total)

private def growRow (alpha : Int) (row : List Int) (smallest largest total best : Int) :
    List Int → List Int × List Int × Int
  | [] => (row, [], total)
  | v :: vs =>
    let next := rowAspect (max largest v) (min smallest v) (total + v) alpha
    if v == 0 || next > best then (row, v :: vs, total)
    else growRow alpha (row ++ [v]) (min smallest v) (max largest v) (total + v) next vs

def nextRow (values : List Int) (r : Tile) (remaining rho : Int) :
    List Int × List Int × Int :=
  let (row, rest, total) := startRow values
  if total == 0 then (row, rest, 0)
  else if min (r.x1 - r.x0) (r.y1 - r.y0) == 0 then (values, [], remaining)
  else
    let alpha := rowAlpha r remaining rho
    growRow alpha row total total total (rowAspect total total total alpha) rest

def placeCells (r : Tile) (dice : Bool) (along thickness total : Int)
    (cumulative previous : Int) : List Int → List Tile
  | [] => []
  | v :: vs =>
    let cumulative' := cumulative + v
    let boundary := if total > 0 then roundDiv (along * cumulative') total else 0
    let cell := if dice then
        Tile.mk (r.x0 + previous) r.y0 (r.x0 + boundary) (r.y0 + thickness)
      else Tile.mk r.x0 (r.y0 + previous) (r.x0 + thickness) (r.y0 + boundary)
    cell :: placeCells r dice along thickness total cumulative' boundary vs

def placeRow (values : List Int) (r : Tile) (total remaining : Int) : List Tile × Tile :=
  let dx := r.x1 - r.x0
  let dy := r.y1 - r.y0
  let dice := decide (dx < dy)
  let along := if dice then dx else dy
  let across := if dice then dy else dx
  let thickness := if total > 0 && remaining > 0 then roundDiv (across * total) remaining else across
  let cells := placeCells r dice along thickness total 0 0 values
  let rest := if dice then { r with y0 := r.y0 + thickness }
    else { r with x0 := r.x0 + thickness }
  (cells, rest)

def tileRows : Nat → Nat → List Int → Tile → Int → Int → List Tile × Bool
  | 0, _, values, r, remaining, _ => ((placeRow values r remaining remaining).1, !values.isEmpty)
  | _ + 1, _, [], _, _, _ => ([], false)
  | steps + 1, fuel, values, r, remaining, rho =>
    let (row, rest, total) := if fuel == 0 then (values, [], remaining)
      else nextRow values r remaining rho
    let (cells, free) := placeRow row r total remaining
    let (later, capped) := tileRows steps (fuel - 1) rest free (remaining - total) rho
    (cells ++ later, fuel == 0 || capped)

def squarify (values : List Int) (r : Tile) (rho : Int) (fuel : Nat) :
    Except LayoutError (List Tile × Bool) :=
  let total := values.foldl (· + ·) 0
  if values.any (· < 0) || total > 2^31 || rho <= 0 || r.x1 < r.x0 || r.y1 < r.y0 then
    .error .domain
  else .ok (tileRows values.length fuel values r total rho)

private theorem placeCells_length (r : Tile) (dice : Bool) (along thickness total cumulative previous : Int)
    (values : List Int) :
    (placeCells r dice along thickness total cumulative previous values).length = values.length := by
  induction values generalizing cumulative previous with
  | nil => rfl
  | cons v vs ih => simp [placeCells, ih]

theorem placeRow_length (values : List Int) (r : Tile) (total remaining : Int) :
    (placeRow values r total remaining).1.length = values.length := by
  simp only [placeRow]
  exact placeCells_length _ _ _ _ _ _ _ _

private theorem startRow_partition (values : List Int) :
    let (row, rest, _) := startRow values
    row ++ rest = values := by
  induction values with
  | nil => rfl
  | cons v vs ih =>
    simp only [startRow]
    split
    · rfl
    · simpa only [List.cons_append] using congrArg (List.cons v) ih

private theorem startRow_nonempty (v : Int) (vs : List Int) :
    (startRow (v :: vs)).1 ≠ [] := by
  simp only [startRow]
  split <;> simp

private theorem growRow_partition (alpha : Int) (row : List Int)
    (smallest largest total best : Int) (values : List Int) :
    let (out, rest, _) := growRow alpha row smallest largest total best values
    out ++ rest = row ++ values := by
  induction values generalizing row smallest largest total best with
  | nil => simp [growRow]
  | cons v vs ih =>
    simp only [growRow]
    split
    · rfl
    · simpa only [List.append_assoc, List.singleton_append] using
        ih (row ++ [v]) (min smallest v) (max largest v) (total + v)
          (rowAspect (max largest v) (min smallest v) (total + v) alpha)

theorem nextRow_partition (values : List Int) (r : Tile) (remaining rho : Int) :
    (nextRow values r remaining rho).1 ++ (nextRow values r remaining rho).2.1 = values := by
  have hp := startRow_partition values
  cases he : startRow values with
  | mk row tail =>
    cases tail with
    | mk rest total =>
      simp only [he] at hp
      simp only [nextRow, he]
      split
      · exact hp
      · split
        · simp
        · exact (growRow_partition _ _ _ _ _ _ _).trans hp

private theorem growRow_nonempty (alpha : Int) (row : List Int)
    (smallest largest total best : Int) (values : List Int) (h : row ≠ []) :
    (growRow alpha row smallest largest total best values).1 ≠ [] := by
  induction values generalizing row smallest largest total best with
  | nil => exact h
  | cons v vs ih =>
    simp only [growRow]
    split
    · exact h
    · apply ih
      simp

theorem nextRow_nonempty (v : Int) (vs : List Int) (r : Tile) (remaining rho : Int) :
    (nextRow (v :: vs) r remaining rho).1 ≠ [] := by
  have hn := startRow_nonempty v vs
  cases he : startRow (v :: vs) with
  | mk row tail =>
    cases tail with
    | mk rest total =>
      simp only [he] at hn
      simp only [nextRow, he]
      split
      · exact hn
      · split
        · simp
        · exact growRow_nonempty _ _ _ _ _ _ _ hn

theorem nextRow_rest_shorter (v : Int) (vs : List Int) (r : Tile) (remaining rho : Int) :
    (nextRow (v :: vs) r remaining rho).2.1.length < (v :: vs).length := by
  have hp := congrArg List.length (nextRow_partition (v :: vs) r remaining rho)
  have hn := nextRow_nonempty v vs r remaining rho
  have hz : 0 < (nextRow (v :: vs) r remaining rho).1.length := by
    cases he : (nextRow (v :: vs) r remaining rho).1 with
    | nil => exact False.elim (hn he)
    | cons a rest => simp
  simp only [List.length_append] at hp
  omega

private theorem tileRows_length (steps fuel : Nat) (values : List Int)
    (r : Tile) (remaining rho : Int) :
    (tileRows steps fuel values r remaining rho).1.length = values.length := by
  induction steps generalizing fuel values r remaining with
  | zero => simp [tileRows, placeRow_length]
  | succ steps ih =>
    cases values with
    | nil => rfl
    | cons v vs =>
      simp only [tileRows]
      split
      · simp [List.length_append, placeRow_length, ih]
      · have hp := congrArg List.length (nextRow_partition (v :: vs) r remaining rho)
        simpa only [List.length_append, placeRow_length, ih] using hp

theorem squarify_length (values : List Int) (r : Tile) (rho : Int) (fuel : Nat)
    (out : List Tile) (capped : Bool)
    (h : squarify values r rho fuel = .ok (out, capped)) :
    out.length = values.length := by
  unfold squarify at h
  dsimp only at h
  split at h
  · contradiction
  · have he := Except.ok.inj h
    have hp := congrArg (fun p : List Tile × Bool => p.1.length) he
    exact hp.symm.trans (tileRows_length _ _ _ _ _ _)

private theorem tileRows_uncapped (steps fuel : Nat) (values : List Int)
    (r : Tile) (remaining rho : Int)
    (hs : values.length ≤ steps) (hf : values.length ≤ fuel) :
    (tileRows steps fuel values r remaining rho).2 = false := by
  induction steps generalizing fuel values r remaining with
  | zero =>
    have hv : values = [] := by cases values <;> simp_all
    subst values
    rfl
  | succ steps ih =>
    cases values with
    | nil => rfl
    | cons v vs =>
      cases fuel with
      | zero => simp only [List.length_cons] at hf; omega
      | succ fuel =>
        let next := nextRow (v :: vs) r remaining rho
        have short := nextRow_rest_shorter v vs r remaining rho
        have hr : next.2.1.length ≤ steps := by
          dsimp [next]
          simp only [List.length_cons] at hs short
          omega
        have hfuel : next.2.1.length ≤ fuel := by
          dsimp [next]
          simp only [List.length_cons] at hf short
          omega
        change (tileRows steps fuel next.2.1
          (placeRow next.1 r next.2.2 remaining).2 (remaining - next.2.2) rho).2 = false
        exact ih _ _ _ _ hr hfuel

theorem treemap_squarify_fuel (values : List Int) (r : Tile) (rho : Int) (fuel : Nat)
    (out : List Tile) (capped : Bool) (hf : values.length ≤ fuel)
    (h : squarify values r rho fuel = .ok (out, capped)) :
    out.length = values.length ∧ capped = false := by
  refine ⟨squarify_length values r rho fuel out capped h, ?_⟩
  unfold squarify at h
  dsimp only at h
  split at h
  · contradiction
  · have he := Except.ok.inj h
    have hp := congrArg (fun p : List Tile × Bool => p.2) he
    exact hp.symm.trans (tileRows_uncapped _ _ _ _ _ _ (Nat.le_refl _) hf)

theorem zero_row_areas (values : List Int) (r : Tile) :
    ((placeRow values r 0 0).1.map area).sum = 0 := by
  have aux : ∀ (vs : List Int) (dice : Bool) (along thickness cumulative : Int),
      ((placeCells r dice along thickness 0 cumulative 0 vs).map area).sum = 0 := by
    intro vs
    induction vs with
    | nil => intros; rfl
    | cons v vs ih =>
      intro dice along thickness cumulative
      cases dice <;> simp [placeCells, area, ih]
  unfold placeRow
  exact aux _ _ _ _ _

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

end Elegant.Treemap

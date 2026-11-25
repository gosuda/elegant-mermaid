import Elegant.Layered.VisibilityRoute

set_option autoImplicit false

namespace Elegant.Layered.Visibility

private theorem eraseDups_nodup (values : List Int) : values.eraseDups.Nodup := by
  suffices byLength : ∀ n (l : List Int), l.length ≤ n → l.eraseDups.Nodup from
    byLength values.length values (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hlen
    cases l with
    | nil => simp
    | cons a rest =>
      simp only [List.length_cons] at hlen
      omega
  | succ n ih =>
    intro l hlen
    cases l with
    | nil => simp
    | cons a rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro ha
        have kept := (List.mem_filter.mp (List.mem_eraseDups.mp ha)).2
        simp at kept
      · apply ih
        have filtered := List.length_filter_le (fun b : Int => !(b == a)) rest
        simp only [List.length_cons] at hlen
        omega

theorem sortedLines_nodup (values : List Int) : (sortedLines values).toList.Nodup := by
  unfold sortedLines
  rw [List.toList_toArray]
  exact eraseDups_nodup _

theorem newGrid_nodup (obstacles : List Rect) (points : List Point) (bound : Option Rect) :
    (newGrid obstacles points bound).xs.toList.Nodup ∧
    (newGrid obstacles points bound).ys.toList.Nodup := by
  cases bound <;> simp only [newGrid] <;> exact ⟨sortedLines_nodup _, sortedLines_nodup _⟩

private theorem neighbour_index_cases {g : Grid} {current next : Vertex}
    (hnext : next ∈ g.neighbours current) :
    (0 < current.x ∧ next = ⟨current.x - 1, current.y, 0⟩) ∨
    (current.x + 1 < g.xs.size ∧ next = ⟨current.x + 1, current.y, 0⟩) ∨
    (0 < current.y ∧ next = ⟨current.x, current.y - 1, 1⟩) ∨
    (current.y + 1 < g.ys.size ∧ next = ⟨current.x, current.y + 1, 1⟩) := by
  simpa only [Grid.neighbours, List.mem_append, List.mem_ite_nil_right,
    List.mem_singleton, or_assoc] using hnext

theorem Grid.neighbour_bounds {g : Grid} {current next : Vertex}
    (hx : current.x < g.xs.size) (hy : current.y < g.ys.size)
    (hnext : next ∈ g.neighbours current) : next.x < g.xs.size ∧ next.y < g.ys.size := by
  rcases neighbour_index_cases hnext with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;>
    dsimp only <;> constructor <;> omega

private theorem line_delta_pos {xs : Array Int} {i j : Nat}
    (unique : xs.toList.Nodup) (hi : i < xs.size) (hj : j < xs.size) (different : i ≠ j) :
    0 < (xs[i]! - xs[j]!).natAbs := by
  apply Int.natAbs_pos.mpr
  rw [getElem!_pos xs i hi, getElem!_pos xs j hj]
  intro h
  have same : xs.toList[i]'hi = xs.toList[j]'hj := by
    simpa only [Array.getElem_toList] using Int.sub_eq_zero.mp h
  exact different ((List.Nodup.getElem_inj (hi := hi) (hj := hj) unique).mp same)

theorem Grid.step_dist_lt_of_neighbour {g : Grid} {current next : Vertex}
    (xUnique : g.xs.toList.Nodup) (yUnique : g.ys.toList.Nodup)
    (hx : current.x < g.xs.size) (hy : current.y < g.ys.size)
    (hnext : next ∈ g.neighbours current) (cost : Cost) :
    cost.dist < (g.step current next cost).dist := by
  obtain ⟨nextX, nextY⟩ := Grid.neighbour_bounds hx hy hnext
  have positive :
      0 < ((g.point current).x - (g.point next).x).natAbs ∨
      0 < ((g.point current).y - (g.point next).y).natAbs := by
    rcases neighbour_index_cases hnext with ⟨left, rfl⟩ | ⟨_, rfl⟩ | ⟨down, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inl (line_delta_pos (i := current.x) (j := current.x - 1)
        xUnique hx nextX (by omega))
    · exact Or.inl (line_delta_pos (i := current.x) (j := current.x + 1)
        xUnique hx nextX (by omega))
    · exact Or.inr (line_delta_pos (i := current.y) (j := current.y - 1)
        yUnique hy nextY (by omega))
    · exact Or.inr (line_delta_pos (i := current.y) (j := current.y + 1)
        yUnique hy nextY (by omega))
  change cost.dist < cost.dist + (((g.point current).x - (g.point next).x).natAbs : Int) +
    (((g.point current).y - (g.point next).y).natAbs : Int)
  rcases positive with dx | dy <;> omega

theorem newGrid_step_dist_lt_of_neighbour
    {obstacles : List Rect} {points : List Point} {bound : Option Rect}
    {current next : Vertex}
    (hx : current.x < (newGrid obstacles points bound).xs.size)
    (hy : current.y < (newGrid obstacles points bound).ys.size)
    (hnext : next ∈ (newGrid obstacles points bound).neighbours current) (cost : Cost) :
    cost.dist < ((newGrid obstacles points bound).step current next cost).dist := by
  have unique := newGrid_nodup obstacles points bound
  exact Grid.step_dist_lt_of_neighbour unique.1 unique.2 hx hy hnext cost

end Elegant.Layered.Visibility

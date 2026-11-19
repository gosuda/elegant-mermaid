import Elegant.GridArchitecturePlacementFacts
import Elegant.GridArchitectureHierarchy

set_option autoImplicit false

namespace Elegant.Grid.Architecture

def unplacedCount : List Bool → Nat
  | [] => 0
  | false :: rest => unplacedCount rest + 1
  | true :: rest => unplacedCount rest

theorem unplacedCount_le_length (flags : List Bool) : unplacedCount flags ≤ flags.length := by
  induction flags with
  | nil => exact Nat.le_refl _
  | cons flag rest ih => cases flag <;> simp only [unplacedCount,List.length_cons] <;> omega

theorem mark_decreases_unplaced (flags : List Bool) (index : Nat)
    (h : flags[index]? = some false) :
    unplacedCount (flags.set index true) + 1 = unplacedCount flags := by
  induction flags generalizing index with
  | nil => simp at h
  | cons flag rest ih =>
    cases index with
    | zero =>
      have heq : flag = false := by simpa using h
      subst flag
      simp [unplacedCount]
    | succ index =>
      have tail : rest[index]? = some false := by simpa using h
      have step := ih index tail
      cases flag <;> simp only [List.set_cons_succ,unplacedCount] <;> omega

/-- Queue length plus the number of unvisited units is the exact native BFS
potential. A newly discovered unit leaves `unplacedCount` and enters the queue. -/
def queuePotential (l : Level) (queue : List Nat) : Nat :=
  unplacedCount l.placed + queue.length

theorem enqueue_preserves_potential (p : Params) (l : Level) (queue : List Nat)
    (v : Nat) (c : Cell) (fresh : l.placed[v]? = some false) :
    queuePotential (put p l v c) (queue ++ [v]) = queuePotential l queue := by
  have count := mark_decreases_unplaced l.placed v fresh
  simp only [queuePotential,put,List.length_append,List.length_cons,List.length_nil]
  omega

theorem fresh_of_getD_false (flags : List Bool) (i : Nat)
    (bound : i < flags.length) (fresh : flags.getD i false = false) :
    flags[i]? = some false := by
  have lookup := List.getElem?_eq_getElem bound
  rw [List.getD_eq_getElem?_getD,lookup] at fresh
  change flags[i] = false at fresh
  rw [lookup]
  exact congrArg some fresh

theorem pop_decreases_potential (l : Level) (u : Nat) (queue : List Nat) :
    queuePotential l (u :: queue) = queuePotential l queue + 1 := by
  simp only [queuePotential,List.length_cons]
  omega

def expandOne (p : Params) (u : Nat) (state : Level × List Nat) (e : Edge) : Level × List Nat :=
  if e.a != u && e.b != u then state else
  let v := if e.b = u then e.a else e.b
  let side := if e.b = u then e.sideB else e.sideA
  if state.1.placed.getD v false then state
  else (put p state.1 v (choose p state.1 v u side),state.2 ++ [v])

theorem expandOne_length (p : Params) (u : Nat) (state : Level × List Nat) (e : Edge) :
    (expandOne p u state e).1.placed.length = state.1.placed.length := by
  unfold expandOne
  split
  · rfl
  · split <;> dsimp only <;> split
    all_goals first | rfl | exact put_placed_length _ _ _ _

theorem expandOne_potential (p : Params) (u : Nat) (state : Level × List Nat) (e : Edge)
    (ha : e.a < state.1.placed.length) (hb : e.b < state.1.placed.length) :
    queuePotential (expandOne p u state e).1 (expandOne p u state e).2 =
      queuePotential state.1 state.2 := by
  unfold expandOne
  split
  · rfl
  · split <;> dsimp only <;> split
    all_goals first
      | rfl
      | apply enqueue_preserves_potential
        apply fresh_of_getD_false
        · first | exact ha | exact hb
        · simp_all

theorem expand_potential (p : Params) (u : Nat) (l : Level) (queue : List Nat)
    (valid : ∀ e ∈ l.edges, e.a < l.placed.length ∧ e.b < l.placed.length) :
    queuePotential (expand p u l queue).1 (expand p u l queue).2 = queuePotential l queue := by
  have fold : ∀ (es : List Edge) (state : Level × List Nat),
      (∀ e ∈ es, e.a < state.1.placed.length ∧ e.b < state.1.placed.length) →
      queuePotential (es.foldl (expandOne p u) state).1 (es.foldl (expandOne p u) state).2 =
        queuePotential state.1 state.2 := by
    intro es
    induction es with
    | nil => intro state _; rfl
    | cons e rest ih =>
      intro state h
      simp only [List.foldl_cons]
      rw [ih]
      · exact expandOne_potential p u state e (h e (by simp)).1 (h e (by simp)).2
      · intro edge he
        rw [expandOne_length]
        exact h edge (by simp [he])
  exact fold l.edges (l,queue) valid

theorem expand_edges (p : Params) (u : Nat) (l : Level) (queue : List Nat) :
    (expand p u l queue).1.edges = l.edges := by
  have one : ∀ (state : Level × List Nat) (e : Edge),
      (expandOne p u state e).1.edges = state.1.edges := by
    intro state e
    unfold expandOne
    split
    · rfl
    · split <;> dsimp only <;> split <;> rfl
  have fold : ∀ (es : List Edge) (state : Level × List Nat),
      (es.foldl (expandOne p u) state).1.edges = state.1.edges := by
    intro es
    induction es with
    | nil => intro state; rfl
    | cons e rest ih =>
      intro state
      simp only [List.foldl_cons]
      rw [ih,one]
  exact fold l.edges (l,queue)

theorem drain_count_bound (p : Params) (fuel : Nat) (l : Level) (queue : List Nat)
    (valid : ∀ e ∈ l.edges, e.a < l.placed.length ∧ e.b < l.placed.length) :
    fuel - (drain p fuel l queue).2 +
      unplacedCount (drain p fuel l queue).1.placed ≤ queuePotential l queue := by
  induction fuel generalizing l queue with
  | zero =>
    cases queue <;> simp only [drain,queuePotential,Nat.zero_sub,Nat.zero_add,List.length_nil,List.length_cons] <;> omega
  | succ fuel ih =>
    cases queue with
    | nil => simp only [drain,queuePotential,List.length_nil,Nat.sub_self,Nat.zero_add,Nat.add_zero,Nat.le_refl]
    | cons u rest =>
      have preserved := expand_potential p u l rest valid
      have nextValid : ∀ e ∈ (expand p u l rest).1.edges,
          e.a < (expand p u l rest).1.placed.length ∧ e.b < (expand p u l rest).1.placed.length := by
        rw [expand_edges,expand_placed_length]
        exact valid
      have inductiveBound := ih (expand p u l rest).1 (expand p u l rest).2 nextValid
      have remaining := drain_fuel_le p fuel (expand p u l rest).1 (expand p u l rest).2
      have potential := pop_decreases_potential l u rest
      simp only [drain]
      omega

theorem drain_edges (p : Params) (fuel : Nat) (l : Level) (queue : List Nat) :
    (drain p fuel l queue).1.edges = l.edges := by
  induction fuel generalizing l queue with
  | zero => cases queue <;> rfl
  | succ fuel ih =>
    cases queue with
    | nil => rfl
    | cons u rest =>
      simp only [drain]
      rw [ih,expand_edges]

theorem visit_edges (p : Params) (state : Level × Nat) (first : Nat) :
    (visit p state first).1.edges = state.1.edges := by
  unfold visit
  split
  · rfl
  · rw [drain_edges]
    rfl

theorem visit_fuel_le (p : Params) (state : Level × Nat) (first : Nat) :
    (visit p state first).2 ≤ state.2 := by
  unfold visit
  split
  · exact Nat.le_refl _
  · exact drain_fuel_le _ _ _ _

theorem visit_count_bound (p : Params) (state : Level × Nat) (first : Nat)
    (bound : first < state.1.placed.length)
    (valid : ∀ e ∈ state.1.edges, e.a < state.1.placed.length ∧ e.b < state.1.placed.length) :
    state.2 - (visit p state first).2 + unplacedCount (visit p state first).1.placed ≤
      unplacedCount state.1.placed := by
  unfold visit
  split
  · simp
  · rename_i hnot
    have freshD : state.1.placed.getD first false = false := by simp_all
    have fresh := fresh_of_getD_false state.1.placed first bound freshD
    have count := mark_decreases_unplaced state.1.placed first fresh
    have nextValid : ∀ e ∈ (put p state.1 first (seedCell p state.1 first)).edges,
        e.a < (put p state.1 first (seedCell p state.1 first)).placed.length ∧
        e.b < (put p state.1 first (seedCell p state.1 first)).placed.length := by
      simpa only [put,List.length_set] using valid
    have inductiveBound := drain_count_bound p state.2 (put p state.1 first (seedCell p state.1 first)) [first] nextValid
    change state.2 - (drain p state.2 (put p state.1 first (seedCell p state.1 first)) [first]).2 + unplacedCount (drain p state.2 (put p state.1 first (seedCell p state.1 first)) [first]).1.placed ≤ unplacedCount (state.1.placed.set first true) + 1 at inductiveBound
    omega

theorem visit_fold_count_bound (p : Params) (indices : List Nat) (state : Level × Nat)
    (bounds : ∀ i ∈ indices, i < state.1.placed.length)
    (valid : ∀ e ∈ state.1.edges, e.a < state.1.placed.length ∧ e.b < state.1.placed.length) :
    state.2 - (indices.foldl (visit p) state).2 +
        unplacedCount (indices.foldl (visit p) state).1.placed ≤ unplacedCount state.1.placed ∧
      (indices.foldl (visit p) state).2 ≤ state.2 := by
  induction indices generalizing state with
  | nil => simp
  | cons first rest ih =>
    have step := visit_count_bound p state first (bounds first (by simp)) valid
    have fuel := visit_fuel_le p state first
    have nextBounds : ∀ i ∈ rest, i < (visit p state first).1.placed.length := by
      intro i hi
      rw [visit_placed_length]
      exact bounds i (by simp [hi])
    have nextValid : ∀ e ∈ (visit p state first).1.edges,
        e.a < (visit p state first).1.placed.length ∧ e.b < (visit p state first).1.placed.length := by
      rw [visit_edges,visit_placed_length]
      exact valid
    have inductiveBound := ih (visit p state first) nextBounds nextValid
    simp only [List.foldl_cons]
    omega

theorem arrange_count_bound (p : Params) (fuel : Nat) (l : Level)
    (lengths : l.placed.length = l.units.length)
    (valid : ∀ e ∈ l.edges, e.a < l.placed.length ∧ e.b < l.placed.length) :
    fuel - (arrange p fuel l).2 ≤ l.units.length := by
  have bounds : ∀ i ∈ List.range l.units.length, i < l.placed.length := by
    intro i hi
    have h := List.mem_range.mp hi
    omega
  have inductiveBound := visit_fold_count_bound p (List.range l.units.length) (l,fuel) bounds valid
  have count := unplacedCount_le_length l.placed
  have used := inductiveBound.1
  change fuel - (arrange p fuel l).2 +
    unplacedCount (arrange p fuel l).1.placed ≤ unplacedCount l.placed at used
  omega

/-- All actual placement units: service/junction nodes, virtual nodes for empty
leaf groups, and the group units themselves. -/
def placementUnitCount (input : Input) : Nat :=
  (virtualParents input).length + input.groups.length

/-- The user-approved corrected global pop-count statement. -/
def ArchPopsBounded (input : Input) (p : Params) (fp : FrameParams) (fuel : Nat) : Prop :=
  fuel - (placeHierarchy input p fp fuel).fuel ≤ placementUnitCount input

end Elegant.Grid.Architecture

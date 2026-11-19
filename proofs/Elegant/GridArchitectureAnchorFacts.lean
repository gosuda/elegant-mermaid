import Elegant.GridArchitectureLevelFacts
import Elegant.GridArchitecturePartitionFacts

set_option autoImplicit false

namespace Elegant.Grid.Architecture

def VisitedValue (l : Level) (i : Nat) (c : Cell) : Prop :=
  l.placed.getD i false = true ∧ l.cells.getD i default = c

private theorem put_preserves_visited (p : Params) (l : Level) (v i : Nat) (c old : Cell)
    (fresh : l.placed.getD v false = false) (visited : VisitedValue l i old) :
    VisitedValue (put p l v c) i old := by
  have different : v ≠ i := by
    intro same
    subst v
    rw [visited.1] at fresh
    contradiction
  simpa only [VisitedValue,put,List.getD_eq_getElem?_getD,List.getElem?_set_ne different] using visited

theorem expandOne_preserves_visited (p : Params) (u : Nat) (state : Level × List Nat) (e : Edge)
    (i : Nat) (c : Cell) (visited : VisitedValue state.1 i c) :
    VisitedValue (expandOne p u state e).1 i c := by
  unfold expandOne
  split
  · exact visited
  · split <;> dsimp only <;> split
    all_goals first
      | exact visited
      | apply put_preserves_visited
        · simp_all
        · exact visited

theorem expand_preserves_visited (p : Params) (u : Nat) (l : Level) (queue : List Nat)
    (i : Nat) (c : Cell) (visited : VisitedValue l i c) :
    VisitedValue (expand p u l queue).1 i c := by
  have fold : ∀ (es : List Edge) (state : Level × List Nat),
      VisitedValue state.1 i c → VisitedValue (es.foldl (expandOne p u) state).1 i c := by
    intro es
    induction es with
    | nil => intro state h; exact h
    | cons e rest ih =>
      intro state h
      simp only [List.foldl_cons]
      exact ih _ (expandOne_preserves_visited p u state e i c h)
  exact fold l.edges (l,queue) visited

theorem drain_preserves_visited (p : Params) (fuel : Nat) (l : Level) (queue : List Nat)
    (i : Nat) (c : Cell) (visited : VisitedValue l i c) :
    VisitedValue (drain p fuel l queue).1 i c := by
  induction fuel generalizing l queue with
  | zero => cases queue <;> exact visited
  | succ fuel ih =>
    cases queue with
    | nil => exact visited
    | cons u rest =>
      simp only [drain]
      exact ih _ _ (expand_preserves_visited p u l rest i c visited)

theorem visit_preserves_visited (p : Params) (state : Level × Nat) (first i : Nat)
    (c : Cell) (visited : VisitedValue state.1 i c) :
    VisitedValue (visit p state first).1 i c := by
  unfold visit
  split
  · exact visited
  · apply drain_preserves_visited
    apply put_preserves_visited
    · simp_all
    · exact visited

theorem fold_visit_preserves_visited (p : Params) (indices : List Nat) (state : Level × Nat)
    (i : Nat) (c : Cell) (visited : VisitedValue state.1 i c) :
    VisitedValue (indices.foldl (visit p) state).1 i c := by
  induction indices generalizing state with
  | nil => exact visited
  | cons first rest ih =>
    simp only [List.foldl_cons]
    exact ih _ (visit_preserves_visited p state first i c visited)

theorem arrange_first_visited (p : Params) (fuel : Nat) (l : Level)
    (positive : 0 < l.units.length) (lengths : l.placed.length = l.units.length)
    (cells : l.cells.length = l.placed.length) (empty : l.bounds = emptySpan)
    (unmarked : ∀ i, l.placed.getD i false = false) :
    VisitedValue (arrange p fuel l).1 0 ⟨0,0⟩ := by
  have firstBound : 0 < l.placed.length := by omega
  have seed : seedCell p l 0 = ⟨0,0⟩ := by simp [seedCell,empty]
  have initial : VisitedValue (put p l 0 (seedCell p l 0)) 0 ⟨0,0⟩ := by
    constructor
    · simp only [put,List.getD_eq_getElem?_getD,List.getElem?_set_self firstBound,Option.getD_some]
    · simp only [put,List.getD_eq_getElem?_getD,List.getElem?_set_self (by omega : 0 < l.cells.length),Option.getD_some,seed]
  unfold arrange
  change VisitedValue ((List.range l.units.length).foldl (visit p) (l,fuel)).1 0 ⟨0,0⟩
  cases indices : List.range l.units.length with
  | nil =>
    have length := congrArg List.length indices
    simp only [List.length_range,List.length_nil] at length
    omega
  | cons first rest =>
    have head := List.head?_range (n := l.units.length)
    rw [indices] at head
    have nonzero : l.units.length ≠ 0 := by omega
    have equal : first = 0 := by simpa [nonzero] using head
    subst first
    simp only [List.foldl_cons]
    apply fold_visit_preserves_visited
    unfold visit
    simp only [unmarked,Bool.false_eq_true,↓reduceIte]
    exact drain_preserves_visited p fuel _ [0] 0 ⟨0,0⟩ initial

private theorem expandOne_rects (p : Params) (u : Nat) (state : Level × List Nat) (e : Edge) :
    (expandOne p u state e).1.rects = state.1.rects := by
  unfold expandOne
  split
  · rfl
  · split <;> dsimp only <;> split <;> rfl

theorem expand_rects (p : Params) (u : Nat) (l : Level) (queue : List Nat) :
    (expand p u l queue).1.rects = l.rects := by
  have fold : ∀ (es : List Edge) (state : Level × List Nat),
      (es.foldl (expandOne p u) state).1.rects = state.1.rects := by
    intro es
    induction es with
    | nil => intro state; rfl
    | cons e rest ih =>
      intro state
      simp only [List.foldl_cons]
      rw [ih,expandOne_rects]
  exact fold l.edges (l,queue)

theorem drain_rects (p : Params) (fuel : Nat) (l : Level) (queue : List Nat) :
    (drain p fuel l queue).1.rects = l.rects := by
  induction fuel generalizing l queue with
  | zero => cases queue <;> rfl
  | succ fuel ih =>
    cases queue with
    | nil => rfl
    | cons u rest => simp only [drain]; rw [ih,expand_rects]

theorem visit_rects (p : Params) (state : Level × Nat) (first : Nat) :
    (visit p state first).1.rects = state.1.rects := by
  unfold visit
  split
  · rfl
  · rw [drain_rects]
    rfl

theorem arrange_rects (p : Params) (fuel : Nat) (l : Level) :
    (arrange p fuel l).1.rects = l.rects := by
  have fold : ∀ (indices : List Nat) (state : Level × Nat),
      (indices.foldl (visit p) state).1.rects = state.1.rects := by
    intro indices
    induction indices with
    | nil => intro state; rfl
    | cons first rest ih => intro state; simp only [List.foldl_cons]; rw [ih,visit_rects]
  exact fold (List.range l.units.length) (l,fuel)

theorem arrange_placed_length (p : Params) (fuel : Nat) (l : Level) :
    (arrange p fuel l).1.placed.length = l.placed.length := by
  have fold : ∀ (indices : List Nat) (state : Level × Nat),
      (indices.foldl (visit p) state).1.placed.length = state.1.placed.length := by
    intro indices
    induction indices with
    | nil => intro state; rfl
    | cons first rest ih => intro state; simp only [List.foldl_cons]; rw [ih,visit_placed_length]
  exact fold (List.range l.units.length) (l,fuel)

private theorem getD_mem {α : Type} (items : List α) (i : Nat) (fallback : α) (bound : i < items.length) :
    items.getD i fallback ∈ items := by
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using List.getElem_mem bound

theorem arrange_frame_anchor (input : Input) (p : Params) (fp : FrameParams) (relative : List Span)
    (parent : Int) (fuel : Nat) (g : Group) (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (positive : 0 < (levelOf input p relative parent).units.length)
    (anchors : AnchorsInvariant p (levelOf input p relative parent)) :
    ContainsAnchor p (frameOf fp g
      ((arrange p fuel (levelOf input p relative parent)).1.absolute.foldl Span.union emptySpan)) := by
  let l := levelOf input p relative parent
  have lengths := level_placed_length input p relative parent
  have initial := initial_level_invariant input p relative parent anchors
  have invariant := arrange_level_invariant p fuel l px py initial lengths
    (level_edges_bound input p relative parent positive)
  have cellLengths : l.cells.length = l.placed.length := by simp only [l,levelOf,List.length_replicate]
  have empty : l.bounds = emptySpan := rfl
  have unmarked : ∀ i, l.placed.getD i false = false := by
    intro i
    simp only [l,levelOf,List.getD_eq_getElem?_getD,List.getElem?_replicate]
    split <;> rfl
  have first := arrange_first_visited p fuel l positive lengths cellLengths empty unmarked
  have bound : 0 < (arrange p fuel l).1.placed.length := by
    rw [arrange_placed_length]
    change 0 < (levelOf input p relative parent).placed.length
    rw [lengths]
    exact positive
  have actual := invariant.2.1.2.2 0 bound first.1
  simp only [arrange_rects,first.2,Span.shift,Int.zero_mul,Int.add_zero] at actual
  have anchor : ContainsAnchor p ((arrange p fuel l).1.absolute.getD 0 default) := by
    rw [actual]
    exact anchors 0 (by omega)
  exact frame_contains_anchor p fp g _ padding line _
    (getD_mem _ 0 default (by rw [invariant.2.1.1]; exact bound)) anchor

theorem group_has_placement_unit (input : Input) (g : Nat) (valid : g < input.groups.length) :
    Int.ofNat g ∈ virtualParents input ∨ ∃ child ∈ input.groups, child.parent = Int.ofNat g := by
  by_cases node : Int.ofNat g ∈ input.parents
  · left
    unfold virtualParents
    exact List.mem_append_left _ node
  · by_cases child : ∃ child ∈ input.groups, child.parent = Int.ofNat g
    · exact Or.inr child
    · left
      unfold virtualParents
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨g,?_,rfl⟩
      rw [List.mem_filter]
      refine ⟨List.mem_range.mpr valid,?_⟩
      simp only [Bool.and_eq_true,Bool.not_eq_true']
      constructor
      · apply Bool.eq_false_of_ne_true
        intro present
        exact node (List.contains_iff_mem.mp present)
      · apply Bool.eq_false_of_ne_true
        intro present
        apply child
        simpa only [List.any_eq_true,beq_iff_eq] using present

theorem group_level_positive (input : Input) (p : Params) (relative : List Span) (g : Nat)
    (valid : g < input.groups.length) : 0 < (levelOf input p relative (Int.ofNat g)).units.length := by
  rw [level_units_length]
  rcases group_has_placement_unit input g valid with node | child
  · have member : Int.ofNat g ∈ (virtualParents input).filter (fun value => value == Int.ofNat g) := by
      exact List.mem_filter.mpr ⟨node,by simp only [beq_self_eq_true]⟩
    have positive := List.length_pos_iff_exists_mem.mpr ⟨Int.ofNat g,member⟩
    omega
  · rcases child with ⟨entry,present,equal⟩
    have member : entry ∈ input.groups.filter (fun group => group.parent == Int.ofNat g) := by
      simp [present,equal]
    have positive := List.length_pos_iff_exists_mem.mpr ⟨entry,member⟩
    omega

theorem arrange_all_placed (p : Params) (fuel : Nat) (l : Level)
    (lengths : l.placed.length = l.units.length) :
    ∀ i, i < l.units.length → (arrange p fuel l).1.placed.getD i false = true := by
  intro i bound
  have marked := arrange_all_marked p fuel l lengths i bound
  change (arrange p fuel l).1.placed[i]? = some true at marked
  simp only [List.getD_eq_getElem?_getD,marked,Option.getD_some]

theorem arranged_parent_all_placed (input : Input) (p : Params) (relative : List Span)
    (parent : Int) (fuel : Nat) :
    ∀ i, i < (levelOf input p relative parent).units.length →
      (arrange p fuel (levelOf input p relative parent)).1.placed.getD i false = true :=
  arrange_all_placed p fuel _ (level_placed_length input p relative parent)

theorem arranged_parent_level_invariant (input : Input) (p : Params) (relative : List Span)
    (parent : Int) (fuel : Nat) (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (anchors : AnchorsInvariant p (levelOf input p relative parent)) :
    LevelInvariant p (arrange p fuel (levelOf input p relative parent)).1 := by
  by_cases positive : 0 < (levelOf input p relative parent).units.length
  · exact arrange_level_invariant p fuel _ px py
      (initial_level_invariant input p relative parent anchors)
      (level_placed_length input p relative parent)
      (level_edges_bound input p relative parent positive)
  · have empty : (levelOf input p relative parent).units.length = 0 := by omega
    simpa only [arrange,empty,List.range_zero,List.foldl_nil] using
      initial_level_invariant input p relative parent anchors

theorem arranged_parent_cells_distinct (input : Input) (p : Params) (relative : List Span)
    (parent : Int) (fuel : Nat) (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (anchors : AnchorsInvariant p (levelOf input p relative parent))
    (i j : Nat) (hi : i < (levelOf input p relative parent).units.length)
    (hj : j < (levelOf input p relative parent).units.length) (different : i ≠ j) :
    (arrange p fuel (levelOf input p relative parent)).1.cells.getD i default ≠
      (arrange p fuel (levelOf input p relative parent)).1.cells.getD j default := by
  have invariant := arranged_parent_level_invariant input p relative parent fuel px py anchors
  have lengths := level_placed_length input p relative parent
  have finalLength := arrange_placed_length p fuel (levelOf input p relative parent)
  exact invariant.2.2.2 i j (by omega) (by omega)
    (arranged_parent_all_placed input p relative parent fuel i hi)
    (arranged_parent_all_placed input p relative parent fuel j hj) different

theorem arranged_parent_frame_contains_unit (input : Input) (p : Params)
    (fp : FrameParams) (relative : List Span) (parent : Int) (fuel : Nat) (g : Group)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (i : Nat) (bound : i < (arrange p fuel (levelOf input p relative parent)).1.absolute.length) :
    (frameOf fp g
      ((arrange p fuel (levelOf input p relative parent)).1.absolute.foldl Span.union emptySpan)).contains
      ((arrange p fuel (levelOf input p relative parent)).1.absolute.getD i default) := by
  exact arch_group_frame_contains_all_members fp g _ padding line _
    (getD_mem _ i default bound)

theorem arranged_parent_cells_nodup (input : Input) (p : Params) (relative : List Span)
    (parent : Int) (fuel : Nat) (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (anchors : AnchorsInvariant p (levelOf input p relative parent)) :
    ((List.range (levelOf input p relative parent).units.length).map
      (fun i => (arrange p fuel (levelOf input p relative parent)).1.cells.getD i default)).Nodup := by
  change List.Pairwise (fun a b : Cell => a ≠ b) _
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj ordered
  simp only [List.length_map,List.length_range] at hi hj
  simp only [List.getElem_map,List.getElem_range]
  exact arranged_parent_cells_distinct input p relative parent fuel px py anchors
    i j hi hj (by omega)

theorem arranged_parent_frame_contains_placed_rect (input : Input) (p : Params)
    (fp : FrameParams) (relative : List Span) (parent : Int) (fuel : Nat) (g : Group)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (anchors : AnchorsInvariant p (levelOf input p relative parent))
    (i : Nat) (bound : i < (levelOf input p relative parent).units.length) :
    (frameOf fp g
      ((arrange p fuel (levelOf input p relative parent)).1.absolute.foldl Span.union emptySpan)).contains
      (((levelOf input p relative parent).rects.getD i default).shift
        (((arrange p fuel (levelOf input p relative parent)).1.cells.getD i default).x * p.pitchX)
        (((arrange p fuel (levelOf input p relative parent)).1.cells.getD i default).y * p.pitchY)) := by
  have invariant := arranged_parent_level_invariant input p relative parent fuel px py anchors
  have lengths := level_placed_length input p relative parent
  have finalLength := arrange_placed_length p fuel (levelOf input p relative parent)
  have placedBound : i < (arrange p fuel (levelOf input p relative parent)).1.placed.length := by
    omega
  have marked := arranged_parent_all_placed input p relative parent fuel i bound
  have coordinates := invariant.2.1.2.2 i placedBound marked
  have inside := arranged_parent_frame_contains_unit input p fp relative parent fuel g
    padding line i (by rw [invariant.2.1.1]; exact placedBound)
  rw [coordinates,arrange_rects] at inside
  exact inside

theorem level_anchors_of_children (input : Input) (p : Params) (relative : List Span)
    (parent : Int)
    (children : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent = parent →
      ContainsAnchor p (relative.getD k default)) :
    AnchorsInvariant p (levelOf input p relative parent) := by
  intro i hi
  have rectLength : (levelOf input p relative parent).rects.length =
      (levelOf input p relative parent).placed.length := by
    simp only [levelOf,List.length_map,List.length_replicate]
  have member := getD_mem (levelOf input p relative parent).rects i default
    (by omega)
  change _ ∈ ((levelOf input p relative parent).units.map _) at member
  rcases List.mem_map.mp member with ⟨u,hu,equal⟩
  rw [← equal]
  by_cases node : u.group < 0
  · simp [node,ContainsAnchor]
  · simp only [node,↓reduceIte]
    change u ∈ ((_ ++ _) : List Unit).mergeSort _ at hu
    rw [List.mem_mergeSort] at hu
    rcases List.mem_append.mp hu with hn | hg
    · rcases List.mem_map.mp hn with ⟨q,_,same⟩
      subst u
      simp at node
    · rcases List.mem_map.mp hg with ⟨q,hq,same⟩
      subst u
      rcases List.mem_filter.mp hq with ⟨indexed,parentEqual⟩
      have lookup := List.mem_zipIdx_iff_getElem?.mp indexed
      have bound := (List.getElem?_eq_some_iff.mp lookup).choose
      have actual : input.groups.getD q.2 default = q.1 := by
        simp only [List.getD_eq_getElem?_getD,lookup,Option.getD_some]
      have owns : q.1.parent = parent := by simpa using parentEqual
      simpa only [Int.toNat_natCast] using
        children q.2 bound (by rw [actual]; exact owns)

private theorem placement_writes_relative (l : Level) (entries : List (Unit × Nat))
    (state : Placement) :
    (entries.foldl (fun state q =>
      let c := l.cells.getD q.2 default
      if q.1.group < 0 then { state with localNodes := state.localNodes.set q.1.node.toNat c }
      else { state with localGroups := state.localGroups.set q.1.group.toNat c }) state).relative =
      state.relative := by
  induction entries generalizing state with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split <;> rfl

theorem arrangeParent_relative (input : Input) (p : Params) (fp : FrameParams)
    (parent : Int) (state : Placement) :
    (arrangeParent input p fp parent state).relative =
      if parent < 0 then state.relative else
        state.relative.set parent.toNat
          (frameOf fp (input.groups.getD parent.toNat default)
            ((arrange p state.fuel (levelOf input p state.relative parent)).1.absolute.foldl
              Span.union emptySpan)) := by
  unfold arrangeParent
  split
  · exact placement_writes_relative _ _ _
  · simp only
    rw [placement_writes_relative]

theorem arrangeParent_preserves_other_frame (input : Input) (p : Params) (fp : FrameParams)
    (g k : Nat) (state : Placement) (different : g ≠ k) :
    (arrangeParent input p fp (Int.ofNat g) state).relative.getD k default =
      state.relative.getD k default := by
  rw [arrangeParent_relative]
  simp only [Int.ofNat_eq_natCast,Int.toNat_natCast]
  rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg g))]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_set_ne different]

theorem arrangeParent_relative_length (input : Input) (p : Params) (fp : FrameParams)
    (parent : Int) (state : Placement) :
    (arrangeParent input p fp parent state).relative.length = state.relative.length := by
  rw [arrangeParent_relative]
  split <;> simp only [List.length_set]

theorem arrangeParent_frame_anchor (input : Input) (p : Params) (fp : FrameParams)
    (g : Nat) (state : Placement) (valid : g < input.groups.length)
    (lengths : state.relative.length = input.groups.length)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (anchors : AnchorsInvariant p (levelOf input p state.relative (Int.ofNat g))) :
    ContainsAnchor p
      ((arrangeParent input p fp (Int.ofNat g) state).relative.getD g default) := by
  rw [arrangeParent_relative]
  simp only [Int.ofNat_eq_natCast,Int.toNat_natCast]
  rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg g))]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_set_self (by omega : g < state.relative.length)]
  simp only [Option.getD_some]
  exact arrange_frame_anchor input p fp state.relative (Int.ofNat g) state.fuel
    (input.groups.getD g default) px py padding line
    (group_level_positive input p state.relative g valid) anchors

theorem reverse_group_fold_anchors (input : Input) (p : Params) (fp : FrameParams)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (n : Nat) (bound : n ≤ input.groups.length) (state : Placement)
    (lengths : state.relative.length = input.groups.length)
    (ready : ∀ k, n ≤ k → k < input.groups.length →
      ContainsAnchor p (state.relative.getD k default)) :
    let result := (List.range n).reverse.foldl
      (fun state g => arrangeParent input p fp (Int.ofNat g) state) state
    result.relative.length = input.groups.length ∧
      ∀ k, k < input.groups.length → ContainsAnchor p (result.relative.getD k default) := by
  induction n generalizing state with
  | zero =>
    simp only [List.range_zero,List.reverse_nil,List.foldl_nil]
    exact ⟨lengths,fun k hk => ready k (Nat.zero_le k) hk⟩
  | succ n ih =>
    have valid : n < input.groups.length := by omega
    have anchors : AnchorsInvariant p (levelOf input p state.relative (Int.ofNat n)) := by
      apply level_anchors_of_children
      intro k hk owns
      have order := ordered k hk
      rw [owns] at order
      simp only [Int.ofNat_eq_natCast] at order
      apply ready k (by omega) hk
    have newAnchor := arrangeParent_frame_anchor input p fp n state valid lengths
      px py padding line anchors
    have newLength : (arrangeParent input p fp (Int.ofNat n) state).relative.length =
        input.groups.length := by
      rw [arrangeParent_relative_length,lengths]
    have newReady : ∀ k, n ≤ k → k < input.groups.length →
        ContainsAnchor p
          ((arrangeParent input p fp (Int.ofNat n) state).relative.getD k default) := by
      intro k lower upper
      by_cases same : n = k
      · subst k
        exact newAnchor
      · rw [arrangeParent_preserves_other_frame input p fp n k state same]
        exact ready k (by omega) upper
    simpa only [List.range_succ,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.foldl_append,List.foldl_cons,List.foldl_nil] using
      ih (by omega) (arrangeParent input p fp (Int.ofNat n) state) newLength newReady

theorem placeHierarchy_frame_anchors (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight) :
    ∀ k, k < input.groups.length →
      ContainsAnchor p ((placeHierarchy input p fp fuel).relative.getD k default) := by
  have folded := reverse_group_fold_anchors input p fp ordered px py padding line
    input.groups.length (Nat.le_refl _) 
    (⟨List.replicate (virtualParents input).length default,
      List.replicate input.groups.length default,
      List.replicate input.groups.length default,fuel,false⟩ : Placement)
    (by simp only [List.length_replicate]) (by intro k lower upper; omega)
  intro k hk
  unfold placeHierarchy
  rw [arrangeParent_relative]
  simp only [show (-1 : Int) < 0 by decide,↓reduceIte]
  exact folded.2 k hk

theorem placeHierarchy_level_anchors (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight) (parent : Int) :
    AnchorsInvariant p
      (levelOf input p (placeHierarchy input p fp fuel).relative parent) := by
  apply level_anchors_of_children
  intro k hk _
  exact placeHierarchy_frame_anchors input p fp fuel ordered px py padding line k hk

theorem placeHierarchy_arranged_level_invariant (input : Input) (p : Params)
    (fp : FrameParams) (fuel remaining : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight) (parent : Int) :
    LevelInvariant p
      (arrange p remaining
        (levelOf input p (placeHierarchy input p fp fuel).relative parent)).1 :=
  arranged_parent_level_invariant input p _ parent remaining px py
    (placeHierarchy_level_anchors input p fp fuel ordered px py padding line parent)

theorem placeHierarchy_arranged_cells_distinct (input : Input) (p : Params)
    (fp : FrameParams) (fuel remaining : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (parent : Int) (i j : Nat)
    (hi : i < (levelOf input p (placeHierarchy input p fp fuel).relative parent).units.length)
    (hj : j < (levelOf input p (placeHierarchy input p fp fuel).relative parent).units.length)
    (different : i ≠ j) :
    (arrange p remaining
      (levelOf input p (placeHierarchy input p fp fuel).relative parent)).1.cells.getD i default ≠
    (arrange p remaining
      (levelOf input p (placeHierarchy input p fp fuel).relative parent)).1.cells.getD j default :=
  arranged_parent_cells_distinct input p _ parent remaining px py
    (placeHierarchy_level_anchors input p fp fuel ordered px py padding line parent)
    i j hi hj different

theorem arranged_parent_rects_separated (input : Input) (p : Params)
    (relative : List Span) (parent : Int) (fuel : Nat)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (anchors : AnchorsInvariant p (levelOf input p relative parent)) :
    RectsSeparated (arrange p fuel (levelOf input p relative parent)).1 := by
  have initial : RectsSeparated (levelOf input p relative parent) := by
    intro i j _ _ marked _ _
    have unmarked : (levelOf input p relative parent).placed.getD i false = false := by
      simp only [levelOf,List.getD_eq_getElem?_getD,List.getElem?_replicate]
      split <;> rfl
    rw [unmarked] at marked
    contradiction
  by_cases positive : 0 < (levelOf input p relative parent).units.length
  · exact arrange_rects_separated p fuel _ px py
      (initial_level_invariant input p relative parent anchors) initial
      (level_placed_length input p relative parent)
      (level_edges_bound input p relative parent positive)
  · have empty : (levelOf input p relative parent).units.length = 0 := by omega
    simpa only [arrange,empty,List.range_zero,List.foldl_nil] using initial

theorem placeHierarchy_arranged_rects_separated (input : Input) (p : Params)
    (fp : FrameParams) (fuel remaining : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight) (parent : Int) :
    RectsSeparated (arrange p remaining
      (levelOf input p (placeHierarchy input p fp fuel).relative parent)).1 :=
  arranged_parent_rects_separated input p _ parent remaining px py
    (placeHierarchy_level_anchors input p fp fuel ordered px py padding line parent)

theorem reverse_group_fold_preserves_frame (input : Input) (p : Params)
    (fp : FrameParams) (n k : Nat) (outside : n ≤ k) (state : Placement) :
    ((List.range n).reverse.foldl
      (fun state g => arrangeParent input p fp (Int.ofNat g) state)
      state).relative.getD k default = state.relative.getD k default := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [ih (by omega)]
    exact arrangeParent_preserves_other_frame input p fp n k state (by omega)

theorem arrangeParent_frame_contains_placed_rect (input : Input) (p : Params)
    (fp : FrameParams) (state : Placement) (g : Nat)
    (valid : g < input.groups.length)
    (lengths : state.relative.length = input.groups.length)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (anchors : AnchorsInvariant p (levelOf input p state.relative (Int.ofNat g)))
    (i : Nat) (bound : i < (levelOf input p state.relative (Int.ofNat g)).units.length) :
    ((arrangeParent input p fp (Int.ofNat g) state).relative.getD g default).contains
      (((levelOf input p state.relative (Int.ofNat g)).rects.getD i default).shift
        (((arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1.cells.getD i default).x
          * p.pitchX)
        (((arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1.cells.getD i default).y
          * p.pitchY)) := by
  rw [arrangeParent_relative]
  simp only [Int.ofNat_eq_natCast,Int.toNat_natCast]
  rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg g))]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_set_self (by omega : g < state.relative.length)]
  simp only [Option.getD_some]
  exact arranged_parent_frame_contains_placed_rect input p fp state.relative
    (Int.ofNat g) state.fuel (input.groups.getD g default) px py padding line anchors i bound

theorem arch_group_frame_contains_members (input : Input) (p : Params)
    (fp : FrameParams) (state : Placement) (g : Nat)
    (valid : g < input.groups.length)
    (lengths : state.relative.length = input.groups.length)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (anchors : AnchorsInvariant p (levelOf input p state.relative (Int.ofNat g)))
    (i : Nat) (bound : i < (levelOf input p state.relative (Int.ofNat g)).units.length) :
    (((List.range g).reverse.foldl
      (fun state k => arrangeParent input p fp (Int.ofNat k) state)
      (arrangeParent input p fp (Int.ofNat g) state)).relative.getD g default).contains
      (((levelOf input p state.relative (Int.ofNat g)).rects.getD i default).shift
        (((arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1.cells.getD i default).x
          * p.pitchX)
        (((arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1.cells.getD i default).y
          * p.pitchY)) := by
  rw [reverse_group_fold_preserves_frame input p fp g g (Nat.le_refl g)]
  exact arrangeParent_frame_contains_placed_rect input p fp state g valid lengths px py
    padding line anchors i bound

def HierarchyRunEvidence (input : Input) (p : Params) (fp : FrameParams) :
    List Nat → Placement → Prop
  | [], state =>
    let l := levelOf input p state.relative (-1)
    let placed := (arrange p state.fuel l).1
    LevelInvariant p placed ∧ RectsSeparated placed ∧
      ∀ i, i < l.units.length → placed.placed.getD i false = true
  | g :: rest, state =>
    let l := levelOf input p state.relative (Int.ofNat g)
    let placed := (arrange p state.fuel l).1
    let next := arrangeParent input p fp (Int.ofNat g) state
    LevelInvariant p placed ∧ RectsSeparated placed ∧
      (∀ i, i < l.units.length → placed.placed.getD i false = true) ∧
      (∀ i, i < l.units.length →
        (next.relative.getD g default).contains
          ((l.rects.getD i default).shift
            ((placed.cells.getD i default).x*p.pitchX)
            ((placed.cells.getD i default).y*p.pitchY))) ∧
      HierarchyRunEvidence input p fp rest next

theorem reverse_group_fold_execution (input : Input) (p : Params) (fp : FrameParams)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (n : Nat) (bound : n ≤ input.groups.length) (state : Placement)
    (lengths : state.relative.length = input.groups.length)
    (ready : ∀ k, n ≤ k → k < input.groups.length →
      ContainsAnchor p (state.relative.getD k default)) :
    HierarchyRunEvidence input p fp (List.range n).reverse state := by
  induction n generalizing state with
  | zero =>
    have anchors : AnchorsInvariant p (levelOf input p state.relative (-1)) := by
      apply level_anchors_of_children
      intro k hk _
      exact ready k (Nat.zero_le k) hk
    exact ⟨arranged_parent_level_invariant input p state.relative (-1) state.fuel px py anchors,
      arranged_parent_rects_separated input p state.relative (-1) state.fuel px py anchors,
      arranged_parent_all_placed input p state.relative (-1) state.fuel⟩
  | succ n ih =>
    have valid : n < input.groups.length := by omega
    have anchors : AnchorsInvariant p (levelOf input p state.relative (Int.ofNat n)) := by
      apply level_anchors_of_children
      intro k hk owns
      have order := ordered k hk
      rw [owns] at order
      simp only [Int.ofNat_eq_natCast] at order
      exact ready k (by omega) hk
    have newLength : (arrangeParent input p fp (Int.ofNat n) state).relative.length =
        input.groups.length := by rw [arrangeParent_relative_length,lengths]
    have newReady : ∀ k, n ≤ k → k < input.groups.length →
        ContainsAnchor p
          ((arrangeParent input p fp (Int.ofNat n) state).relative.getD k default) := by
      intro k lower upper
      by_cases same : n = k
      · subst k
        exact arrangeParent_frame_anchor input p fp n state valid lengths px py padding line anchors
      · rw [arrangeParent_preserves_other_frame input p fp n k state same]
        exact ready k (by omega) upper
    simp only [List.range_succ,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.singleton_append,HierarchyRunEvidence]
    refine ⟨arranged_parent_level_invariant input p state.relative (Int.ofNat n) state.fuel
      px py anchors,
      arranged_parent_rects_separated input p state.relative (Int.ofNat n) state.fuel px py anchors,
      arranged_parent_all_placed input p state.relative (Int.ofNat n) state.fuel,?_,?_⟩
    · intro i hi
      exact arrangeParent_frame_contains_placed_rect input p fp state n valid lengths px py
        padding line anchors i hi
    · exact ih (by omega) (arrangeParent input p fp (Int.ofNat n) state) newLength newReady

theorem placeHierarchy_execution_invariants (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight) :
    HierarchyRunEvidence input p fp (List.range input.groups.length).reverse
      ⟨List.replicate (virtualParents input).length default,
        List.replicate input.groups.length default,
        List.replicate input.groups.length default,fuel,false⟩ := by
  apply reverse_group_fold_execution input p fp ordered px py padding line _ (Nat.le_refl _)
  · simp only [List.length_replicate]
  · intro k lower upper
    omega

private def appendOrigin (placed : Placement) (origins : List Cell) (q : Group × Nat) :
    List Cell :=
  let base := if q.1.parent < 0 then default else origins.getD q.1.parent.toNat default
  let offset := placed.localGroups.getD q.2 default
  origins ++ [(⟨base.x+offset.x,base.y+offset.y⟩ : Cell)]

private theorem appendOrigin_length (placed : Placement) (origins : List Cell)
    (q : Group × Nat) :
    (appendOrigin placed origins q).length = origins.length+1 := by
  simp only [appendOrigin,List.length_append,List.length_singleton]

private theorem origin_fold_length (placed : Placement) (entries : List (Group × Nat))
    (origins : List Cell) :
    (entries.foldl (appendOrigin placed) origins).length = origins.length+entries.length := by
  induction entries generalizing origins with
  | nil => simp only [List.foldl_nil,List.length_nil,Nat.add_zero]
  | cons q rest ih =>
    rw [List.foldl_cons,ih,appendOrigin_length]
    simp only [List.length_cons]
    omega

private theorem origin_fold_preserves_prefix (placed : Placement)
    (entries : List (Group × Nat)) (origins : List Cell) (i : Nat)
    (bound : i < origins.length) :
    (entries.foldl (appendOrigin placed) origins).getD i default = origins.getD i default := by
  induction entries generalizing origins with
  | nil => rfl
  | cons q rest ih =>
    rw [List.foldl_cons,ih _ (by rw [appendOrigin_length]; omega)]
    simp only [appendOrigin,List.getD_eq_getElem?_getD,
      List.getElem?_append_left bound]

private def OriginEquation (placed : Placement) (origins : List Cell)
    (q : Group × Nat) : Prop :=
  origins.getD q.2 default =
    let base := if q.1.parent < 0 then default else origins.getD q.1.parent.toNat default
    let offset := placed.localGroups.getD q.2 default
    (⟨base.x+offset.x,base.y+offset.y⟩ : Cell)

private theorem origin_fold_equations (placed : Placement) (groups : List Group)
    (start : Nat) (origins : List Cell) (lengths : origins.length = start)
    (ordered : ∀ q ∈ groups.zipIdx start, q.1.parent < Int.ofNat q.2) :
    ∀ q ∈ groups.zipIdx start,
      OriginEquation placed ((groups.zipIdx start).foldl (appendOrigin placed) origins) q := by
  induction groups generalizing start origins with
  | nil =>
    intro q member
    simp only [List.zipIdx_nil,List.not_mem_nil] at member
  | cons group rest ih =>
    simp only [List.zipIdx_cons,List.foldl_cons]
    intro q member
    rcases List.mem_cons.mp member with same | tail
    · subst q
      let next := appendOrigin placed origins (group,start)
      have nextLength : next.length = start+1 := by
        rw [appendOrigin_length,lengths]
      have saved := origin_fold_preserves_prefix placed (rest.zipIdx (start+1)) next start
        (by rw [nextLength]; omega)
      have head : next.getD start default =
          let base := if group.parent < 0 then default else origins.getD group.parent.toNat default
          let offset := placed.localGroups.getD start default
          (⟨base.x+offset.x,base.y+offset.y⟩ : Cell) := by
        dsimp only [next,appendOrigin]
        simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : origins.length ≤ start),
          lengths,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
      unfold OriginEquation
      rw [saved,head]
      by_cases root : group.parent < 0
      · simp only [root,↓reduceIte]
      · have parentOrder := ordered (group,start) (by simp)
        have parentBound : group.parent.toNat < origins.length := by
          simp only [Int.ofNat_eq_natCast] at parentOrder
          omega
        have preserved := origin_fold_preserves_prefix placed (rest.zipIdx (start+1))
          next group.parent.toNat (by rw [nextLength]; omega)
        have original : next.getD group.parent.toNat default =
            origins.getD group.parent.toNat default := by
          dsimp only [next,appendOrigin]
          simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left parentBound]
        have finalParent :
            ((rest.zipIdx (start+1)).foldl (appendOrigin placed)
              (appendOrigin placed origins (group,start))).getD group.parent.toNat default =
              origins.getD group.parent.toNat default := preserved.trans original
        simp only [root,↓reduceIte]
        rw [finalParent]
    · apply ih (start+1) (appendOrigin placed origins (group,start))
        (by rw [appendOrigin_length,lengths])
      · intro entry present
        exact ordered entry (by simp [present])
      · exact tail

theorem resolveHierarchy_origins_equations (input : Input) (placed : Placement)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k) :
    let origins := input.groups.zipIdx.foldl
      (fun origins q =>
        let base := if q.1.parent < 0 then default else origins.getD q.1.parent.toNat default
        let offset := placed.localGroups.getD q.2 default
        origins ++ [(⟨base.x+offset.x,base.y+offset.y⟩ : Cell)]) ([] : List Cell)
    ∀ q ∈ input.groups.zipIdx,
      origins.getD q.2 default =
        let base := if q.1.parent < 0 then default else origins.getD q.1.parent.toNat default
        let offset := placed.localGroups.getD q.2 default
        (⟨base.x+offset.x,base.y+offset.y⟩ : Cell) := by
  have order : ∀ q ∈ input.groups.zipIdx, q.1.parent < Int.ofNat q.2 := by
    intro q member
    have lookup := List.mem_zipIdx_iff_getElem?.mp member
    have bound := (List.getElem?_eq_some_iff.mp lookup).choose
    have actual : input.groups.getD q.2 default = q.1 := by
      simp only [List.getD_eq_getElem?_getD,lookup,Option.getD_some]
    rw [← actual]
    exact ordered q.2 bound
  exact origin_fold_equations placed input.groups 0 [] rfl order

theorem resolveHierarchy_execution (input : Input) (p : Params) (placed : Placement)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k) :
    ∃ origins : List Cell,
      origins.length = input.groups.length ∧
      (∀ q ∈ input.groups.zipIdx,
        origins.getD q.2 default =
          let base := if q.1.parent < 0 then default else origins.getD q.1.parent.toNat default
          let offset := placed.localGroups.getD q.2 default
          (⟨base.x+offset.x,base.y+offset.y⟩ : Cell)) ∧
      (resolveHierarchy input p placed).frames =
        placed.relative.zipIdx.map (fun q =>
          let base := origins.getD q.2 default
          q.1.shift (base.x*p.pitchX) (base.y*p.pitchY)) ∧
      (resolveHierarchy input p placed).nodes =
        (virtualParents input).zipIdx.map (fun q =>
          let base := if q.1 < 0 then default else origins.getD q.1.toNat default
          let offset := placed.localNodes.getD q.2 default
          (⟨base.x+offset.x,base.y+offset.y⟩ : Cell)) := by
  let origins := input.groups.zipIdx.foldl (appendOrigin placed) []
  refine ⟨origins,?_,?_,rfl,rfl⟩
  · simp only [origins,origin_fold_length,List.length_zipIdx,List.length_nil,Nat.zero_add]
  · exact resolveHierarchy_origins_equations input placed ordered

private theorem placement_writes_lengths (l : Level) (entries : List (Unit × Nat))
    (state : Placement) :
    let final := entries.foldl (fun state q =>
      let c := l.cells.getD q.2 default
      if q.1.group < 0 then { state with localNodes := state.localNodes.set q.1.node.toNat c }
      else { state with localGroups := state.localGroups.set q.1.group.toNat c }) state
    final.localNodes.length = state.localNodes.length ∧
      final.localGroups.length = state.localGroups.length := by
  induction entries generalizing state with
  | nil => exact ⟨rfl,rfl⟩
  | cons q rest ih =>
    simp only [List.foldl_cons]
    split
    · simpa only [List.length_set] using
        ih { state with localNodes :=
          (state.localNodes.set q.1.node.toNat (l.cells.getD q.2 default)) }
    · simpa only [List.length_set] using
        ih { state with localGroups :=
          (state.localGroups.set q.1.group.toNat (l.cells.getD q.2 default)) }

theorem arrangeParent_storage_lengths (input : Input) (p : Params) (fp : FrameParams)
    (parent : Int) (state : Placement) :
    (arrangeParent input p fp parent state).localNodes.length = state.localNodes.length ∧
      (arrangeParent input p fp parent state).localGroups.length = state.localGroups.length ∧
      (arrangeParent input p fp parent state).relative.length = state.relative.length := by
  have storage :
      (arrangeParent input p fp parent state).localNodes.length = state.localNodes.length ∧
      (arrangeParent input p fp parent state).localGroups.length = state.localGroups.length := by
    unfold arrangeParent
    split <;> exact placement_writes_lengths _ _ _
  exact ⟨storage.1,storage.2,arrangeParent_relative_length input p fp parent state⟩

theorem placeHierarchy_storage_lengths (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat) :
    (placeHierarchy input p fp fuel).localNodes.length = (virtualParents input).length ∧
      (placeHierarchy input p fp fuel).localGroups.length = input.groups.length ∧
      (placeHierarchy input p fp fuel).relative.length = input.groups.length := by
  have fold : ∀ (indices : List Nat) (state : Placement),
      let final := indices.foldl (fun state g => arrangeParent input p fp (Int.ofNat g) state) state
      final.localNodes.length = state.localNodes.length ∧
        final.localGroups.length = state.localGroups.length ∧
        final.relative.length = state.relative.length := by
    intro indices
    induction indices with
    | nil => intro state; exact ⟨rfl,rfl,rfl⟩
    | cons g rest ih =>
      intro state
      have step := arrangeParent_storage_lengths input p fp (Int.ofNat g) state
      have tail := ih (arrangeParent input p fp (Int.ofNat g) state)
      exact ⟨tail.1.trans step.1,tail.2.1.trans step.2.1,tail.2.2.trans step.2.2⟩
  let initial : Placement :=
    ⟨List.replicate (virtualParents input).length default,
      List.replicate input.groups.length default,
      List.replicate input.groups.length default,fuel,false⟩
  let bottom := (List.range input.groups.length).reverse.foldl
    (fun state g => arrangeParent input p fp (Int.ofNat g) state) initial
  have bottomLengths := fold (List.range input.groups.length).reverse initial
  have rootLengths := arrangeParent_storage_lengths input p fp (-1) bottom
  refine ⟨?_,?_,?_⟩
  · exact rootLengths.1.trans (bottomLengths.1.trans (List.length_replicate ..))
  · exact rootLengths.2.1.trans (bottomLengths.2.1.trans (List.length_replicate ..))
  · exact rootLengths.2.2.trans (bottomLengths.2.2.trans (List.length_replicate ..))

theorem resolveHierarchy_storage_lengths (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat) :
    (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.length =
      (virtualParents input).length ∧
    (resolveHierarchy input p (placeHierarchy input p fp fuel)).frames.length =
      input.groups.length := by
  constructor
  · simp only [resolveHierarchy,List.length_map,List.length_zipIdx]
  · simp only [resolveHierarchy,List.length_map,List.length_zipIdx]
    exact (placeHierarchy_storage_lengths input p fp fuel).2.2

theorem level_node_owner (input : Input) (p : Params) (relative : List Span)
    (parent : Int) (u : Unit)
    (member : u ∈ (levelOf input p relative parent).units) (node : u.group < 0) :
    u.node.toNat < (virtualParents input).length ∧
      (virtualParents input).getD u.node.toNat (-1) = parent := by
  change u ∈ ((_ ++ _) : List Unit).mergeSort _ at member
  rw [List.mem_mergeSort] at member
  rcases List.mem_append.mp member with nodes | groups
  · rcases List.mem_map.mp nodes with ⟨q,present,rfl⟩
    rcases List.mem_filter.mp present with ⟨indexed,owns⟩
    have lookup := List.mem_zipIdx_iff_getElem?.mp indexed
    have bound := (List.getElem?_eq_some_iff.mp lookup).choose
    have actual : (virtualParents input).getD q.2 (-1) = q.1 := by
      simp only [List.getD_eq_getElem?_getD,lookup,Option.getD_some]
    simp only [Int.toNat_natCast]
    exact ⟨bound,actual.trans (by simpa using owns)⟩
  · rcases List.mem_map.mp groups with ⟨q,_,equal⟩
    subst u
    dsimp only at node
    omega

private theorem placement_writes_preserve_foreign_node (l : Level)
    (entries : List (Unit × Nat)) (state : Placement) (target : Nat)
    (foreign : ∀ q ∈ entries, q.1.group < 0 → q.1.node.toNat ≠ target) :
    (entries.foldl (fun state q =>
      let c := l.cells.getD q.2 default
      if q.1.group < 0 then { state with localNodes := state.localNodes.set q.1.node.toNat c }
      else { state with localGroups := state.localGroups.set q.1.group.toNat c })
      state).localNodes.getD target default = state.localNodes.getD target default := by
  induction entries generalizing state with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by intro entry present; exact foreign entry (by simp [present]))]
    split
    · rename_i node
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (foreign q (by simp) node)]
    · rfl

theorem arrangeParent_preserves_foreign_node (input : Input) (p : Params)
    (fp : FrameParams) (parent : Int) (state : Placement) (target : Nat)
    (foreign : (virtualParents input).getD target (-1) ≠ parent) :
    (arrangeParent input p fp parent state).localNodes.getD target default =
      state.localNodes.getD target default := by
  let l := (arrange p state.fuel (levelOf input p state.relative parent)).1
  let initial : Placement := ⟨state.localNodes,state.localGroups,state.relative,
    (arrange p state.fuel (levelOf input p state.relative parent)).2,
    state.budgetExhausted || l.budgetExhausted⟩
  have preserved := placement_writes_preserve_foreign_node l l.units.zipIdx initial target
    (by
      intro q member node same
      have indexed := List.mem_zipIdx_iff_getElem?.mp member
      have unitMember : q.1 ∈ l.units := List.mem_of_getElem? indexed
      have original : q.1 ∈ (levelOf input p state.relative parent).units := by
        simpa only [l,arrange_units] using unitMember
      have owner := (level_node_owner input p state.relative parent q.1 original node).2
      rw [same] at owner
      exact foreign owner)
  unfold arrangeParent
  split <;> exact preserved

theorem hierarchy_fold_preserves_foreign_node (input : Input) (p : Params)
    (fp : FrameParams) (indices : List Nat) (state : Placement) (target : Nat)
    (foreign : ∀ g ∈ indices, (virtualParents input).getD target (-1) ≠ Int.ofNat g) :
    (indices.foldl (fun state g => arrangeParent input p fp (Int.ofNat g) state)
      state).localNodes.getD target default = state.localNodes.getD target default := by
  induction indices generalizing state with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons,ih _ (by intro i member; exact foreign i (by simp [member]))]
    exact arrangeParent_preserves_foreign_node input p fp (Int.ofNat g) state target
      (foreign g (by simp))

theorem lower_levels_preserve_group_node (input : Input) (p : Params)
    (fp : FrameParams) (g target : Nat) (state : Placement)
    (owner : (virtualParents input).getD target (-1) = Int.ofNat g) :
    (arrangeParent input p fp (-1)
      ((List.range g).reverse.foldl
        (fun state i => arrangeParent input p fp (Int.ofNat i) state)
        state)).localNodes.getD target default = state.localNodes.getD target default := by
  rw [arrangeParent_preserves_foreign_node input p fp (-1) _ target
    (by rw [owner]; simp only [Int.ofNat_eq_natCast]; omega)]
  apply hierarchy_fold_preserves_foreign_node
  intro i member
  have bound := List.mem_range.mp (List.mem_reverse.mp member)
  rw [owner]
  simp only [Int.ofNat_eq_natCast]
  omega

theorem group_levels_preserve_root_node (input : Input) (p : Params)
    (fp : FrameParams) (indices : List Nat) (state : Placement) (target : Nat)
    (owner : (virtualParents input).getD target (-1) = -1) :
    (indices.foldl (fun state i => arrangeParent input p fp (Int.ofNat i) state)
      state).localNodes.getD target default = state.localNodes.getD target default := by
  apply hierarchy_fold_preserves_foreign_node
  intro i _
  rw [owner]
  simp only [Int.ofNat_eq_natCast]
  omega

def NodeKeysDistinct (units : List Unit) : Prop :=
  units.Pairwise (fun a b => a.group < 0 → b.group < 0 → a.node.toNat ≠ b.node.toNat)

theorem level_node_keys_distinct (input : Input) (p : Params) (relative : List Span)
    (parent : Int) : NodeKeysDistinct (levelOf input p relative parent).units := by
  let nodes := ((virtualParents input).zipIdx.filter (fun q => q.1 == parent)).map
    (fun q => (⟨q.2,-1⟩ : Unit))
  let groups := (input.groups.zipIdx.filter (fun q => q.1.parent == parent)).map
    (fun q => (⟨-1,q.2⟩ : Unit))
  have nodeKeys : NodeKeysDistinct nodes := by
    have numbered : ((virtualParents input).zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]
      exact List.nodup_range' _
    change List.Pairwise (fun a b : Nat => a ≠ b) _ at numbered
    have pairs := List.pairwise_map.mp numbered
    have filtered := List.Pairwise.filter (fun q : Int × Nat => q.1 == parent) pairs
    apply List.pairwise_map.mpr
    exact filtered.imp (by
      intro a b different _ _
      simpa only [Int.toNat_natCast] using different)
  have groupKeys : NodeKeysDistinct groups := by
    apply List.pairwise_map.mpr
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj ordered node _
    dsimp only at node
    omega
  have combined : NodeKeysDistinct (nodes++groups) := by
    apply List.pairwise_append.mpr
    refine ⟨nodeKeys,groupKeys,?_⟩
    intro a _ b member _ node
    rcases List.mem_map.mp member with ⟨q,_,rfl⟩
    dsimp only at node
    omega
  have symmetric : ∀ {a b : Unit},
      (a.group < 0 → b.group < 0 → a.node.toNat ≠ b.node.toNat) →
      b.group < 0 → a.group < 0 → b.node.toNat ≠ a.node.toNat := by
    intro a b different hb ha
    exact Ne.symm (different ha hb)
  exact ((List.mergeSort_perm (nodes++groups) _).symm.pairwise_iff symmetric).mp combined

private theorem placement_writes_node_lookup (l : Level) (entries : List (Unit × Nat))
    (state : Placement) (q : Unit × Nat) (member : q ∈ entries)
    (node : q.1.group < 0) (bound : q.1.node.toNat < state.localNodes.length)
    (keys : NodeKeysDistinct (entries.map Prod.fst)) :
    (entries.foldl (fun state q =>
      let c := l.cells.getD q.2 default
      if q.1.group < 0 then { state with localNodes := state.localNodes.set q.1.node.toNat c }
      else { state with localGroups := state.localGroups.set q.1.group.toNat c })
      state).localNodes.getD q.1.node.toNat default = l.cells.getD q.2 default := by
  induction entries generalizing state with
  | nil => simp only [List.not_mem_nil] at member
  | cons first rest ih =>
    have pairwise := List.pairwise_map.mp keys
    have headKeys := (List.pairwise_cons.mp pairwise).1
    have tailKeys : NodeKeysDistinct (rest.map Prod.fst) :=
      List.pairwise_map.mpr (List.pairwise_cons.mp pairwise).2
    rcases List.mem_cons.mp member with same | tail
    · subst q
      simp only [List.foldl_cons,node,↓reduceIte]
      have foreign : ∀ entry ∈ rest, entry.1.group < 0 →
          entry.1.node.toNat ≠ first.1.node.toNat := by
        intro entry present isNode
        exact Ne.symm (headKeys entry present node isNode)
      rw [placement_writes_preserve_foreign_node l rest _ _ foreign]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_set_self bound,Option.getD_some]
    · simp only [List.foldl_cons]
      apply ih _ tail _ tailKeys
      split <;> simpa only [List.length_set] using bound

theorem arrangeParent_node_placement (input : Input) (p : Params) (fp : FrameParams)
    (parent : Int) (state : Placement)
    (storage : state.localNodes.length = (virtualParents input).length)
    (q : Unit × Nat)
    (member : q ∈ (arrange p state.fuel (levelOf input p state.relative parent)).1.units.zipIdx)
    (node : q.1.group < 0) :
    (arrangeParent input p fp parent state).localNodes.getD q.1.node.toNat default =
      (arrange p state.fuel (levelOf input p state.relative parent)).1.cells.getD q.2 default ∧
    (arrange p state.fuel (levelOf input p state.relative parent)).1.placed.getD q.2 false = true := by
  let l := (arrange p state.fuel (levelOf input p state.relative parent)).1
  have lookup := List.mem_zipIdx_iff_getElem?.mp member
  have original : q.1 ∈ (levelOf input p state.relative parent).units := by
    have present : q.1 ∈ l.units := List.mem_of_getElem? lookup
    simpa only [l,arrange_units] using present
  have owner := level_node_owner input p state.relative parent q.1 original node
  let initial : Placement := ⟨state.localNodes,state.localGroups,state.relative,
    (arrange p state.fuel (levelOf input p state.relative parent)).2,
    state.budgetExhausted || l.budgetExhausted⟩
  have keys : NodeKeysDistinct (l.units.zipIdx.map Prod.fst) := by
    rw [List.zipIdx_map_fst]
    simpa only [l,arrange_units] using level_node_keys_distinct input p state.relative parent
  have stored := placement_writes_node_lookup l l.units.zipIdx initial q member node
    (by change q.1.node.toNat < state.localNodes.length; rw [storage]; exact owner.1) keys
  constructor
  · unfold arrangeParent
    split <;> exact stored
  · have indexedBound := (List.getElem?_eq_some_iff.mp lookup).choose
    have levelBound : q.2 < (levelOf input p state.relative parent).units.length := by
      simpa only [arrange_units] using indexedBound
    exact arranged_parent_all_placed input p state.relative parent state.fuel q.2 levelBound

theorem group_node_placement_survives_lower_levels (input : Input) (p : Params)
    (fp : FrameParams) (g : Nat) (state : Placement)
    (storage : state.localNodes.length = (virtualParents input).length)
    (q : Unit × Nat)
    (member : q ∈ (arrange p state.fuel
      (levelOf input p state.relative (Int.ofNat g))).1.units.zipIdx)
    (node : q.1.group < 0) :
    (arrangeParent input p fp (-1)
      ((List.range g).reverse.foldl
        (fun state i => arrangeParent input p fp (Int.ofNat i) state)
        (arrangeParent input p fp (Int.ofNat g) state))).localNodes.getD q.1.node.toNat default =
      (arrange p state.fuel
        (levelOf input p state.relative (Int.ofNat g))).1.cells.getD q.2 default := by
  have lookup := List.mem_zipIdx_iff_getElem?.mp member
  have original : q.1 ∈ (levelOf input p state.relative (Int.ofNat g)).units := by
    have present := List.mem_of_getElem? lookup
    simpa only [arrange_units] using present
  have owner := (level_node_owner input p state.relative (Int.ofNat g) q.1 original node).2
  rw [lower_levels_preserve_group_node input p fp g q.1.node.toNat
    (arrangeParent input p fp (Int.ofNat g) state) owner]
  exact (arrangeParent_node_placement input p fp (Int.ofNat g) state storage q member node).1

private theorem map_zipIdx_getD {α β : Type} (items : List α) (f : α × Nat → β)
    (i : Nat) (a : α) (b : β) (bound : i < items.length) :
    (items.zipIdx.map f).getD i b = f (items.getD i a,i) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_zipIdx,
    List.getElem?_eq_getElem bound,Option.map_some,Option.getD_some,Nat.zero_add]

theorem resolveHierarchy_same_parent_distinct (input : Input) (p : Params)
    (placed : Placement) (i j : Nat)
    (hi : i < (virtualParents input).length) (hj : j < (virtualParents input).length)
    (sameParent : (virtualParents input).getD i (-1) = (virtualParents input).getD j (-1))
    (localDistinct : placed.localNodes.getD i default ≠ placed.localNodes.getD j default) :
    (resolveHierarchy input p placed).nodes.getD i default ≠
      (resolveHierarchy input p placed).nodes.getD j default := by
  dsimp only [resolveHierarchy]
  rw [map_zipIdx_getD (virtualParents input) _ i (-1) default hi,
    map_zipIdx_getD (virtualParents input) _ j (-1) default hj]
  simp only [sameParent]
  intro equal
  have equalX := congrArg Cell.x equal
  have equalY := congrArg Cell.y equal
  apply localDistinct
  cases left : placed.localNodes.getD i default with
  | mk ax ay =>
    cases right : placed.localNodes.getD j default with
    | mk bx by_ =>
      simp only [left,right] at equalX equalY ⊢
      have x : ax = bx := by omega
      have y : ay = by_ := by omega
      rw [x,y]

theorem resolved_own_level_nodes_distinct (input : Input) (p : Params) (fp : FrameParams)
    (g : Nat) (state : Placement)
    (storage : state.localNodes.length = (virtualParents input).length)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (anchors : AnchorsInvariant p (levelOf input p state.relative (Int.ofNat g)))
    (q r : Unit × Nat)
    (hq : q ∈ (arrange p state.fuel
      (levelOf input p state.relative (Int.ofNat g))).1.units.zipIdx)
    (hr : r ∈ (arrange p state.fuel
      (levelOf input p state.relative (Int.ofNat g))).1.units.zipIdx)
    (qNode : q.1.group < 0) (rNode : r.1.group < 0) (different : q.2 ≠ r.2) :
    let placed := arrangeParent input p fp (-1)
      ((List.range g).reverse.foldl
        (fun state i => arrangeParent input p fp (Int.ofNat i) state)
        (arrangeParent input p fp (Int.ofNat g) state))
    (resolveHierarchy input p placed).nodes.getD q.1.node.toNat default ≠
      (resolveHierarchy input p placed).nodes.getD r.1.node.toNat default := by
  have qLookup := List.mem_zipIdx_iff_getElem?.mp hq
  have rLookup := List.mem_zipIdx_iff_getElem?.mp hr
  have qMember : q.1 ∈ (levelOf input p state.relative (Int.ofNat g)).units := by
    have present := List.mem_of_getElem? qLookup
    simpa only [arrange_units] using present
  have rMember : r.1 ∈ (levelOf input p state.relative (Int.ofNat g)).units := by
    have present := List.mem_of_getElem? rLookup
    simpa only [arrange_units] using present
  have qOwner := level_node_owner input p state.relative (Int.ofNat g) q.1 qMember qNode
  have rOwner := level_node_owner input p state.relative (Int.ofNat g) r.1 rMember rNode
  apply resolveHierarchy_same_parent_distinct input p _ _ _ qOwner.1 rOwner.1
    (qOwner.2.trans rOwner.2.symm)
  rw [group_node_placement_survives_lower_levels input p fp g state storage q hq qNode,
    group_node_placement_survives_lower_levels input p fp g state storage r hr rNode]
  have qBound := (List.getElem?_eq_some_iff.mp qLookup).choose
  have rBound := (List.getElem?_eq_some_iff.mp rLookup).choose
  apply arranged_parent_cells_distinct input p state.relative (Int.ofNat g) state.fuel px py
    anchors q.2 r.2 _ _ different
  · simpa only [arrange_units] using qBound
  · simpa only [arrange_units] using rBound

theorem hierarchyRunEvidence_after_prefix (input : Input) (p : Params) (fp : FrameParams)
    (before suffix : List Nat) (state : Placement)
    (evidence : HierarchyRunEvidence input p fp (before++suffix) state) :
    HierarchyRunEvidence input p fp suffix
      (before.foldl (fun state g => arrangeParent input p fp (Int.ofNat g) state) state) := by
  induction before generalizing state with
  | nil => exact evidence
  | cons g rest ih =>
    exact ih _ evidence.2.2.2.2

private theorem hierarchy_fold_node_length (input : Input) (p : Params) (fp : FrameParams)
    (indices : List Nat) (state : Placement) :
    (indices.foldl (fun state g => arrangeParent input p fp (Int.ofNat g) state)
      state).localNodes.length = state.localNodes.length := by
  induction indices generalizing state with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons,ih]
    exact (arrangeParent_storage_lengths input p fp (Int.ofNat g) state).1

theorem group_node_placement_survives_suffix (input : Input) (p : Params)
    (fp : FrameParams) (g : Nat) (suffix : List Nat)
    (lower : ∀ i ∈ suffix, i < g) (state : Placement)
    (storage : state.localNodes.length = (virtualParents input).length)
    (q : Unit × Nat)
    (member : q ∈ (arrange p state.fuel
      (levelOf input p state.relative (Int.ofNat g))).1.units.zipIdx)
    (node : q.1.group < 0) :
    (arrangeParent input p fp (-1)
      (suffix.foldl (fun state i => arrangeParent input p fp (Int.ofNat i) state)
        (arrangeParent input p fp (Int.ofNat g) state))).localNodes.getD q.1.node.toNat default =
      (arrange p state.fuel
        (levelOf input p state.relative (Int.ofNat g))).1.cells.getD q.2 default := by
  have lookup := List.mem_zipIdx_iff_getElem?.mp member
  have original : q.1 ∈ (levelOf input p state.relative (Int.ofNat g)).units := by
    have present := List.mem_of_getElem? lookup
    simpa only [arrange_units] using present
  have owner := (level_node_owner input p state.relative (Int.ofNat g) q.1 original node).2
  rw [arrangeParent_preserves_foreign_node input p fp (-1) _ q.1.node.toNat
    (by rw [owner]; simp only [Int.ofNat_eq_natCast]; omega)]
  rw [hierarchy_fold_preserves_foreign_node input p fp suffix _ q.1.node.toNat (by
    intro i present
    have bound := lower i present
    rw [owner]
    simp only [Int.ofNat_eq_natCast]
    omega)]
  exact (arrangeParent_node_placement input p fp (Int.ofNat g) state storage q member node).1

theorem executed_group_nodes_distinct (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (before suffix : List Nat) (g : Nat)
    (position : (List.range input.groups.length).reverse = before++g::suffix) :
    let initial : Placement := ⟨List.replicate (virtualParents input).length default,
      List.replicate input.groups.length default,
      List.replicate input.groups.length default,fuel,false⟩
    let state := before.foldl (fun state i => arrangeParent input p fp (Int.ofNat i) state) initial
    let l := (arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1
    ∀ q ∈ l.units.zipIdx, ∀ r ∈ l.units.zipIdx,
      q.1.group < 0 → r.1.group < 0 → q.2 ≠ r.2 →
      (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.getD q.1.node.toNat default ≠
        (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.getD r.1.node.toNat default := by
  intro initial state l q hq r hr qNode rNode different
  have full := placeHierarchy_execution_invariants input p fp fuel ordered px py padding line
  rw [position] at full
  have executed := hierarchyRunEvidence_after_prefix input p fp before (g::suffix) initial full
  have level : LevelInvariant p l := executed.1
  have decreasing : ((List.range input.groups.length).reverse).Pairwise (fun a b => b < a) :=
    List.pairwise_reverse.mpr List.pairwise_lt_range
  rw [position] at decreasing
  have lower : ∀ i ∈ suffix, i < g :=
    (List.pairwise_cons.mp (List.pairwise_append.mp decreasing).2.1).1
  have storage : state.localNodes.length = (virtualParents input).length := by
    rw [hierarchy_fold_node_length]
    exact List.length_replicate ..
  have qLookup := List.mem_zipIdx_iff_getElem?.mp hq
  have rLookup := List.mem_zipIdx_iff_getElem?.mp hr
  have qMember : q.1 ∈ (levelOf input p state.relative (Int.ofNat g)).units := by
    have present := List.mem_of_getElem? qLookup
    simpa only [l,arrange_units] using present
  have rMember : r.1 ∈ (levelOf input p state.relative (Int.ofNat g)).units := by
    have present := List.mem_of_getElem? rLookup
    simpa only [l,arrange_units] using present
  have qOwner := level_node_owner input p state.relative (Int.ofNat g) q.1 qMember qNode
  have rOwner := level_node_owner input p state.relative (Int.ofNat g) r.1 rMember rNode
  apply resolveHierarchy_same_parent_distinct input p _ _ _ qOwner.1 rOwner.1
    (qOwner.2.trans rOwner.2.symm)
  change (arrangeParent input p fp (-1)
    (((List.range input.groups.length).reverse).foldl
      (fun state i => arrangeParent input p fp (Int.ofNat i) state) initial)).localNodes.getD
      q.1.node.toNat default ≠
    (arrangeParent input p fp (-1)
      (((List.range input.groups.length).reverse).foldl
        (fun state i => arrangeParent input p fp (Int.ofNat i) state) initial)).localNodes.getD
        r.1.node.toNat default
  rw [position,List.foldl_append,List.foldl_cons]
  rw [group_node_placement_survives_suffix input p fp g suffix lower state storage q hq qNode,
    group_node_placement_survives_suffix input p fp g suffix lower state storage r hr rNode]
  have qBound := (List.getElem?_eq_some_iff.mp qLookup).choose
  have rBound := (List.getElem?_eq_some_iff.mp rLookup).choose
  have qPlaced := arranged_parent_all_placed input p state.relative (Int.ofNat g) state.fuel q.2
    (by simpa only [l,arrange_units] using qBound)
  have rPlaced := arranged_parent_all_placed input p state.relative (Int.ofNat g) state.fuel r.2
    (by simpa only [l,arrange_units] using rBound)
  exact level.2.2.2 q.2 r.2
    (by rw [arrange_placed_length,level_placed_length]; simpa only [l,arrange_units] using qBound)
    (by rw [arrange_placed_length,level_placed_length]; simpa only [l,arrange_units] using rBound)
    qPlaced rPlaced different

theorem executed_group_unit_rects_separated (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (before suffix : List Nat) (g : Nat)
    (position : (List.range input.groups.length).reverse = before++g::suffix) :
    let initial : Placement := ⟨List.replicate (virtualParents input).length default,
      List.replicate input.groups.length default,
      List.replicate input.groups.length default,fuel,false⟩
    let state := before.foldl (fun state i => arrangeParent input p fp (Int.ofNat i) state) initial
    let l := (arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1
    ∀ i j, i < l.units.length → j < l.units.length → i ≠ j →
      (l.absolute.getD i default).overlaps (l.absolute.getD j default) = false := by
  intro initial state l i j hi hj different
  have full := placeHierarchy_execution_invariants input p fp fuel ordered px py padding line
  rw [position] at full
  have executed := hierarchyRunEvidence_after_prefix input p fp before (g::suffix) initial full
  have iBound : i < (levelOf input p state.relative (Int.ofNat g)).units.length := by
    simpa only [l,arrange_units] using hi
  have jBound : j < (levelOf input p state.relative (Int.ofNat g)).units.length := by
    simpa only [l,arrange_units] using hj
  exact executed.2.1 i j
    (by rw [arrange_placed_length,level_placed_length]; exact iBound)
    (by rw [arrange_placed_length,level_placed_length]; exact jBound)
    (executed.2.2.1 i iBound) (executed.2.2.1 j jBound) different

theorem separated_subtrees_after_origin_shift (left right a b : Span)
    (dx dy : Int)
    (separated : left.overlaps right = false)
    (leftContains : left.contains a) (rightContains : right.contains b) :
    (a.shift dx dy).overlaps (b.shift dx dy) = false := by
  unfold Span.overlaps at separated ⊢
  unfold Span.contains at leftContains rightContains
  simp only [Span.shift] at *
  apply decide_eq_false_iff_not.mpr
  have disjoint := decide_eq_false_iff_not.mp separated
  intro overlap
  apply disjoint
  rcases leftContains with ⟨lx0,ly0,lx1,ly1⟩
  rcases rightContains with ⟨rx0,ry0,rx1,ry1⟩
  exact ⟨by omega,by omega,by omega,by omega⟩

theorem executed_group_frame_contains_unit (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (before suffix : List Nat) (g : Nat)
    (position : (List.range input.groups.length).reverse = before++g::suffix) :
    let initial : Placement := ⟨List.replicate (virtualParents input).length default,
      List.replicate input.groups.length default,
      List.replicate input.groups.length default,fuel,false⟩
    let state := before.foldl (fun state i => arrangeParent input p fp (Int.ofNat i) state) initial
    let l := (arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1
    ∀ i, i < l.units.length →
      ((placeHierarchy input p fp fuel).relative.getD g default).contains
        (l.absolute.getD i default) := by
  intro initial state l i hi
  have full := placeHierarchy_execution_invariants input p fp fuel ordered px py padding line
  rw [position] at full
  have executed := hierarchyRunEvidence_after_prefix input p fp before (g::suffix) initial full
  have decreasing : ((List.range input.groups.length).reverse).Pairwise (fun a b => b < a) :=
    List.pairwise_reverse.mpr List.pairwise_lt_range
  rw [position] at decreasing
  have lower : ∀ k ∈ suffix, k < g :=
    (List.pairwise_cons.mp (List.pairwise_append.mp decreasing).2.1).1
  have preserves : ∀ (indices : List Nat) (s : Placement),
      (∀ k ∈ indices, k < g) →
      (indices.foldl (fun s k => arrangeParent input p fp (Int.ofNat k) s) s).relative.getD
        g default = s.relative.getD g default := by
    intro indices
    induction indices with
    | nil => intro s _; rfl
    | cons k rest ih =>
      intro s bounds
      rw [List.foldl_cons,ih _ (by
        intro j member
        exact bounds j (List.mem_cons_of_mem k member))]
      exact arrangeParent_preserves_other_frame input p fp k g s
        (by have bound := bounds k (List.mem_cons_self); omega)
  have finalFrame : (placeHierarchy input p fp fuel).relative.getD g default =
      (arrangeParent input p fp (Int.ofNat g) state).relative.getD g default := by
    unfold placeHierarchy
    rw [arrangeParent_relative]
    simp only [show (-1 : Int) < 0 by decide,↓reduceIte]
    rw [position,List.foldl_append,List.foldl_cons]
    exact preserves suffix _ lower
  rw [finalFrame]
  have bound : i < (levelOf input p state.relative (Int.ofNat g)).units.length := by
    simpa only [l,arrange_units] using hi
  have marked := executed.2.2.1 i bound
  have coordinates := executed.1.2.1.2.2 i
    (by rw [arrange_placed_length,level_placed_length]; exact bound) marked
  have inside := executed.2.2.2.1 i bound
  dsimp only [state]
  simpa only [l,state,coordinates,arrange_rects] using inside

theorem descendant_span_containment (outer middle inner : Span)
    (dx dy ex ey : Int) (parent : outer.contains (middle.shift dx dy))
    (child : middle.contains (inner.shift ex ey)) :
    outer.contains (inner.shift (ex+dx) (ey+dy)) := by
  unfold Span.contains at *
  simp only [Span.shift] at *
  rcases parent with ⟨px0,py0,px1,py1⟩
  rcases child with ⟨cx0,cy0,cx1,cy1⟩
  exact ⟨by omega,by omega,by omega,by omega⟩

theorem separated_descendant_spans (left right a b : Span)
    (ax ay bx by_ dx dy : Int)
    (separated : left.overlaps right = false)
    (leftContains : left.contains (a.shift ax ay))
    (rightContains : right.contains (b.shift bx by_)) :
    (a.shift (ax+dx) (ay+dy)).overlaps
      (b.shift (bx+dx) (by_+dy)) = false := by
  have shifted := separated_subtrees_after_origin_shift left right
    (a.shift ax ay) (b.shift bx by_) dx dy separated leftContains rightContains
  simpa only [Span.shift,Int.add_assoc] using shifted

theorem executed_group_descendant_spans_separated (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (before suffix : List Nat) (g : Nat)
    (position : (List.range input.groups.length).reverse = before++g::suffix) :
    let initial : Placement := ⟨List.replicate (virtualParents input).length default,
      List.replicate input.groups.length default,
      List.replicate input.groups.length default,fuel,false⟩
    let state := before.foldl (fun state i => arrangeParent input p fp (Int.ofNat i) state) initial
    let l := (arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1
    ∀ i j, i < l.units.length → j < l.units.length → i ≠ j →
      ∀ a b : Span, ∀ ax ay bx by_ dx dy : Int,
        (l.absolute.getD i default).contains (a.shift ax ay) →
        (l.absolute.getD j default).contains (b.shift bx by_) →
        (a.shift (ax+dx) (ay+dy)).overlaps
          (b.shift (bx+dx) (by_+dy)) = false := by
  intro initial state l i j hi hj different a b ax ay bx by_ dx dy left right
  have separated := executed_group_unit_rects_separated input p fp fuel
    ordered px py padding line before suffix g position i j hi hj different
  exact separated_descendant_spans (l.absolute.getD i default)
    (l.absolute.getD j default) a b ax ay bx by_ dx dy separated left right

theorem executed_root_unit_rects_separated (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight) :
    let initial : Placement := ⟨List.replicate (virtualParents input).length default,
      List.replicate input.groups.length default,
      List.replicate input.groups.length default,fuel,false⟩
    let state := (List.range input.groups.length).reverse.foldl
      (fun state i => arrangeParent input p fp (Int.ofNat i) state) initial
    let l := (arrange p state.fuel (levelOf input p state.relative (-1))).1
    ∀ i j, i < l.units.length → j < l.units.length → i ≠ j →
      (l.absolute.getD i default).overlaps (l.absolute.getD j default) = false := by
  intro initial state l i j hi hj different
  have full := placeHierarchy_execution_invariants input p fp fuel ordered px py padding line
  have executed := hierarchyRunEvidence_after_prefix input p fp
    (List.range input.groups.length).reverse [] initial
    (by simpa only [List.append_nil] using full)
  have iBound : i < (levelOf input p state.relative (-1)).units.length := by
    simpa only [l,arrange_units] using hi
  have jBound : j < (levelOf input p state.relative (-1)).units.length := by
    simpa only [l,arrange_units] using hj
  exact executed.2.1 i j
    (by rw [arrange_placed_length,level_placed_length]; exact iBound)
    (by rw [arrange_placed_length,level_placed_length]; exact jBound)
    (executed.2.2 i iBound) (executed.2.2 j jBound) different

theorem divergent_common_prefix (left right : List Unit) (parent owner : Int)
    (a b : Unit) (found : divergent left right parent = some (owner,a,b)) :
    a ≠ b ∧ ∃ shared leftRest rightRest,
      left = shared ++ a::leftRest ∧ right = shared ++ b::rightRest ∧
      owner = shared.foldl (fun _ u => u.group) parent := by
  induction left generalizing right parent with
  | nil => simp only [divergent] at found; cases found
  | cons first rest ih =>
    cases right with
    | nil => simp only [divergent] at found; cases found
    | cons second tail =>
      by_cases same : first = second
      · subst second
        simp only [divergent,↓reduceIte] at found
        obtain ⟨different,shared,leftRest,rightRest,leftEq,rightEq,ownerEq⟩ :=
          ih tail first.group found
        refine ⟨different,first::shared,leftRest,rightRest,?_,?_,?_⟩
        · simp only [List.cons_append,leftEq]
        · simp only [List.cons_append,rightEq]
        · simpa only [List.foldl_cons] using ownerEq
      · simp only [divergent,same,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at found
        rcases found with ⟨ownerEq,firstEq,secondEq⟩
        subst owner
        subst a
        subst b
        exact ⟨same,[],rest,tail,rfl,rfl,rfl⟩

theorem resolveHierarchy_node_at (input : Input) (p : Params) (placed : Placement)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (n : Nat) (bound : n < (virtualParents input).length) :
    ∃ origins : List Cell,
      (resolveHierarchy input p placed).nodes.getD n default =
        let parent := (virtualParents input).getD n (-1)
        let base := if parent < 0 then default else origins.getD parent.toNat default
        let offset := placed.localNodes.getD n default
        (⟨base.x+offset.x,base.y+offset.y⟩ : Cell) := by
  obtain ⟨origins,_,_,_,nodes⟩ := resolveHierarchy_execution input p placed ordered
  refine ⟨origins,?_⟩
  rw [nodes]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_zipIdx,
    List.getElem?_eq_getElem bound,Option.map_some,Option.getD_some,Nat.zero_add]

theorem resolved_siblings_distinct (input : Input) (p : Params) (placed : Placement)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (a b : Nat) (ha : a < (virtualParents input).length)
    (hb : b < (virtualParents input).length)
    (siblings : (virtualParents input).getD a (-1) =
      (virtualParents input).getD b (-1))
    (different : placed.localNodes.getD a default ≠ placed.localNodes.getD b default) :
    (resolveHierarchy input p placed).nodes.getD a default ≠
      (resolveHierarchy input p placed).nodes.getD b default := by
  obtain ⟨origins,_,_,_,nodes⟩ := resolveHierarchy_execution input p placed ordered
  have nodeAt : ∀ n, n < (virtualParents input).length →
      (resolveHierarchy input p placed).nodes.getD n default =
        let parent := (virtualParents input).getD n (-1)
        let base := if parent < 0 then default else origins.getD parent.toNat default
        let offset := placed.localNodes.getD n default
        (⟨base.x+offset.x,base.y+offset.y⟩ : Cell) := by
    intro n bound
    rw [nodes]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_zipIdx,
      List.getElem?_eq_getElem bound,Option.map_some,Option.getD_some,Nat.zero_add]
  intro equal
  rw [nodeAt a ha,nodeAt b hb,siblings] at equal
  apply different
  have x := congrArg Cell.x equal
  have y := congrArg Cell.y equal
  have xeq : (placed.localNodes.getD a default).x =
      (placed.localNodes.getD b default).x := by
    dsimp only at x
    omega
  have yeq : (placed.localNodes.getD a default).y =
      (placed.localNodes.getD b default).y := by
    dsimp only at y
    omega
  cases ha_cell : placed.localNodes.getD a default
  cases hb_cell : placed.localNodes.getD b default
  rw [ha_cell, hb_cell] at xeq yeq
  simp only [Cell.mk.injEq]
  exact ⟨xeq, yeq⟩

theorem groupChain_groups_nonnegative (groups : List Group) (fuel : Nat) (parent : Int) :
    ∀ unit ∈ groupChain groups fuel parent, 0 ≤ unit.group := by
  induction fuel generalizing parent with
  | zero =>
    intro unit member
    cases member
  | succ fuel ih =>
    intro unit member
    simp only [groupChain] at member
    split at member
    · simp only [List.not_mem_nil] at member
    · rename_i nonnegative
      rcases List.mem_append.mp member with previous | last
      · exact ih _ unit previous
      · have equal : unit = (⟨-1, parent⟩ : Unit) := List.mem_singleton.mp last
        subst unit
        dsimp only
        omega

theorem divergent_terminal_nodes (left right : List Unit) (a b : Nat)
    (leftGroups : ∀ unit ∈ left, 0 ≤ unit.group)
    (rightGroups : ∀ unit ∈ right, 0 ≤ unit.group)
    (different : a ≠ b) (parent : Int) :
    ∃ owner first second,
      divergent (left ++ [(⟨a, -1⟩ : Unit)])
        (right ++ [(⟨b, -1⟩ : Unit)]) parent = some (owner, first, second) := by
  revert leftGroups rightGroups
  induction left generalizing right parent with
  | nil =>
    intro leftGroups rightGroups
    cases right with
    | nil =>
      have unequal : (⟨a, -1⟩ : Unit) ≠ (⟨b, -1⟩ : Unit) := by
        intro equal
        have nodes := congrArg Unit.node equal
        apply different
        dsimp only at nodes
        omega
      exact ⟨parent, ⟨a, -1⟩, ⟨b, -1⟩, by simp_all [divergent]⟩
    | cons unit rest =>
      have nonnegative := rightGroups unit List.mem_cons_self
      have unequal : (⟨a, -1⟩ : Unit) ≠ unit := by
        intro equal
        have groups := congrArg Unit.group equal
        dsimp only at groups
        omega
      exact ⟨parent, ⟨a, -1⟩, unit, by
        simp_all [divergent]⟩
  | cons unit rest ih =>
    intro leftGroups rightGroups
    have nonnegative := leftGroups unit List.mem_cons_self
    have remaining : ∀ entry ∈ rest, 0 ≤ entry.group := by
      intro entry member
      exact leftGroups entry (List.mem_cons_of_mem unit member)
    cases right with
    | nil =>
      have unequal : unit ≠ (⟨b, -1⟩ : Unit) := by
        intro equal
        have groups := congrArg Unit.group equal
        dsimp only at groups
        omega
      exact ⟨parent, unit, ⟨b, -1⟩, by
        simp_all [divergent]⟩
    | cons other tail =>
      by_cases equal : unit = other
      · subst other
        have rightRemaining : ∀ entry ∈ tail, 0 ≤ entry.group := by
          intro entry member
          exact rightGroups entry (List.mem_cons_of_mem unit member)
        obtain ⟨owner, first, second, found⟩ :=
          ih (right := tail) (parent := unit.group) remaining rightRemaining
        exact ⟨owner, first, second, by
          simpa [divergent] using found⟩
      · exact ⟨parent, unit, other, by
          simp_all [divergent]⟩

theorem chainOf_divergent (input : Input) (a b : Nat) (different : a ≠ b) :
    ∃ owner first second,
      divergent (chainOf input a) (chainOf input b) (-1) =
        some (owner, first, second) := by
  exact divergent_terminal_nodes _ _ a b
    (groupChain_groups_nonnegative input.groups input.groups.length _)
    (groupChain_groups_nonnegative input.groups input.groups.length _) different (-1)

theorem chainOf_divergent_common_prefix (input : Input) (a b : Nat) (different : a ≠ b) :
    ∃ owner first second shared leftRest rightRest,
      divergent (chainOf input a) (chainOf input b) (-1) =
        some (owner, first, second) ∧
      first ≠ second ∧
      chainOf input a = shared ++ first :: leftRest ∧
      chainOf input b = shared ++ second :: rightRest ∧
      owner = shared.foldl (fun _ unit => unit.group) (-1) := by
  obtain ⟨owner, first, second, found⟩ := chainOf_divergent input a b different
  obtain ⟨distinct, shared, leftRest, rightRest, leftEq, rightEq, ownerEq⟩ :=
    divergent_common_prefix (chainOf input a) (chainOf input b) (-1)
      owner first second found
  exact ⟨owner, first, second, shared, leftRest, rightRest,
    found, distinct, leftEq, rightEq, ownerEq⟩

theorem chainOf_unit_cases (input : Input) (node : Nat) (unit : Unit)
    (member : unit ∈ chainOf input node) :
    0 ≤ unit.group ∨ unit = (⟨node, -1⟩ : Unit) := by
  rcases List.mem_append.mp member with ancestor | terminal
  · exact Or.inl
      (groupChain_groups_nonnegative input.groups input.groups.length _ unit ancestor)
  · exact Or.inr (List.mem_singleton.mp terminal)

theorem chainOf_divergent_units (input : Input) (a b : Nat)
    (owner : Int) (first second : Unit)
    (found : divergent (chainOf input a) (chainOf input b) (-1) =
      some (owner, first, second)) :
    first ≠ second ∧ first ∈ chainOf input a ∧ second ∈ chainOf input b ∧
      (0 ≤ first.group ∨ first = (⟨a, -1⟩ : Unit)) ∧
      (0 ≤ second.group ∨ second = (⟨b, -1⟩ : Unit)) := by
  obtain ⟨distinct, shared, leftRest, rightRest, leftEq, rightEq, _⟩ :=
    divergent_common_prefix (chainOf input a) (chainOf input b) (-1)
      owner first second found
  have leftMember : first ∈ chainOf input a := by
    rw [leftEq]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have rightMember : second ∈ chainOf input b := by
    rw [rightEq]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  exact ⟨distinct, leftMember, rightMember,
    chainOf_unit_cases input a first leftMember,
    chainOf_unit_cases input b second rightMember⟩

theorem chainOf_divergent_chain_indices (input : Input) (a b : Nat)
    (owner : Int) (first second : Unit)
    (found : divergent (chainOf input a) (chainOf input b) (-1) =
      some (owner, first, second)) :
    ∃ depth,
      depth < (chainOf input a).length ∧
      depth < (chainOf input b).length ∧
      (chainOf input a).getD depth default = first ∧
      (chainOf input b).getD depth default = second ∧
      first ≠ second := by
  obtain ⟨distinct, shared, leftRest, rightRest, leftEq, rightEq, _⟩ :=
    divergent_common_prefix (chainOf input a) (chainOf input b) (-1)
      owner first second found
  refine ⟨shared.length, ?_, ?_, ?_, ?_, distinct⟩
  · rw [leftEq, List.length_append, List.length_cons]
    omega
  · rw [rightEq, List.length_append, List.length_cons]
    omega
  · rw [leftEq]
    simp
  · rw [rightEq]
    simp

theorem executed_root_descendant_spans_separated (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight) :
    let initial : Placement := ⟨List.replicate (virtualParents input).length default,
      List.replicate input.groups.length default,
      List.replicate input.groups.length default, fuel, false⟩
    let state := (List.range input.groups.length).reverse.foldl
      (fun state i => arrangeParent input p fp (Int.ofNat i) state) initial
    let l := (arrange p state.fuel (levelOf input p state.relative (-1))).1
    ∀ i j, i < l.units.length → j < l.units.length → i ≠ j →
      ∀ a b : Span, ∀ ax ay bx by_ : Int,
        (l.absolute.getD i default).contains (a.shift ax ay) →
        (l.absolute.getD j default).contains (b.shift bx by_) →
        (a.shift ax ay).overlaps (b.shift bx by_) = false := by
  intro initial state l i j hi hj different a b ax ay bx by_ left right
  have separated := executed_root_unit_rects_separated input p fp fuel
    ordered px py padding line i j hi hj different
  have descendants := separated_descendant_spans
    (l.absolute.getD i default) (l.absolute.getD j default)
    a b ax ay bx by_ 0 0 separated left right
  simpa only [Int.add_zero] using descendants

theorem arrangeParent_own_level_lookup (input : Input) (p : Params) (fp : FrameParams)
    (parent : Int) (state : Placement)
    (storage : state.localNodes.length = (virtualParents input).length)
    (i : Nat)
    (bound : i < (levelOf input p state.relative parent).units.length)
    (node : ((levelOf input p state.relative parent).units.getD i default).group < 0) :
    let unit := (levelOf input p state.relative parent).units.getD i default
    (arrangeParent input p fp parent state).localNodes.getD unit.node.toNat default =
      (arrange p state.fuel (levelOf input p state.relative parent)).1.cells.getD i default := by
  let unit := (levelOf input p state.relative parent).units.getD i default
  have lookup :
      (arrange p state.fuel (levelOf input p state.relative parent)).1.units[i]? =
        some unit := by
    rw [arrange_units]
    simp only [unit,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem bound,Option.getD_some]
  exact (arrangeParent_node_placement input p fp parent state storage (unit,i)
    (List.mem_zipIdx_iff_getElem?.mpr lookup) node).1

theorem executed_group_nodes_nodup (input : Input) (p : Params) (fp : FrameParams)
    (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight)
    (before suffix : List Nat) (g : Nat)
    (position : (List.range input.groups.length).reverse = before++g::suffix) :
    let initial : Placement := ⟨List.replicate (virtualParents input).length default,
      List.replicate input.groups.length default,
      List.replicate input.groups.length default,fuel,false⟩
    let state := before.foldl (fun state i => arrangeParent input p fp (Int.ofNat i) state) initial
    let l := (arrange p state.fuel (levelOf input p state.relative (Int.ofNat g))).1
    ((l.units.zipIdx.filter (fun q => q.1.group < 0)).map
      (fun q => (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.getD
        q.1.node.toNat default)).Nodup := by
  intro initial state l
  have indices : (l.units.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  have indexed := List.pairwise_map.mp indices
  have selected := List.Pairwise.filter (fun q : Unit × Nat => q.1.group < 0) indexed
  apply List.pairwise_map.mpr
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj less
  let entries := l.units.zipIdx.filter (fun q => q.1.group < 0)
  have left : entries[i] ∈ entries := List.getElem_mem hi
  have right : entries[j] ∈ entries := List.getElem_mem hj
  have leftInfo := List.mem_filter.mp left
  have rightInfo := List.mem_filter.mp right
  have different := List.pairwise_iff_getElem.mp selected i j hi hj less
  exact executed_group_nodes_distinct input p fp fuel ordered px py padding line
    before suffix g position entries[i] leftInfo.1 entries[j] rightInfo.1
    (by simpa only [decide_eq_true_eq] using leftInfo.2)
    (by simpa only [decide_eq_true_eq] using rightInfo.2) different

theorem executed_root_nodes_distinct (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight) :
    let initial : Placement := ⟨List.replicate (virtualParents input).length default,
      List.replicate input.groups.length default,
      List.replicate input.groups.length default, fuel, false⟩
    let state := (List.range input.groups.length).reverse.foldl
      (fun state i => arrangeParent input p fp (Int.ofNat i) state) initial
    let l := (arrange p state.fuel (levelOf input p state.relative (-1))).1
    ∀ q ∈ l.units.zipIdx, ∀ r ∈ l.units.zipIdx,
      q.1.group < 0 → r.1.group < 0 → q.2 ≠ r.2 →
      (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.getD
        q.1.node.toNat default ≠
      (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.getD
        r.1.node.toNat default := by
  intro initial state l q hq r hr qNode rNode different
  have qLookup := List.mem_zipIdx_iff_getElem?.mp hq
  have rLookup := List.mem_zipIdx_iff_getElem?.mp hr
  have qMember : q.1 ∈ (levelOf input p state.relative (-1)).units := by
    simpa only [l,arrange_units] using List.mem_of_getElem? qLookup
  have rMember : r.1 ∈ (levelOf input p state.relative (-1)).units := by
    simpa only [l,arrange_units] using List.mem_of_getElem? rLookup
  have qOwner := level_node_owner input p state.relative (-1) q.1 qMember qNode
  have rOwner := level_node_owner input p state.relative (-1) r.1 rMember rNode
  have storage : state.localNodes.length = (virtualParents input).length := by
    rw [hierarchy_fold_node_length]
    exact List.length_replicate ..
  apply resolveHierarchy_same_parent_distinct input p _ _ _ qOwner.1 rOwner.1
    (qOwner.2.trans rOwner.2.symm)
  change (arrangeParent input p fp (-1) state).localNodes.getD q.1.node.toNat default ≠
    (arrangeParent input p fp (-1) state).localNodes.getD r.1.node.toNat default
  rw [(arrangeParent_node_placement input p fp (-1) state storage q hq qNode).1,
    (arrangeParent_node_placement input p fp (-1) state storage r hr rNode).1]
  have full := placeHierarchy_execution_invariants input p fp fuel ordered px py padding line
  have executed := hierarchyRunEvidence_after_prefix input p fp
    (List.range input.groups.length).reverse [] initial
    (by simpa only [List.append_nil] using full)
  have qBound := (List.getElem?_eq_some_iff.mp qLookup).choose
  have rBound := (List.getElem?_eq_some_iff.mp rLookup).choose
  have qi : q.2 < (levelOf input p state.relative (-1)).units.length := by
    simpa only [l,arrange_units] using qBound
  have ri : r.2 < (levelOf input p state.relative (-1)).units.length := by
    simpa only [l,arrange_units] using rBound
  exact executed.1.2.2.2 q.2 r.2
    (by rw [arrange_placed_length,level_placed_length]; exact qi)
    (by rw [arrange_placed_length,level_placed_length]; exact ri)
    (executed.2.2 q.2 qi) (executed.2.2 r.2 ri) different

theorem executed_root_nodes_nodup (input : Input) (p : Params)
    (fp : FrameParams) (fuel : Nat)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k)
    (px : 0 < p.pitchX) (py : 0 < p.pitchY)
    (padding : 0 ≤ fp.padding) (line : 0 ≤ fp.lineHeight) :
    let initial : Placement := ⟨List.replicate (virtualParents input).length default,
      List.replicate input.groups.length default,
      List.replicate input.groups.length default, fuel, false⟩
    let state := (List.range input.groups.length).reverse.foldl
      (fun state i => arrangeParent input p fp (Int.ofNat i) state) initial
    let l := (arrange p state.fuel (levelOf input p state.relative (-1))).1
    ((l.units.zipIdx.filter (fun q => q.1.group < 0)).map
      (fun q => (resolveHierarchy input p (placeHierarchy input p fp fuel)).nodes.getD
        q.1.node.toNat default)).Nodup := by
  intro initial state l
  have indices : (l.units.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  have indexed := List.pairwise_map.mp indices
  have selected := List.Pairwise.filter (fun q : Unit × Nat => q.1.group < 0) indexed
  apply List.pairwise_map.mpr
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj less
  let entries := l.units.zipIdx.filter (fun q => q.1.group < 0)
  have left : entries[i] ∈ entries := List.getElem_mem hi
  have right : entries[j] ∈ entries := List.getElem_mem hj
  have leftInfo := List.mem_filter.mp left
  have rightInfo := List.mem_filter.mp right
  have different := List.pairwise_iff_getElem.mp selected i j hi hj less
  exact executed_root_nodes_distinct input p fp fuel ordered px py padding line
    entries[i] leftInfo.1 entries[j] rightInfo.1
    (by simpa only [decide_eq_true_eq] using leftInfo.2)
    (by simpa only [decide_eq_true_eq] using rightInfo.2) different

theorem divergent_self (chain : List Unit) (parent : Int) :
    divergent chain chain parent = none := by
  induction chain generalizing parent with
  | nil => rfl
  | cons unit rest ih =>
    simpa only [divergent, ↓reduceIte] using ih unit.group

theorem chainOf_injective (input : Input) :
    Function.Injective (chainOf input) := by
  intro a b equal
  apply Classical.byContradiction
  intro different
  obtain ⟨owner, first, second, found⟩ := chainOf_divergent input a b different
  rw [equal, divergent_self] at found
  cases found

theorem chainOf_nodes_nodup (input : Input) :
    ((List.range (virtualParents input).length).map (chainOf input)).Nodup := by
  apply List.pairwise_map.mpr
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj less
  simp only [List.length_range] at hi hj
  simp only [List.getElem_range]
  intro equal
  have same := chainOf_injective input equal
  omega

theorem resolveHierarchy_indexed_execution (input : Input) (p : Params)
    (placed : Placement)
    (ordered : ∀ k, k < input.groups.length →
      (input.groups.getD k default).parent < Int.ofNat k) :
    ∃ origins : List Cell,
      origins.length = input.groups.length ∧
      (∀ g, g < input.groups.length →
        origins.getD g default =
          let parent := (input.groups.getD g default).parent
          let base := if parent < 0 then default else origins.getD parent.toNat default
          let offset := placed.localGroups.getD g default
          (⟨base.x + offset.x, base.y + offset.y⟩ : Cell)) ∧
      (∀ n, n < (virtualParents input).length →
        (resolveHierarchy input p placed).nodes.getD n default =
          let parent := (virtualParents input).getD n (-1)
          let base := if parent < 0 then default else origins.getD parent.toNat default
          let offset := placed.localNodes.getD n default
          (⟨base.x + offset.x, base.y + offset.y⟩ : Cell)) := by
  obtain ⟨origins, lengths, equations, _, nodes⟩ :=
    resolveHierarchy_execution input p placed ordered
  refine ⟨origins, lengths, ?_, ?_⟩
  · intro g bound
    have lookup : input.groups[g]? = some (input.groups.getD g default) := by
      simp only [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem bound, Option.getD_some]
    exact equations (input.groups.getD g default, g)
      (List.mem_zipIdx_iff_getElem?.mpr lookup)
  · intro n bound
    rw [nodes]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_zipIdx, List.getElem?_eq_getElem bound,
      Option.map_some, Option.getD_some, Nat.zero_add]

end Elegant.Grid.Architecture

import Elegant.GridArchitecturePartitionFacts

set_option autoImplicit false

namespace Elegant.Grid.Architecture

def parentLevels (input : Input) : List Int :=
  ((List.range input.groups.length).reverse.map Int.ofNat) ++ [-1]

theorem parentLevels_unique (input : Input) : (parentLevels input).Nodup := by
  have hr : (List.range input.groups.length).reverse.Nodup := by
    change List.Pairwise (fun a b : Nat => a ≠ b) _
    rw [List.pairwise_reverse]
    exact (List.nodup_range).imp (fun h => Ne.symm h)
  have hm : ((List.range input.groups.length).reverse.map Int.ofNat).Nodup := by
    change List.Pairwise (fun a b : Int => a ≠ b) _
    rw [List.pairwise_map]
    exact hr.imp (fun h heq => h (Int.ofNat.inj heq))
  unfold parentLevels
  change List.Pairwise (fun a b : Int => a ≠ b) _
  rw [List.pairwise_append]
  refine ⟨hm,by simp,?_⟩
  intro a ha b hb
  have hb' : b = -1 := by simpa using hb
  subst b
  rcases List.mem_map.mp ha with ⟨n,_,rfl⟩
  intro impossible
  cases impossible

theorem level_units_independent (input : Input) (p : Params) (a b : List Span) (parent : Int) :
    (levelOf input p a parent).units = (levelOf input p b parent).units := rfl

private theorem store_fuel (l : Level) (entries : List (Unit × Nat)) (state : Placement) :
    (entries.foldl (fun state q =>
      let c := l.cells.getD q.2 default
      if q.1.group < 0 then {state with localNodes := state.localNodes.set q.1.node.toNat c}
      else {state with localGroups := state.localGroups.set q.1.group.toNat c}) state).fuel = state.fuel := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split <;> rfl

theorem arrangeParent_fuel (input : Input) (p : Params) (fp : FrameParams)
    (parent : Int) (state : Placement) :
    (arrangeParent input p fp parent state).fuel =
      (arrange p state.fuel (levelOf input p state.relative parent)).2 := by
  unfold arrangeParent
  split <;> simp only [store_fuel]

theorem arrangeParent_count (input : Input) (p : Params) (fp : FrameParams)
    (parent : Int) (state : Placement) :
    state.fuel - (arrangeParent input p fp parent state).fuel ≤ (levelOf input p [] parent).units.length ∧
      (arrangeParent input p fp parent state).fuel ≤ state.fuel := by
  rw [arrangeParent_fuel]
  have count := arrange_level_count input p state.relative parent state.fuel
  have fuel := arrange_fuel_le p state.fuel (levelOf input p state.relative parent)
  rw [level_units_independent input p state.relative [] parent] at count
  exact ⟨count,fuel⟩

theorem fold_parent_count (input : Input) (p : Params) (fp : FrameParams)
    (parents : List Int) (state : Placement) :
    state.fuel - (parents.foldl (fun state parent => arrangeParent input p fp parent state) state).fuel ≤
      (parents.map (fun parent => (levelOf input p [] parent).units.length)).sum ∧
    (parents.foldl (fun state parent => arrangeParent input p fp parent state) state).fuel ≤ state.fuel := by
  induction parents generalizing state with
  | nil => simp
  | cons parent rest ih =>
    have step := arrangeParent_count input p fp parent state
    have tail := ih (arrangeParent input p fp parent state)
    simp only [List.foldl_cons,List.map_cons,List.sum_cons]
    omega

theorem placeHierarchy_as_fold (input : Input) (p : Params) (fp : FrameParams) (fuel : Nat) :
    placeHierarchy input p fp fuel =
      (parentLevels input).foldl (fun state parent => arrangeParent input p fp parent state)
        ⟨List.replicate (virtualParents input).length default,
          List.replicate input.groups.length default,List.replicate input.groups.length default,fuel,false⟩ := by
  simp only [placeHierarchy,parentLevels,List.foldl_append,List.foldl_cons,List.foldl_nil,List.foldl_map]

/-- Every pop consumes one distinct service, junction, empty-leaf placeholder, or
container unit. The bound counts the actual native placement units across levels. -/
theorem arch_pops_le_placement_units (input : Input) (p : Params) (fp : FrameParams) (fuel : Nat) :
    fuel - (placeHierarchy input p fp fuel).fuel ≤ placementUnitCount input := by
  rw [placeHierarchy_as_fold]
  let initial : Placement := ⟨List.replicate (virtualParents input).length default,
    List.replicate input.groups.length default,List.replicate input.groups.length default,fuel,false⟩
  have count := (fold_parent_count input p fp (parentLevels input) initial).1
  have partition := level_units_partition input p [] (parentLevels input) (parentLevels_unique input)
  exact Nat.le_trans count partition

theorem arch_pops_le_initial_fuel (input : Input) (p : Params) (fp : FrameParams) (fuel : Nat) :
    fuel - (placeHierarchy input p fp fuel).fuel ≤ fuel := Nat.sub_le _ _

theorem arch_pops_bounded (input : Input) (p : Params) (fp : FrameParams) (initialBudget : Nat) :
    initialBudget - (placeHierarchy input p fp initialBudget).fuel ≤
      (virtualParents input).length + input.groups.length ∧
    initialBudget - (placeHierarchy input p fp initialBudget).fuel ≤ initialBudget := by
  exact ⟨arch_pops_le_placement_units input p fp initialBudget,
    arch_pops_le_initial_fuel input p fp initialBudget⟩

end Elegant.Grid.Architecture

import Elegant.GridArchitectureCountFacts

set_option autoImplicit false

namespace Elegant.Grid.Architecture

theorem zipIdx_filter_length {α : Type} (items : List α) (predicate : α → Bool) :
    (items.zipIdx.filter (fun q => predicate q.1)).length = (items.filter predicate).length := by
  have projected : ((items.zipIdx.filter (fun q => predicate q.1)).map Prod.fst) = items.filter predicate := by
    calc
      _ = (items.zipIdx.map Prod.fst).filter predicate :=
        (List.filter_map (f := Prod.fst) (p := predicate) (l := items.zipIdx)).symm
      _ = items.filter predicate := by rw [List.zipIdx_map_fst]
  have lengths := congrArg List.length projected
  simpa only [List.length_map] using lengths

theorem filter_cons_sum {α : Type} (parents : List Int) (owner : α → Int)
    (item : α) (items : List α) :
    (parents.map (fun parent => ((item :: items).filter (fun x => owner x == parent)).length)).sum =
      parents.count (owner item) +
        (parents.map (fun parent => (items.filter (fun x => owner x == parent)).length)).sum := by
  induction parents with
  | nil => simp
  | cons parent rest ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [ih]
    by_cases h : owner item = parent
    · simp [h] <;> omega
    · simp [h,Ne.symm h] <;> omega

theorem partition_filter_count_le {α : Type} (parents : List Int) (owner : α → Int)
    (items : List α) (unique : parents.Nodup) :
    (parents.map (fun parent => (items.filter (fun x => owner x == parent)).length)).sum ≤ items.length := by
  induction items with
  | nil => induction parents <;> simp_all
  | cons item rest ih =>
    rw [filter_cons_sum]
    have count := unique.count (a := owner item)
    have bound : parents.count (owner item) ≤ 1 := by split at count <;> omega
    simp only [List.length_cons]
    omega

theorem level_units_length (input : Input) (p : Params) (relative : List Span) (parent : Int) :
    (levelOf input p relative parent).units.length =
      ((virtualParents input).filter (fun value => value == parent)).length +
      (input.groups.filter (fun group => group.parent == parent)).length := by
  simp only [levelOf,List.length_mergeSort,List.length_append,List.length_map]
  rw [zipIdx_filter_length (virtualParents input) (fun value => value == parent),
    zipIdx_filter_length input.groups (fun group => group.parent == parent)]

theorem level_units_partition (input : Input) (p : Params) (relative : List Span)
    (parents : List Int) (unique : parents.Nodup) :
    (parents.map (fun parent => (levelOf input p relative parent).units.length)).sum ≤
      placementUnitCount input := by
  have nodes := partition_filter_count_le parents id (virtualParents input) unique
  have groups := partition_filter_count_le parents (fun group : Group => group.parent) input.groups unique
  have distribute : ∀ (ps : List Int),
      (ps.map (fun parent => (levelOf input p relative parent).units.length)).sum =
        (ps.map (fun parent => ((virtualParents input).filter (fun value => value == parent)).length)).sum +
        (ps.map (fun parent => (input.groups.filter (fun group => group.parent == parent)).length)).sum := by
    intro ps
    induction ps with
    | nil => rfl
    | cons parent rest ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [ih,level_units_length]
      omega
  rw [distribute]
  unfold placementUnitCount
  exact Nat.add_le_add nodes groups

theorem findIdx_getD_lt {α : Type} (items : List α) (predicate : α → Bool)
    (positive : 0 < items.length) : (items.findIdx? predicate).getD 0 < items.length := by
  cases h : items.findIdx? predicate with
  | none => simpa only [h,Option.getD_none] using positive
  | some i =>
    have bound := (List.findIdx?_eq_some_iff_findIdx_eq.mp h).1
    simpa only [h,Option.getD_some] using bound

theorem level_placed_length (input : Input) (p : Params) (relative : List Span) (parent : Int) :
    (levelOf input p relative parent).placed.length = (levelOf input p relative parent).units.length := by
  simp only [levelOf,List.length_replicate]

theorem level_edges_bound (input : Input) (p : Params) (relative : List Span) (parent : Int)
    (positive : 0 < (levelOf input p relative parent).units.length) :
    ∀ e ∈ (levelOf input p relative parent).edges,
      e.a < (levelOf input p relative parent).placed.length ∧
      e.b < (levelOf input p relative parent).placed.length := by
  dsimp only [levelOf] at positive ⊢
  intro e he
  rcases List.mem_map.mp he with ⟨edge,_,rfl⟩
  simp only [List.length_replicate]
  exact ⟨findIdx_getD_lt _ _ positive,findIdx_getD_lt _ _ positive⟩

theorem arrange_level_count (input : Input) (p : Params) (relative : List Span)
    (parent : Int) (fuel : Nat) :
    fuel - (arrange p fuel (levelOf input p relative parent)).2 ≤
      (levelOf input p relative parent).units.length := by
  by_cases hz : (levelOf input p relative parent).units.length = 0
  · simp [arrange,hz]
  · exact arrange_count_bound p fuel _ (level_placed_length _ _ _ _)
      (level_edges_bound _ _ _ _ (by omega))

end Elegant.Grid.Architecture

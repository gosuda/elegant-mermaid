import Elegant.Layered.VisibilityRoute
import Std.Data.HashMap.Lemmas

set_option autoImplicit false

namespace Elegant.Layered.Visibility

local instance chainVertexLawfulBEq : LawfulBEq Vertex where
  rfl := by deriving_ReflEq_tactic
  eq_of_beq := by deriving_LawfulEq_tactic

theorem Grid.chain_head_root_of_rank_preserving (g : Grid) (prev : Std.HashMap Vertex Vertex)
    (v : Vertex) (rank : Vertex → Nat) (predicate : Vertex → Prop)
    (decreases : ∀ (u p : Vertex), prev[u]? = some p → rank p < rank u)
    (initial : predicate v)
    (preserves : ∀ (u p : Vertex), prev[u]? = some p → predicate u → predicate p) :
    ∃ root, prev[root]? = none ∧ predicate root ∧
      (g.chain prev (prev.size + 1) v []).head? = some (g.point root) := by
  have walk : ∀ (fuel : Nat) (current : Vertex) (acc : List Point) (seen : List Vertex),
      predicate current → seen.Nodup → seen ⊆ prev.keys →
      (∀ u ∈ seen, rank current < rank u) →
      prev.size < fuel + seen.length →
      ∃ root, prev[root]? = none ∧ predicate root ∧
        (g.chain prev fuel current acc).head? = some (g.point root) := by
    intro fuel
    induction fuel with
    | zero =>
      intro _ _ seen _ unique inKeys _ budget
      have count := unique.length_le_of_subset inKeys
      rw [Std.HashMap.length_keys] at count
      simp only [Nat.zero_add] at budget
      exact (Nat.not_lt_of_ge count budget).elim
    | succ fuel ih =>
      intro current acc seen holds unique inKeys above budget
      cases edge : prev[current]? with
      | none =>
        exact ⟨current, edge, holds, by simp only [Grid.chain, edge, List.head?_cons]⟩
      | some parent =>
        have smaller := decreases current parent edge
        have fresh : current ∉ seen := fun h => Nat.lt_irrefl _ (above current h)
        have currentKey : current ∈ prev.keys := by
          rw [← Std.HashMap.map_fst_toList_eq_keys]
          exact List.mem_map_of_mem (f := Prod.fst)
            (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr edge)
        have nextKeys : current :: seen ⊆ prev.keys := by
          intro u hu
          rcases List.mem_cons.mp hu with rfl | old
          · exact currentKey
          · exact inKeys old
        have nextAbove : ∀ u ∈ current :: seen, rank parent < rank u := by
          intro u hu
          rcases List.mem_cons.mp hu with rfl | old
          · exact smaller
          · exact Nat.lt_trans smaller (above u old)
        have nextBudget : prev.size < fuel + (current :: seen).length := by
          simp only [List.length_cons]
          omega
        simpa only [Grid.chain, edge] using
          ih parent (g.point current :: acc) (current :: seen) (preserves current parent edge holds)
            (List.nodup_cons.mpr ⟨fresh, unique⟩) nextKeys nextAbove nextBudget
  apply walk (prev.size + 1) v [] [] initial List.nodup_nil (List.nil_subset _)
  · intro _ h
    cases h
  · exact Nat.lt_succ_self _

/-- A strictly decreasing predecessor map reaches a root with the fuel used by `Grid.shortest`. -/
theorem Grid.chain_head_root_of_rank (g : Grid) (prev : Std.HashMap Vertex Vertex)
    (v : Vertex) (rank : Vertex → Nat)
    (decreases : ∀ (u p : Vertex), prev[u]? = some p → rank p < rank u) :
    ∃ root, prev[root]? = none ∧
      (g.chain prev (prev.size + 1) v []).head? = some (g.point root) := by
  obtain ⟨root, hprev, _, hhead⟩ :=
    g.chain_head_root_of_rank_preserving prev v rank (fun _ => True)
      decreases True.intro (fun _ _ _ h => h)
  exact ⟨root, hprev, hhead⟩

end Elegant.Layered.Visibility

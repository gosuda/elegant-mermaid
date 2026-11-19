import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.ParentContainmentFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RouteImpl

/-! ### Bottom frame clearance, step one: the constraint edge of a member-less, child-less group

`Compound.constraints` pairs every group's top marker with its bottom marker. For a group with
neither plain members nor nested groups it emits the single direct edge `top -> bottom`; this is
the leaf case of every nesting argument about frame clearance. -/

theorem compound_empty_group_constraint_edge {graph : Graph}
    {top bottom : Node × Nat}
    (htop : top ∈ graph.nodes.zipIdx) (hgroup : top.1.border = -2)
    (hbottom : (graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == top.1.decl) = some bottom)
    (hmembers : (graph.nodes.zipIdx.filter fun entry =>
      entry.1.border == 0 && entry.1.clusterPath.contains top.1.decl).isEmpty = true)
    (hchildren : ((graph.nodes.zipIdx.filter fun entry =>
      entry.1.border == -2).filter fun entry =>
        entry.1.clusterPath.dropLast == top.1.clusterPath).isEmpty = true) :
    (⟨top.2, bottom.2, 1, 0, false⟩ : Edge) ∈ Compound.constraints graph := by
  unfold Compound.constraints
  apply List.mem_flatMap.mpr
  refine ⟨top, List.mem_filter.mpr ⟨htop, by simp [hgroup]⟩, ?_⟩
  rw [hbottom]
  dsimp only
  split
  · exact List.mem_singleton.mpr rfl
  · rename_i hnonempty
    rw [hmembers, hchildren] at hnonempty
    simp at hnonempty

/-- The empty-group edge in ranked form: the bottom marker ranks strictly below the top marker of
the same group. -/
theorem ranked_empty_group_interval {graph : Graph} {rr : RankImpl.RankResult}
    (hrank : rankWithBudget (Compound.rankingGraph graph) = .ok rr)
    {top bottom : Node × Nat}
    (htop : top ∈ graph.nodes.zipIdx) (hgroup : top.1.border = -2)
    (hbottom : (graph.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == top.1.decl) = some bottom)
    (hmembers : (graph.nodes.zipIdx.filter fun entry =>
      entry.1.border == 0 && entry.1.clusterPath.contains top.1.decl).isEmpty = true)
    (hchildren : ((graph.nodes.zipIdx.filter fun entry =>
      entry.1.border == -2).filter fun entry =>
        entry.1.clusterPath.dropLast == top.1.clusterPath).isEmpty = true) :
    rk rr.ranks top.2 + 1 ≤ rk rr.ranks bottom.2 := by
  have hfeasible := rankingGraph_constraint_feasible hrank
    (compound_empty_group_constraint_edge htop hgroup hbottom hmembers hchildren)
  dsimp only at hfeasible
  omega

end Elegant.Layered.PipelineImpl

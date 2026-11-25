import Elegant.Layered.ForeignBorderAnchorsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Every candidate group title has its paired bottom marker in the same
candidate: the executed `componentRun` exposes, through the titled proper
graph, a path-matched `border = 2` bottom for the title, and the titled
bottom record transfers back to a candidate node with the same declaration
(by the candidate path/decl lookup congruence) and the same cluster path. -/
theorem foreignBottomInCandidate : ForeignBottomInCandidate := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions
    hrun u uNode hu hbU
  obtain ⟨_, _, bottomP, _, _, hk, _, hrecords, _, _, hfind⟩ :=
    componentRun_group_bottom_source hgraph hcomp hrun hu hbU
  obtain ⟨original, horiginal, hborder, hpath, _, hsourceFind⟩ :=
    candidate_titled_bottom_constraint_source hgraph hk hrecords hu hbU hfind
  have hpred := List.find?_some hsourceFind
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  exact ⟨bottomP.2, original, horiginal, hborder, hpred.2, hpath⟩

/-- The title-level anchor lookups, with the bottom colocation discharged. -/
theorem foreignRankPairAnchors' : ForeignRankPairAnchors :=
  foreignRankPairAnchors foreignBottomInCandidate

end Elegant.Layered.PipelineImpl

import Elegant.Layered.GroupTopFacts
import Elegant.Layered.GroupTopRank

/-!
# Group attachment from the rank seam

`GroupAttachMeasured` (`GroupRouteAttachment.lean`) is the true, measured form
of the group-endpoint attachment fact.  It follows from
`GroupTopEndpointFactsCandidate`, which `groupTopEndpointFactsCandidate`
(`GroupTopFacts.lean`) proves from one open seam: the executed rank closure
`GroupTopSubtreeRankProper` (`GroupTopRank.lean`).
-/

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The candidate-graph endpoint facts from the executed rank closure. -/
theorem groupTopEndpointFactsCandidate_of_rank
    (hrank : GroupTopSubtreeRankProper) : GroupTopEndpointFactsCandidate := by
  intro P inp o lines graph hgraph hlines hwf hfp comp hcomp candidate run labels
    orderOptions hrun v hcb
  have hvcg : v < (componentCandidate graph comp candidate).nodes.length := by
    apply Classical.byContradiction
    intro hge
    have hnone : (componentCandidate graph comp candidate).nodes[v]? = none :=
      List.getElem?_eq_none (by omega)
    have hdefault : (default : Node).border = 0 := rfl
    rw [List.getD_eq_getElem?_getD, hnone] at hcb
    simp only [Option.getD_none] at hcb
    omega
  have hnode : (componentCandidate graph comp candidate).nodes[v]? =
      some ((componentCandidate graph comp candidate).nodes.getD v default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvcg]
    rfl
  exact groupTopEndpointFactsCandidate hgraph hrun hcb
    (fun hi hin => hrank hgraph hlines hwf hfp hcomp hrun hnode hcb hvcg hi hin)

/-- The measured group-endpoint attachment fact from the executed rank closure. -/
theorem groupAttachMeasured_of_rank
    (hrank : GroupTopSubtreeRankProper) : GroupAttachMeasured :=
  groupAttachMeasured_of_candidate_facts (groupTopEndpointFactsCandidate_of_rank hrank)

end Elegant.Layered.PipelineImpl

import Elegant.Layered.BottomClearanceNesting
import Elegant.Layered.BottomSeamsRank

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! ### Executed rank closure for group top proxies

This unit names the two rank facts `GroupTopEndpointFactsCandidate` needs.
Both are OPEN seams.  The executed form: every proper node whose cluster path
contains a candidate `-2` group's declaration ranks at or below that group's
top proxy.  The cg-level form is the corresponding ranking-graph closure over
the candidate graph; dummies materialized by
`componentRun_dummy_path_chain_source` inherit the common path of their chain
endpoints, so their `clusterPath.contains` membership is witnessed at the
ranking graph before transport.

Intended proof of the cg-level form: strong induction like
`componentRun_group_top_lt_bottom` (`BottomClearanceNesting.lean`), by cases on
the border of the contained node: `0` through `ranked_compound_member_interval`,
`-2` through `ranked_compound_child_interval`, and `2` through
`componentRun_group_top_lt_bottom` (`GroupWidthFacts.lean`).  The executed form
follows by the rank-record transport `rankSource_of_componentRun`
(`BottomSeamsRank.lean`). -/

/-- Open seam, executed rank closure for a `-2` group top: every executed node
whose cluster path contains the top's declaration ranks at or below the top
proxy. -/
def GroupTopSubtreeRankProper : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {v : Nat} {nd : Node},
    (componentCandidate graph comp candidate).nodes[v]? = some nd →
    nd.border = -2 →
    v < (componentCandidate graph comp candidate).nodes.length →
    ∀ {i : Nat}, i < run.proper.nodes.length →
    (run.proper.nodes.getD i default).node.clusterPath.contains nd.decl = true →
    rk run.proper.rank v ≤ rk run.proper.rank i

/-- Open seam, cg-level rank closure for a `-2` group top: every candidate graph
node whose cluster path contains the top's declaration ranks at or below the
top. -/
def GroupTopSubtreeRankCg : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {v : Nat} {nd : Node},
    (componentCandidate graph comp candidate).nodes[v]? = some nd →
    nd.border = -2 →
    ∃ rr : RankImpl.RankResult,
      rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
        .ok rr ∧
      ∀ j : Nat, j < (componentCandidate graph comp candidate).nodes.length →
        ((componentCandidate graph comp candidate).nodes.getD j default).clusterPath.contains
          nd.decl = true →
        rk rr.ranks v ≤ rk rr.ranks j

end Elegant.Layered.PipelineImpl

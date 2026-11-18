import Elegant.Layered.BottomClearanceInside
import Elegant.Layered.GroupWidthFacts

/-!
Rank seams of `bracket_inside_rank_below_bottom`
(`BottomClearanceInside.bracket_inside_rank_below_bottom`).

This unit holds the shared rank transport for the rank seams of
`bracket_inside_rank_below_bottom`
(`BottomClearanceInside.bracket_inside_rank_below_bottom`):

* `plainMemberRankLtProxy` is PROVED (`BracketInsideRankFacts.lean`, via
  this transport plus `ranked_compound_member_interval` and
  `componentRun_cg_top_of_bottom`).
* `dummyInsideSameRankFalse` is REFUTED (a label dummy can share a bottom
  proxy's rank; witness probe `wip/Layered/DummySameRankRefuted.lean`) and
  is restated as the geometric `dummyInsideProxyRowClear`, which stays an
  open premise of `BracketInsidePremises`.
* `insidePrefixHypothesis`: inside the bracket of a group every non-dummy
  layer node has the group's cluster path as a prefix of its node path
  (layer contiguity plus `OrderImpl.BordersWellFormed`) — open.

The remaining open seams ride the executed transports landed in
`GroupWidthFacts` (`componentRun_ranked_node_records`,
`ranked_compound_member_interval`, `componentRun_titled_border_ready`, the
coordinate-graph border order well-formedness chain), the order contiguity
theorem `OrderImpl.order_clusters_contiguous`, and `rankSource_of_componentRun`
below.
-/

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RouteImpl

/-! ### Shared transports -/

/-- A successful component run exposes the ranking result, the labeled proper
graph (whose `coordinateGraph` image is the run's coordinate graph) and the
rank-record transfer from the ranking to the coordinate graph. -/
theorem rankSource_of_componentRun {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper),
      rankWithBudget
        (Compound.rankingGraph (componentCandidate graph comp candidate)) =
        .ok rr ∧
      coordinateGraph P labeled = run.coordinateProper ∧
      NodeKeys (componentCandidate graph comp candidate) labeled ∧
      (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
        labeled.rank[index]? = some rank) ∧
      (∀ (index : Nat) (node : Node),
        (componentCandidate graph comp candidate).nodes[index]? = some node →
          labeled.nodes[index]? = some ⟨node, false, none, false⟩) ∧
      (∀ (index : Nat) (node : Node),
        (componentCandidate graph comp candidate).nodes[index]? = some node →
          (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
            (node.border = -2 → node.clusterPath ≠ [])) :=
  by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks⟩ :=
    componentRun_prepared_titled_source hgraph hcomp hrun
  exact ⟨rr, labeled, hrr, hc, hk, hranks, hrecords,
    fun index node hnode => componentCandidate_marker_shape hgraph hnode⟩
end Elegant.Layered.PipelineImpl

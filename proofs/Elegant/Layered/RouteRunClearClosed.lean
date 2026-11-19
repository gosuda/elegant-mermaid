import Elegant.Layered.RouteRunClearCases
import Elegant.Layered.RouteLabelForeignClearProof
import Elegant.Layered.RouteLabelDummyCellProof
import Elegant.Layered.RouteNonforwardLabelClearProof
import Elegant.Layered.RouteLabelLeftoverPairProof
import Elegant.Layered.StrictDummyFrameProof
import Elegant.Layered.ForeignMemberRankBoundsProof
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.PartFrameCoresProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Closed route-label clearance for one executed component run

`route_run_clear_closed` discharges `route_run_clear_executed`
(`RouteRunClearCases.lean`) to the two still-open per-run residuals. Of the
three span seams, only `ForeignBorderChainXAligned` stays open: the other two
are proved facts (`foreignClusterRankSpans'` from
`ForeignMemberRankBoundsProof.lean`, `bracketMarkersAtRank'` from
`SideMarkerTopInCandidateProof.lean`). The loop-footprint facts are taken
exactly as `routeNonforwardLabelClear_of_run` states them
(`RunLocalLoopFootprint`, `LoopFootprintTopSeparationG`,
`LoopFootprintBeyondProperG`); the two per-run residuals are
`LoopFootprintGroupHullClear` (another worker) and `DummyMarkerBracket`
(another worker). `routeRunClear_closed` restates the conclusion in the
`RouteRunClear` form the part-level consumer uses. -/

theorem route_run_clear_closed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hxalign : ForeignBorderChainXAligned)
    (hfoot : RunLocalLoopFootprint inp o res)
    (htop : LoopFootprintTopSeparationG inp o res)
    (hbeyond : LoopFootprintBeyondProperG inp o res)
    (hres : LoopFootprintGroupHullClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured)
    (hbracket : DummyMarkerBracket
      (componentCandidate execution.graph comp candidate) run) :
    RouteRunClearInlined execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  have hrank : ForeignClusterRankSpans := foreignClusterRankSpans'
  have hbr : BracketMarkersAtRank := bracketMarkersAtRank'
  have hcell :=
    routeLabelDummyCellForeignClear_of_run execution hwf hframed hcomp hrun hbr hrank hxalign
  have hforeign :=
    routeLabelForeignClear_of_run execution hwf hframed hcomp hrun hbr hrank hxalign hcell
  have hloop :=
    routeNonforwardLabelClear_of_run execution hcomp hrun hfoot htop hbeyond hres
  have hstrict := strictDummyFrame_of_run execution hwf hframed hcomp hrun hbracket
  have hleftover :=
    routeLabelLeftoverPair_of_run execution hwf hframed hcomp hrun hstrict hbr hrank hxalign
      hforeign hloop
  exact route_run_clear_executed execution hwf hframed hcomp hrun hstrict hbr hrank hxalign
    hforeign hloop hleftover hfoot

/-- Bridge to the part-level consumer form: `RouteRunClear` differs from
`RouteRunClearInlined` only in how the frame position is quantified (an
equation `frameRect P cg run pos = g0` instead of the direct term), so the
bridge is a rewrite. -/
theorem routeRunClear_of_inlined {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel}
    (h : RouteRunClearInlined P cg run labels) :
    RouteRunClear P cg run labels := by
  intro k rect hmem pos g0 hpos heq
  rw [← heq]
  exact h k rect hmem pos hpos

theorem routeRunClear_closed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hxalign : ForeignBorderChainXAligned)
    (hfoot : RunLocalLoopFootprint inp o res)
    (htop : LoopFootprintTopSeparationG inp o res)
    (hbeyond : LoopFootprintBeyondProperG inp o res)
    (hres : LoopFootprintGroupHullClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured)
    (hbracket : DummyMarkerBracket
      (componentCandidate execution.graph comp candidate) run) :
    RouteRunClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured :=
  routeRunClear_of_inlined (route_run_clear_closed execution hwf hframed hcomp hrun hxalign
    hfoot htop hbeyond hres hbracket)

end Elegant.Layered.PipelineImpl

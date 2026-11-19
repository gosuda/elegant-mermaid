import Elegant.Layered.FlatC6ClosedProof
import Elegant.Layered.PartPositiveContentProof
import Elegant.Layered.LoopHullCoverProof
import Elegant.Layered.LoopFootprintTopSeparationCondProof
import Elegant.Layered.LoopResGroupHullRightProof
import Elegant.Layered.LoopResNeighborGapGroupProof
import Elegant.Layered.LoopTopSliverGapProof
import Elegant.Layered.LoopResNeighborDisjointProof
import Elegant.Layered.LoopResNeighborGapOffRankProof
import Elegant.Layered.LoopResNeighborGapGroupTopWitnessProof
import Elegant.Layered.ForeignBorderChainXAlignedClosed
import Elegant.Layered.ForeignBorderAnchorsProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Witness-free `flatC6_closed`: replays `flatC6_closed` with
`partPositiveContent_holds` (no `PartFrameWitness` premise). -/
theorem flatC6_closed_nowit
    (htop : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LoopRectTopReal inp o res)
    (hfix : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LoopRectFixedReal inp o res)
    (htitle : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LoopRectTitleReal inp o res)
    (hbot : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LoopRectBottomReal inp o res)
    (hrange : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LoopRectRangeDegReal inp o res)
    (hftop : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LoopFootprintTopSeparation inp o res)
    (hfbeyond : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LoopFootprintBeyondProper inp o res) :
    FlatC6 := by
  intro inp o res hwf hframed hclear hlay
  have hkeys : ProperChainEndpointKeys inp o res :=
    properChainEndpointKeys' inp o res hwf hframed
  have hcontent : PartPositiveContent inp o res :=
    partPositiveContent_holds (inp := inp) (o := o) (res := res) hwf hframed
  have hnd := properDeclPreserved (inp := inp) (o := o) (res := res)
  have hsc := runRouteEndpointIdsScoped_of_keys (inp := inp) (o := o) (res := res) hnd hkeys
  have hdecl := exclusiveRunNodeDecl_of_preserved (inp := inp) (o := o) (res := res) hnd
  have hpa := exclusiveDeclOutsideEndpointPaths_of_clusterPath (inp := inp) (o := o) (res := res)
    (measuredGraphClusterPathOfPlainNode (inp := inp) (o := o) (res := res) hwf hframed)
    (exclusiveRunNodeDecl_of_preserved (inp := inp) (o := o) (res := res) hnd)
    (runClusterPathGroupMembers (inp := inp) (o := o) (res := res) hwf hframed)
  have hpo := routePartShelfPositive_of_content (inp := inp) (o := o) (res := res) hcontent
  have hlr : ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
      (run : Run) (v : Nat),
      comp ∈ components e.graph →
      componentRun e.params
        (componentCandidate e.graph comp candidate) e.measured
        (candidateOrder candidate) = .ok run →
      LoopReservation (componentCandidate e.graph comp candidate) run e.measured v :=
    fun e comp candidate run v hcomp hrun =>
      loopReservation_executed e comp candidate run v hcomp hrun
  have hls : ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
      (run : Run) (v b : Nat),
      comp ∈ components e.graph →
      ((componentCandidate e.graph comp candidate).nodes.getD b default).border = 0 →
      componentRun e.params
        (componentCandidate e.graph comp candidate) e.measured
        (candidateOrder candidate) = .ok run →
      LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
        e.measured v b :=
    fun e comp candidate run v b hcomp hbord hrun =>
      loopFootprintSeparation_executed e comp candidate run v b hcomp hbord hrun
        (loopFootprintSeparationResidual (hftop inp o res hwf hframed)
          (hfbeyond inp o res hwf hframed))
  have hbordReal : LoopForeignBoxBorderZeroReal inp o res := by
    intro execution candidate run packed hpack c q hselected area loops hpart hcomp hrun
      v b hreal hbmem hexcl hrect
    exact loopForeignBoxBorderZeroRealQ
      (execution := execution) (candidate := candidate) (run := run)
      (packed := packed) (hpack := hpack) (c := c) (q := q)
      (hselected := hselected) (area := area) (loops := loops)
      (hpart := hpart) (hcomp := hcomp) (hrun := hrun)
      (v := v) (b := b)
      (htop inp o res hwf hframed) (hfix inp o res hwf hframed)
      (htitle inp o res hwf hframed) (hbot inp o res hwf hframed)
      (hrange inp o res hwf hframed)
      hreal hbmem hexcl hrect
  obtain ⟨execution⟩ := layout_sceneExecution hlay
  have hbridge : RouteScopeBridge inp o res :=
    routeScopeBridge hwf hframed execution hpa
  exact layout_c6 (flatC6ChainCase hwf hframed hdecl hsc hpa hpo)
    (flatC6LoopCase hpo hbordReal) hclear hbridge hlr hls hlay

/-- Right hull cover from the narrow ordered-marker witness (`emptyNested`
true: looping group with no plain descendant still orders its markers). -/
theorem hullCover_of_witness {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned) (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hord : LoopResGroupHullRightWitness
      (componentCandidate execution.graph comp candidate) run) :
    LoopHullRightCover execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured :=
  loopHullRightCover_closed hwf hfp hx execution hcomp hrun hord

/-- Closed beyond-proper footprint seam for one input:
`loopFootprintBeyondProper_closed` (`LoopTopSliverGapProof.lean`) over the
closed alignment (`foreignBorderChainXAligned'` of the ordering-stage
stability residual) and the marker readiness derived from the proved span
(`topSliverMarkerReady_of_span` of `topSliverSpanCovered_holds`). Replaces
the old `LayeredSeams.loopFootprintBeyondProper` field. -/
theorem beyondProper_closed (hstab : ForeignBorderDivergeStable)
    (inp : Input) (o : Options) (res : FamilyResult)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true) :
    LoopFootprintBeyondProper inp o res :=
  loopFootprintBeyondProper_closed inp o res hwf hfp
    (foreignBorderChainXAligned' hstab)
    (topSliverMarkerReady_of_span hwf hfp topSliverSpanCovered_holds)

/-- Bottom-owner disjoint gap on executed runs: the `x`-gap disjunct of
`LoopResNeighborGapBottomOwnerDisj` is the proved vacuous
`loopResNeighborGapBottomOwner_holds` (`LoopResNeighborGapGroupProof.lean`).
Needs no seam field. -/
theorem neighborGapBottomOwnerDisj_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    LoopResNeighborGapBottomOwnerDisj execution.params
      (componentCandidate execution.graph comp candidate) run
      execution.measured := by
  intro t nt hnt htB het pos np hnp hgrpB hne hne2 hni1 hni2 hFL
  exact Or.inl (loopResNeighborGapBottomOwner_holds execution hcomp hrun
    t nt hnt htB het pos np hnp hgrpB hne hne2 hni1 hni2 hFL)
/-- Shared-rank group-top witness on executed runs:
`loopResNeighborGapGroupTopWitnessShared_holds`
(`LoopResNeighborGapGroupTopWitnessProof.lean`) over the closed layer order
(`foreignBorderLayerOrder'`). Discharges the witness premise of
`loopResNeighborGapGroupTopShared_holds` below. -/
theorem groupTopSharedWitness_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (_hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    LoopResNeighborGapGroupTopWitnessShared execution hcomp hrun :=
  loopResNeighborGapGroupTopWitnessShared_holds hwf hfp _hx
    foreignBorderLayerOrder' execution hcomp hrun

/-- Shared-rank instances of the group-top disjoint residual:
`loopResNeighborGapGroupTopShared_holds` over the closed shared witness
above; the `x`-gap gives the first disjunct of
`LoopResNeighborGapGroupTopDisj`. This is the proved discharge path for
shared-rank pairs of the `loopNeighborGapGroupTopDisj` seam residual. -/
theorem groupTopDisj_of_shared {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htG : nt.border = -2)
    (het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrp : np.border = -2)
    (hne : pos ≠ t) (hne2 : nt.decl ≠ np.decl)
    (hni1 : np.decl ∉ nt.clusterPath) (hni2 : nt.decl ∉ np.clusterPath)
    (hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x)
    (hShared : ∃ (a b : Nat) (na nb : ProperNode),
      run.proper.nodes[a]? = some na ∧
      na.node.clusterPath.contains nt.decl = true ∧
      run.proper.nodes[b]? = some nb ∧
      nb.node.clusterPath.contains np.decl = true ∧
      rk run.proper.rank a = rk run.proper.rank b) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).x +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x ∨
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).h ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y ∨
    (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).y +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).h ≤
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).y :=
  Or.inl (loopResNeighborGapGroupTopShared_holds hwf hfp hx execution hcomp hrun
    (groupTopSharedWitness_holds hwf hfp hx execution hcomp hrun)
    hnt htG het hnp hgrp hne hne2 hni1 hni2 hFL hShared)

/-- Executed foreign-hull right-neighbor cover from the disjoint residuals:
`loopResNeighborGapDisj_holds` (`LoopResNeighborDisjointProof.lean`) over the
parent-chain seam residual, the group-top disjoint seam residual, and the
proved bottom-owner disjoint gap, fed to
`loopHullRightNeighborCover_Disj_holds`. Replaces `r3_of_narrow` (which
needed the false `LoopResNeighborGapOffRank` `x`-gap). -/
theorem neighborCover_of_disjoint {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hchain : LoopResOffRankParentChain)
    (hgrp : LoopResNeighborGapGroupTopDisj execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured)
    (hbot : LoopResNeighborGapBottomOwnerDisj execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured) :
    LoopHullRightNeighborCover execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured :=
  loopHullRightNeighborCover_Disj_holds hwf hfp execution hcomp hrun
    (fun _t _nt hnt het _pos _np hnp hgrpB hne hne2 hni1 hni2 hFL =>
      loopResNeighborGapDisj_holds hwf hfp hx execution hcomp hrun hchain hgrp hbot
        hnt het hnp hgrpB hne hne2 hni1 hni2 hFL)
end PipelineImpl
end Layered
end Elegant

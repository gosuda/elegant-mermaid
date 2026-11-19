import Elegant.Layered.FlatC6ClosedProof
import Elegant.Layered.PartPositiveContentProof
import Elegant.Layered.LoopHullCoverProof
import Elegant.Layered.LoopFootprintTopSeparationCondProof
import Elegant.Layered.LoopResGroupHullRightProof
import Elegant.Layered.LoopResNeighborGapGroupProof
import Elegant.Layered.LoopResNeighborGapProof

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

/-- `R3ExtentFitGap` from the off-rank case and the group-top witness. -/
theorem r3_of_narrow {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hx : ForeignBorderChainXAligned) (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hoff : LoopResNeighborGapOffRank execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured)
    (hwit : LoopResNeighborGapGroupTopWitness execution.params
      (componentCandidate execution.graph comp candidate) run) :
    R3ExtentFitGap execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  intro t nt hnt het pos np hnp hgrpB hne hne2 hni1 hni2 hFL
  exact loopResNeighborGap_holds hwf hfp hx execution hcomp hrun hoff
    (loopResNeighborGapGroupTop_holds hwf hfp hx execution hcomp hrun hwit)
    (loopResNeighborGapBottomOwner_holds execution hcomp hrun)
    hnt het hnp hgrpB hne hne2 hni1 hni2 hFL

end PipelineImpl
end Layered
end Elegant

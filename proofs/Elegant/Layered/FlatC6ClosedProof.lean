import Elegant.Layered.FlatC6Assembly
import Elegant.Layered.RunStageNodeFacts
import Elegant.Layered.FlatC6ScopeResidualsProof
import Elegant.Layered.FlatC6ScopeBridgeProof
import Elegant.Layered.FlatC6LoopProof
import Elegant.Layered.LoopBoxBorderZeroProof
import Elegant.Layered.LoopFootprintFactsProof
import Elegant.Layered.LoopFootprintResidualProof
import Elegant.Layered.LoopRectPlainSourceProof
import Elegant.Layered.RunStageChainKeys
import Elegant.Layered.RunStageChainKeysResiduals
import Elegant.Layered.RecursiveC6

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Flat clause 6 from the narrow residuals.

Each hypothesis is quantified the way `FlatC6` needs: for all `inp o res`
under the well-formed and framed premises. The id/shelf residuals of
`layout_c6` close through the proved reductions (`properDeclPreserved`,
`runClusterPathGroupMembers`, `measuredGraphClusterPathOfPlainNode`,
`runRouteEndpointIdsScoped_of_keys`, `routePartShelfPositive_of_content`),
the loop case closes through `flatC6LoopCase` with the real-`q` border fact
(`loopForeignBoxBorderZeroRealQ` from the five `LoopRect*Real` residuals)
and the executed loop footprint facts
(`loopFootprintSeparationResidual` from `LoopFootprintTopSeparation` and
`LoopFootprintBeyondProper`), and the `FrameClearanceSeam` premise of
`FlatC6` stays a premise.
None of the four old broad hypotheses (`ProperChainEndpointKeys`,
`PartPositiveContent`, `LoopRectPlainSource`,
`LoopFootprintSeparationResidual`) appears, nor the intermediate narrow
ones (`AliasDeclTransport`, `FrameRectPositive`, plain-node existence):
`ProperChainEndpointKeys` closes outright via `properChainEndpointKeys'`,
and `PartPositiveContent` closes via `partPositiveContent'` from the single
`PartFrameWitness` hypothesis. -/
theorem flatC6_closed
    (hwit : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      PartFrameWitness inp o res)
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
    partPositiveContent' inp o res hwf hframed (hwit inp o res hwf hframed)
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

end PipelineImpl
end Layered
end Elegant

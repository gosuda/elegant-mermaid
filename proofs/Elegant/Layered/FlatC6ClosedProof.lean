import Elegant.Layered.FlatC6SeamProof
import Elegant.Layered.RunStageNodeFacts
import Elegant.Layered.FlatC6ScopeResidualsProof
import Elegant.Layered.FlatC6ScopeBridgeProof
import Elegant.Layered.FlatC6LoopProof
import Elegant.Layered.LoopBoxBorderZeroProof
import Elegant.Layered.LoopFootprintFactsProof
import Elegant.Layered.RecursiveC6

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Flat clause 6 from the smallest remaining set of named residuals.

Each hypothesis is quantified the way `FlatC6` needs: for all `inp o res`
under the well-formed and framed premises. The id/shelf residuals of
`flatC6_of_residuals` close through the proved reductions
(`properDeclPreserved`, `runClusterPathGroupMembers`,
`measuredGraphClusterPathOfPlainNode`, `runRouteEndpointIdsScoped_of_keys`,
`routePartShelfPositive_of_content`), the loop case closes through
`flatC6LoopCase` with `loopForeignBoxBorderZero` and the executed loop
footprint facts, and the `FrameClearanceSeam` premise of `FlatC6` stays a
premise: it is independently closable via `frameClearanceSeam_holds` applied
to `bracketInsidePremises` over `dummyInsideProxyRowClear_executed'` and
`titleCopySpanClearStrict_executed`.

`ProperChainEndpointKeys` and `PartPositiveContent` stay hypotheses for now:
`properChainEndpointKeys` (needs only `AliasDeclTransport`) and
`partPositiveContent` (needs only `FrameRectPositive` plus the plain-node
existence premise) exist with fitting signatures, but their home module
`RunStageChainKeys` does not compile at this writing, so they cannot be
referenced yet. Tightening is mechanical once it builds; see the report. -/
theorem flatC6_closed
    (hkeys : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ProperChainEndpointKeys inp o res)
    (hcontent : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      PartPositiveContent inp o res)
    (hlink : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LoopRectPlainSource inp o res)
    (hres : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      LoopFootprintSeparationResidual inp o res) :
    FlatC6 :=
  flatC6_of_residuals
    (fun inp o res _hwf _hframed _hlay =>
      exclusiveRunNodeDecl_of_preserved (inp := inp) (o := o) (res := res)
        (properDeclPreserved (inp := inp) (o := o) (res := res)))
    (fun inp o res hwf hframed _hlay =>
      runRouteEndpointIdsScoped_of_keys (inp := inp) (o := o) (res := res)
        (properDeclPreserved (inp := inp) (o := o) (res := res))
        (hkeys inp o res hwf hframed))
    (fun inp o res hwf hframed _hlay =>
      exclusiveDeclOutsideEndpointPaths_of_clusterPath (inp := inp) (o := o) (res := res)
        (measuredGraphClusterPathOfPlainNode (inp := inp) (o := o) (res := res)
          hwf hframed)
        (exclusiveRunNodeDecl_of_preserved (inp := inp) (o := o) (res := res)
          (properDeclPreserved (inp := inp) (o := o) (res := res)))
        (runClusterPathGroupMembers (inp := inp) (o := o) (res := res) hwf hframed))
    (fun inp o res hwf hframed _hlay =>
      routePartShelfPositive_of_content (inp := inp) (o := o) (res := res)
        (hcontent inp o res hwf hframed))
    (fun _ _ _ _ _ _ e comp candidate run v hcomp hrun =>
      loopReservation_executed e comp candidate run v hcomp hrun)
    (fun inp o res hwf hframed _hlay e comp candidate run v b hcomp hbord hrun =>
      loopFootprintSeparation_executed e comp candidate run v b hcomp hbord hrun
        (hres inp o res hwf hframed))
    (fun inp o res hwf hframed hlay =>
      loopForeignBoxBorderZero (inp := inp) (o := o) (res := res)
        hwf hframed hlay (hlink inp o res hwf hframed))

end PipelineImpl
end Layered
end Elegant

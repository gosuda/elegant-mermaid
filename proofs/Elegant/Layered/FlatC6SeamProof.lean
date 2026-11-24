import Elegant.Layered.FlatC6Assembly
import Elegant.Layered.FlatC6ScopeBridgeProof
import Elegant.Layered.FlatC6LoopProof
import Elegant.Layered.RecursiveC6

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Flat clause 6 assembled from its residuals

`flatC6_of_residuals` closes `FlatC6` from the seven executed residuals the two
transport cases consume: the four id/shelf residuals discharged in
`FlatC6ScopeBridgeProof` (`ExclusiveRunNodeDecl`, `RunRouteEndpointIdsScoped`,
`ExclusiveDeclOutsideEndpointPaths`, `RoutePartShelfPositive`), the two
loop-side facts (`LoopReservation`, `LoopFootprintSeparation`) stated per
executed run of a reported component, and the real-part loop-box border
fact (`LoopForeignBoxBorderZeroReal`) the loop case consumes. Each hypothesis
is guarded by the
`WellFormed`, `framedParents`, and `layout = .ok` facts available at its use
site, so every hypothesis is as weak as this proof allows. No new residual is
introduced: the component-membership side condition rides on the existing
`actual_components_parts_geometry` coverage the transport proofs already use.
-/

/-- Flat clause 6 from its residuals: the chain case, the loop case, and the
route scope bridge discharge `layout_c6`, whose conclusion is `FlatC6`. -/
theorem flatC6_of_residuals
    (hnodeDecl : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layout inp o = .ok res → ExclusiveRunNodeDecl inp o res)
    (hscoped : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layout inp o = .ok res → RunRouteEndpointIdsScoped inp o res)
    (hpaths : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layout inp o = .ok res → ExclusiveDeclOutsideEndpointPaths inp o res)
    (hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layout inp o = .ok res → RoutePartShelfPositive inp o res)
    (hloopRes : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layout inp o = .ok res →
      ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
        (run : Run) (v : Nat),
        comp ∈ components e.graph →
        componentRun e.params
          (componentCandidate e.graph comp candidate) e.measured
          (candidateOrder candidate) = .ok run →
        LoopReservation (componentCandidate e.graph comp candidate) run e.measured v)
    (hloopSep : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layout inp o = .ok res →
      ∀ (e : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
        (run : Run) (v b : Nat),
        comp ∈ components e.graph →
        ((componentCandidate e.graph comp candidate).nodes.getD b default).border = 0 →
        componentRun e.params
          (componentCandidate e.graph comp candidate) e.measured
          (candidateOrder candidate) = .ok run →
        LoopFootprintSeparation (componentCandidate e.graph comp candidate) run
          e.measured v b)
    (hbord : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layout inp o = .ok res → LoopForeignBoxBorderZeroReal inp o res) :
    FlatC6 := by
  intro inp o res hwf hframed hclear hlay
  have hnd := hnodeDecl inp o res hwf hframed hlay
  have hsc := hscoped inp o res hwf hframed hlay
  have hpa := hpaths inp o res hwf hframed hlay
  have hpo := hpos inp o res hwf hframed hlay
  have hlr := hloopRes inp o res hwf hframed hlay
  have hls := hloopSep inp o res hwf hframed hlay
  have hbo := hbord inp o res hwf hframed hlay
  obtain ⟨execution⟩ := layout_sceneExecution hlay
  have hbridge : RouteScopeBridge inp o res :=
    routeScopeBridge hwf hframed execution hpa
  exact layout_c6 (flatC6ChainCase hwf hframed hnd hsc hpa hpo)
    (flatC6LoopCase hpo hbo) hclear hbridge hlr hls hlay

end PipelineImpl
end Layered
end Elegant

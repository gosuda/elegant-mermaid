import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.RouteScopeClearance
import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.Pack
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Layered
/-- Frame-clearance premise the parent discharges per component run. -/
def FrameClearRuns (_inp : Input) (_o : Options) (P : PipelineImpl.Params)
    (_lines : List (List Measure.Line)) (measured : List PipelineImpl.MeasuredLabel)
    (graph : Graph) : Prop :=
  ∀ {comp : List Nat} {candidate : Nat} {run : PipelineImpl.Run}
    {orderOptions : OrderOptions},
    comp ∈ PipelineImpl.components graph →
    PipelineImpl.componentRun P
      (PipelineImpl.componentCandidate graph comp candidate) measured orderOptions = .ok run →
    PipelineImpl.FrameClearance run.proper run.layers run.xs


end Elegant.Layered

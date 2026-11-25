import Elegant.Layered.RegionFallbackFitProof
import Elegant.Layered.RegionFoundation
import Elegant.Layered.RegionReduction
import Elegant.Layered.ExactAncestorFrameStrictClosedProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private def exactExecutionOfEmptyRegions {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionR exactIds [] inp o res) :
    SceneExecutionX exactIds inp o res where
  params := execution.params
  metric := execution.metric
  lines := execution.lines
  measured := execution.measured
  graph0 := execution.graph0
  graph := execution.graph
  componentsAcc := execution.componentsAcc
  packedAcc := execution.packedAcc
  checked := execution.checked
  metric_eq := execution.metric_eq
  lines_eq := execution.lines_eq
  measured_eq := execution.measured_eq
  graph0_eq := execution.graph0_eq
  graph_eq := execution.graph_eq
  components_eq := by
    have hnone : (components execution.graph).foldlM
        (fun acc comp => layoutComponentR execution.params exactIds none inp o
          execution.graph acc comp execution.measured)
        ⟨0, 0, 0, Array.replicate inp.boxes.length default,
          Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
          false, [], []⟩ = .ok execution.componentsAcc := execution.components_eq
    simpa only [layoutComponentR_none] using hnone
  packed_eq := execution.packed_eq
  scene_eq := execution.scene_eq

/-- On an empty region set, the ancestor walk is the one from the exact execution. -/
theorem R_ancestorFrameStrictW_none (exactIds : List String) :
    R_AncestorFrameStrictW exactIds [] := by
  intro inp o res execution hwf hfp
  exact X_ancestorFrameStrictW_closed exactIds (exactExecutionOfEmptyRegions execution) hwf hfp

theorem R_ownerFrameDisjointW_none (exactIds : List String) :
    R_OwnerFrameDisjointW exactIds [] :=
  R_ownerFrameDisjointW_holds exactIds []

theorem R_fallbackCaptionClearB8W_none (exactIds : List String) :
    R_FallbackCaptionClearBW exactIds [] :=
  R_fallbackCaptionClearB8W_holds exactIds [] (R_ancestorFrameStrictW_none exactIds)

end Elegant.Layered.PipelineImpl

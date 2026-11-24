import Elegant.Layered.ExactGroupLoopFixedLeafGapProof
import Elegant.Layered.ExactNonSelfFixedLeafMissProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

theorem exactFlatFixedLeafMiss_holds (exactIds : List String) :
    ExactFlatFixedLeafMiss exactIds := by
  unfold ExactFlatFixedLeafMiss
  intro inp o res fixed entry hrun hwf hframed hfixed hleaf
  unfold ExpandChildParentRouteFrameClear
  intro frame hframe route hroute hfrom hto
  by_cases hself : route.fromId = route.toId
  · exact layoutX_selfLoop_fixedLeaf_frame_miss hrun hwf hframed
      (boxId := fixed.id) hfixed hleaf hframe hroute hself
  · exact layoutX_nonSelf_fixedLeaf_frame_miss hrun hwf hframed
      (boxId := fixed.id) hfixed hleaf hframe hroute hfrom hto hself

end Elegant.Layered.PipelineImpl

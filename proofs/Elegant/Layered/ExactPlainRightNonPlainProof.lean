import Elegant.Layered.ExactLoopEnvelopeRightProof
import Elegant.Layered.ExactLoopEnvelopeSidesProof
import Elegant.Layered.ExactLoopEnvelopeLeftNonPlainProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

theorem xlem_plainRightNonPlain_holds (exactIds : List String) :
    XLEM_PlainRightNonPlain exactIds := by
  intro inp o res execution comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope0 hscope1 hB0 hOrig
    layer hlayer pu pv hpu hpv hlt
  obtain ⟨ndV, hrecV⟩ : ∃ nd, run.proper.nodes[v]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hv⟩
  by_cases hpx : ndV.node.border = -2 ∨ ndV.node.border = 2
  · exact XLEM_plainRightProxyMiss_holds exactIds inp o res execution comp
      candidate run orderOptions cg e v hcomp hcg hrun ndV hrecV hpx
  · exact XLEM_plainRightGap_of_nonproxy exactIds inp o res execution comp
      candidate run orderOptions cg k e v hcomp hcg hrun hk hB0 ndV hrecV hpx
      hlayer hpu hpv hlt

end PipelineImpl
end Layered
end Elegant

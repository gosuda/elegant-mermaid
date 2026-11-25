import Elegant.Layered.ExactSeamClosureGlue
import Elegant.Layered.ExactStepFacts
import Elegant.Layered.ExactStepLeafFactsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

theorem XSGL_stepC7Caption_closed (exactIds : List String) : XG_StepC7CaptionB exactIds := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctxB hparams
  exact XSGL_stepC7Caption_of_owners exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams
    (XB_label_owners exactIds fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)

end Elegant.Layered.PipelineImpl

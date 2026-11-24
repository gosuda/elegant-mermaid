import Elegant.Layered.ExactFlatChildLabelsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

theorem XSGL_stepC7ChildFit_closed (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hfix : InputFixedFit inp o) :
    ExpandChildC7ChildInside P inp o group titleHeight parent child :=
  XSGL_stepC7Child_of_labels exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams
    (xsgl_stepC8bChildLabelsFit_closed exactIds fuel P inp o group titleLines
      titleHeight parent child res hexpand hframed hctxB hparams hfix)

end Elegant.Layered.PipelineImpl

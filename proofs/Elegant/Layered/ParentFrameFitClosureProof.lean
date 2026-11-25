import Elegant.Layered.ExpandChildParentFrameProof
import Elegant.Layered.ExecutedParentFrameStrictProof
import Elegant.Layered.FlatFixedFrameLabelProof
import Elegant.Layered.ChildFrameFitObstructionProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Fit at the root of the obstruction descent rules out both the flat and
recursive child-label cases. -/
theorem not_executedParentFrameObstruction_of_fit {root : Input} {options : Options}
    (hfit : InputFixedFit root options) : ¬ ExecutedParentFrameObstruction root options := by
  intro obstruction
  cases obstruction with
  | flat reached hwf framed run fixed lookup _role member foreignOwner inside =>
    exact flatFixedFrameLabel_not_strictInside_of_top_fit reached hfit hwf framed run
      fixed lookup member foreignOwner inside
  | childLabel reached ctx params framed _fixed _frameLookup _trackedLookup _role _offsetX
      _offsetY member _foreignOwner _notCaption _emitted _owner _rect _inside notFit =>
    exact notFit (expandChild_child_labels_fit_of_top hfit reached ctx params framed member)

/-- No foreign label lies strictly inside the frame in the executed parent
scene when the parent sub-input has fixed-size fit. -/
theorem executedParentFrameStrict_of_parent_fit
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int} {parent child res : FamilyResult}
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hfit : InputFixedFit (parentSubInput inp group P titleLines child) o) :
    ExpandChildParentFrameStrict group parent := by
  intro frame hframe label hlabel howner hinside
  exact not_executedParentFrameObstruction_of_fit hfit
    (executedParentFrameStrict_obstruction hframed hctx hparams hframe hlabel howner hinside)

/-- For an executed expansion, the current input's fit suffices: the wrapped
caption and successful child run supply the fit of the newly reserved frame. -/
theorem executedParentFrameStrict_of_fit
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int} {parent child res : FamilyResult}
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hfit : InputFixedFit inp o) : ExpandChildParentFrameStrict group parent :=
  executedParentFrameStrict_of_parent_fit hframed hctx hparams
    (fitParent_of_top hfit FitReached.refl hctx hparams)

end Elegant.Layered.PipelineImpl

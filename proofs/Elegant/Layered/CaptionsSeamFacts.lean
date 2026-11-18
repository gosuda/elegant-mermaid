import Elegant.Layered.LabelsC7Captions
import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.CaptionSizingFacts
import Elegant.Layered.CaptionOwnerScopeFacts
import Elegant.Layered.CaptionTitleBranchFacts
import Elegant.Layered.CaptionDescendantFacts

/-!
# Caption seam assembly

`LayeredSeams.captions` asks for `SceneCaptionBoxContainment inp o res`.  This
unit chains every landed caption reduction, so the seam follows from the input
well-formedness and five named residuals:

* `CaptionDescendantSamePartClear` (`CaptionDescendantFacts.lean`): the caption
  of an owner misses the exclusive members of its own subtree.
* `CaptionInputs` (`CaptionSizingFacts.lean`): the caption input contract and
  the nonfixed-group size clause.  It needs a premise on the input: a
  fixed-size box may be smaller than its label.
* `OwnerScopeSamePartClear` (`CaptionOwnerScopeFacts.lean`): the owner box
  misses the foreign exclusive boxes of its own packed part.
* the frame-label pair `LabelFramePackedClear` and `FallbackCaptionClear`
  (`LabelsC8b.lean`), which is the `LayeredSeams.frameLabels` field.
* `TitleExclusiveFrameDisjoint` (`CaptionTitleBranchFacts.lean`): an installed
  title rect misses foreign exclusive frames.
-/

set_option autoImplicit false

namespace Elegant.Layered

variable {inp : Input} {o : Options} {res : FamilyResult}

/-- `CaptionScopeClearance` from the five named caption residuals. -/
theorem captionScopeClearance_of_residuals
    (hdesc : CaptionDescendantSamePartClear inp o res)
    (hinputs : CaptionInputs inp o res)
    (hsame : OwnerScopeSamePartClear inp o res)
    (hframes : ∀ (execution : PipelineImpl.SceneExecution inp o res),
      PipelineImpl.LabelFramePackedClear execution.params inp o execution.lines
        execution.packedAcc ∧ PipelineImpl.FallbackCaptionClear execution)
    (hnode : ∀ (execution : PipelineImpl.SceneExecution inp o res),
      PipelineImpl.TitleExclusiveFrameDisjoint execution) :
    CaptionScopeClearance inp o res :=
  captionScopeClearance (captionDescendantClear_of_same_part hdesc)
    (ownerCaptionContainFallback_of_contain
      (ownerCaptionContain (sceneCaptionSizing_of_inputs hinputs)))
    (ownerScopeExclusiveClear_of_same_part hsame)
    (PipelineImpl.captionTitleBranchClear_of_frames hframes hnode)

/-- The caption seam of flat clause 7 for a well-formed input, from the five
named caption residuals. -/
theorem sceneCaptionBoxContainment_of_residuals
    (hwf : WellFormed (inputModel inp o))
    (hdesc : CaptionDescendantSamePartClear inp o res)
    (hinputs : CaptionInputs inp o res)
    (hsame : OwnerScopeSamePartClear inp o res)
    (hframes : ∀ (execution : PipelineImpl.SceneExecution inp o res),
      PipelineImpl.LabelFramePackedClear execution.params inp o execution.lines
        execution.packedAcc ∧ PipelineImpl.FallbackCaptionClear execution)
    (hnode : ∀ (execution : PipelineImpl.SceneExecution inp o res),
      PipelineImpl.TitleExclusiveFrameDisjoint execution) :
    SceneCaptionBoxContainment inp o res :=
  sceneCaptionBoxContainment hwf
    (captionScopeClearance_of_residuals hdesc hinputs hsame hframes hnode)

end Elegant.Layered

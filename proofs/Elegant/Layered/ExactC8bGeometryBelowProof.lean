import Elegant.Layered.ExactBorderChainBProof
import Elegant.Layered.ExactC8bBelowFuelProof
import Elegant.Layered.ExactFlatC8aCore
import Elegant.Layered.ExactFlatChildLabelsProof
import Elegant.Layered.ExactForeignRankPairAnchorsProof
import Elegant.Layered.ExactPlainNodePathProof
import Elegant.Layered.ExactRecursiveParentStrictProof
import Elegant.Layered.ExactSideMarkerFactsProof
import Elegant.Layered.ExactStepLeafFactsProof
import Elegant.Layered.ExecutedExactParentFrameFitProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The parent run at fuel `F` needs C8b geometry only at expansion fuels `< F`. -/
theorem stepC8bGeometry_layoutX_of_flat (exactIds : List String)
    (hflat8b : FlatC8bB (layoutX exactIds))
    (hflatLeaf : ExactFlatFixedLeafLabelExclusion exactIds) :
    RecursiveStepFactsB (layoutX exactIds)
      (fun P inp o group titleHeight parent child res =>
        InputFixedFit inp o → ExpandChildC8bGeometry P inp o group titleHeight parent child res) := by
  have hchain : X_ForeignBorderChainXAligned exactIds :=
    X_foreignBorderChainXAligned_framed exactIds
  have hflat8a : FlatC8aB (layoutX exactIds) :=
    flatC8aB_layoutX exactIds
      (XB_foreignClusterRankSpans_holds exactIds (XB_foreignRankPairAnchors_holds exactIds))
      (XB_foreignBorderLayerOrder_holds exactIds)
      hchain
      (XN_bracketMarkersAtRank_holds exactIds)
      (XN_plainClearOfSideMarker_of_path exactIds (XN_plainNodePathResidual_holds exactIds))
      (XN_sideMarkerSpanAligned_of_chain exactIds hchain)
  have hrecursive8a := layoutRecursiveB_c8a (layoutX exactIds) hflat8a
    (subInputWellFormedB_layoutX exactIds)
    (stepC8a_layoutX exactIds (stepC8aGeometry_layoutX exactIds) (stepC8aAncestry_layoutX exactIds))
  refine recursiveStepFactsB_of_below (layoutX exactIds) _ ?_
  intro fuel below8b P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams hfit
  have hC8a : Validator.C8a parent.scene.layoutDump := by
    obtain ⟨hwf, _, _, hchild, hparent, _⟩ := hctx
    obtain ⟨hP, _, metric, hm, hwrap⟩ := hparams
    obtain ⟨_, _, hwfParent, hframedParent⟩ :=
      subInputWellFormedB_layoutX exactIds fuel inp o group P metric titleLines child parent
        hwf hframed hP hm hwrap hchild hparent
    exact hrecursive8a fuel (parentSubInput inp group P titleLines child) o parent
      hwfParent hframedParent hparent
  have hC8b := XSGLB_parentScene_c8b_below exactIds hflat8b below8b hframed hctx hparams hfit
  have hframeStrict := executedExactParentFrameStrict_of_flat_fit
    hflatLeaf hframed hctx hparams hfit
  have hstepStrict := parentStrictStepB_of_recursion exactIds fuel P inp o group titleLines
    titleHeight parent child res hframed hctx
  have hParentFrame := XSGL_stepC8bParentFrame_of exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctx hparams hC8a hC8b hframeStrict hstepStrict
  exact XSGL_c8bCore exactIds fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams
    (XG_child_boxes_insetB exactIds fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx hparams)
    (xsgl_stepC8bChildLabelsFit_closed exactIds fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx hparams hfit)
    (fun frame lines dx dy hframe hdx hdy hwrapped =>
      XG_content_fit_strict exactIds fuel P inp o group titleLines titleHeight
        parent child res hexpand hframed hctx hparams frame lines dx dy
        hframe hdx hdy hwrapped (insetRect child.scene.canvas P.canvasMargin)
        (Rect.Contained.refl _))
    (XSGL_stepC8bCapStrict exactIds fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx hparams)
    (XSGL_stepC8bCapDisj exactIds fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx hparams)
    (stepC8aAncestry_layoutX exactIds fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx hparams)
    hParentFrame

end Elegant.Layered.PipelineImpl

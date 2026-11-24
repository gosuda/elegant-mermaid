import Elegant.Layered.ExactC8bGeometryBelowProof
import Elegant.Layered.ExactSeamClosureGlue

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Parent C7 clearance follows from parent C8a, C8b from smaller expansion
fuels, and strictness of the executed parent frame. -/
theorem xg_stepC7ParentB_of_flat (exactIds : List String)
    (hflat8b : FlatC8bB (layoutX exactIds))
    (hflatLeaf : ExactFlatFixedLeafLabelExclusion exactIds) :
    XG_StepC7ParentB exactIds := by
  have hgeoC8bB := stepC8bGeometry_layoutX_of_flat exactIds hflat8b hflatLeaf
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
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams hfit
  have below8b : StepFactsBelowB (layoutX exactIds) fuel
      (fun P inp o group titleHeight parent child res =>
        InputFixedFit inp o → ExpandChildC8bGeometry P inp o group titleHeight parent child res) :=
    fun fuel' _ => hgeoC8bB fuel'
  have hC8b := XSGLB_parentScene_c8b_below exactIds hflat8b below8b hframed hctx hparams hfit
  have hC8a : Validator.C8a parent.scene.layoutDump := by
    obtain ⟨hwf, _, _, hchild, hparent, _⟩ := hctx
    obtain ⟨hP, _, metric, hm, hwrap⟩ := hparams
    obtain ⟨_, _, hwfParent, hframedParent⟩ :=
      subInputWellFormedB_layoutX exactIds fuel inp o group P metric titleLines child parent
        hwf hframed hP hm hwrap hchild hparent
    exact hrecursive8a fuel (parentSubInput inp group P titleLines child) o parent
      hwfParent hframedParent hparent
  have hframeStrict := executedExactParentFrameStrict_of_flat_fit
    hflatLeaf hframed hctx hparams hfit
  have hstepStrict := parentStrictStepB_of_recursion exactIds fuel P inp o group titleLines
    titleHeight parent child res hframed hctx
  have hParentFrame := XSGL_stepC8bParentFrame_of exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctx hparams hC8a hC8b hframeStrict hstepStrict
  intro frame lines dx dy hframe hdx hdy hwrap
  have hclear := hParentFrame frame lines dx dy hframe hdx hdy hwrap
  exact ⟨hclear.1, hclear.2.1⟩

end Elegant.Layered.PipelineImpl

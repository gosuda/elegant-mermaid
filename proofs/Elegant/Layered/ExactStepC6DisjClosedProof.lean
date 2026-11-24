import Elegant.Layered.ExactBorderChainBProof
import Elegant.Layered.ExactFlatC8aCore
import Elegant.Layered.ExactForeignBorderSpansProof
import Elegant.Layered.ExactForeignRankPairAnchorsProof
import Elegant.Layered.ExactPlainNodePathProof
import Elegant.Layered.ExactSeamClosureGlue
import Elegant.Layered.ExactSideMarkerFactsProof
import Elegant.Layered.ExactStepFacts
import Elegant.Layered.ExactStepLeafFactsProof
import Elegant.Layered.ExactStepShortFacts
import Elegant.Layered.ExactSubInputStepC2
import Elegant.Layered.FramedParentsSub
import Elegant.Layered.RecursiveBLiftsB
import Elegant.Layered.SubInputWellFormedFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

theorem XSGL_stepC6Disj_closed (exactIds : List String) :
    XG_StepC6DisjB exactIds := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
  have hwf : WellFormed (inputModel inp o) := hctxB.1
  have hparent : layoutRecursiveB (layoutX exactIds) fuel
      (parentSubInput inp group P titleLines child) o = .ok parent := hctxB.2.2.2.2.1
  have hwfParent : WellFormed (inputModel (parentSubInput inp group P titleLines child) o) :=
    (subInputWellFormedC2 inp o group hwf).2 _ _ _
  have hframedParent : framedParents (parentSubInput inp group P titleLines child) = true :=
    framedParents_selectInput_outside_append inp o group hwf hframed _ child.scene child.itemArea
  have hchain : X_ForeignBorderChainXAligned exactIds :=
    X_foreignBorderChainXAligned_framed exactIds
  have hflat : FlatC8aB (layoutX exactIds) :=
    flatC8aB_layoutX exactIds
      (XB_foreignClusterRankSpans_holds exactIds (XB_foreignRankPairAnchors_holds exactIds))
      (XB_foreignBorderLayerOrder_holds exactIds)
      hchain
      (XN_bracketMarkersAtRank_holds exactIds)
      (XN_plainClearOfSideMarker_of_path exactIds (XN_plainNodePathResidual_holds exactIds))
      (XN_sideMarkerSpanAligned_of_chain exactIds hchain)
  have hC8a : Validator.C8a parent.scene.layoutDump :=
    layoutRecursiveB_c8a (layoutX exactIds) hflat (subInputWellFormedB_layoutX exactIds)
      (stepC8a_layoutX exactIds (stepC8aGeometry_layoutX exactIds) (stepC8aAncestry_layoutX exactIds))
      fuel (parentSubInput inp group P titleLines child) o parent hwfParent hframedParent hparent
  exact XSGL_stepC6Disj_of_c8a exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams hC8a

end Elegant.Layered.PipelineImpl

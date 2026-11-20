import Elegant.Layered.ExactFlatC8aCore
import Elegant.Layered.ExactForeignBorderSpansProof
import Elegant.Layered.ExactForeignRankPairAnchorsProof
import Elegant.Layered.ExactSideMarkerFactsProof
import Elegant.Layered.ExactPlainNodePathProof
import Elegant.Layered.LabelsC8b
import Elegant.Layered.ExactFallbackCaptionFactsProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact owner-frame disjointness: the fallback-owner C8a instance closed
in its executed `W` form.

`XFB_OwnerFrameDisjointW` (`ExactFallbackCaptionFactsProof.lean`) states
the C8a instance the fallback owner-frame proof consumes: a group scene box
is disjoint from the owner's scene box at `ownerIndex` whenever the two ids
differ and neither is a dump ancestor of the other. The proof here discharges
that residual outright from the `c8aChain` seam
(`X_ForeignBorderChainXAligned`, the former `ExactSeams.fbDisj` feeder),
with the standard local
admission premises (`WellFormed`, `framedParents`) after the execution
binder.

The argument is the one-pair projection of the executed flat C8a clause
`xC8a_executed_of_spans` (`ExactFlatC8aCore.lean`): the six span leaves
reduce to the single `c8aChain` seam (`X_ForeignBorderChainXAligned`, the
`ExactSeams.c8aChain` field) because the other five are closed, and C8a
applied to the group box and the owner scene box yields the disjointness
after `sceneBox_source_rectX` identifies the owner box by index. The
installed-title premise is not needed for the disjointness conclusion. -/

/-- The `W` owner-frame disjointness from the `c8aChain` seam alone: the
executed flat C8a clause specialized to the pair (group scene box, owner
scene box at `ownerIndex`). -/
theorem XFB_ownerFrameDisjointW_of_chain (exactIds : List String)
    (hchain : X_ForeignBorderChainXAligned exactIds) :
    XFB_OwnerFrameDisjointW exactIds := by
  intro inp o res execution hwf hfp ownerIndex obox g hobox _hnone hgMem hgRole
    hne hganc hobanc
  have hC8a : Validator.C8a res.scene.layoutDump :=
    xC8a_executed_of_spans execution hwf hfp
      (XB_foreignClusterRankSpans_holds exactIds
        (XB_foreignRankPairAnchors_holds exactIds))
      (XB_foreignBorderLayerOrder_holds exactIds)
      hchain
      (XN_bracketMarkersAtRank_holds exactIds)
      (XN_plainClearOfSideMarker_of_path exactIds
        (XN_plainNodePathResidual_holds exactIds))
      (XN_sideMarkerSpanAligned_of_chain exactIds hchain)
  have hbl : (sceneBoxesExpr execution.params inp o execution.packedAcc).length
      = inp.boxes.length := by
    simp [sceneBoxesExpr]
  have hlt : ownerIndex < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hobox).1
  have hi : ownerIndex <
      (sceneBoxesExpr execution.params inp o execution.packedAcc).length := by
    omega
  obtain ⟨ob, hobb⟩ : ∃ box : Box,
      (sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
        some box := ⟨_, List.getElem?_eq_getElem hi⟩
  have hgetD : (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩ = ob := by
    rw [List.getD_eq_getElem?_getD, hobb]
    rfl
  have hboxScene : res.scene.boxes[ownerIndex]? = some ob := by
    rw [execution.boxes_eq_mapX]
    exact hobb
  obtain ⟨source, hsrc, hobIdSrc, _, _, _⟩ :=
    sceneBox_source_rectX execution hboxScene
  have hsrcEq : source = obox := Option.some.inj (hsrc.symm.trans hobox)
  have hobId : ob.id = obox.id := by rw [hobIdSrc, hsrcEq]
  have gMemDump : g ∈ res.scene.layoutDump.boxes := by
    simpa only [Scene.layoutDump] using hgMem
  have hobMemDump : ob ∈ res.scene.layoutDump.boxes := by
    simpa only [Scene.layoutDump] using List.mem_of_getElem? hboxScene
  have hd := hC8a g gMemDump hgRole ob hobMemDump
    (by rw [hobId]; exact fun heq => hne heq.symm)
    (by rw [hobId]; exact hganc)
    (by rw [hobId]; exact hobanc)
  rw [hgetD]
  exact hd

end PipelineImpl
end Layered
end Elegant

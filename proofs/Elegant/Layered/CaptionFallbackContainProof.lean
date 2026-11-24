import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.InputFixedFit
import Elegant.Layered.FixedOwnerFit
import Elegant.Layered.CaptionFallbackOwnerProof
import Elegant.Layered.SizingCoverageBridge

set_option autoImplicit false

/-! # Fallback caption containment from the fixed-size fit premise

`OwnerCaptionContainFallback` for an executed run, from `WellFormed` and the
`InputFixedFit` premise.  The owner box carries no installed title, so by
`fallback_owner_cases` it is either a non-fixed node box or a fixed-size box:

* a non-fixed node owner: `ordinary_box_line_height` gives the height fit, and
  the centred node caption lies inside the owner rect;
* a fixed owner: `fixed_owner_fit` gives the fit at the output rect, then the
  `titleRect` inset contains the caption for a group owner and the centred
  node inset contains it for a node owner.
-/

namespace Elegant.Layered

/-- A node-owner fallback caption is centred horizontally at full width, so a
height fit puts it inside the owner rect. -/
private theorem node_ownedTextRect_contained {P : PipelineImpl.Params} {box : Box}
    {ls : List Measure.Line} (hrole : box.role = "node")
    (hpos : 0 ≤ P.lineH)
    (hf : ((ls.length : Int) * P.lineH) ≤ box.rect.h) :
    box.rect.Contained (PipelineImpl.ownedTextRect P box ls) := by
  unfold PipelineImpl.ownedTextRect
  rw [ite_eq_right (by simp [hrole] : ¬((box.role == "group") = true))]
  have hprod : 0 ≤ (ls.length : Int) * P.lineH :=
    Int.mul_nonneg (Int.natCast_nonneg _) hpos
  have hdiff : 0 ≤ box.rect.h - (ls.length : Int) * P.lineH := by
    simpa using hf
  have hfeq : Int.fdiv (box.rect.h - (ls.length : Int) * P.lineH) 2 =
      (box.rect.h - (ls.length : Int) * P.lineH) / 2 :=
    Int.fdiv_eq_ediv_of_nonneg _ (by omega)
  have hhalf_nonneg : 0 ≤ (box.rect.h - (ls.length : Int) * P.lineH) / 2 :=
    Int.ediv_nonneg hdiff (by decide)
  have hhalf_le : (box.rect.h - (ls.length : Int) * P.lineH) / 2 ≤ box.rect.h -
      (ls.length : Int) * P.lineH :=
    Int.ediv_le_self 2 hdiff
  dsimp only
  rw [hfeq]
  show box.rect.x ≤ box.rect.x ∧
    box.rect.x + box.rect.w ≤ box.rect.x + box.rect.w ∧
    box.rect.y ≤ box.rect.y + (box.rect.h - (ls.length : Int) * P.lineH) / 2 ∧
    box.rect.y + (box.rect.h - (ls.length : Int) * P.lineH) / 2 + (ls.length : Int) * P.lineH ≤ box.rect.y + box.rect.h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The fallback caption of the owner box lies inside the owner scene box
rect, from well-formedness and the fixed-size fit premise. -/
theorem ownerCaptionContainFallback_of_fit {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hfit : PipelineImpl.InputFixedFit inp o) :
    OwnerCaptionContainFallback inp o res := by
  intro execution ownerIndex obox hobox hnone hex hown
  show ((PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩).rect.Contained
    (PipelineImpl.ownedTextRect execution.params
      ((PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩)
      (execution.lines.getD ownerIndex []))
  have hbl : (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).length
      = inp.boxes.length := by
    simp [PipelineImpl.sceneBoxesExpr]
  have hlt : ownerIndex < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hobox).1
  have hi : ownerIndex <
      (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).length := by
    omega
  obtain ⟨box, hbox⟩ : ∃ box : Box,
      (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
        some box := ⟨_, List.getElem?_eq_getElem hi⟩
  have hboxScene : res.scene.boxes[ownerIndex]? = some box := by
    rw [execution.boxes_eq_map]; exact hbox
  have hgetD : (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩ = box := by
    rw [List.getD_eq_getElem?_getD, hbox]
    rfl
  rw [hgetD]
  obtain ⟨actual, hactual, hboxeq⟩ := execution.box_index_origin hboxScene
  rw [hobox] at hactual
  have hact : actual = obox := (Option.some.inj hactual).symm
  have hroleEq : box.role = obox.role.id := by rw [hboxeq, hact]
  by_cases hany : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = true
  · have hfit' := execution.fixed_owner_fit hfit hboxScene hobox hany hex hown
    by_cases hg : obox.role = .group
    · rw [hg] at hfit'
      simp only [PipelineImpl.FixedSizeFit] at hfit'
      obtain ⟨hgw, hgh⟩ := hfit'
      have hpad : 0 ≤ execution.params.clusterPad :=
        execution.parameter_signs.2.1
      have hgroup : box.role = "group" := by
        simp only [hroleEq, hg, BoxRole.id]
      rw [ownedTextRect_group_eq hgroup]
      exact titleRect_contained hpad hgw (Int.le_of_lt hgh)
    · have hroleN : obox.role = .node := by
        cases h : obox.role with
        | node => rfl
        | group => exact absurd h hg
      have hgnode : box.role = "node" := by
        simp only [hroleEq, hroleN, BoxRole.id]
      rw [hroleN] at hfit'
      simp only [PipelineImpl.FixedSizeFit] at hfit'
      have hpos : 0 ≤ execution.params.lineH := execution.parameter_signs.1
      exact node_ownedTextRect_contained hgnode hpos hfit'
  · have hfixFalse : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false :=
      Bool.eq_false_iff.mpr hany
    have hfall := execution.fallback_owner_cases hwf hobox hnone
    have hroleN : obox.role = .node := by
      rcases hfall with h | h
      · exact h
      · rw [hfixFalse] at h; exact absurd h Bool.false_ne_true
    obtain ⟨ls, hls⟩ : ∃ ls, execution.lines[ownerIndex]? = some ls := by
      have hlinesLen : execution.lines.length = inp.boxes.length := by
        have hl := execution.lines_eq
        unfold PipelineImpl.boxLines at hl
        calc execution.lines.length = (inp.boxes.zipIdx).length :=
            (PipelineImpl.mapM_getElem? _ _ _ hl).1
          _ = inp.boxes.length := List.length_zipIdx
      have hi' : ownerIndex < execution.lines.length := by omega
      exact ⟨_, List.getElem?_eq_getElem hi'⟩
    have hfitH :=
      execution.ordinary_box_line_height hboxScene hobox hroleN hfixFalse hls
    have hgetLs : execution.lines.getD ownerIndex [] = ls := by
      rw [List.getD_eq_getElem?_getD, hls]
      rfl
    have hgnode : box.role = "node" := by
      simp only [hroleEq, hroleN, BoxRole.id]
    have hpos : 0 ≤ execution.params.lineH := execution.parameter_signs.1
    have hf : (((execution.lines.getD ownerIndex []).length : Int) *
        execution.params.lineH) ≤ box.rect.h := by
      rw [hgetLs]; exact hfitH.2
    exact node_ownedTextRect_contained hgnode hpos hf

end Elegant.Layered

import Elegant.Layered.CaptionFallbackContainProof
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.PartFrameCoresProof

set_option autoImplicit false

/-! # Fallback caption clearance from the fixed-size fit premise

`PipelineImpl.FallbackCaptionClear` for an executed run, from `WellFormed`,
the fixed-size fit premise `PipelineImpl.InputFixedFit`, and the single
residual `FallbackOwnerFrameClear`. The fallback caption lies inside its
owner frame by `ownerCaptionContainFallback_of_fit`; the owner's own frame is
then the strict title inset of a fixed group owner, while any other group
frame is related to the owner frame by the residual and the caption follows
through containment.
-/

namespace Elegant.Layered

/-- Residual owner-frame fact: every group scene box other than the owner's
own frame is disjoint from, or strictly contains, the owner's scene frame.
The owner's scene box is the exact `sceneBoxesExpr` projection that
`FallbackCaptionClear` uses. -/
def FallbackOwnerFrameClear {inp : Input} {o : Options} {res : FamilyResult}
    (execution : PipelineImpl.SceneExecution inp o res) : Prop :=
  ∀ (ownerIndex : Nat) (obox : ModelBox) (g : Box),
    inp.boxes[ownerIndex]? = some obox →
    (PipelineImpl.sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none →
    g ∈ res.scene.boxes → g.role = "group" → g.id ≠ obox.id →
    Disjoint g.rect
      ((PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩).rect ∨
      g.rect.StrictInside
        ((PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
          ownerIndex ⟨"", "", default, "", false⟩).rect

/-- The group title inset is strictly inside its frame once the fixed-size
fit holds with a positive cluster pad: the pad is positive, twice the pad
fits the frame width, and the pad plus the title band fits the frame
height. -/
theorem titleRect_strictInside_of_fit {P : PipelineImpl.Params} {r : Rect}
    {lines : List Measure.Line}
    (hcp : 0 < P.clusterPad) (hw : 2 * P.clusterPad ≤ r.w)
    (hh : P.clusterPad + (max 1 lines.length : Int) * P.lineH < r.h) :
    r.StrictInside (PipelineImpl.titleRect P r lines) := by
  have hle : max 0 (r.w - 2 * P.clusterPad) ≤ r.w - 2 * P.clusterPad := by
    rw [Int.max_le]
    exact ⟨by omega, by omega⟩
  unfold PipelineImpl.titleRect
  show r.x < r.x + P.clusterPad ∧
    r.x + P.clusterPad + max 0 (r.w - 2 * P.clusterPad) < r.x + r.w ∧
    r.y < r.y + P.clusterPad ∧
    r.y + P.clusterPad + (max 1 lines.length : Int) * P.lineH < r.y + r.h
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- The fallback-caption branch of the scene C8b clause, from
well-formedness, the fixed-size fit premise, and the owner-frame residual. -/
theorem fallbackCaptionClear_of_fit {inp : Input} {o : Options} {res : FamilyResult}
    (execution : PipelineImpl.SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (hfit : PipelineImpl.InputFixedFit inp o)
    (hframe : FallbackOwnerFrameClear execution) :
    PipelineImpl.FallbackCaptionClear execution := by
  intro source _ ownerIndex g hsrc hfind hnone hgMem hgRole
  obtain ⟨hlt, hpred, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
  obtain ⟨obox, hobox⟩ : ∃ obox, inp.boxes[ownerIndex]? = some obox :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have hge : inp.boxes[ownerIndex] = obox :=
    Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hobox)
  rw [hge] at hpred
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hpred
  obtain ⟨hownId, hex⟩ := hpred
  have hnone' : (PipelineImpl.sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none := by
    rw [hownId]
    exact hnone
  have hown : ∃ l ∈ inp.labels, l.owner = obox.id :=
    ⟨source, List.mem_of_getElem? hsrc, hownId.symm⟩
  have hbl : (PipelineImpl.sceneBoxesExpr execution.params inp o
      execution.packedAcc).length = inp.boxes.length := by
    simp [PipelineImpl.sceneBoxesExpr]
  have hi : ownerIndex <
      (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).length := by
    omega
  obtain ⟨ob, hobb⟩ : ∃ box : Box,
      (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
        some box := ⟨_, List.getElem?_eq_getElem hi⟩
  have hboxScene : res.scene.boxes[ownerIndex]? = some ob := by
    rw [execution.boxes_eq_map]; exact hobb
  have hgetD : (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩ = ob := by
    rw [List.getD_eq_getElem?_getD, hobb]
    rfl
  obtain ⟨actual, hactual, hboxeq⟩ := execution.box_index_origin hboxScene
  rw [hobox] at hactual
  have hact : actual = obox := (Option.some.inj hactual).symm
  have hroleEq : ob.role = obox.role.id := by rw [hboxeq, hact]
  have hcontain : ob.rect.Contained (PipelineImpl.ownedTextRect execution.params ob
      (execution.lines.getD ownerIndex [])) := by
    rw [←hgetD]
    exact ownerCaptionContainFallback_of_fit hwf hfit execution ownerIndex obox
      hobox hnone' hex hown
  have hcp : 0 < execution.params.clusterPad :=
    PipelineImpl.checkedParams_clusterPad_pos execution.checked
  have hcapGroup : obox.role = .group →
      ob.rect.StrictInside (PipelineImpl.ownedTextRect execution.params ob
        (execution.lines.getD ownerIndex [])) := by
    intro hgroup
    have hfall := execution.fallback_owner_cases hwf hobox hnone'
    have hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = true := by
      rcases hfall with hnode | hfixed
      · rw [hnode] at hgroup
        exact absurd hgroup (by decide)
      · exact hfixed
    have hfit' := execution.fixed_owner_fit hfit hboxScene hobox hfixed hex hown
    rw [hgroup] at hfit'
    simp only [PipelineImpl.FixedSizeFit] at hfit'
    obtain ⟨hgw, hgh⟩ := hfit'
    have hgroupScene : ob.role = "group" := by
      simp only [hroleEq, hgroup, BoxRole.id]
    rw [ownedTextRect_group_eq hgroupScene]
    exact titleRect_strictInside_of_fit hcp hgw hgh
  rw [hgetD]
  show Disjoint g.rect (PipelineImpl.ownedTextRect execution.params ob
      (execution.lines.getD ownerIndex [])) ∨
    g.rect.StrictInside (PipelineImpl.ownedTextRect execution.params ob
      (execution.lines.getD ownerIndex []))
  by_cases heq : g.id = obox.id
  · obtain ⟨j, hj⟩ := List.getElem?_of_mem hgMem
    obtain ⟨gsrc, hgsrc, hgeq⟩ := execution.box_index_origin hj
    have hgid : g.id = gsrc.id := by rw [hgeq]
    have hids := Model.boxIds_nodup hwf
    have ha : (inp.boxes.map (·.id))[ownerIndex]? = some obox.id := by
      simp [List.getElem?_map, hobox]
    have hb : (inp.boxes.map (·.id))[j]? = some gsrc.id := by
      simp [List.getElem?_map, hgsrc]
    have heq2 : obox.id = gsrc.id := heq.symm.trans hgid
    have hlookups : (inp.boxes.map (·.id))[ownerIndex]? =
        (inp.boxes.map (·.id))[j]? := by
      rw [ha, hb, heq2]
    have hbound : ownerIndex < (inp.boxes.map (·.id)).length := by
      rw [List.length_map]; exact hlt
    have hidxEq : ownerIndex = j := (List.Nodup.getElem?_inj hbound hids).mp hlookups
    have hboxEq : obox = gsrc := by
      have hsame : inp.boxes[ownerIndex]? = inp.boxes[j]? := by rw [hidxEq]
      rw [hobox, hgsrc] at hsame
      exact Option.some.inj hsame
    have hgr : obox.role = .group := by
      have hgrole : g.role = gsrc.role.id := by rw [hgeq]
      rw [←hboxEq] at hgrole
      cases h : obox.role with
      | node =>
        rw [h] at hgrole
        simp only [BoxRole.id] at hgrole
        rw [hgRole] at hgrole
        exact absurd hgrole (by decide)
      | group => rfl
    have hobForm : ob = Box.mk obox.id obox.role.id
        (PipelineImpl.shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD ownerIndex default)))
        obox.parent obox.exclusive := by rw [hboxeq, hact]
    have hgob : g = ob := by
      rw [hgeq, hobForm, hboxEq, hidxEq]
    subst hgob
    exact Or.inr (hcapGroup hgr)
  · obtain hdisj | hstrict :=
      hframe ownerIndex obox g hobox hnone' hgMem hgRole heq
    · rw [hgetD] at hdisj
      exact Or.inl ((Disjoint.comm _ _).mpr
        (PipelineImpl.disjoint_of_sub_disjoint hcontain
          ((Disjoint.comm _ _).mp hdisj)))
    · rw [hgetD] at hstrict
      by_cases hgr : obox.role = .group
      · have hsc := hcapGroup hgr
        have hcont2 : g.rect.Contained ob.rect := by
          unfold Rect.StrictInside at hstrict
          unfold Rect.Contained at ⊢
          omega
        exact Or.inr (PipelineImpl.strictInside_of_contained hsc hcont2)
      · have hgoal : g.rect.StrictInside (PipelineImpl.ownedTextRect execution.params ob
            (execution.lines.getD ownerIndex [])) := by
          unfold Rect.StrictInside at hstrict ⊢
          unfold Rect.Contained at hcontain
          omega
        exact Or.inr hgoal

end Elegant.Layered

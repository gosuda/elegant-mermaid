import Elegant.Layered.ExactStepChildLabelsProof
import Elegant.Layered.ExpandChildChildSceneProof
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactFlatC3Closure
import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.ExactCaptionFitFactsProof
import Elegant.Layered.ExactCaptionTitleBranchProof
import Elegant.Layered.ExactFallbackStructuralProof
import Elegant.Layered.ExactPackedTransportResidualsProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact flat child-label inset.

Proved: `xscl_flatChildLabelsFit_holds` discharges the residual
`XSCL_FlatChildLabelsFit` of `ExactStepChildLabelsProof.lean` (labels of a
successful flat `layoutX exactIds` lie in the margin inset), by replaying the
plain twin `flat_layout_labels_inset` (`ExpandChildChildSceneProof.lean`)
over `SceneExecutionX`:

* measured labels: packed `labels_bounded` plus the margin/orientation
  projection, exactly as in the plain case;
* installed title captions: the same fold through `packAcc`, with the
  per-part step supplied by the closed `X_exactTitleCaptionFit_closed`
  (`xsclf_packed_title_caption_fit`);
* fallback owner captions: the closed
  `xctb_ownerCaptionContainFallbackFitW_of_cases` chain
  (`X_NonfixedGroupTitleX_holds` into `X_FallbackOwnerCasesX_holds`),
  plus the box inset from the closed `layoutX_inset`.

Open: none. Closes with `xsgl_stepC8bChildLabelsFit_closed`, which feeds the
proved flat case into `xsgl_stepC8bChildLabelsFit_holds`.
-/

/-- X mirror of the `fits` fold in `SceneExecution.packed_title_caption_fit`
(`SceneBounds.lean`): every packed title of an exact execution covers its
measured caption. The fold skeleton is base-independent; the per-part step
uses the closed `X_exactTitleCaptionFit_closed`. -/
private theorem xsclf_packed_title_caption_fit {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    ∀ title ∈ execution.packedAcc.titles,
      let lines := execution.lines.getD title.1 []
      let width := lines.foldl (fun value line => max value line.width) 0
      let height := (max 1 lines.length : Int) * execution.params.lineH
      let size := match o.direction with
        | .LR | .RL => Size.mk height width
        | .TB | .BT => Size.mk width height
      0 ≤ size.w ∧ 0 ≤ size.h ∧ size.w ≤ title.2.w ∧ size.h ≤ title.2.h := by
  let fits : Nat × Rect → Prop := fun title =>
    let lines := execution.lines.getD title.1 []
    let width := lines.foldl (fun value line => max value line.width) 0
    let height := (max 1 lines.length : Int) * execution.params.lineH
    let size := match o.direction with
      | .LR | .RL => Size.mk height width
      | .TB | .BT => Size.mk width height
    0 ≤ size.w ∧ 0 ≤ size.h ∧ size.w ≤ title.2.w ∧ size.h ≤ title.2.h
  have fold : ∀ (pairs : List ((List Nat × Part) × Rect)) (start : Acc),
      (∀ pair ∈ pairs, ∀ title ∈ pair.1.2.titles,
        fits (pair.1.1.getD title.1 0, shiftRect pair.2.x pair.2.y title.2)) →
      (∀ title ∈ start.titles, fits title) →
      ∀ title ∈ (pairs.foldl packStep start).titles, fits title := by
    intro pairs
    induction pairs with
    | nil => intro start _ hstart; exact hstart
    | cons pair pairs ih =>
      intro start hpairs hstart
      rw [List.foldl_cons]
      apply ih _ (fun p hp => hpairs p (List.mem_cons_of_mem _ hp))
      intro title htitle
      change title ∈ start.titles ++ pair.1.2.titles.map
        (fun raw => (pair.1.1.getD raw.1 0, shiftRect pair.2.x pair.2.y raw.2)) at htitle
      rcases List.mem_append.mp htitle with hold | hnew
      · exact hstart title hold
      · obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hnew
        exact hpairs pair List.mem_cons_self raw hraw
  change ∀ title ∈ execution.packedAcc.titles, fits title
  have hpack := execution.packed_eq
  unfold packAcc at hpack
  obtain ⟨packed, _, hpack⟩ := bind_ok hpack
  rw [inlineFold_eq_packStep] at hpack
  have he := Except.ok.inj hpack
  rw [← he]
  apply fold
  · intro pair hpair title htitle
    have hfit := X_exactTitleCaptionFit_closed exactIds execution
      (List.of_mem_zip hpair).1 htitle
    exact hfit
  · intro title htitle
    simp at htitle

/-- The exact flat base case: labels of a successful flat `layoutX` lie in
the margin inset of its canvas. Replay of `flat_layout_labels_inset` over
`SceneExecutionX`. -/
theorem xscl_flatChildLabelsFit_holds (exactIds : List String) :
    XSCL_FlatChildLabelsFit exactIds := by
  intro inp o res hwf hfp hfit h Q hQ cl hcl
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hfallW : X_OwnerCaptionContainFallbackFitW exactIds :=
    xctb_ownerCaptionContainFallbackFitW_of_cases exactIds
      (X_FallbackOwnerCasesX_holds exactIds (X_NonfixedGroupTitleX_holds exactIds))
  have hQeq : Q = execution.params :=
    Except.ok.inj (hQ.symm.trans execution.checked)
  subst hQeq
  obtain ⟨P', hchecked', _hm', hinset⟩ :=
    layoutX_inset h hwf hfp exactComponentPlacement
  have hP'eq : P' = execution.params :=
    Except.ok.inj (hchecked'.symm.trans execution.checked)
  subst hP'eq
  rw [execution.scene_eq] at hinset
  have hacc := SceneExecutionX.packedAcc_bounded execution
    (exactPartsBounded' execution)
  have hmargin : 0 ≤ execution.params.canvasMargin := by
    have := checkedParams_canvasMargin_ge_one execution.checked
    omega
  rw [execution.scene_eq] at hcl ⊢
  obtain ⟨q, hqmem, hemitted⟩ := List.mem_filterMap.mp hcl
  cases hexclusive : inp.boxes.any
      (fun box => box.id == q.1.owner && box.exclusive) with
  | true => simp only [hexclusive, ↓reduceIte] at hemitted; cases hemitted
  | false =>
    simp only [hexclusive, Bool.false_eq_true, ↓reduceIte] at hemitted
    cases hm : execution.measured.find? (fun item => item.index == q.2) with
    | some measured =>
      simp only [hm, Option.some.injEq] at hemitted
      subst cl
      have hrect : let rect := execution.packedAcc.labels.getD measured.index default
          0 ≤ rect.x ∧ rect.x + rect.w ≤ execution.packedAcc.canvasW ∧
          0 ≤ rect.y ∧ rect.y + rect.h ≤ execution.packedAcc.canvasH ∧
          0 ≤ rect.w ∧ 0 ≤ rect.h := by
        cases hget : execution.packedAcc.labels[measured.index]? with
        | none =>
          rw [Array.getD_eq_getD_getElem?, hget]
          change 0 ≤ (0 : Int) ∧ 0 ≤ execution.packedAcc.canvasW ∧
            0 ≤ (0 : Int) ∧ 0 ≤ execution.packedAcc.canvasH ∧
            0 ≤ (0 : Int) ∧ 0 ≤ (0 : Int)
          exact ⟨by omega, hacc.canvas_w_nonneg, by omega, hacc.canvas_h_nonneg,
            by omega, by omega⟩
        | some stored =>
          rw [Array.getD_eq_getD_getElem?, hget]
          exact hacc.labels_bounded measured.index stored hget
      exact orient_shiftRect_inset_containsCellRect o.direction
        execution.packedAcc.canvasW execution.packedAcc.canvasH
        execution.params.canvasMargin _ hrect hmargin
    | none =>
      simp only [hm] at hemitted
      cases ho : inp.boxes.findIdx?
          (fun box => box.id == q.1.owner && !box.exclusive) with
      | none => simp only [ho] at hemitted; cases hemitted
      | some ownerIndex =>
        simp only [ho, Option.some.injEq] at hemitted
        subst cl
        show (insetRect (sceneOf execution.params inp o execution.lines
              execution.packedAcc execution.measured).canvas
              execution.params.canvasMargin).Contained
            (sceneCaptionRect execution.params inp o execution.lines
              execution.packedAcc ownerIndex q.1.owner)
        simp only [sceneCaptionRect]
        cases hT : (sceneTitlesExpr execution.params inp o execution.lines
            execution.packedAcc).find? (fun title => title.1 == q.1.owner) with
        | none =>
          simp only [Option.map_none, Option.getD_none]
          obtain ⟨hltB, hmatch, _⟩ :=
            List.findIdx?_eq_some_iff_getElem.mp ho
          have hobox : inp.boxes[ownerIndex]? =
              some (inp.boxes[ownerIndex]'hltB) :=
            List.getElem?_eq_getElem hltB
          have hpred : (((inp.boxes[ownerIndex]'hltB).id == q.1.owner &&
              !(inp.boxes[ownerIndex]'hltB).exclusive) = true) := by
            simpa using hmatch
          cases hid : ((inp.boxes[ownerIndex]'hltB).id == q.1.owner) with
          | false =>
            simp [hid] at hpred
          | true =>
            have hoboxId : (inp.boxes[ownerIndex]'hltB).id = q.1.owner :=
              beq_iff_eq.mp hid
            cases hexb : (inp.boxes[ownerIndex]'hltB).exclusive with
            | true =>
              simp [hid, hexb] at hpred
            | false =>
              have hex : (inp.boxes[ownerIndex]'hltB).exclusive = false := hexb
              have hqget : inp.labels[q.2]? = some q.1 :=
                List.mem_zipIdx_iff_getElem?.mp hqmem
              have hqlabel : q.1 ∈ inp.labels := List.mem_of_getElem? hqget
              have hnone : (sceneTitlesExpr execution.params inp o execution.lines
                  execution.packedAcc).find? (fun title => title.1 ==
                    (inp.boxes[ownerIndex]'hltB).id) = none := by
                rw [hoboxId]
                exact hT
              have hown : ∃ l ∈ inp.labels,
                  l.owner = (inp.boxes[ownerIndex]'hltB).id :=
                ⟨q.1, hqlabel, hoboxId.symm⟩
              have hcontain :
                  ((sceneBoxesExpr execution.params inp o
                    execution.packedAcc).getD ownerIndex
                    ⟨"", "", default, "", false⟩).rect.Contained
                    (ownedTextRect execution.params
                      ((sceneBoxesExpr execution.params inp o
                        execution.packedAcc).getD ownerIndex
                        ⟨"", "", default, "", false⟩)
                      (execution.lines.getD ownerIndex [])) :=
                hfallW inp o res execution hwf hfit ownerIndex _ hobox hnone hex hown
              have hlt : ownerIndex <
                  (sceneBoxesExpr execution.params inp o
                    execution.packedAcc).length := by
                have hlt' := (List.findIdx?_eq_some_iff_getElem.mp ho).1
                simp only [sceneBoxesExpr, List.length_map, List.length_zipIdx]
                omega
              have hgetD : (sceneBoxesExpr execution.params inp o
                    execution.packedAcc).getD ownerIndex ⟨"", "", default, "", false⟩ =
                  (sceneBoxesExpr execution.params inp o
                    execution.packedAcc)[ownerIndex]'hlt := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
                rfl
              have hmem : (sceneBoxesExpr execution.params inp o
                    execution.packedAcc).getD ownerIndex ⟨"", "", default, "", false⟩ ∈
                  (sceneOf execution.params inp o execution.lines
                    execution.packedAcc execution.measured).boxes := by
                rw [hgetD]
                exact List.getElem_mem _
              have hboxIn := hinset _ hmem
              exact Rect.Contained.trans hboxIn hcontain
        | some title =>
          simp only [Option.map_some, Option.getD_some]
          obtain ⟨stored, hstored, hproduced⟩ :=
            List.mem_filterMap.mp (List.mem_of_find?_eq_some hT)
          obtain ⟨box, _, hproduced⟩ := Option.bind_eq_some_iff.mp hproduced
          have he := Option.some.inj hproduced
          subst title
          let lines := execution.lines.getD stored.1 []
          let width := lines.foldl (fun value line => max value line.width) 0
          let height := (max 1 lines.length : Int) * execution.params.lineH
          let size := match o.direction with
            | .LR | .RL => Size.mk height width
            | .TB | .BT => Size.mk width height
          have hfit := xsclf_packed_title_caption_fit execution stored hstored
          change 0 ≤ size.w ∧ 0 ≤ size.h ∧ size.w ≤ stored.2.w ∧
            size.h ≤ stored.2.h at hfit
          have hstoredB := hacc.titles_bounded stored hstored
          have hrect : 0 ≤ stored.2.x ∧ stored.2.x + size.w ≤
              execution.packedAcc.canvasW ∧
              0 ≤ stored.2.y ∧ stored.2.y + size.h ≤
                execution.packedAcc.canvasH ∧
              0 ≤ size.w ∧ 0 ≤ size.h :=
            ⟨hstoredB.1, by omega, hstoredB.2.2.1, by omega, hfit.1, hfit.2.1⟩
          exact orient_shiftRect_inset_containsCellRect o.direction
            execution.packedAcc.canvasW execution.packedAcc.canvasH
            execution.params.canvasMargin { stored.2 with w := size.w, h := size.h }
            hrect hmargin

/-- Closed exact recursive-step child-label inset: the flat residual above
feeds the fuel induction of `xsgl_stepC8bChildLabelsFit_holds`. -/
theorem xsgl_stepC8bChildLabelsFit_closed (exactIds : List String) :
    XSGL_StepC8bChildLabelsFit exactIds :=
  xsgl_stepC8bChildLabelsFit_holds exactIds (xscl_flatChildLabelsFit_holds exactIds)

end PipelineImpl
end Layered
end Elegant

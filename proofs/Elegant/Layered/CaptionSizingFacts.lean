import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.SizingFacts
import Elegant.Layered.SizingCoverageBridge
import Elegant.Layered.PlainNodeSizingFacts
import Elegant.Layered.GroupFrameSizingFacts
import Elegant.Layered.CaptionWidthFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.PipelineFacts

/-!
# Caption sizing residual

`SceneCaptionSizing` for one executed layered run. The statement is fully
discharged for fixed-size boxes (through `fixed_box_fallback_sizing_of_coverage`,
whose `PipelineImpl.CaptionInputs` premise carries the measured fixed-caption
fit), for ordinary nonfixed node boxes (through the coverage lemmas), and for
nonfixed group boxes whose per-index caption clause is supplied as evidence.
The remaining nonfixed-group bounds (`2 * clusterPad ≤ box.rect.w` and the
LR/RL caption height) depend on the border-bracket reconstruction in
`GroupWidthFacts` (`componentRun_border_hull_width_of_layer_configuration`),
which is not yet connected to the executed component fold at the
`SceneExecution` level; the corresponding per-index premise keeps the seam
honest instead of claiming an unproved bound. Fixed-size boxes may be smaller
than their labels; the `FrameCaptionFit` premise inside
`PipelineImpl.CaptionInputs` excludes exactly those fixed entries that cannot
carry their caption, so the node clause holds for every admitted fixed entry.
-/

namespace Elegant.Layered

variable {inp : Input} {o : Options} {res : FamilyResult}

/-- Sufficient inputs for the caption sizing residual of one successful
execution:

* a pinned `SceneExecution` (all fields are equations from one successful
  `layout`),
* the existing `PipelineImpl.CaptionInputs captions inp o` contract (caption
  matching, unique ids, and measured caption fit for every fixed entry),
* for every nonfixed group box, the executed per-index caption clause
  `2 * clusterPad ≤ oriented box width ∧ clusterPad + caption block height ≤
  oriented box height` on the packed rect that `sceneBoxesExpr` will orient. -/
def CaptionInputs (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res),
    ∃ captions : String → String,
      PipelineImpl.CaptionInputs captions inp o ∧
      ∀ (i : Nat) (source : ModelBox), inp.boxes[i]? = some source →
        source.role = .group →
        inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false →
        2 * execution.params.clusterPad ≤
            (PipelineImpl.shiftRect execution.params.canvasMargin
              execution.params.canvasMargin
              (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
                (execution.packedAcc.rects.getD i default))).w ∧
          execution.params.clusterPad +
              (max 1 (execution.lines.getD i []).length : Int) *
              execution.params.lineH ≤
            (PipelineImpl.shiftRect execution.params.canvasMargin
              execution.params.canvasMargin
              (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
                (execution.packedAcc.rects.getD i default))).h

/-- The caption sizing statement for an executed run holds given the caption
input contract and the nonfixed-group per-index clause. -/
theorem sceneCaptionSizing_of_inputs (h : CaptionInputs inp o res) :
    SceneCaptionSizing inp o res := by
  unfold SceneCaptionSizing
  intro execution
  obtain ⟨captions, hcap, hgroupClause⟩ := h execution
  have hpad : 0 ≤ execution.params.clusterPad :=
    execution.parameter_signs.2.1
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have hl := execution.lines_eq
    unfold PipelineImpl.boxLines at hl
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
        (PipelineImpl.mapM_getElem? _ _ _ hl).1
      _ = inp.boxes.length := List.length_zipIdx
  refine ⟨hpad, hlinesLen, ?_⟩
  intro i box hidx
  refine ⟨?_, ?_⟩
  · -- node clause
    intro hroleBox
    have hboxScene : res.scene.boxes[i]? = some box := by
      rw [execution.boxes_eq_map]; exact hidx
    obtain ⟨source, hsource, hboxeq⟩ := execution.box_index_origin hboxScene
    have hroleEq : box.role = source.role.id := by rw [hboxeq]
    have hrect :
        box.rect = PipelineImpl.shiftRect execution.params.canvasMargin
          execution.params.canvasMargin
          (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD i default)) := by
      rw [hboxeq]
    obtain ⟨rect, hrectPacked⟩ := execution.packed_rect_exists
      (List.getElem?_eq_some_iff.mp hsource).1
    have hget : execution.packedAcc.rects.getD i default = rect := by
      obtain ⟨hi, heq⟩ := Array.getElem?_eq_some_iff.mp hrectPacked
      simpa [Array.getD, hi] using heq
    rw [hroleEq] at hroleBox
    cases hc : source.role with
    | group => exact absurd hroleBox (by simp [hc, BoxRole.id])
    | node =>
      simp only [hc, BoxRole.id] at hroleBox
      rw [hrect]
      by_cases hfixedAny : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true
      · obtain ⟨entry, hentry⟩ : ∃ entry,
            inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) = some entry := by
          cases hf : inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) with
          | none =>
            obtain ⟨entry, hmem, hid⟩ := List.any_eq_true.mp hfixedAny
            exact absurd (List.find?_eq_none.mp hf entry hmem) (by rw [hid]; decide)
          | some entry => exact ⟨entry, rfl⟩
        obtain ⟨hnode, -, -⟩ :=
          execution.fixed_box_fallback_sizing_of_coverage hcap execution.parts_coverage
            hboxScene hsource hentry hrectPacked
        rw [hrect] at hnode
        exact hnode
      · have hfixedFalse :
            inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false :=
          Bool.eq_false_iff.mpr hfixedAny
        obtain ⟨ls, hls⟩ : ∃ ls, execution.lines[i]? = some ls := by
          have hi : i < execution.lines.length :=
            hlinesLen ▸ (List.getElem?_eq_some_iff.mp hsource).1
          exact ⟨_, List.getElem?_eq_getElem hi⟩
        obtain ⟨-, hheight⟩ :=
          execution.ordinary_box_line_height hboxScene hsource hc hfixedFalse hls
        rw [hrect] at hheight
        simp only [List.getD_eq_getElem?_getD, hls, Option.getD_some] at ⊢
        exact hheight
  · -- group clause
    intro hroleBox
    have hboxScene : res.scene.boxes[i]? = some box := by
      rw [execution.boxes_eq_map]; exact hidx
    obtain ⟨source, hsource, hboxeq⟩ := execution.box_index_origin hboxScene
    have hroleEq : box.role = source.role.id := by rw [hboxeq]
    have hrect :
        box.rect = PipelineImpl.shiftRect execution.params.canvasMargin
          execution.params.canvasMargin
          (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD i default)) := by
      rw [hboxeq]
    obtain ⟨rect, hrectPacked⟩ := execution.packed_rect_exists
      (List.getElem?_eq_some_iff.mp hsource).1
    have hget : execution.packedAcc.rects.getD i default = rect := by
      obtain ⟨hi, heq⟩ := Array.getElem?_eq_some_iff.mp hrectPacked
      simpa [Array.getD, hi] using heq
    rw [hroleEq] at hroleBox
    cases hc : source.role with
    | node => exact absurd hroleBox (by simp [hc, BoxRole.id])
    | group =>
      simp only [hc, BoxRole.id] at hroleBox
      rw [hrect]
      by_cases hfixedAny : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true
      · obtain ⟨entry, hentry⟩ : ∃ entry,
            inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) = some entry := by
          cases hf : inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) with
          | none =>
            obtain ⟨entry, hmem, hid⟩ := List.any_eq_true.mp hfixedAny
            exact absurd (List.find?_eq_none.mp hf entry hmem) (by rw [hid]; decide)
          | some entry => exact ⟨entry, rfl⟩
        obtain ⟨-, hgroupW, hgroupH⟩ :=
          execution.fixed_box_fallback_sizing_of_coverage hcap execution.parts_coverage
            hboxScene hsource hentry hrectPacked
        rw [hrect] at hgroupW hgroupH
        exact ⟨hgroupW, hgroupH⟩
      · have hfixedFalse :
            inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false :=
          Bool.eq_false_iff.mpr hfixedAny
        obtain ⟨hgroupW, hgroupH⟩ := hgroupClause i source hsource hc hfixedFalse
        refine ⟨hgroupW, ?_⟩
        obtain ⟨nodes, edges, titles, hprepared, hlength, -⟩ :=
          PipelineImpl.measuredGraph_prepared_source execution.graph_eq
        have hlinesSame : nodes.length = execution.lines.length := by
          rw [hlength, hlinesLen]
        have hi : i < nodes.length := by
          rw [hlinesSame]
          exact hlinesLen ▸ (List.getElem?_eq_some_iff.mp hsource).1
        have hpreparedSource :
            (inp.boxes.map fun b =>
              if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
                { b with role := .node } else b)[i]? = some source := by
          simp [List.getElem?_map, hsource, hfixedFalse]
        have hrecord := Compound.prepare_group_title_record
          (inp.boxes.map fun b =>
            if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
              { b with role := .node } else b)
          execution.params.clusterPad titles
          { nodes := nodes, edges := edges, slot := execution.params.slot }
          hi hpreparedSource hc
        rw [← hprepared] at hrecord
        have hcase := execution.group_caption_output_rank_fit hboxScene hsource hrecord rfl
        rw [hrect] at hcase
        cases hd : o.direction with
        | LR =>
          rw [hd] at hgroupH
          exact hgroupH
        | RL =>
          rw [hd] at hgroupH
          exact hgroupH
        | TB =>
          rw [hd] at hcase
          simp only at hcase ⊢
          omega
        | BT =>
          rw [hd] at hcase
          simp only at hcase ⊢
          omega

end Elegant.Layered

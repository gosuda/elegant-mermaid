import Elegant.Layered.ExpandChildChildSceneProof
import Elegant.Layered.ExpandChildFitPerCallProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem rect_dims_of_cell_bounds {canvas : Size} {rect : Rect}
    (h : Size.containsCellRect canvas rect = true) : 0 ≤ rect.w ∧ 0 ≤ rect.h := by
  simp only [Size.containsCellRect, decide_eq_true_iff] at h
  exact ⟨h.2.2.1, h.2.2.2.1⟩

private theorem flat_layout_label_dims {inp : Input} {o : Options} {res : FamilyResult}
    (run : layout inp o = .ok res) :
    ∀ label ∈ res.scene.labels, 0 ≤ label.rect.w ∧ 0 ≤ label.rect.h := by
  obtain ⟨execution⟩ := layout_sceneExecution run
  have boxesBounded := (layout_scene_box_route_bounded_of_success run).2.2.1
  have lineHeight := (checkedParams_sizing_nonneg execution.checked).1
  have boxesEq : res.scene.boxes = sceneBoxesExpr execution.params inp o execution.packedAcc :=
    execution.boxes_eq_map
  intro label member
  rw [execution.scene_eq] at member
  obtain ⟨source, _, emitted⟩ := List.mem_filterMap.mp member
  cases exclusive : inp.boxes.any (fun box => box.id == source.1.owner && box.exclusive) with
  | true => simp only [exclusive, ↓reduceIte] at emitted; cases emitted
  | false =>
    simp only [exclusive, Bool.false_eq_true, ↓reduceIte] at emitted
    cases measuredAt : execution.measured.find? (fun item => item.index == source.2) with
    | some measured =>
      simp only [measuredAt, Option.some.injEq] at emitted
      subst label
      exact rect_dims_of_cell_bounds (execution.measured_rect_bounded measured.index)
    | none =>
      simp only [measuredAt] at emitted
      cases ownerAt : inp.boxes.findIdx?
          (fun box => box.id == source.1.owner && !box.exclusive) with
      | none => simp only [ownerAt] at emitted; cases emitted
      | some ownerIndex =>
        simp only [ownerAt, Option.some.injEq] at emitted
        subst label
        let rect := sceneCaptionRect execution.params inp o execution.lines
          execution.packedAcc ownerIndex source.1.owner
        change 0 ≤ rect.w ∧ 0 ≤ rect.h
        simp only [rect, sceneCaptionRect]
        cases titleAt : (sceneTitlesExpr execution.params inp o execution.lines
            execution.packedAcc).find? (fun title => title.1 == source.1.owner) with
        | some title =>
          simp only [Option.map_some, Option.getD_some]
          exact rect_dims_of_cell_bounds
            (execution.scene_titles_bounded title (List.mem_of_find?_eq_some titleAt))
        | none =>
          simp only [Option.map_none, Option.getD_none, ← boxesEq]
          let box := res.scene.boxes.getD ownerIndex ⟨"", "", default, "", false⟩
          let lines := execution.lines.getD ownerIndex []
          change 0 ≤ (ownedTextRect execution.params box lines).w ∧
            0 ≤ (ownedTextRect execution.params box lines).h
          unfold ownedTextRect
          split
          · unfold titleRect
            exact ⟨Int.le_max_left _ _, Int.mul_nonneg (by omega) lineHeight⟩
          · have width : 0 ≤ box.rect.w := by
              dsimp only [box]
              rw [List.getD_eq_getElem?_getD]
              cases hget : res.scene.boxes[ownerIndex]? with
              | none => exact Int.le_refl 0
              | some actual =>
                exact (rect_dims_of_cell_bounds (boxesBounded (actual, ownerIndex)
                  (List.mem_zipIdx_iff_getElem?.mpr hget))).1
            exact ⟨width, Int.mul_nonneg (Int.natCast_nonneg _) lineHeight⟩

private theorem title_width_nonneg (lines : List Measure.Line) (width : Int)
    (hwidth : 0 ≤ width) : 0 ≤ lines.foldl (fun w line => max w line.width) width := by
  induction lines generalizing width with
  | nil => exact hwidth
  | cons line lines ih => exact ih _ (Int.le_trans hwidth (Int.le_max_left _ _))

/-- Every label emitted by a successful recursive layout has nonnegative dimensions,
including fallback captions, even when the input lacks fixed-size fit. -/
theorem layoutRecursive_label_dims (fuel : Nat) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult},
      layoutRecursive fuel inp o = .ok res →
      ∀ label ∈ res.scene.labels, 0 ≤ label.rect.w ∧ 0 ≤ label.rect.h := by
  induction fuel with
  | zero =>
    intro inp o res run
    exact flat_layout_label_dims run
  | succ fuel ih =>
    intro inp o res run label member
    rcases layoutRecursive_succ_sources run with ⟨_, hflat⟩ |
      ⟨group, P, metric, child, titleLines, parent, _, hP, hm, hchild, hwrap, hparent, hexpand⟩
    · exact flat_layout_label_dims hflat label member
    · obtain ⟨frame, actualMetric, actualLines, _, dx, dy, frameAt, hmetric, hlines,
        _, hdx, hdy, _, _⟩ := expandChild_sources hexpand
      have metricEq := Except.ok.inj (hmetric.symm.trans hm)
      subst actualMetric
      have linesEq := Except.ok.inj (hlines.symm.trans hwrap)
      subst actualLines
      rw [expandChild_labels_eq_wrapped hexpand frame titleLines dx dy frameAt hdx hdy
        ⟨metric, hm, hwrap⟩] at member
      obtain ⟨model, _, hbind⟩ := List.mem_filterMap.mp member
      obtain ⟨placed, found, emitted⟩ := Option.bind_eq_some_iff.mp hbind
      have heq := Option.some.inj emitted
      split at heq
      · rw [← heq]
        have width := title_width_nonneg titleLines 0 (Int.le_refl 0)
        have height : 0 ≤ (max 1 titleLines.length : Int) * P.lineH :=
          Int.mul_nonneg (by omega) (checkedParams_sizing_nonneg hP).1
        let caption := childTitleRect group.direction P.clusterPad
          (titleLines.foldl (fun w line => max w line.width) 0)
          ((max 1 titleLines.length : Int) * P.lineH) frame.rect
        change 0 ≤ caption.w ∧ 0 ≤ caption.h
        dsimp only [caption]
        unfold childTitleRect
        split <;> exact ⟨width, height⟩
      · rw [← heq]
        rcases List.mem_append.mp (List.mem_of_find?_eq_some found) with fromChild | fromParent
        · obtain ⟨source, sourceMember, shifted⟩ := List.mem_map.mp fromChild
          rw [← shifted]
          exact ih hchild source sourceMember
        · exact ih hparent placed fromParent

/-- The positive conjunction negated by `ExecutedParentFrameObstruction.childLabel`.
Only containment uses top-level fixed-size fit; both dimensions come from execution. -/
theorem expandChild_child_labels_fit_of_top
    {root : Input} {options : Options} {fuel : Nat} {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (htop : InputFixedFit root options) (reached : FitReached root options inp o)
    (ctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
    (params : ExpandChildCallParams P inp o group titleLines titleHeight)
    (framed : framedParents inp = true) {label : SceneLabel} (member : label ∈ child.scene.labels) :
    (insetRect child.scene.canvas P.canvasMargin).Contained label.rect ∧
      0 ≤ label.rect.w ∧ 0 ≤ label.rect.h := by
  have hinset := expandChild_child_labels_inset fuel P inp o group titleLines titleHeight
    parent child res ctx.2.2.2.2.2 framed (fitPerCall_of_top htop reached) ctx params.1 label member
  exact ⟨hinset, layoutRecursive_label_dims fuel ctx.2.2.2.1 label member⟩

end Elegant.Layered.PipelineImpl

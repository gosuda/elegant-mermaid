import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.CaptionWidthFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SelectFacts
import Elegant.Layered.RecursiveC6
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.RecursiveCallParams

set_option autoImplicit false

/-!
# Canvas fit of the recursive group expansion

Anchor: Tony Hoare, Edsger W. Dijkstra.

For one `expandChild` call the recursion performs, with the frame and shift
binders used in the statements below:

(a) The non-strict whole-canvas fit
`frame.rect.Contained (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump))`
is FALSE as stated. The shift is `dx = frame.x + inset.x - margin`, so the
first containment conjunct `frame.x ≤ dx` is exactly
`P.canvasMargin ≤ (childInset group.direction P.clusterPad width titleHeight).x`,
independent of the frame size. It fails whenever the margin exceeds the inset
padding on an axis. In particular the vector profile gives
`diagram_padding` 1280 (`vector.usecase.diagram_padding`) against
`cluster_pad` 1024, so every executed usecase-vector call with a non-`"LR"`
group has `dx = frame.x - 256 < frame.x`; the `example` at the end witnesses
the failure at exactly those table numbers with the frame at precisely the
reserved `childFrameSize`. No frame-size fact can save it.

(b) The strict content fit `expandChild_content_fit_strict` below IS true and
is proved here: every rect inside the child canvas shrunk by `P.canvasMargin`
on all four sides (the size `parentSubInput` hands to `childFrameSize`) lands
strictly inside the group frame. The margin cancels in the shift, so only the
inset padding, the title sizes, and the frame reservation matter.
-/

namespace Elegant.Layered.PipelineImpl

/-- Positivity of the cluster pad from the checked parameters of an executed
call, via the existing table lemma. -/
theorem callParams_clusterPad_pos {o : Options} {inp : Input} {P : Params}
    (h : checkedParams o.profile inp.kind = .ok P) : 0 < P.clusterPad :=
  checkedParams_clusterPad_pos h

/-- Positivity of the line height from the checked parameters of an executed
call, via the existing table lemma. -/
theorem callParams_lineH_pos {o : Options} {inp : Input} {P : Params}
    (h : checkedParams o.profile inp.kind = .ok P) : 0 < P.lineH :=
  checkedParams_lineH_pos h

/-- The canvas margin is at least one from the checked parameters of an
executed call, via the existing table lemma. -/
theorem callParams_canvasMargin_pos {o : Options} {inp : Input} {P : Params}
    (h : checkedParams o.profile inp.kind = .ok P) : 1 ≤ P.canvasMargin :=
  checkedParams_canvasMargin_ge_one h

/-- Arithmetic core of the strict content fit: a frame dominating the
`childFrameSize` reservation strictly contains the shifted margin-shrunk
canvas. The margin cancels in the shift (`dx + margin = frame.x + inset.x`),
so no `margin ≤ pad` premise is needed; only positivity of the pad and
nonnegativity of the title sizes. Pure arithmetic over the direction arms. -/
theorem childInsetContent_strict {direction : String}
    {pad titleWidth titleHeight margin cw ch fw fh fx fy : Int}
    (hpad : 0 < pad) (htw : 0 ≤ titleWidth) (hth : 0 ≤ titleHeight)
    (hfw : (childFrameSize direction pad titleWidth titleHeight
      ⟨cw - 2 * margin, ch - 2 * margin⟩).w ≤ fw)
    (hfh : (childFrameSize direction pad titleWidth titleHeight
      ⟨cw - 2 * margin, ch - 2 * margin⟩).h ≤ fh) :
    (⟨fx, fy, fw, fh⟩ : Rect).StrictInside
      (shiftRect (fx + (childInset direction pad titleWidth titleHeight).x - margin)
        (fy + (childInset direction pad titleWidth titleHeight).y - margin)
        ⟨margin, margin, cw - 2 * margin, ch - 2 * margin⟩) := by
  unfold childInset shiftRect Rect.StrictInside
  unfold childFrameSize at hfw hfh
  split <;> split at hfw <;> split at hfh <;> simp_all <;> omega

/-- Frame reservation of an executed call, stated at the quantified wrapped
title lines: the located group frame dominates the `childFrameSize` the
recursion stored in the parent sub-input's `fixedSizes`. The quantified lines
are identified with the call context lines through the wrapped-title
equations; the fixed-source minimum then applies. Consumed by the title band
worker as well as the content fit below. -/
theorem expandChild_frame_size_bounds
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (frame : Box) (titleLines' : List Measure.Line)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hwrap' : ExpandChildTitleWrapped P inp o group titleLines') :
    (childFrameSize group.direction P.clusterPad
      (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).w ≤ frame.rect.w ∧
    (childFrameSize group.direction P.clusterPad
      (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).h ≤ frame.rect.h := by
  obtain ⟨_, hheightEq, hwrapCtx⟩ := hparams
  obtain ⟨metric, hmetric, hwrapEq⟩ := hwrapCtx
  obtain ⟨metric', hmetric', hwrapEq'⟩ := hwrap'
  have hmetricEq : metric' = metric := Except.ok.inj (hmetric'.symm.trans hmetric)
  subst hmetricEq
  have htlEq : titleLines' = titleLines := Except.ok.inj (hwrapEq'.symm.trans hwrapEq)
  subst titleLines'
  obtain ⟨hwf, hgroup, _hpboxes, _hchild, hparent, _hexpand'⟩ := hctx
  have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hcovered : RoutesCovered inp := inputRoutesCovered hwf
  have hparentCovered : RoutesCovered (parentSubInput inp group P titleLines child) := by
    change RoutesCovered
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id))
    exact selectInput_routesCovered inp _ ""
  have hparentIds :
      ((parentSubInput inp group P titleLines child).boxes.map (·.id)).Nodup := by
    change ((selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id)).boxes.map (·.id)).Nodup
    rw [selectInput_box_ids]
    exact List.Nodup.sublist ((List.filter_sublist).map _) hboxIds
  have hparentOutputIds := (layoutRecursive_ids (fun _ _ _ h => layout_ids h)
    fuel (parentSubInput inp group P titleLines child) o parent hparentCovered hparent).1
  have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
  have hparentSourceId : group.id ∈
      (parentSubInput inp group P titleLines child).boxes.map (·.id) := by
    rw [← hparentOutputIds, ← hframeId]
    exact List.mem_map.mpr ⟨frame, List.mem_of_find?_eq_some hframe, rfl⟩
  obtain ⟨source, hsource, hsourceId⟩ := List.mem_map.mp hparentSourceId
  have hnotfixed : inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
    have hs := List.find?_some hgroup
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
    exact hs.2
  have hnone : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hnotfixed)
  let size := childFrameSize group.direction P.clusterPad
    (titleLines.foldl (fun width line => max width line.width) 0)
    ((max 1 titleLines.length : Int) * P.lineH)
    ⟨child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩
  have hfixed : (parentSubInput inp group P titleLines child).fixedSizes.find?
      (fun fixed => fixed.1 == source.id) = some (group.id, size) := by
    change (inp.fixedSizes ++ [(group.id, size)]).find?
      (fun fixed => fixed.1 == source.id) = some (group.id, size)
    simp [List.find?_append, hsourceId, hnone]
  obtain ⟨actual, hactual, _, hw, hh⟩ :=
    layoutRecursive_fixed_source_box_minimum_dimensions_with_role fuel
      hparentIds hparentCovered hparent hsource hfixed
  rw [hsourceId] at hactual
  have hactualEq : actual = frame := Option.some.inj (hactual.symm.trans hframe)
  subst actual
  have hw' : (childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).w ≤ frame.rect.w := by
    have hw'' : (childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩).w ≤ frame.rect.w := hw
    rw [← hheightEq] at hw''
    exact hw''
  have hh' : (childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).h ≤ frame.rect.h := by
    have hh'' : (childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩).h ≤ frame.rect.h := hh
    rw [← hheightEq] at hh''
    exact hh''
  exact ⟨hw', hh'⟩

/-- Strict content fit of an executed `expandChild` call: every rect inside
the child canvas shrunk by `P.canvasMargin` on all four sides (the size the
parent sub-input hands to `childFrameSize`) lands strictly inside the group
frame. The quantified title lines are identified with the call context lines
through the wrapped-title equations, the frame reservation comes from the
fixed-size entry, and the margin cancels in the shift. -/
theorem expandChild_content_fit_strict
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines' →
    ∀ (r : Rect),
    (⟨P.canvasMargin, P.canvasMargin, child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained r →
    frame.rect.StrictInside (shiftRect dx dy r) := by
  intro frame titleLines' dx dy hframe hdx hdy hwrap' r hr
  obtain ⟨hw, hh⟩ := expandChild_frame_size_bounds fuel P inp o group titleLines
    titleHeight parent child res _hexpand _hframed hctx hparams frame titleLines'
    hframe hwrap'
  obtain ⟨hP, hheightEq, _hwrapCtx⟩ := hparams
  have hpad : 0 < P.clusterPad := callParams_clusterPad_pos hP
  have htw : 0 ≤ titleLines'.foldl (fun width line => max width line.width) 0 := by
    suffices key : ∀ (ls : List Measure.Line) (acc : Int), 0 ≤ acc →
        0 ≤ ls.foldl (fun width line => max width line.width) acc by
      exact key titleLines' 0 (by omega)
    intro ls acc hac
    induction ls generalizing acc with
    | nil => simpa using hac
    | cons line ls ih =>
      simp only [List.foldl_cons]
      exact ih _ (Int.le_trans hac (Int.le_max_left _ _))
  have hth : 0 ≤ titleHeight := by
    rw [hheightEq]
    exact Int.mul_nonneg (by omega)
      (Int.le_of_lt (callParams_lineH_pos hP))
  have hS : frame.rect.StrictInside
      (shiftRect dx dy ⟨P.canvasMargin, P.canvasMargin,
        child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩) := by
    rw [hdx, hdy]
    exact childInsetContent_strict hpad htw hth hw hh
  have hshift : (shiftRect dx dy ⟨P.canvasMargin, P.canvasMargin,
      child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩).Contained (shiftRect dx dy r) :=
    (contained_shiftRect dx dy).mpr hr
  unfold Rect.StrictInside at hS ⊢
  unfold Rect.Contained at hshift
  omega

/-- Witness for (a): at the vector usecase table numbers
(`diagram_padding` 1280 against `cluster_pad` 1024, direction `"TB"`, empty
title, child canvas 2000 by 1000, frame at exactly the reserved
`childFrameSize` 2048 by 488) the shifted whole canvas starts at `x = -256`,
outside the frame. The failure is in the first containment conjunct and uses
nothing about the frame size. -/
example : ¬ ((⟨0, 0, 2048, 488⟩ : Rect).Contained
    (shiftRect (0 + (childInset "TB" 1024 0 0).x - 1280)
      (0 + (childInset "TB" 1024 0 0).y - 1280)
      (Validator.canvasRect ⟨⟨2000, 1000⟩, [], [], []⟩))) := by
  decide

end Elegant.Layered.PipelineImpl

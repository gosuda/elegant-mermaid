import Elegant.Layered.ExpandChildC6GeometryProof
import Elegant.Layered.ExpandChildCanvasFitProof
import Elegant.Layered.ExpandChildChildSceneProof
import Elegant.Layered.ExpandChildFrameLiftProof
import Elegant.Layered.ExpandChildFrameLiftResiduals
import Elegant.Layered.ExpandChildParentFrameProof
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.ExpandChildAncestryProof
import Elegant.Layered.ExactStepFacts
import Elegant.Layered.RecursiveStepFacts
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams

set_option autoImplicit false

/-!
# Executed C6 geometry, restated at the child inset

`expandChild_c6_geometry` (`ExpandChildC6GeometryProof`) is false as stated:
its whole-canvas hypotheses (`hFitStrict`, `hChild`) fail because the child
canvas starts one margin before the true content inset
(`ExpandChildC7GeometryProof` records the same whole-canvas failure, and
`ExpandChildCanvasFitProof` proves the strict content fit for the inset
rect). This module proves the same `ExpandChildC6Geometry` conclusion from
the true inset forms, discharging every base-independent premise inline:

* `hFit`: the inset content fit `expandChild_content_fit_strict`;
* `hBox` / `hRt`: the inset bounds `expandChild_child_boxes_inset` and
  `expandChild_child_routes_inset` (labels are not needed for C6);
* `hPos`: the frame reservation `expandChild_frame_size_bounds` plus
  positivity of the reserved `childFrameSize`.

Two strictly narrower, probe-tested residuals remain as hypotheses of the
plain theorem: the parent scene satisfies C8a (`hC8aParent`, validator form
of the smaller-fuel clause), and parent routes clear the group frame
(`hRouteClear : ExpandChildParentRouteClear group parent`). The `B` twin
takes the same six per-call facts in `ExpandChildCallContextB` form.
-/

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- The located frame carries the group id. -/
private theorem stepC6_frame_id_eq {group : ModelBox} {parent : FamilyResult}
    {frame : Box}
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame) :
    frame.id = group.id := by
  simpa using List.find?_some hframe

/-- Inset restatement of `expandChild_c6_geometry`: the whole-canvas
containment hypotheses are replaced by the margin-inset forms, which hold
for every executed call. Pure rectangle glue over the six premises. -/
theorem expandChild_c6_geometry_inset
    (_fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (_titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hFit : ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group titleLines' →
      ∀ (r : Rect),
      (insetRect child.scene.canvas P.canvasMargin).Contained r →
      frame.rect.StrictInside (shiftRect dx dy r))
    (hBox : ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect)
    (hRt : ∀ cr ∈ child.scene.routes, ∀ p ∈ cr.points,
      PointIn (insetRect child.scene.canvas P.canvasMargin) p)
    (hDisj : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
        pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
        Disjoint frame.rect pb.rect)
    (hMiss : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pr ∈ parent.scene.routes, ∀ (r : Rect), frame.rect.StrictInside r →
        ¬ Polyline.hitsRect pr.points r)
    (hPos : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      0 < frame.rect.w ∧ 0 < frame.rect.h) :
    ExpandChildC6Geometry P inp o group titleHeight parent child res := by
  intro frame tl dx dy hframe hdx hdy hwrap
  have hfitS : ∀ (r : Rect), (insetRect child.scene.canvas P.canvasMargin).Contained r →
      frame.rect.StrictInside (shiftRect dx dy r) :=
    hFit frame tl dx dy hframe hdx hdy hwrap
  obtain ⟨hfw, hfh⟩ := hPos frame hframe
  have ha : ∀ cr ∈ child.scene.routes, ∀ pb ∈ parent.scene.boxes,
      pb.exclusive = true →
      pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
      ¬ Polyline.hitsRect (cr.points.map (shiftPoint dx dy)) pb.rect := by
    intro cr hcr pb hpb hex hscope
    have hconf : ∀ p ∈ cr.points.map (shiftPoint dx dy), PointIn frame.rect p := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hqI := hRt cr hcr q hq
      have hqs : PointIn (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin))
          (shiftPoint dx dy q) :=
        pointIn_shift hqI
      have hSI := hfitS _ (Rect.Contained.refl _)
      have hC : frame.rect.Contained
          (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) := by
        simp only [Rect.StrictInside, Rect.Contained] at hSI ⊢
        omega
      have hdeg := pointIn_contained.mp hqs
      exact pointIn_contained.mpr (Rect.Contained.trans hC hdeg)
    have hdisj := hDisj frame hframe pb hpb hex hscope
    exact polyline_in_box_misses_disjoint hfw hfh hconf hdisj
  have hb : ∀ pr ∈ parent.scene.routes, ∀ cb ∈ child.scene.boxes,
      cb.exclusive = true →
      ¬ Polyline.hitsRect pr.points (shiftRect dx dy cb.rect) := by
    intro pr hpr cb hcb hex
    have hcbI := hBox cb hcb
    have hinner : frame.rect.StrictInside (shiftRect dx dy cb.rect) :=
      hfitS _ hcbI
    exact hMiss frame hframe pr hpr (shiftRect dx dy cb.rect) hinner
  exact ⟨ha, hb⟩

/-- Frame positivity for an executed call: the located group frame dominates
the reserved `childFrameSize`, which is positive from the pad, title, and
canvas-margin bounds. -/
private theorem stepC6_frame_pos
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      0 < frame.rect.w ∧ 0 < frame.rect.h := by
  intro frame hframe
  have hP : checkedParams o.profile inp.kind = .ok P := hparams.1
  have hheightEq : titleHeight = (max 1 titleLines.length : Int) * P.lineH :=
    hparams.2.1
  have hwrapCtx : ExpandChildTitleWrapped P inp o group titleLines := hparams.2.2
  have hchild : layoutRecursive fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child := hctx.2.2.2.1
  have htw : 0 ≤ titleLines.foldl (fun width line => max width line.width) 0 := by
    suffices key : ∀ (ls : List Measure.Line) (acc : Int), 0 ≤ acc →
        0 ≤ ls.foldl (fun width line => max width line.width) acc by
      exact key titleLines 0 (by omega)
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
  have hpad : 0 < P.clusterPad := callParams_clusterPad_pos hP
  have hcm := layoutRecursive_canvas_margins fuel hchild
  have hcw : 2 * P.canvasMargin ≤ child.scene.canvas.w := by
    rw [checkedParams_canvasMargin hP]
    exact hcm.1
  have hch : 2 * P.canvasMargin ≤ child.scene.canvas.h := by
    rw [checkedParams_canvasMargin hP]
    exact hcm.2
  have hposS : 0 < (childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).w ∧
      0 < (childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).h := by
    unfold childFrameSize
    split <;> refine ⟨?_, ?_⟩ <;> dsimp only <;> omega
  obtain ⟨hw, hh⟩ := expandChild_frame_size_bounds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctx hparams frame titleLines
    hframe hwrapCtx
  omega

/-- The per-expansion C6 geometry holds for every executed call, modulo the
two strictly narrower parent-scene residuals: parent C8a (`hC8aParent`) and
parent route clearance (`hRouteClear`). -/
theorem stepC6Geometry_holds
    (hC8aParent : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      Validator.C8a parent.scene.layoutDump)
    (hRouteClear : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentRouteClear group parent) :
    RecursiveStepFacts ExpandChildC6Geometry := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams
  have hP : checkedParams o.profile inp.kind = .ok P := hparams.1
  have hFit : ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
          (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin →
      ExpandChildTitleWrapped P inp o group titleLines' →
      ∀ (r : Rect),
      (insetRect child.scene.canvas P.canvasMargin).Contained r →
      frame.rect.StrictInside (shiftRect dx dy r) := by
    intro frame tl' dx dy hframe hdx hdy hwrap' r hr
    exact expandChild_content_fit_strict fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx hparams frame tl' dx dy hframe hdx hdy
      hwrap' r hr
  have hBox : ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect := by
    intro cb hcb
    exact expandChild_child_boxes_inset fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx hP cb hcb
  have hRt : ∀ cr ∈ child.scene.routes, ∀ p ∈ cr.points,
      PointIn (insetRect child.scene.canvas P.canvasMargin) p := by
    intro cr hcr p hp
    exact expandChild_child_routes_inset fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx hP cr hcr p hp
  have hPos := stepC6_frame_pos fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hparams
  have hC8a := hC8aParent fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams
  have hanc := stepC8aAncestry_holds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hparams
  have hDisj : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
        pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
        Disjoint frame.rect pb.rect := by
    intro frame hframe pb hpb hex hscope
    obtain ⟨_, _, _, _, hrole, _, _, hiso⟩ :=
      expandChild_c8a_structure fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx hanc frame titleLines _ _ hframe rfl rfl hparams.2.2
    have hfid := stepC6_frame_id_eq hframe
    have hframeMem : frame ∈ parent.scene.layoutDump.boxes :=
      List.mem_of_find?_eq_some hframe
    have hpbMem : pb ∈ parent.scene.layoutDump.boxes := hpb
    have hne' : pb.id ≠ group.id := by
      intro h
      apply hscope
      rw [h]
      exact List.mem_cons.mpr (Or.inl rfl)
    have hne : pb.id ≠ frame.id := by
      rw [hfid]
      exact hne'
    have h1 : frame.id ∉ parent.scene.layoutDump.ancestors pb.id := by
      rw [hfid]
      exact hiso pb hpb hne'
    have h2 : pb.id ∉ parent.scene.layoutDump.ancestors frame.id := by
      rw [hfid]
      exact fun hm => hscope (List.mem_cons.mpr (Or.inr hm))
    exact hC8a frame hframeMem hrole pb hpbMem hne h1 h2
  have hrc := hRouteClear fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams
  have hMiss : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pr ∈ parent.scene.routes, ∀ (r : Rect), frame.rect.StrictInside r →
        ¬ Polyline.hitsRect pr.points r := by
    intro frame hframe pr hpr r hSI
    exact expandChild_parentFrame_routes hrc hexpand hframed hctx frame titleLines _ _
      hframe rfl rfl hparams.2.2 pr hpr r hSI
  exact expandChild_c6_geometry_inset fuel P inp o group titleLines titleHeight
    parent child res hFit hBox hRt hDisj hMiss hPos

/-- `B` twin of `stepC6Geometry_holds`: the inset glue is base-independent,
so at any `base` the same conclusion follows from the same six per-call
facts stated over `ExpandChildCallContextB base`. -/
theorem stepC6Geometry_holdsB (base : Input → Options → Except LayoutError FamilyResult)
    (hFitB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
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
      (insetRect child.scene.canvas P.canvasMargin).Contained r →
      frame.rect.StrictInside (shiftRect dx dy r))
    (hBoxB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect)
    (hRtB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ∀ cr ∈ child.scene.routes, ∀ p ∈ cr.points,
      PointIn (insetRect child.scene.canvas P.canvasMargin) p)
    (hDisjB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
        pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
        Disjoint frame.rect pb.rect)
    (hMissB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pr ∈ parent.scene.routes, ∀ (r : Rect), frame.rect.StrictInside r →
        ¬ Polyline.hitsRect pr.points r)
    (hPosB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      0 < frame.rect.w ∧ 0 < frame.rect.h) :
    RecursiveStepFactsB base ExpandChildC6Geometry := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
  exact expandChild_c6_geometry_inset fuel P inp o group titleLines titleHeight
    parent child res
    (hFitB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)
    (hBoxB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)
    (hRtB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)
    (hDisjB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)
    (hMissB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)
    (hPosB fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctxB hparams)

end PipelineImpl
end Layered
end Elegant

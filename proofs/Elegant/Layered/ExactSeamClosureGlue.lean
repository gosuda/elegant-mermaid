import Elegant.Layered.ExactStepGeometryProof
import Elegant.Layered.ExpandChildC7GeometryProof
import Elegant.Layered.RecursiveBEq
import Elegant.Layered.ExpandChildStructureFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact seam closure glue: named step-geometry residuals.

The three `stepC*Geometry_layoutX` assemblers
(`ExactStepGeometryProof.lean`) take their open per-call premises as anonymous
`∀`-types. `Kinds/UsecaseValidExact.lean` needs strictly narrower PUBLIC named
defs for those premises, so they are named here, copied verbatim from the
theorem binders (each carries the local `framedParents` premise and the local
`WellFormed` fact inside `ExpandChildCallContextB`). Premises already proved in
`ExactStepGeometryProof.lean` (`XG_child_boxes_insetB`, `XG_frame_posB`,
`XG_child_routes_insetB`, `XG_content_fit_strict`) or closed elsewhere
(`stepC6Anchors_layoutX`, `stepC8aAncestry_layoutX`, both
`ExactStepShortFacts.lean`) are discharged at the use site, not renamed here;
the `XG_C8bCoreB` inset core is already a named def and is reused directly.
-/

/-- Open C6 residual: the located group frame misses every foreign exclusive
parent box. Verbatim copy of `hDisjB` in `stepC6Geometry_layoutX`. -/
def XG_StepC6DisjB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
      pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
      Disjoint frame.rect pb.rect

/-- Open C6 residual: no parent route hits any rect strictly inside the
located group frame. Verbatim copy of `hMissB` in `stepC6Geometry_layoutX`. -/
def XG_StepC6MissB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pr ∈ parent.scene.routes, ∀ (r : Rect), frame.rect.StrictInside r →
      ¬ Polyline.hitsRect pr.points r

/-- Open C7 residual: shifted child boxes and labels lie in the located group
frame. Verbatim copy of `hchildB` in `stepC7Geometry_layoutX`. -/
def XG_StepC7ChildB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC7ChildInside P inp o group titleHeight parent child

/-- Open C7 residual: the located group frame is clear of foreign parent boxes
and parent labels. Verbatim copy of `hparentB` in `stepC7Geometry_layoutX`. -/
def XG_StepC7ParentB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC7ParentClear P inp o group titleHeight parent

/-- Open C7 residual: group-owned result labels fit the title band clear of
exclusive child boxes. Verbatim copy of `hcaptionB` in
`stepC7Geometry_layoutX`. -/
def XG_StepC7CaptionB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC7CaptionFit P inp o group titleHeight parent child res

/-- Open C8b residual: child labels lie in the margin inset of the child
canvas. Verbatim copy of `hChildLabelsB` in `stepC8bGeometry_layoutX` (the
companion box fact is the proved `XG_child_boxes_insetB`). -/
def XG_StepC8bChildLabelsB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ∀ cl ∈ child.scene.labels,
      (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect

/-- Open C8b residual: the C8 title rect misses the shifted child margin
inset. Verbatim copy of `hCapDisjB` in `stepC8bGeometry_layoutX`. -/
def XG_StepC8bCapDisjB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
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
    Disjoint (groupTitleRectC8 group P titleLines' titleHeight frame)
      (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin))
/-- Open C8b residual: the located group frame strictly contains the shifted
C8 title rect. Verbatim copy of `hCapStrictB` in `stepC8bGeometry_layoutX`. -/
def XG_StepC8bCapStrictB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
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
    frame.rect.StrictInside (groupTitleRectC8 group P titleLines' titleHeight frame)

/-- Open C8b residual: the exact call preserves the parent frame placement.
Verbatim copy of `hParentFrameB` in `stepC8bGeometry_layoutX`. -/
def XG_StepC8bParentFrameB (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
      parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildParentFrame P inp o group titleHeight parent child

/-- Discharged C8b premise: the child margin inset lands strictly inside the
located group frame. Specialization of the proved `XG_content_fit_strict` to
the inset rect itself (via `Contained.refl`), matching `hFitStrictB` in
`stepC8bGeometry_layoutX` so the use site needs no extra field. -/
theorem XG_fitStrictB_of_content (exactIds : List String) :
    ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB (layoutX exactIds) fuel P inp o group titleLines titleHeight
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
      frame.rect.StrictInside
        (shiftRect dx dy (insetRect child.scene.canvas P.canvasMargin)) := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams frame titleLines' dx dy hframe hdx hdy hwrap
  have hr : (⟨P.canvasMargin, P.canvasMargin,
      child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained
      (insetRect child.scene.canvas P.canvasMargin) := by
    unfold insetRect
    exact Rect.Contained.refl _
  exact XG_content_fit_strict exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams frame titleLines' dx dy
    hframe hdx hdy hwrap _ hr

end PipelineImpl
end Layered
end Elegant

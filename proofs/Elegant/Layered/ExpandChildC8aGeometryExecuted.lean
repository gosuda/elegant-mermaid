import Elegant.Layered.ExpandChildStepsFacts
import Elegant.Layered.RecursiveStepFacts
import Elegant.Layered.ExpandChildC8GeometryProof
import Elegant.Layered.ExpandChildCanvasFitProof
import Elegant.Layered.ExpandChildChildSceneProof
import Elegant.Layered.RecursiveBEq

set_option autoImplicit false

/-!
# Executed-call C8a geometry: shifted child boxes lie in the group frame

`expandChild_c8a_geometry` (`ExpandChildC8GeometryProof.lean`) discharges the
C8a remainder from two whole-canvas hypotheses: `ExpandChildCanvasFit` (the
shifted child canvas is strictly inside the frame) and `ExpandChildChildScene`
(every child box is in the child canvas). Both are false as stated: the
shifted whole canvas starts one margin before the inset content the frame
was reserved for.

The true inset forms are proved: `expandChild_content_fit_strict`
(`ExpandChildCanvasFitProof.lean`) puts every rect inside the shrunk canvas
strictly inside the frame, and `expandChild_child_boxes_inset`
(`ExpandChildChildSceneProof.lean`) puts every child box in the margin inset
of the child canvas. This file composes them through the shift: the child box
is contained in the inset content, the shifted inset content is strictly
inside the frame, and strict containment weakens to containment.

The rectangle core is context-free and shared by both forms. The plain form
closes `RecursiveStepFacts ExpandChildC8aGeometry` outright. The `B` form
cannot reuse the plain inset lemmas: they consume the plain
`ExpandChildCallContext` (successful `layoutRecursive` calls), while a
`base`-parametric call provides `layoutRecursiveB base` successes instead.
The `B` theorem therefore takes exactly the two `base`-stage facts as
hypotheses; both are strictly narrower than the target (one pipeline stage
each). Its conclusion is stated as the unfolding of `RecursiveStepFactsB`
(`ExactStepFacts.lean` defines that abbrev, which this leaf does not import
to keep the dependency direction acyclic), so it is definitionally that
proposition and applies wherever the abbrev is expected.
-/

namespace Elegant.Layered.PipelineImpl

/-- Rectangle core of the C8a step: content contained in a box whose shift
lands strictly inside a frame is itself contained in the frame after the
shift. -/
theorem c8a_frame_contained_shifted
    {frame content cb : Rect} {dx dy : Int}
    (hfit : ∀ r : Rect, content.Contained r → frame.StrictInside (shiftRect dx dy r))
    (hmem : content.Contained cb) :
    frame.Contained (shiftRect dx dy cb) := by
  have h := hfit cb hmem
  simp only [Rect.StrictInside, Rect.Contained, shiftRect] at h ⊢
  omega

/-- Executed-call C8a geometry: every shifted child box lies in the located
group frame. The child box is contained in the inset content
(`expandChild_child_boxes_inset`), the shifted inset content is strictly
inside the frame (`expandChild_content_fit_strict`), and the core above
composes them. -/
theorem stepC8aGeometry_holds : RecursiveStepFacts ExpandChildC8aGeometry := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctx hparams
  have hchild := expandChild_child_boxes_inset fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hparams.1
  intro frame tl dx dy hframe hdx hdy hwrap cb hcb
  have hr : (⟨P.canvasMargin, P.canvasMargin, child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained cb.rect := by
    simpa [insetRect] using hchild cb hcb
  have hfit := expandChild_content_fit_strict fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hparams frame tl dx dy hframe hdx hdy hwrap
  exact c8a_frame_contained_shifted hfit hr

/-- `B` twin of `stepC8aGeometry_holds` at an arbitrary base: the same
composition, with the two `base`-stage facts (`hfitB` for the frame
reservation, `hchildB` for the child inset) as hypotheses. -/
theorem stepC8aGeometry_holdsB
    (base : Input → Options → Except LayoutError FamilyResult)
    (hfitB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ∀ (frame : Box) (tl : List Measure.Line) (dx dy : Int),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      dx = frame.rect.x + (childInset group.direction P.clusterPad
        (tl.foldl (fun width line => max width line.width) 0) titleHeight).x - P.canvasMargin →
      dy = frame.rect.y + (childInset group.direction P.clusterPad
        (tl.foldl (fun width line => max width line.width) 0) titleHeight).y - P.canvasMargin →
      ExpandChildTitleWrapped P inp o group tl →
      ∀ (r : Rect),
      (⟨P.canvasMargin, P.canvasMargin, child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained r →
      frame.rect.StrictInside (shiftRect dx dy r))
    (hchildB : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContextB base fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect)
    : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB base fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC8aGeometry P inp o group titleHeight parent child res := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hframed hctxB hparams
  have hchild := hchildB fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams
  intro frame tl dx dy hframe hdx hdy hwrap cb hcb
  have hr : (⟨P.canvasMargin, P.canvasMargin, child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩ : Rect).Contained cb.rect := by
    simpa [insetRect] using hchild cb hcb
  have hfit := hfitB fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctxB hparams frame tl dx dy hframe hdx hdy hwrap
  exact c8a_frame_contained_shifted hfit hr

end Elegant.Layered.PipelineImpl

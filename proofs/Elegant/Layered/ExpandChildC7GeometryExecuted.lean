import Elegant.Layered.ExpandChildC7GeometryProof
import Elegant.Layered.ExpandChildC8aGeometryExecuted
import Elegant.Layered.ExpandChildParentFrameDirect
import Elegant.Layered.ExpandChildChildSceneProof
import Elegant.Layered.ExpandChildCanvasFitProof
import Elegant.Layered.ExpandChildAncestryProof
import Elegant.Layered.ExpandChildLabelFactsProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- The per-expansion C7 geometry holds for every executed call, modulo the
flat clauses, the below-fuel C8b step facts, the three parent-frame residuals
of `expandChild_parentFrame_direct`, and the per-call `InputFixedFit` premise
the child-label inset needs (the family theorem carries `InputFixedFit` at top
level; `InputFixedFit.childSubInput` threads it to the child sub-input). The
below-fuel C8a facts come from the proved `stepC8aGeometry_holds`, so only C8b
stays open — and only below the call fuel, the fuel-stratified shape. -/
theorem stepC7Geometry_holds
    (hflat8a : FlatC8a)
    (hflat8b : FlatC8b)
    (hbelow8b : ∀ (fuel : Nat), StepFactsBelow fuel ExpandChildC8bGeometry)
    (hframeStrict : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentFrameStrict group parent)
    (hstepStrict : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildParentStrictStep parent)
    (hfitParent : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      InputFixedFit (parentSubInput inp group P titleLines child) o)
    (hfit : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      InputFixedFit inp o) :
    RecursiveStepFacts ExpandChildC7Geometry := by
  intro fuel P inp o group titleLines titleHeight parent child res
    hexpand hframed hctx hparams
  have hP : checkedParams o.profile inp.kind = .ok P := hparams.1
  have below8a : StepFactsBelow fuel ExpandChildC8aGeometry :=
    fun f _ => stepC8aGeometry_holds f
  have below8b : StepFactsBelow fuel ExpandChildC8bGeometry := hbelow8b fuel
  have hpf : ExpandChildParentFrame P inp o group titleHeight parent child :=
    expandChild_parentFrame_direct hflat8a hflat8b below8a below8b
      hexpand hframed hctx hparams
      (hframeStrict fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx hparams)
      (hstepStrict fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx hparams)
      (hfitParent fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx hparams)
  have hchildBoxes : ∀ cb ∈ child.scene.boxes,
      (insetRect child.scene.canvas P.canvasMargin).Contained cb.rect :=
    fun cb hcb => expandChild_child_boxes_inset fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx hP cb hcb
  have hchildLabels : ∀ cl ∈ child.scene.labels,
      (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect :=
    fun cl hcl => expandChild_child_labels_inset fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed
      (hfit fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx hparams)
      hctx hP cl hcl
  have hparentBoxes : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
        pb.id ∉ group.id :: parent.scene.layoutDump.ancestors group.id →
        Disjoint frame.rect pb.rect := by
    intro frame hframe pb hpb hex hforeign
    have hq := hpf frame titleLines _ _ hframe rfl rfl hparams.2.2
    exact hq.1 pb hpb hex hforeign
  have hparentLabels : ∀ (frame : Box),
      parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ pl ∈ parent.scene.labels, pl.owner ≠ group.id →
        Disjoint frame.rect pl.rect := by
    intro frame hframe pl hpl hown
    have hq := hpf frame titleLines _ _ hframe rfl rfl hparams.2.2
    exact hq.2.1 pl hpl hown
  have howners : ExpandChildLabelOwners inp parent child :=
    expandChild_label_owners fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams
  exact expandChild_c7_geometry_executed fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hparams
    hchildBoxes hchildLabels hparentBoxes hparentLabels howners

end PipelineImpl
end Layered
end Elegant

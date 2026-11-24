import Elegant.Layered.ExactAttachedRecursiveLiftProof
import Elegant.Layered.OrdinaryAttachedFlatFrameProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Attached parent routes miss the interior of their fixed frame and hence
    every rectangle strictly inside it. -/
theorem parentRouteAttachedClear_closed
    (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildParentRouteAttachedClear group parent := by
  obtain ⟨_, source⟩ := expandChild_parent_attached_fixed_leaf hctx
  intro frame hframe route hroute hatt r hstrict
  have hframeDump : parent.scene.layoutDump.box? group.id = some frame := hframe
  obtain ⟨_, _, _, _, _, _, _, hleaf, hwf, hfixed, hleafFrame, hleafRoute,
    hfrom, hto, hpoints, hrect⟩ := source hframeDump hroute hatt
  obtain ⟨execution⟩ := layout_sceneExecution hleaf
  have hmiss : ¬ Polyline.hitsRect route.points frame.rect := by
    rw [hpoints, hrect, hitsRect_shift]
    exact execution.attached_fixed_frame_miss hwf hfixed hleafFrame hleafRoute
      (by simpa only [hfrom, hto] using hatt)
  exact fun hhit => hmiss (hitsRect_of_strictInside hstrict hhit)

end Elegant.Layered.PipelineImpl

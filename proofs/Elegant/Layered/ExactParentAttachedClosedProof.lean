import Elegant.Layered.ExactAttachedRecursiveLiftProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The attached-route case of `XG_StepC6MissB` follows from the exact parent
    recursion alone. -/
theorem parentRouteAttachedClear_layoutX
    {exactIds : List String} {fuel : Nat} {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hctx : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res) :
    ExpandChildParentRouteAttachedClear group parent := by
  obtain ⟨hwf, hfind, _, _, hparent, _⟩ := hctx
  let parentInput := parentSubInput inp group P titleLines child
  have hpred := List.find?_some hfind
  simp only [Bool.and_eq_true] at hpred
  have hany : inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
    simpa using hpred.2
  have hnone : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hany)
  let entry : String × Size :=
    (group.id, childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0)
      ((max 1 titleLines.length : Int) * P.lineH)
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩)
  have hfixed : parentInput.fixedSizes.find? (fun fixed => fixed.1 == group.id) = some entry := by
    change (inp.fixedSizes ++ [entry]).find? (fun fixed => fixed.1 == group.id) = some entry
    rw [List.find?_append, hnone]
    simp [entry]
  have hparentWf : WellFormed (inputModel parentInput o) :=
    (subInputWellFormedC2 inp o group hwf).2
      parentInput.fixedSizes parentInput.fixedChildren parentInput.fixedAreas
  have hparentLayout : layoutRecursiveX exactIds fuel parentInput o = .ok parent := hparent
  intro frame hframe route hroute hatt r hstrict hhit
  have hframeDump : parent.scene.layoutDump.box? group.id = some frame := hframe
  exact layoutRecursiveX_attached_fixed_frame_miss hparentWf hparentLayout hfixed hframeDump
    hroute hatt (hitsRect_of_strictInside hstrict hhit)

end Elegant.Layered.PipelineImpl

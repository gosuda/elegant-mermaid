import Elegant.Layered.NotesFoundation
import Elegant.Layered.RegionCanvasMargins

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem contractedKind (layouts : List BundleLayout) (inp : Input) :
    (layouts.foldl contractOne inp).kind = inp.kind := by
  induction layouts generalizing inp with
  | nil => rfl
  | cons _ _ ih => exact ih _

theorem canvasMarginsN_rngNotesBase (exactIds : List String)
    (idSets : List (String × List String)) (outerFuel : Nat) :
    CanvasMarginsB (layoutNotes
      (fun ids sub o => layoutRIds ids (reindexRegionSets idSets sub) sub o)
      exactIds outerFuel) := by
  have hregion (ids : List String) (inp : Input) (o : Options) (res : FamilyResult)
      (h : (fun ids sub o => layoutRIds ids (reindexRegionSets idSets sub) sub o)
        ids inp o = .ok res)
      (P : Params) (hP : checkedParams o.profile inp.kind = .ok P) :
      2 * P.canvasMargin ≤ res.scene.canvas.w ∧ 2 * P.canvasMargin ≤ res.scene.canvas.h :=
    exactCanvasMarginsR ids idSets 0 inp o res h P hP
  have hnotes (inp : Input) (o : Options) (res : FamilyResult)
      (h : layoutNotes
        (fun ids sub o => layoutRIds ids (reindexRegionSets idSets sub) sub o)
        exactIds outerFuel inp o = .ok res)
      (P : Params) (hP : checkedParams o.profile inp.kind = .ok P) :
      2 * P.canvasMargin ≤ res.scene.canvas.w ∧ 2 * P.canvasMargin ≤ res.scene.canvas.h := by
    cases outerFuel with
    | zero => exact hregion exactIds inp o res h P hP
    | succ fuel =>
      rcases layoutNotes_success_phases h with ⟨_, hflat⟩ | ⟨⟨e⟩⟩
      · exact hregion exactIds inp o res hflat P hP
      · have hkind : e.contractedInput.kind = inp.kind := by
          rw [e.contractedInput_eq]
          exact contractedKind e.layouts inp
        rw [e.canvas_eq]
        exact hregion (exactIds ++ e.layouts.map (·.top.id)) e.contractedInput o e.contracted
          e.contracted_eq P (by rwa [hkind])
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res h P hP
    exact hnotes inp o res h P hP
  | succ fuel ih =>
    intro inp o res h P hP
    rcases layoutRecursiveB_succ_sources
      (layoutNotes
        (fun ids sub o => layoutRIds ids (reindexRegionSets idSets sub) sub o)
        exactIds outerFuel) h with ⟨_, hflat⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, hparent, hexpand⟩
    · exact hnotes inp o res hflat P hP
    · rw [expandChild_canvas hexpand]
      exact ih _ _ _ hparent P hP

end Elegant.Layered.PipelineImpl

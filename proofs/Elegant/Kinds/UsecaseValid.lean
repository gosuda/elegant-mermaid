import Elegant.Kinds.UsecaseDrawShapesProof
import Elegant.Kinds.UsecaseValidExact

set_option autoImplicit false

/-! Usecase validity for its exact-box family run.

`Usecase.usecase_exact_family_valid` establishes validity of the admitted exact-box
run. The redraw proof transfers validity to the final scene given clearance for
the moved captions. -/

namespace Elegant
namespace Kinds
namespace Usecase

/-- The moved labels meet C7 and C8b on the redraw of the admitted exact-family
scene that `Usecase.layout` actually projects. -/
def ExecutedDrawClearance (m : Model) : Prop :=
  ∀ {fixed : List (String × Size)} {base : Layered.FamilyResult} {drawn : Scene},
    sizes m = .ok fixed →
    Layered.admit (input m fixed)
      (Layered.layoutFamilyB
        (Layered.PipelineImpl.layoutRecursiveX (actorIds m) (m.boxes.length + 1))
        (input m fixed) m.options) = .ok base →
    let projected := base.scene.projectCellAttachments (Common.routeMarkers m)
    drawShapes m projected = .ok drawn →
    drawShapesMovedC7 m projected drawn ∧ drawShapesMovedC8b m projected drawn

end Usecase

/-- A successful usecase layout satisfies the hard constraints if its moved
labels clear unrelated boxes and frames on that execution. -/
theorem usecase_valid_of_executed_draw_clearance
    {m : Model} {r : Layered.FamilyResult}
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (hDraw : Usecase.ExecutedDrawClearance m)
    (h : Usecase.layout m = .ok r) :
    HardConstraints r.scene.layoutDump := by
  unfold Usecase.layout at h
  cases hs : Usecase.sizes m with
  | error e => simp [hs] at h
  | ok fixed =>
    cases ha : Layered.admit (Usecase.input m fixed)
        (Layered.layoutFamilyB
          (Layered.PipelineImpl.layoutRecursiveX
            ((m.boxes.filter fun b => Usecase.isActor b.shape).map (·.id))
            (m.boxes.length + 1))
          (Usecase.input m fixed) m.options) with
    | error e => simp [hs, ha] at h
    | ok res =>
      cases hd : Usecase.drawShapes m
          (res.scene.projectCellAttachments (Common.routeMarkers m)) with
      | error e => simp [hs, ha, hd] at h
      | ok scene =>
        simp only [hs, ha, hd, Except.ok.injEq] at h
        subst h
        show HardConstraints scene.layoutDump
        obtain ⟨hadm, hrun⟩ := Layered.admit_ok ha
        have hfam := Usecase.usecase_exact_family_valid hadm hwf hlim hs hrun
        obtain ⟨hc7, hc8b⟩ := hDraw hs ha hd
        exact Usecase.drawShapes_hardConstraints (base := res.scene) rfl hd hfam hc7 hc8b

end Kinds
end Elegant

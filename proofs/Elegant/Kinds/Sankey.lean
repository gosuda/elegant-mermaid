import Elegant.Kinds.Common
import Elegant.Chart.SankeyFacts

set_option autoImplicit false

namespace Elegant.Kinds.Sankey

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult := do
  match Chart.Sankey.layout m with
  | .error e => throw (.geometry e)
  | .ok scene => pure { scene, budgetExhausted := false }

theorem layout_scene_success (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) :
    Chart.Sankey.layout m = .ok result.scene := by
  unfold layout at h
  cases hs : Chart.Sankey.layout m with
  | error e => simp [hs] at h
  | ok scene =>
    simp [hs] at h
    cases h
    rfl

theorem layout_canvas (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : Validator.C1 result.scene.layoutDump :=
  Chart.Sankey.layout_canvas m result.scene (layout_scene_success m result h)

theorem layout_metadata_clauses (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) :
    Validator.C2 result.scene.layoutDump ∧ Validator.C3 result.scene.layoutDump ∧
      Validator.C4 result.scene.layoutDump ∧ Validator.C6 result.scene.layoutDump ∧
      Validator.C7 result.scene.layoutDump ∧ Validator.C8 result.scene.layoutDump :=
  Chart.Sankey.layout_metadata_clauses m result.scene (layout_scene_success m result h)

end Elegant.Kinds.Sankey

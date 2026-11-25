import Elegant.Kinds.Common
import Elegant.Chart.Info

set_option autoImplicit false

namespace Elegant.Kinds.Info

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult := do
  let text := (m.labels.find? (fun l => l.id == "version")).map (·.text) |>.getD "v0.1.0"
  match Chart.Info.layout (fontFamily := m.options.fontFamily) m.profile text with
  | .error e => throw (.geometry e)
  | .ok r => pure { scene := Chart.Info.sceneOf m r, budgetExhausted := false }

theorem info_lines_in_canvas {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    ∀ label ∈ result.scene.labels,
      Rect.Contained ⟨0, 0, result.scene.canvas.w, result.scene.canvas.h⟩ label.rect := by
  unfold layout at h
  generalize ht :
    ((m.labels.find? (fun l => l.id == "version")).map (·.text) |>.getD "v0.1.0") =
      text at h
  cases hr : Chart.Info.layout (fontFamily := m.options.fontFamily) m.profile text with
  | error e =>
    simp only [hr, reduceCtorEq] at h
  | ok r =>
    have he : ({ scene := Chart.Info.sceneOf m r, budgetExhausted := false } :
        Layered.FamilyResult) = result := by
      simpa only [hr, Pure.pure, Except.pure, Except.ok.injEq] using h
    cases he
    have hc := Chart.Info.layout_lines_in_canvas m.profile text r hr
    intro label hl
    simp only [Chart.Info.sceneOf, List.mem_singleton] at hl
    subst label
    exact hc

theorem info_valid {m : Model} {result : Layered.FamilyResult}
    (_hw : Elegant.WellFormed m) (_hl : WithinLimits m)
    (h : layout m = .ok result) : HardConstraints result.scene.layoutDump := by
  cases hr : Chart.Info.layout (fontFamily := m.options.fontFamily) m.profile
      ((m.labels.find? (fun l => l.id == "version")).map (·.text) |>.getD "v0.1.0") with
  | error e =>
    simp only [layout, hr, reduceCtorEq] at h
  | ok r =>
    have he : ({ scene := Chart.Info.sceneOf m r, budgetExhausted := false } :
        Layered.FamilyResult) = result := by
      simpa only [layout, hr, Pure.pure, Except.pure, Except.ok.injEq] using h
    cases he
    exact Chart.Info.info_valid m r

end Elegant.Kinds.Info

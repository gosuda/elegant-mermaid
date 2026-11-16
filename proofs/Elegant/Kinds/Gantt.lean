import Elegant.Kinds.Common
import Elegant.Chart.GanttCalendar

set_option autoImplicit false

namespace Elegant.Kinds.Gantt

def admittedConfig (m : Model) : Bool :=
  m.options.config.all fun entry =>
    match entry.2 with
    | .integer value =>
      if entry.1 == "barHeight" then 1 ≤ value && value ≤ 1024
      else if entry.1 == "barGap" then 0 ≤ value && value ≤ 1024
      else true
    | _ => true

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult := do
  if !admittedConfig m then throw (.geometry .domain)
  match Chart.Gantt.layout m with
  | .error error => throw (.geometry error)
  | .ok (scene, capped) => pure { scene := scene, budgetExhausted := capped }


theorem successful_config (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : admittedConfig m = true := by
  cases hc : admittedConfig m with
  | false =>
    unfold layout at h
    exact (Common.guarded_error (by rw [hc]; rfl) h).elim
  | true => rfl

theorem successful_barHeight (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) (value : Int)
    (hmem : ("barHeight", ConfigValue.integer value) ∈ m.options.config) :
    1 ≤ value ∧ value ≤ 1024 := by
  have hall := successful_config m result h
  simp only [admittedConfig, List.all_eq_true] at hall
  have hv := hall ("barHeight", ConfigValue.integer value) hmem
  simpa using hv

theorem successful_barGap (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) (value : Int)
    (hmem : ("barGap", ConfigValue.integer value) ∈ m.options.config) :
    0 ≤ value ∧ value ≤ 1024 := by
  have hall := successful_config m result h
  simp only [admittedConfig, List.all_eq_true] at hall
  have hv := hall ("barGap", ConfigValue.integer value) hmem
  simpa using hv

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x.bind f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem successful_scene (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) :
    ∃ (p : Chart.Gantt.Plan) (boxes : List Box)
      (labels : List Chart.Gantt.PlacedLabel) (excluded : List Primitive),
      Chart.Gantt.prepare m = .ok p ∧
      (m.boxes.mapM fun (b : ModelBox) => do
        let rect ← p.boxRect b
        pure ({
          id := b.id
          role := b.role.id
          rect := rect
          parent := b.parent
          exclusive := b.exclusive } : Box)) = .ok boxes ∧
      Chart.Gantt.placeLabels p boxes m.labels [] = .ok labels ∧
      Chart.Gantt.excludedItems p = .ok excluded ∧
      result.scene = Chart.Gantt.sceneOf p boxes labels excluded ∧
      InI32 result.scene.canvas.w ∧ InI32 result.scene.canvas.h := by
  unfold layout at h
  replace h := Common.guarded_ok h
  cases hc : Chart.Gantt.layout m with
  | error e => simp [hc] at h
  | ok output =>
    rcases output with ⟨scene, capped⟩
    simp only [hc, pure, Except.pure, Except.ok.injEq] at h
    subst result
    unfold Chart.Gantt.layout at hc
    rcases bind_ok hc with ⟨p, hp, hc⟩
    rcases bind_ok hc with ⟨boxes, hb, hc⟩
    rcases bind_ok hc with ⟨labels, hl, hc⟩
    rcases bind_ok hc with ⟨excluded, he, hc⟩
    dsimp only at hc
    split at hc
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
      rename_i hvalid
      rcases hc with ⟨rfl, rfl⟩
      exact ⟨p, boxes, labels, excluded, hp, hb, hl, he, rfl,
        hvalid.1, hvalid.2.1⟩
    · cases hc

theorem successful_routes_empty (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : result.scene.routes = [] := by
  rcases successful_scene m result h with
    ⟨p, boxes, labels, excluded, _, _, _, _, hs, _, _⟩
  rw [hs]
  rfl

theorem gantt_c4 (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : Validator.C4 result.scene.layoutDump := by
  simp [Validator.C4, Scene.layoutDump, successful_routes_empty m result h]

theorem gantt_c5 (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : Validator.C5 result.scene.layoutDump := by
  simp [Validator.C5, Scene.layoutDump, successful_routes_empty m result h]

theorem gantt_c6 (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : Validator.C6 result.scene.layoutDump := by
  simp [Validator.C6, Scene.layoutDump, successful_routes_empty m result h]
end Elegant.Kinds.Gantt

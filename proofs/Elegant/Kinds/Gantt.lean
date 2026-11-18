import Elegant.Kinds.Common
import Elegant.Chart.GanttCalendar

set_option autoImplicit false

namespace Elegant.Kinds.Gantt

private def supportedBox (b : ModelBox) : Bool :=
  decide (b.role = .node ∧ b.exclusive = false)

/-- Raw Gantt time fields are zigzag encoded; admission checks the decoded task values
against the same bounds `prepare` enforces, plus the ordering the geometry proofs need. -/
private def supportedStructure (m : Model) : Bool :=
  m.boxes.all supportedBox &&
    m.boxes.all (fun b =>
      (b.id == "plot" && b.parent == "") || (b.id != "plot" && b.parent == "plot")) &&
    m.regionSets.all fun r =>
      match Chart.Gantt.decodeTask r with
      | some t =>
        decide (-8640000000000 ≤ t.startTime ∧ t.startTime ≤ 8640000000000 ∧
          -8640000000000 ≤ t.endTime ∧ t.endTime ≤ 8640000000000 ∧
          -8640000000000 ≤ t.renderEnd ∧ t.renderEnd ≤ 8640000000000 ∧
          t.startTime ≤ t.endTime ∧ t.renderEnd ≤ t.endTime ∧
          -1 ≤ t.«section» ∧ (t.«section» : Int) <
            (List.countP (fun b => (Chart.Gantt.boxIndex 's' b.id).isSome) m.boxes : Int))
      | none => true

def admittedConfig (m : Model) : Bool :=
  m.options.config.all fun entry =>
    match entry.2 with
    | .integer value =>
      if entry.1 == "barHeight" then 1 ≤ value && value ≤ 1024
      else if entry.1 == "barGap" then 0 ≤ value && value ≤ 1024
      else if entry.1 == "topPadding" || entry.1 == "leftPadding" ||
          entry.1 == "rightPadding" then 0 ≤ value && value ≤ 1048576
      else true
    | _ => true

/-- Constants the geometry proofs rely on: non-negative pads and sizes, a positive canvas
width, room for the edge stroke inside the gutters, and bars/markers that fit the canvas. -/
def admittedConstants (m : Model) : Bool :=
  match Chart.Gantt.loadConsts m with
  | .ok c =>
    decide (0 ≤ c.topPad ∧ 0 ≤ c.gutter ∧ 0 ≤ c.sidePad ∧ 0 ≤ c.barH ∧
      0 ≤ c.rowGap ∧ 0 ≤ c.axisH ∧ 0 ≤ c.vertW ∧ 0 ≤ c.edge ∧
      0 < c.width ∧ c.barH ≤ c.width ∧ c.vertW ≤ c.width ∧
      c.edge ≤ c.gutter + c.sidePad ∧ c.gutter ≤ c.width - c.sidePad)
  | .error _ => false

def admitted (m : Model) : Bool :=
  admittedConfig m && supportedStructure m && admittedConstants m

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult := do
  if !admitted m then throw (.geometry .domain)
  match Chart.Gantt.layout m with
  | .error error => throw (.geometry error)
  | .ok (scene, capped) => pure { scene := scene, budgetExhausted := capped }

theorem successful_admitted (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : admitted m = true := by
  cases hc : admitted m with
  | false =>
    unfold layout at h
    exact (Common.guarded_error (by rw [hc]; rfl) h).elim
  | true => rfl

theorem successful_config (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : admittedConfig m = true := by
  have ha := successful_admitted m result h
  simp only [admitted, Bool.and_eq_true] at ha
  exact ha.1.1

theorem successful_structure (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : supportedStructure m = true := by
  have ha := successful_admitted m result h
  simp only [admitted, Bool.and_eq_true] at ha
  exact ha.1.2

theorem successful_constants (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) :
    match Chart.Gantt.loadConsts m with
    | .ok c =>
      0 ≤ c.topPad ∧ 0 ≤ c.gutter ∧ 0 ≤ c.sidePad ∧ 0 ≤ c.barH ∧
      0 ≤ c.rowGap ∧ 0 ≤ c.axisH ∧ 0 ≤ c.vertW ∧ 0 ≤ c.edge ∧
      0 < c.width ∧ c.barH ≤ c.width ∧ c.vertW ≤ c.width ∧
      c.edge ≤ c.gutter + c.sidePad ∧ c.gutter ≤ c.width - c.sidePad
    | .error _ => False := by
  have ha := successful_admitted m result h
  simp only [admitted, Bool.and_eq_true] at ha
  have hc := ha.2
  cases hload : Chart.Gantt.loadConsts m with
  | error e =>
    simp only [admittedConstants, hload, Bool.false_eq_true] at hc
  | ok c =>
    simp only [admittedConstants, hload] at hc
    exact of_decide_eq_true hc

def supportedBoxOk (b : ModelBox) : Prop := b.role = .node ∧ b.exclusive = false

theorem supportedBox_iff (b : ModelBox) :
    supportedBox b = true ↔ supportedBoxOk b := by
  unfold supportedBox supportedBoxOk
  simp only [decide_eq_true_eq]

theorem successful_supported_box (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) (b : ModelBox) (hb : b ∈ m.boxes) :
    b.role = .node ∧ b.exclusive = false := by
  have hs := successful_structure m result h
  simp only [supportedStructure, Bool.and_eq_true, List.all_eq_true] at hs
  have h1 := hs.1.1 b hb
  rw [supportedBox_iff] at h1
  exact h1

/-- The parent rule of the supported structure: the plot box is parentless and every
other box is parented directly to it. -/
theorem successful_box_parent (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) (b : ModelBox) (hb : b ∈ m.boxes) :
    (b.id = "plot" ∧ b.parent = "") ∨ (b.id ≠ "plot" ∧ b.parent = "plot") := by
  have hs := successful_structure m result h
  simp only [supportedStructure, Bool.and_eq_true, List.all_eq_true] at hs
  have hpar := hs.1.2 b hb
  simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] using hpar

/-- Per-task facts a successful layout guarantees: decoded time bounds, ordering, and a
valid section index matching `prepare`'s own check. -/
theorem successful_region_task (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) (r : ModelRegionSet) (hr : r ∈ m.regionSets)
    (t : Chart.Gantt.Task) (hd : Chart.Gantt.decodeTask r = some t) :
    -8640000000000 ≤ t.startTime ∧ t.startTime ≤ 8640000000000 ∧
    -8640000000000 ≤ t.endTime ∧ t.endTime ≤ 8640000000000 ∧
    -8640000000000 ≤ t.renderEnd ∧ t.renderEnd ≤ 8640000000000 ∧
    t.startTime ≤ t.endTime ∧ t.renderEnd ≤ t.endTime ∧
    -1 ≤ t.«section» ∧ (t.«section» : Int) <
      (List.countP (fun b => (Chart.Gantt.boxIndex 's' b.id).isSome) m.boxes : Int) := by
  have hs := successful_structure m result h
  simp only [supportedStructure, Bool.and_eq_true, List.all_eq_true] at hs
  have hmatch := hs.2 r hr
  rw [hd] at hmatch
  exact of_decide_eq_true hmatch


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

end Elegant.Kinds.Gantt

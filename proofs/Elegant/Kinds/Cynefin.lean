import Elegant.Kinds.Common
import Elegant.Chart.Cynefin

set_option autoImplicit false

namespace Elegant.Kinds.Cynefin

def admitted (m : Model) : Bool :=
  let c := Chart.Cynefin.constants m
  decide (0 ≤ c.width ∧ 0 ≤ c.height) &&
    m.boxes.all (fun b => decide (b.role = .node))

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult := do
  if admitted m = false then throw (.geometry .domain)
  match Chart.Cynefin.layout m with
  | .error e => throw (.geometry e)
  | .ok scene => pure {
      scene := scene.projectCellAttachments (Common.routeMarkers m)
      budgetExhausted := false }

theorem layout_dump_of_success {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    ∃ scene, Chart.Cynefin.layout m = .ok scene ∧
      result.scene.layoutDump = scene.layoutDump := by
  have ha : admitted m = true := by
    cases ha : admitted m with
    | false =>
      unfold layout at h
      exact (Common.guarded_error ha h).elim
    | true => rfl
  cases hc : Chart.Cynefin.layout m with
  | error e => simp [layout, ha, hc] at h
  | ok scene =>
    have he : ({
        scene := scene.projectCellAttachments (Common.routeMarkers m)
        budgetExhausted := false } : Layered.FamilyResult) = result := by
      simpa [layout, ha, hc, Pure.pure, Except.pure] using h
    cases he
    exact ⟨scene, rfl, Scene.projectCellAttachments_layoutDump scene
      (Common.routeMarkers m)⟩

theorem successful_model_relations {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    ∀ b ∈ m.boxes, b.exclusive = false ∧
      (if b.id = "frame" then b.parent = "" else b.parent = "frame") := by
  obtain ⟨scene, hs, _hdump⟩ := layout_dump_of_success h
  exact Chart.Cynefin.relationsConsistent_box m
    (Chart.Cynefin.layout_relations_consistent m scene hs)

theorem successful_dump_nonexclusive {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    ∀ b ∈ result.scene.layoutDump.boxes, b.exclusive = false := by
  obtain ⟨scene, hs, hd⟩ := layout_dump_of_success h
  rw [hd]
  exact Chart.Cynefin.successful_scene_nonexclusive m scene hs

theorem cynefin_c2 {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : Validator.C2 result.scene.layoutDump := by
  intro b hb _c _hc _ hexclusive
  simp [successful_dump_nonexclusive h b hb] at hexclusive

theorem cynefin_c4 {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : Validator.C4 result.scene.layoutDump := by
  obtain ⟨scene, hs, hd⟩ := layout_dump_of_success h
  rw [hd]
  intro r hr _horthogonal
  exact Chart.Cynefin.successful_scene_orthogonal m scene hs r hr

theorem cynefin_c6 {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : Validator.C6 result.scene.layoutDump := by
  intro _r _hr b hb hexclusive
  simp [successful_dump_nonexclusive h b hb] at hexclusive

theorem cynefin_c7 {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : Validator.C7 result.scene.layoutDump := by
  intro _l _hl b hb hexclusive
  simp [successful_dump_nonexclusive h b hb] at hexclusive

theorem cynefin_c5 {m : Model} {result : Layered.FamilyResult}
    (_hwf : WellFormed m) (_hlimits : WithinLimits m)
    (h : layout m = .ok result) : Validator.C5 result.scene.layoutDump := by
  obtain ⟨scene, hs, hd⟩ := layout_dump_of_success h
  rw [hd]
  exact Chart.Cynefin.successful_scene_ports m scene hs

theorem cynefin_c1_of_nonneg_dims {m : Model} {result : Layered.FamilyResult}
    (_hwf : WellFormed m) (_hlimits : WithinLimits m)
    (hdims : 0 ≤ (Chart.Cynefin.constants m).width ∧
      0 ≤ (Chart.Cynefin.constants m).height)
    (h : layout m = .ok result) : Validator.C1 result.scene.layoutDump := by
  obtain ⟨scene, hs, hd⟩ := layout_dump_of_success h
  rw [hd]
  exact Chart.Cynefin.cynefin_c1_of_nonneg_dims m scene hdims hs

theorem cynefin_c3_of_nonneg_dims {m : Model} {result : Layered.FamilyResult}
    (_hwf : WellFormed m) (_hlimits : WithinLimits m)
    (hdims : 0 ≤ (Chart.Cynefin.constants m).width ∧
      0 ≤ (Chart.Cynefin.constants m).height)
    (h : layout m = .ok result) : Validator.C3 result.scene.layoutDump := by
  obtain ⟨scene, hs, hd⟩ := layout_dump_of_success h
  rw [hd]
  exact Chart.Cynefin.cynefin_c3_of_nonneg_dims m scene hdims hs

theorem rejected_of_not_admitted (m : Model) (h : admitted m = false) :
    layout m = .error (.geometry .domain) := by
  unfold layout
  rw [ite_eq_left h]
  rfl

theorem successful_nonnegative_dimensions {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    0 ≤ (Chart.Cynefin.constants m).width ∧
      0 ≤ (Chart.Cynefin.constants m).height := by
  have ha : admitted m = true := by
    cases ha : admitted m with
    | false =>
      unfold layout at h
      exact (Common.guarded_error ha h).elim
    | true => rfl
  have hd := (Bool.and_eq_true_iff.mp ha).1
  simpa only [decide_eq_true_eq] using hd

theorem cynefin_c1 {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (h : layout m = .ok result) : Validator.C1 result.scene.layoutDump :=
  cynefin_c1_of_nonneg_dims hwf hlim (successful_nonnegative_dimensions h) h

theorem cynefin_c3 {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (h : layout m = .ok result) : Validator.C3 result.scene.layoutDump :=
  cynefin_c3_of_nonneg_dims hwf hlim (successful_nonnegative_dimensions h) h

theorem cynefin_valid_of_c8 (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (h : layout m = .ok result)
    (hgroups : Validator.C8 result.scene.layoutDump) :
    HardConstraints result.scene.layoutDump := by
  exact Chart.Cynefin.hardConstraints_of_nonexclusive result.scene.layoutDump
    (successful_dump_nonexclusive h) (cynefin_c1 hwf hlim h)
    (cynefin_c3 hwf hlim h) (cynefin_c4 h) (cynefin_c5 hwf hlim h) hgroups

theorem cynefin_c8_of_node_roles {m : Model} {result : Layered.FamilyResult}
    (hroles : ∀ b ∈ m.boxes, b.role = .node)
    (h : layout m = .ok result) : Validator.C8 result.scene.layoutDump := by
  obtain ⟨scene, hs, hd⟩ := layout_dump_of_success h
  rw [hd]
  obtain ⟨_title, domains, _routes, _labels, _dumpLabels, _hd, _hroutes,
    _hc, hboxes, _hr, _hl⟩ :=
    Chart.Cynefin.successful_layout_decompose m scene hs
  have hn : ∀ b ∈ scene.layoutDump.boxes, b.role = "node" := by
    intro b hb
    change b ∈ scene.boxes at hb
    rw [hboxes] at hb
    obtain ⟨source, hsource, _hid, hrole, _hparent, _hexclusive⟩ :=
      Chart.Cynefin.dumpBoxes_metadata m domains scene.canvas b hb
    rw [hrole, hroles source hsource]
    rfl
  constructor
  · intro g hg hgroup
    simp [hn g hg] at hgroup
  · intro g hg hgroup
    simp [hn g hg] at hgroup

theorem cynefin_valid_of_node_roles (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (hroles : ∀ b ∈ m.boxes, b.role = .node)
    (h : layout m = .ok result) : HardConstraints result.scene.layoutDump :=
  cynefin_valid_of_c8 m result hwf hlim h (cynefin_c8_of_node_roles hroles h)


theorem negativeHeightWitness_rejected :
    layout Chart.Cynefin.negativeHeightWitness = .error (.geometry .domain) := by
  apply rejected_of_not_admitted
  simp [admitted, Chart.Cynefin.negativeHeightWitness,
    Chart.Cynefin.constants, Chart.Cynefin.integer]

def c8OverlapWitness : Model :=
  { kind := "cynefin", profile := .cell,
    boxes := [
      { id := "frame", exclusive := false },
      { id := "complex", parent := "frame", exclusive := false },
      { id := "g", role := .group, parent := "frame", exclusive := false }],
    labels :=
      ({ id := "complex.label", owner := "complex", text := "X" } ::
        (List.range 20).map fun i =>
          { id := "complex.i" ++ toString i, owner := "complex", text := "X" }) ++
      [{ id := "g.label", owner := "g", text := "X" }] }

theorem successful_node_roles {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : ∀ b ∈ m.boxes, b.role = .node := by
  have ha : admitted m = true := by
    cases ha : admitted m with
    | false =>
      unfold layout at h
      exact (Common.guarded_error ha h).elim
    | true => rfl
  have hroles := (Bool.and_eq_true_iff.mp ha).2
  intro b hb
  exact of_decide_eq_true (List.all_eq_true.mp hroles b hb)

theorem cynefin_valid (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (h : layout m = .ok result) : HardConstraints result.scene.layoutDump :=
  cynefin_valid_of_node_roles m result hwf hlim (successful_node_roles h) h

theorem c8OverlapWitness_wellFormed : WellFormed c8OverlapWitness := by decide

theorem c8OverlapWitness_withinLimits : WithinLimits c8OverlapWitness := by decide

theorem c8OverlapWitness_rejected :
    layout c8OverlapWitness = .error (.geometry .domain) := by
  apply rejected_of_not_admitted
  decide

end Elegant.Kinds.Cynefin

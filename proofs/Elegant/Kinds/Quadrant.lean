import Elegant.Kinds.Common
import Elegant.Chart.QuadrantFacts

set_option autoImplicit false

namespace Elegant.Kinds.Quadrant

def decode (m : Model) : List Chart.Quadrant.InputPoint :=
  Chart.Quadrant.pointInputs m

def isPointId (id : String) : Bool :=
  match (String.ofList id.toList.tail).toNat? with
  | none => false
  | some n => id == "p" ++ toString n

def admitted (m : Model) : Bool :=
  decide ((0 ≤ (Chart.Quadrant.constants m).padX ∧
    0 ≤ (Chart.Quadrant.constants m).padY) ∧
    0 ≤ (Chart.Quadrant.constants m).titlePad ∧
    0 ≤ (Chart.Quadrant.constants m).xPad ∧
    0 ≤ (Chart.Quadrant.constants m).yPad ∧
    0 ≤ (Chart.Quadrant.constants m).radiusX ∧
    0 ≤ (Chart.Quadrant.constants m).radiusY) &&
  m.boxes.all (fun b =>
    (!b.exclusive && decide (b.parent = "" ∨ b.parent = "plot")) &&
      decide (b.role.id ≠ "group"))

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  if m.boxes.any (fun b => (b.id == "plot" || ["q1", "q2", "q3", "q4"].contains b.id) && b.exclusive) then
    .error (.geometry .domain)
  else
    if m.boxes.any (fun b => isPointId b.id && b.exclusive) then
      .error (.geometry .domain)
    else
      if admitted m then
        match Chart.Quadrant.layout m with
        | .error e => .error (.geometry e)
        | .ok scene => .ok { scene, budgetExhausted := false }
      else .error (.geometry .domain)

theorem successful_plot_nonexclusive (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) (b : ModelBox) (hb : b ∈ m.boxes) (hid : b.id = "plot") :
    b.exclusive = false := by
  unfold layout at h
  split at h
  · contradiction
  · rename_i hg
    have hf : (m.boxes.any fun a => (a.id == "plot" || ["q1", "q2", "q3", "q4"].contains a.id) && a.exclusive) = false := by
      cases hx : (m.boxes.any fun a => (a.id == "plot" || ["q1", "q2", "q3", "q4"].contains a.id) && a.exclusive) with
      | false => rfl
      | true => exact False.elim (hg hx)
    have hx := (List.any_eq_false.mp hf) b hb
    cases he : b.exclusive with
    | false => rfl
    | true =>
      have hp : ((b.id == "plot" || ["q1", "q2", "q3", "q4"].contains b.id) && b.exclusive) = true := by simp [hid, he]
      exact False.elim (hx hp)

theorem successful_tile_nonexclusive (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) (b : ModelBox) (hb : b ∈ m.boxes)
    (hid : ["q1", "q2", "q3", "q4"].contains b.id = true) :
    b.exclusive = false := by
  unfold layout at h
  split at h
  · contradiction
  · rename_i hg
    have hf : (m.boxes.any fun a => (a.id == "plot" || ["q1", "q2", "q3", "q4"].contains a.id) && a.exclusive) = false := by
      cases hx : (m.boxes.any fun a => (a.id == "plot" || ["q1", "q2", "q3", "q4"].contains a.id) && a.exclusive) with
      | false => rfl
      | true => exact False.elim (hg hx)
    have hx := (List.any_eq_false.mp hf) b hb
    cases he : b.exclusive with
    | false => rfl
    | true =>
      have hp : ((b.id == "plot" || ["q1", "q2", "q3", "q4"].contains b.id) && b.exclusive) = true := by
        simp only [hid, he, Bool.or_true, Bool.and_self]
      exact False.elim (hx hp)

theorem successful_layout_geometry (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) :
    Chart.Quadrant.layout m = .ok r.scene ∧ r.budgetExhausted = false := by
  unfold layout at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · cases hg : Chart.Quadrant.layout m with
        | error e => simp only [hg] at h; contradiction
        | ok s =>
          simp only [hg] at h
          cases h
          exact ⟨rfl, rfl⟩
      · contradiction

theorem successful_route_constraints (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) :
    Validator.C4 r.scene.layoutDump ∧ Validator.C5 r.scene.layoutDump ∧
      Validator.C6 r.scene.layoutDump := by
  exact Chart.Quadrant.successful_route_constraints m r.scene
    (successful_layout_geometry m r h).1

theorem successful_point_nonexclusive (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) (b : ModelBox) (hb : b ∈ m.boxes)
    (hid : isPointId b.id = true) : b.exclusive = false := by
  unfold layout at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i hg
      have hf : (m.boxes.any fun a => isPointId a.id && a.exclusive) = false := by
        cases hx : (m.boxes.any fun a => isPointId a.id && a.exclusive) with
        | false => rfl
        | true => exact False.elim (hg hx)
      have hx := (List.any_eq_false.mp hf) b hb
      cases he : b.exclusive with
      | false => rfl
      | true =>
        have hp : (isPointId b.id && b.exclusive) = true := by simp [hid, he]
        exact False.elim (hx hp)

theorem successful_point_coordinates (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) (p : Chart.Quadrant.InputPoint)
    (hp : p ∈ decode m) :
    0 ≤ p.x ∧ p.x ≤ 1000 ∧ 0 ≤ p.y ∧ p.y ≤ 1000 := by
  exact Chart.Quadrant.successful_point_coordinates m r.scene
    (successful_layout_geometry m r h).1 p hp

def tileParentWitness : Model :=
  { kind := "quadrant", profile := .cell
    boxes := [
      { id := "plot", exclusive := false },
      { id := "q1", parent := "q2", exclusive := false },
      { id := "q2", parent := "plot", exclusive := false },
      { id := "q3", parent := "plot", exclusive := false },
      { id := "q4", parent := "plot", exclusive := false }] }

private def emptyLabelGeometry : Chart.Quadrant.Geometry :=
  let plot : Rect := ⟨1, 1, 61, 30⟩
  let tiles := (List.range 4).map (Chart.Quadrant.tile plot)
  { canvas := ⟨63, 32⟩, plot, tiles
    inner := tiles.zipIdx.map (fun (r, i) =>
      Chart.Quadrant.innerTile (Chart.Quadrant.constants tileParentWitness) r i)
    centres := [], radii := [], pointBoxes := [] }

def tileParentWitnessResult : Layered.FamilyResult :=
  { scene := Chart.Quadrant.sceneOf tileParentWitness
      (Chart.Quadrant.constants tileParentWitness) emptyLabelGeometry []
    budgetExhausted := false }

theorem tileParentWitness_wellFormed : WellFormed tileParentWitness := by
  decide

theorem tileParentWitness_withinLimits : WithinLimits tileParentWitness := by
  decide

theorem tileParentWitness_not_c3 :
    ¬ Validator.C3 tileParentWitnessResult.scene.layoutDump := by
  intro h
  have hc := Validator.c3_iff tileParentWitnessResult.scene.layoutDump
  have hf : Validator.c3 tileParentWitnessResult.scene.layoutDump = false := by decide
  have ht := hc.mpr h
  rw [hf] at ht
  contradiction

def exclusiveIdWitness : Model :=
  { kind := "quadrant", profile := .cell
    boxes := [{ id := "a" }, { id := "b" }] }

def exclusiveIdWitnessResult : Layered.FamilyResult :=
  { scene := Chart.Quadrant.sceneOf exclusiveIdWitness
      (Chart.Quadrant.constants exclusiveIdWitness) emptyLabelGeometry []
    budgetExhausted := false }

theorem exclusiveIdWitness_wellFormed : WellFormed exclusiveIdWitness := by
  decide

theorem exclusiveIdWitness_withinLimits : WithinLimits exclusiveIdWitness := by
  decide

theorem exclusiveIdWitness_not_c2 :
    ¬ Validator.C2 exclusiveIdWitnessResult.scene.layoutDump := by
  intro h
  have hc := Validator.c2_iff exclusiveIdWitnessResult.scene.layoutDump
  have hf : Validator.c2 exclusiveIdWitnessResult.scene.layoutDump = false := by decide
  have ht := hc.mpr h
  rw [hf] at ht
  contradiction

theorem quadrant_c4 (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) : Validator.C4 r.scene.layoutDump :=
  (successful_route_constraints m r h).1

theorem quadrant_c5 (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) : Validator.C5 r.scene.layoutDump :=
  (successful_route_constraints m r h).2.1

theorem quadrant_c6 (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) : Validator.C6 r.scene.layoutDump :=
  (successful_route_constraints m r h).2.2

def foreignGroupWitness : Model :=
  { kind := "quadrant", profile := .cell
    boxes := [
      { id := "a", role := .group, exclusive := false },
      { id := "b", exclusive := false }] }

def foreignGroupWitnessResult : Layered.FamilyResult :=
  { scene := Chart.Quadrant.sceneOf foreignGroupWitness
      (Chart.Quadrant.constants foreignGroupWitness) emptyLabelGeometry []
    budgetExhausted := false }

theorem foreignGroupWitness_wellFormed : WellFormed foreignGroupWitness := by
  decide

theorem foreignGroupWitness_withinLimits : WithinLimits foreignGroupWitness := by
  decide

theorem foreignGroupWitness_not_c8 :
    ¬ Validator.C8 foreignGroupWitnessResult.scene.layoutDump := by
  intro h
  have hc := Validator.c8_iff foreignGroupWitnessResult.scene.layoutDump
  have hf : Validator.c8 foreignGroupWitnessResult.scene.layoutDump = false := by decide
  have ht := hc.mpr h
  rw [hf] at ht
  contradiction

def negativePaddingWitness : Model :=
  { kind := "quadrant", profile := .cell
    options := { config := [("quadrantPadding", .integer (-16))] }
    boxes := [{ id := "plot", exclusive := false }] }

private def negativePaddingGeometry : Chart.Quadrant.Geometry :=
  let plot : Rect := ⟨-2, -1, 67, 34⟩
  let tiles := (List.range 4).map (Chart.Quadrant.tile plot)
  { canvas := ⟨63, 32⟩, plot, tiles
    inner := tiles.zipIdx.map (fun (r, i) =>
      Chart.Quadrant.innerTile (Chart.Quadrant.constants negativePaddingWitness) r i)
    centres := [], radii := [], pointBoxes := [] }

def negativePaddingWitnessResult : Layered.FamilyResult :=
  { scene := Chart.Quadrant.sceneOf negativePaddingWitness
      (Chart.Quadrant.constants negativePaddingWitness) negativePaddingGeometry []
    budgetExhausted := false }

theorem negativePaddingWitness_wellFormed : WellFormed negativePaddingWitness := by
  decide

theorem negativePaddingWitness_withinLimits : WithinLimits negativePaddingWitness := by
  decide

theorem negativePaddingWitness_not_c1 :
    ¬ Validator.C1 negativePaddingWitnessResult.scene.layoutDump := by
  intro h
  have hc := Validator.c1_iff negativePaddingWitnessResult.scene.layoutDump
  have hf : Validator.c1 negativePaddingWitnessResult.scene.layoutDump = false := by decide
  have ht := hc.mpr h
  rw [hf] at ht
  contradiction

theorem quadrant_c7 (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) (hn : ∀ b ∈ m.boxes, b.exclusive = false) :
    Validator.C7 r.scene.layoutDump := by
  exact Chart.Quadrant.successful_label_clearance m r.scene
    (successful_layout_geometry m r h).1 hn

theorem successful_canonical_boxes_nonexclusive (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r)
    (hids : ∀ b ∈ m.boxes,
      b.id = "plot" ∨ ["q1", "q2", "q3", "q4"].contains b.id = true ∨
        isPointId b.id = true) :
    ∀ b ∈ m.boxes, b.exclusive = false := by
  intro b hb
  rcases hids b hb with hp | hq | hi
  · exact successful_plot_nonexclusive m r h b hb hp
  · exact successful_tile_nonexclusive m r h b hb hq
  · exact successful_point_nonexclusive m r h b hb hi

theorem quadrant_c2_of_canonical_boxes (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r)
    (hids : ∀ b ∈ m.boxes,
      b.id = "plot" ∨ ["q1", "q2", "q3", "q4"].contains b.id = true ∨
        isPointId b.id = true) :
    Validator.C2 r.scene.layoutDump := by
  have hn := successful_canonical_boxes_nonexclusive m r h hids
  have hout := Chart.Quadrant.successful_boxes_nonexclusive m r.scene
    (successful_layout_geometry m r h).1 hn
  intro b hb _ _ _ he
  have hf := hout b hb
  rw [hf] at he
  contradiction

theorem quadrant_c7_of_canonical_boxes (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r)
    (hids : ∀ b ∈ m.boxes,
      b.id = "plot" ∨ ["q1", "q2", "q3", "q4"].contains b.id = true ∨
        isPointId b.id = true) :
    Validator.C7 r.scene.layoutDump := by
  exact quadrant_c7 m r h (successful_canonical_boxes_nonexclusive m r h hids)

theorem quadrant_c1_of_nonneg_pads (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r)
    (hx : 0 ≤ (Chart.Quadrant.constants m).padX)
    (hy : 0 ≤ (Chart.Quadrant.constants m).padY)
    (hreservations : ∀ g,
      Chart.Quadrant.arrange m (Chart.Quadrant.constants m)
        (Chart.Quadrant.pointInputs m) = .ok g →
      (Chart.Quadrant.constants m).padX ≤ g.plot.x ∧
      (Chart.Quadrant.constants m).padY ≤ g.plot.y ∧
      g.plot.y + g.plot.h + (Chart.Quadrant.constants m).padY ≤ g.canvas.h)
    (hboxes : ∀ g,
      Chart.Quadrant.arrange m (Chart.Quadrant.constants m)
        (Chart.Quadrant.pointInputs m) = .ok g →
      ∀ a i, (a, i) ∈ m.boxes.zipIdx →
        Rect.Contained g.plot (Chart.Quadrant.boxRect g i)) :
    Validator.C1 r.scene.layoutDump := by
  obtain ⟨g, ps, hg, _, hs⟩ := Chart.Quadrant.successful_scene_assembly
    m r.scene (successful_layout_geometry m r h).1
  rw [hs]
  apply Chart.Quadrant.sceneOf_c1_of_plot_containment
  · obtain ⟨hl, ht, hb⟩ := hreservations g hg
    have hr := Chart.Quadrant.successful_arrange_plot_right_margin
      m (Chart.Quadrant.constants m) (Chart.Quadrant.pointInputs m) g hg hx
    apply Chart.Quadrant.plot_contained <;> omega
  · exact hboxes g hg

theorem quadrant_c3_of_canonical_parents (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r)
    (hparents : ∀ a ∈ m.boxes, a.parent = "" ∨ a.parent = "plot")
    (hgeometry : ∀ g,
      Chart.Quadrant.arrange m (Chart.Quadrant.constants m)
        (Chart.Quadrant.pointInputs m) = .ok g →
      (∀ a i, (a, i) ∈ m.boxes.zipIdx → a.id = "plot" →
        Chart.Quadrant.boxRect g i = g.plot) ∧
      (∀ a i, (a, i) ∈ m.boxes.zipIdx → a.parent = "plot" →
        Rect.Contained g.plot (Chart.Quadrant.boxRect g i))) :
    Validator.C3 r.scene.layoutDump := by
  obtain ⟨g, ps, hg, _, hs⟩ := Chart.Quadrant.successful_scene_assembly
    m r.scene (successful_layout_geometry m r h).1
  rw [hs]
  exact Chart.Quadrant.sceneOf_c3_of_canonical_parents
    m (Chart.Quadrant.constants m) g ps hparents
      (hgeometry g hg).1 (hgeometry g hg).2

theorem successful_admitted (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) : admitted m = true := by
  unfold layout at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · assumption
      · contradiction

theorem successful_metadata (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) :
    (0 ≤ (Chart.Quadrant.constants m).padX ∧
      0 ≤ (Chart.Quadrant.constants m).padY) ∧
    ∀ b ∈ m.boxes, b.exclusive = false ∧
      (b.parent = "" ∨ b.parent = "plot") ∧ b.role.id ≠ "group" := by
  have ha := successful_admitted m r h
  unfold admitted at ha
  obtain ⟨hp, hb⟩ := Bool.and_eq_true_iff.mp ha
  refine ⟨(of_decide_eq_true hp).1, ?_⟩
  intro b hm
  have ht := List.all_eq_true.mp hb b hm
  obtain ⟨ht, hr⟩ := Bool.and_eq_true_iff.mp ht
  obtain ⟨he, hparent⟩ := Bool.and_eq_true_iff.mp ht
  refine ⟨?_, of_decide_eq_true hparent, of_decide_eq_true hr⟩
  cases hx : b.exclusive <;> simp_all

theorem quadrant_c2 (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) : Validator.C2 r.scene.layoutDump := by
  have hn : ∀ b ∈ m.boxes, b.exclusive = false :=
    fun b hb => ((successful_metadata m r h).2 b hb).1
  have hout := Chart.Quadrant.successful_boxes_nonexclusive m r.scene
    (successful_layout_geometry m r h).1 hn
  intro b hb _ _ _ he
  have hf := hout b hb
  rw [hf] at he
  contradiction

theorem quadrant_c7_admitted (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) : Validator.C7 r.scene.layoutDump :=
  quadrant_c7 m r h (fun b hb => ((successful_metadata m r h).2 b hb).1)

theorem quadrant_c8 (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) : Validator.C8 r.scene.layoutDump :=
  Chart.Quadrant.successful_no_group_frames m r.scene
    (successful_layout_geometry m r h).1
    (fun b hb => ((successful_metadata m r h).2 b hb).2.2)

theorem tileParentWitness_rejected :
    layout tileParentWitness = .error (.geometry .domain) := by
  simp [layout, admitted, tileParentWitness]

theorem exclusiveIdWitness_rejected :
    layout exclusiveIdWitness = .error (.geometry .domain) := by
  simp [layout, admitted, exclusiveIdWitness]

theorem foreignGroupWitness_rejected :
    layout foreignGroupWitness = .error (.geometry .domain) := by
  have ha : admitted foreignGroupWitness = false := by decide
  unfold layout
  rw [ha]
  simp [foreignGroupWitness]

theorem negativePaddingWitness_rejected :
    layout negativePaddingWitness = .error (.geometry .domain) := by
  have ha : admitted negativePaddingWitness = false := by decide
  unfold layout
  rw [ha]
  simp [negativePaddingWitness]

theorem successful_reservation_constants (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r) :
    0 ≤ (Chart.Quadrant.constants m).titlePad ∧
    0 ≤ (Chart.Quadrant.constants m).xPad ∧
    0 ≤ (Chart.Quadrant.constants m).yPad ∧
    0 ≤ (Chart.Quadrant.constants m).radiusX ∧
    0 ≤ (Chart.Quadrant.constants m).radiusY := by
  have ha := successful_admitted m r h
  unfold admitted at ha
  have hp := of_decide_eq_true (Bool.and_eq_true_iff.mp ha).1
  exact hp.2

def negativeTitlePaddingWitness : Model :=
  { kind := "quadrant"
    profile := .cell
    options := { config := [("titlePadding", .integer (-16000))] }
    boxes := [{ id := "plot", exclusive := false }] }

theorem negativeTitlePaddingWitness_rejected :
    layout negativeTitlePaddingWitness = .error (.geometry .domain) := by
  have ha : admitted negativeTitlePaddingWitness = false := by decide
  unfold layout
  rw [ha]
  simp [negativeTitlePaddingWitness]

theorem quadrant_c1_of_nonnegative_reservations (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r)
    (ht : 0 ≤ (Chart.Quadrant.constants m).titlePad)
    (hx : 0 ≤ (Chart.Quadrant.constants m).xPad)
    (hy : 0 ≤ (Chart.Quadrant.constants m).yPad)
    (hp : ∀ g,
      Chart.Quadrant.arrange m (Chart.Quadrant.constants m)
        (Chart.Quadrant.pointInputs m) = .ok g →
      ∀ p ∈ g.pointBoxes, Rect.Contained g.plot p) :
    Validator.C1 r.scene.layoutDump := by
  have hm := (successful_metadata m r h).1
  apply quadrant_c1_of_nonneg_pads m r h hm.1 hm.2
  · intro g hg
    exact Chart.Quadrant.successful_arrange_nonnegative_reservations m
      (Chart.Quadrant.constants m) (Chart.Quadrant.pointInputs m) g hg ht hx hy
  · intro g hg _ i _
    exact Chart.Quadrant.successful_arrange_boxRect_contained m
      (Chart.Quadrant.constants m) (Chart.Quadrant.pointInputs m) g hg (hp g hg) i

theorem quadrant_c3_of_plot_index (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r)
    (hi : ∀ a i, (a, i) ∈ m.boxes.zipIdx → a.id = "plot" → i = 0)
    (hp : ∀ g,
      Chart.Quadrant.arrange m (Chart.Quadrant.constants m)
        (Chart.Quadrant.pointInputs m) = .ok g →
      ∀ p ∈ g.pointBoxes, Rect.Contained g.plot p) :
    Validator.C3 r.scene.layoutDump := by
  apply quadrant_c3_of_canonical_parents m r h
    (fun a ha => ((successful_metadata m r h).2 a ha).2.1)
  intro g hg
  constructor
  · intro a i ha hid
    rw [hi a i ha hid]
    rfl
  · intro _ i _ _
    exact Chart.Quadrant.successful_arrange_boxRect_contained m
      (Chart.Quadrant.constants m) (Chart.Quadrant.pointInputs m) g hg (hp g hg) i

theorem successful_pointBoxes_contained (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r)
    (hr : ∀ p ∈ decode m, -1 ≤ p.radius)
    (g : Chart.Quadrant.Geometry)
    (hg : Chart.Quadrant.arrange m (Chart.Quadrant.constants m)
      (Chart.Quadrant.pointInputs m) = .ok g) :
    ∀ p ∈ g.pointBoxes, Rect.Contained g.plot p := by
  have hc := successful_reservation_constants m r h
  apply Chart.Quadrant.successful_arrange_pointBoxes_contained m g hg
  · exact successful_point_coordinates m r h
  · exact Chart.Quadrant.successful_arrange_radii_nonneg m
      (Chart.Quadrant.constants m) (Chart.Quadrant.pointInputs m) g hg
      hc.2.2.2.1 hc.2.2.2.2 hr

theorem quadrant_c1_of_point_radii (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r)
    (hr : ∀ p ∈ decode m, -1 ≤ p.radius) :
    Validator.C1 r.scene.layoutDump := by
  have hc := successful_reservation_constants m r h
  exact quadrant_c1_of_nonnegative_reservations m r h hc.1 hc.2.1 hc.2.2.1
    (successful_pointBoxes_contained m r h hr)

theorem quadrant_c3_of_plot_first (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r)
    (hi : ∀ a i, (a, i) ∈ m.boxes.zipIdx → a.id = "plot" → i = 0)
    (hr : ∀ p ∈ decode m, -1 ≤ p.radius) :
    Validator.C3 r.scene.layoutDump :=
  quadrant_c3_of_plot_index m r h hi (successful_pointBoxes_contained m r h hr)

theorem quadrant_valid_of_plot_first_and_point_radii
    (m : Model) (r : Layered.FamilyResult)
    (h : layout m = .ok r)
    (hi : ∀ a i, (a, i) ∈ m.boxes.zipIdx → a.id = "plot" → i = 0)
    (hr : ∀ p ∈ decode m, -1 ≤ p.radius) :
    HardConstraints r.scene.layoutDump :=
  ⟨quadrant_c1_of_point_radii m r h hr,
    quadrant_c2 m r h,
    quadrant_c3_of_plot_first m r h hi hr,
    quadrant_c4 m r h,
    quadrant_c5 m r h,
    quadrant_c6 m r h,
    quadrant_c7_admitted m r h,
    quadrant_c8 m r h⟩

end Elegant.Kinds.Quadrant

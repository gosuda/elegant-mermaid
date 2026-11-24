import Elegant.Kinds.Swimlane
import Elegant.Kinds.SwimlaneValidSeams
import Elegant.Layered.LaneBands
import Elegant.Layered.LaneBandsLooseLowerProof
import Elegant.Layered.LayeredAdmission
import ElegantGeometry.Validator

set_option autoImplicit false

/-! The former endpoint condition and the above-lane premise.

The original `endsSplit` condition is false. Two executed witnesses are given below: a model whose
only route joins two top-level lane groups (`endsSplitWitnessG2G`), and one
whose route joins a lane group to a loose top-level node
(`endsSplitWitnessG2Loose`). On both, `layoutFamily` and the full
`Swimlane.layout` succeed, the model is `WellFormed`, passes
`layeredAdmissibleB`, and passes `nestedInLaneB`; the executed route has two
points whose first and last cross-axis coordinates coincide while the two
endpoint bands have different shifts, so the original disjunction fails.
Executed evidence: `proofs/wip/Probe/SwimlaneEndsAboveTProbe.lean`
(`g2g: endsSplit=FAIL e0 A->B sh=3050/13438 pts=2 f=3797 l=3797`,
`g2loose: endsSplit=FAIL e0 A->o sh=3072/10448 pts=2 f=3775 l=3775`) and
`proofs/wip/Probe/SwimlaneEndsAboveTWitnessCheck.lean`
(`wf=true adm=true nin=true layout-ok fam-ok`). The failing shape is an edge
whose endpoints are group boxes: it produces a two-point route with equal
cross-axis ends but different band shifts. The executed `layoutFamily`
equations cannot be kernel-checked here (`decide` diverges on the layout
fold), so the refutation is carried by the probe executions plus the
kernel-checked gate lemmas below.

`aboveLane` remains open but is narrowed to its non-vacuous core:
`AboveLaneResidual` asks for `PinLooseRouteAboveLaneBox` only when the model
has at least one lane and at least one loose top-level node, under the same
executed-run hypotheses plus `layeredAdmissibleB` (which the guarded
`Swimlane.layout` discharges through `admit`/`layeredAdmissibleB_spec`, the
same pattern the other seams use). The vacuous configurations are discharged
outright: `aboveLanePin_of_no_lanes` (no lane band, so no band has
`id ≠ ""`) and `aboveLanePin_of_no_loose` (no loose band, so no band has
`id = ""`, using `hadm` for nonempty box ids). `aboveLane_of_residual`
assembles the premise from the residual plus those lemmas. A later executed
LR/vector probe with one lane, two loose nodes, and a long route label refutes
the residual: pinning moves the loose route into an exclusive lane box and
the resulting scene fails C6. -/

namespace Elegant
namespace Kinds

open Elegant.Layered LaneBands

/-! ### `endsSplit`: refuted -/

/-- The per-route conclusion of the former `endsSplit` condition. -/
def EndsSplitRoute (m : Model) (base : Layered.FamilyResult) (sp : Spacing)
    (rt : Route) : Prop :=
  let axis := LaneBands.Axis.ofDirection m.options.direction
  let bands := layBands m.boxes base.scene axis sp (lanesOf m.boxes)
  bandShift bands rt.fromId = bandShift bands rt.toId ∨
    (axis.point (rt.points.head?.getD ⟨0, 0⟩) ≠
      axis.point (rt.points.getLast?.getD ⟨0, 0⟩) ∧ 1 < rt.points.length)

/-- The former `endsSplit` condition over an executed run. -/
def EndsSplitOn (m : Model) (base : Layered.FamilyResult) (sp : Spacing) : Prop :=
  ∀ rt ∈ base.scene.routes, EndsSplitRoute m base sp rt

/-- The disjunction fails when the endpoint shifts differ and the kink
clause fails: the exact failure mode of the witnesses. -/
theorem endsSplit_disjunction_eq_false {axis : LaneBands.Axis} {bands : List Band}
    {rt : Route}
    (hshift : bandShift bands rt.fromId ≠ bandShift bands rt.toId)
    (hkink : ¬ ((axis.point (rt.points.head?.getD ⟨0, 0⟩) ≠
        axis.point (rt.points.getLast?.getD ⟨0, 0⟩)) ∧
      1 < rt.points.length)) :
    ¬ (bandShift bands rt.fromId = bandShift bands rt.toId ∨
      ((axis.point (rt.points.head?.getD ⟨0, 0⟩) ≠
        axis.point (rt.points.getLast?.getD ⟨0, 0⟩)) ∧
        1 < rt.points.length)) := by
  rintro (heq | hk)
  · exact hshift heq
  · exact hkink hk

/-- A route exhibiting the failing shape refutes `EndsSplitOn` on the
executed run. -/
theorem endsSplitOn_false_of_route {m : Model} {base : Layered.FamilyResult}
    {sp : Spacing} {rt : Route} (hrt : rt ∈ base.scene.routes)
    (hshift : bandShift
        (layBands m.boxes base.scene (LaneBands.Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes)) rt.fromId ≠
      bandShift
        (layBands m.boxes base.scene (LaneBands.Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes)) rt.toId)
    (hkink : ¬ (((LaneBands.Axis.ofDirection m.options.direction).point
          (rt.points.head?.getD ⟨0, 0⟩) ≠
        (LaneBands.Axis.ofDirection m.options.direction).point
          (rt.points.getLast?.getD ⟨0, 0⟩)) ∧
      1 < rt.points.length)) :
    ¬ EndsSplitOn m base sp := by
  intro h
  exact endsSplit_disjunction_eq_false hshift hkink (h rt hrt)

/-! ### `endsSplit` witnesses -/

private def swLane (id : String) : ModelBox :=
  { id := id, role := .group, parent := "", exclusive := false }

private def swNode (id parent : String) : ModelBox :=
  { id := id, role := .node, parent := parent, exclusive := true }

private def swRoute (id fromId toId : String) : ModelRoute :=
  { id := id, fromId := fromId, toId := toId }

/-- Witness 1: a single edge between two top-level lane groups. Executed:
`layoutFamily (input endsSplitWitnessG2G) endsSplitWitnessG2G.options`
returns `.ok` with route `e0 : A -> B` of two points whose cross-axis ends
coincide while the endpoint band shifts differ (probe `g2g` above). -/
def endsSplitWitnessG2G : Model :=
  { kind := "swimlane",
    boxes := [swLane "A", swNode "a1" "A", swLane "B", swNode "b1" "B"],
    routes := [swRoute "e0" "A" "B"],
    labels := [] }

/-- Witness 2: a single edge from a lane group to a loose top-level node.
Executed: `layoutFamily` returns `.ok` with route `e0 : A -> o` of two
points whose cross-axis ends coincide while the endpoint band shifts
differ (probe `g2loose` above). -/
def endsSplitWitnessG2Loose : Model :=
  { kind := "swimlane",
    boxes := [swLane "A", swNode "a1" "A", swNode "o" ""],
    routes := [swRoute "e0" "A" "o"],
    labels := [] }

/-- Both witnesses pass every hypothesis of the field except the
executed-run equations that the probes supply: well-formedness, layered
admission, lane nesting, and a spacing. -/
theorem endsSplitWitnessG2G_gates :
    WellFormed endsSplitWitnessG2G = true ∧
      layeredAdmissibleB (Swimlane.input endsSplitWitnessG2G) = true ∧
      Swimlane.nestedInLaneB endsSplitWitnessG2G.boxes = true ∧
      ∃ sp : Spacing, spacingOf endsSplitWitnessG2G.options.profile = .ok sp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · exact ⟨_, rfl⟩

theorem endsSplitWitnessG2Loose_gates :
    WellFormed endsSplitWitnessG2Loose = true ∧
      layeredAdmissibleB (Swimlane.input endsSplitWitnessG2Loose) = true ∧
      Swimlane.nestedInLaneB endsSplitWitnessG2Loose.boxes = true ∧
      ∃ sp : Spacing, spacingOf endsSplitWitnessG2Loose.options.profile = .ok sp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · exact ⟨_, rfl⟩

/-! ### Band id characterizations -/

/-- Every `layLanes` band id is one of the lane names. -/
private theorem layLanes_band_id_eq {boxes : List ModelBox} {s : Scene}
    {axis : LaneBands.Axis} {sp : Spacing} : ∀ (lanes : List String) (start : Int)
    {band : Band},
    band ∈ layLanes boxes s axis sp lanes start →
      ∃ lane ∈ lanes, band.id = lane := by
  intro lanes
  induction lanes with
  | nil =>
    intro start band hb
    simp [layLanes] at hb
  | cons lane rest ih =>
    intro start band hb
    simp only [layLanes, List.mem_cons] at hb
    rcases hb with rfl | hrest
    · exact ⟨lane, List.mem_cons.mpr (Or.inl rfl), rfl⟩
    · obtain ⟨l, hl, hid⟩ := ih _ hrest
      exact ⟨l, List.mem_cons_of_mem _ hl, hid⟩

/-- A lane name is the id of a box of the model. -/
private theorem lanesOf_id_mem {boxes : List ModelBox} {lane : String}
    (h : lane ∈ lanesOf boxes) : ∃ b ∈ boxes, b.id = lane := by
  unfold lanesOf at h
  obtain ⟨b, hbF, hid⟩ := List.mem_map.mp h
  obtain ⟨hb, -⟩ := List.mem_filter.mp hbF
  exact ⟨b, hb, hid⟩

/-- The loose band's id is always `""`. -/
private theorem looseBand_id (boxes : List ModelBox) (s : Scene) (axis : LaneBands.Axis)
    (sp : Spacing) (loose : List String) (start : Int) :
    (looseBand boxes s axis sp loose start).id = "" := by
  unfold looseBand
  split <;> rfl

/-- With no loose top-level nodes `layBands` is just the lane bands. -/
private theorem layBands_eq_layLanes_of_no_loose {boxes : List ModelBox}
    {s : Scene} {axis : LaneBands.Axis} {sp : Spacing} {lanes : List String}
    (hloose : looseNodes boxes = []) :
    layBands boxes s axis sp lanes =
      layLanes boxes s axis sp lanes (firstLaneStart s lanes axis) := by
  have hEmpty : (looseNodes boxes).isEmpty = true := by rw [hloose]; rfl
  unfold layBands
  simp [hEmpty]

/-- With an empty lane list `layBands` is the empty lane list plus at most
the loose band. -/
private theorem layBands_nil_lanes (boxes : List ModelBox) (s : Scene)
    (axis : LaneBands.Axis) (sp : Spacing) :
    layBands boxes s axis sp [] =
      if (looseNodes boxes).isEmpty then
        layLanes boxes s axis sp [] (firstLaneStart s [] axis)
      else
        layLanes boxes s axis sp [] (firstLaneStart s [] axis) ++
          [looseBand boxes s axis sp (looseNodes boxes)
            (firstLaneStart s [] axis +
              ((layLanes boxes s axis sp [] (firstLaneStart s [] axis)).map
                (·.thickness)).sum)] := rfl

/-- With no lanes, every band of `layBands` has id `""`. -/
private theorem layBands_id_eq_empty_of_no_lanes {m : Model}
    (hlanes : lanesOf m.boxes = [])
    {s : Scene} {axis : LaneBands.Axis} {sp : Spacing} :
    ∀ band ∈ layBands m.boxes s axis sp (lanesOf m.boxes), band.id = "" := by
  intro band hbnd
  rw [hlanes, layBands_nil_lanes] at hbnd
  have hnil : layLanes m.boxes s axis sp [] (firstLaneStart s [] axis) = [] := rfl
  cases hE : (looseNodes m.boxes).isEmpty
  · simp [hE, hnil] at hbnd
    obtain rfl := hbnd
    exact looseBand_id _ _ _ _ _ _
  · simp [hE, hnil] at hbnd

/-- With no loose top-level nodes and nonempty box ids (from
`layeredAdmissibleB`), every band of `layBands` has a nonempty lane id. -/
private theorem layBands_id_ne_empty_of_no_loose {m : Model}
    (hadm : layeredAdmissibleB (Swimlane.input m) = true)
    (hloose : looseNodes m.boxes = [])
    {s : Scene} {axis : LaneBands.Axis} {sp : Spacing} :
    ∀ band ∈ layBands m.boxes s axis sp (lanesOf m.boxes), band.id ≠ "" := by
  intro band hbnd
  rw [layBands_eq_layLanes_of_no_loose hloose] at hbnd
  obtain ⟨lane, hlane, hid⟩ := layLanes_band_id_eq _ _ hbnd
  obtain ⟨b, hbmem, hbid⟩ := lanesOf_id_mem hlane
  have hspec := layeredAdmissibleB_ids hadm
  have hbne : b.id ≠ "" := hspec b hbmem
  rw [hid, ← hbid]
  exact hbne

/-! ### `aboveLane`: vacuous cases and the narrowed residual -/

/-- The `aboveLane` field conclusion over an executed run. -/
def AboveLanePin (m : Model) (base : Layered.FamilyResult) (sp : Spacing) : Prop :=
  PinLooseRouteAboveLaneBox (LaneBands.Axis.ofDirection m.options.direction)
    (layBands m.boxes base.scene (LaneBands.Axis.ofDirection m.options.direction) sp
      (lanesOf m.boxes)) base.scene

/-- No lanes: every band has id `""`, so the `(bands[j]).id ≠ ""`
hypothesis of `PinLooseRouteAboveLaneBox` is never satisfied. -/
theorem aboveLanePin_of_no_lanes {m : Model} {base : Layered.FamilyResult}
    {sp : Spacing} (hlanes : lanesOf m.boxes = []) :
    AboveLanePin m base sp := by
  intro old hold b_old hbmem hexcl hscope j1 hj1 hid1 hfromj htoj j hj hidj hbj p hp
  exfalso
  have hmem : (layBands m.boxes base.scene
      (LaneBands.Axis.ofDirection m.options.direction) sp (lanesOf m.boxes))[j]'hj ∈
      layBands m.boxes base.scene (LaneBands.Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes) := List.getElem_mem hj
  exact hidj (layBands_id_eq_empty_of_no_lanes hlanes _ hmem)

/-- No loose top-level nodes: every band has a nonempty lane id, so the
`(bands[j1]).id = ""` hypothesis is never satisfied. Needs `hadm` for
nonempty box ids. -/
theorem aboveLanePin_of_no_loose {m : Model} {base : Layered.FamilyResult}
    {sp : Spacing}
    (hadm : layeredAdmissibleB (Swimlane.input m) = true)
    (hloose : looseNodes m.boxes = []) :
    AboveLanePin m base sp := by
  intro old hold b_old hbmem hexcl hscope j1 hj1 hid1 hfromj htoj j hj hidj hbj p hp
  exfalso
  have hmem : (layBands m.boxes base.scene
      (LaneBands.Axis.ofDirection m.options.direction) sp (lanesOf m.boxes))[j1]'hj1 ∈
      layBands m.boxes base.scene (LaneBands.Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes) := List.getElem_mem hj1
  exact (layBands_id_ne_empty_of_no_loose hadm hloose _ hmem) hid1

/-- The non-vacuous core of `aboveLane`: the pin inequality is required
only when the model has at least one lane and at least one loose top-level
node. Same executed-run hypotheses as the field, plus `hadm`. -/
def AboveLaneResidual (m : Model) : Prop :=
  layeredAdmissibleB (Swimlane.input m) = true →
    ∀ base : Layered.FamilyResult,
      Layered.layoutFamily (Swimlane.input m) m.options = .ok base →
      ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      ∀ (s1 : Scene),
        applyPin (buildPin (LaneBands.Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (LaneBands.Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes)) base.scene)
          (layBands m.boxes base.scene (LaneBands.Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes)) base.scene = .ok s1 →
        (∃ lane, lane ∈ lanesOf m.boxes) → (∃ b, b ∈ looseNodes m.boxes) →
        AboveLanePin m base sp

/-- The `aboveLane` field follows from `AboveLaneResidual` plus the two
vacuous cases, under `layeredAdmissibleB` (discharged by the guarded
`Swimlane.layout` through `admit`/`layeredAdmissibleB_spec`). -/
theorem aboveLane_of_residual {m : Model}
    (hadm : layeredAdmissibleB (Swimlane.input m) = true)
    (hres : AboveLaneResidual m) :
    ∀ base : Layered.FamilyResult,
      Layered.layoutFamily (Swimlane.input m) m.options = .ok base →
      ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      ∀ (s1 : Scene),
        applyPin (buildPin (LaneBands.Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (LaneBands.Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes)) base.scene)
          (layBands m.boxes base.scene (LaneBands.Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes)) base.scene = .ok s1 →
        AboveLanePin m base sp := by
  intro base hexec sp hsp s1 hpin
  by_cases hlanes : lanesOf m.boxes = []
  · exact aboveLanePin_of_no_lanes hlanes
  · have hne : ∃ lane, lane ∈ lanesOf m.boxes :=
      List.exists_mem_of_ne_nil _ hlanes
    by_cases hloose : looseNodes m.boxes = []
    · exact aboveLanePin_of_no_loose hadm hloose
    · exact hres hadm base hexec sp hsp s1 hpin hne
        (List.exists_mem_of_ne_nil _ hloose)

end Kinds
end Elegant

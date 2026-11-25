import Elegant.Kinds.Swimlane
import Elegant.Kinds.SwimlaneEndsSplitCutover
import Elegant.Kinds.SwimlaneEndsExecutedProof
import Elegant.Kinds.SwimlaneBaseFactsProof
import Elegant.Layered.FamilyAssembly
import Elegant.Layered.InputFixedFit
import Elegant.Layered.BoxRouteIdsDisjoint
import Elegant.Layered.LayeredAdmission
import Elegant.Layered.LaneEndsPinLanesClauses
import Elegant.Layered.LaneEndsPinFacts
import Elegant.Layered.LaneEndsPinGapClear
import Elegant.Layered.LaneEndsPinRerouteBoundary
import Elegant.Layered.LaneEndsRouteClauses
import Elegant.Layered.LaneEndsClauses
import Elegant.Layered.LaneBandsCoverage
import Elegant.Layered.LaneBandsCoverageProof
import Elegant.Layered.LaneBandsBoxClausesProof
import Elegant.Layered.LaneBandsSetupResidualProof
import Elegant.Layered.LaneBandsFrameClause
import Elegant.Layered.LaneBandsFindRouteFactsProof
import Elegant.Layered.LaneBandsKeptClearExecutedProof
import Elegant.Layered.LaneBandsFrameClauseExecuted
import Elegant.Layered.LaneBandsLooseRouteBoundProof
import Elegant.Layered.LaneBandsRouteClausesProof
import Elegant.Layered.SceneParentsProof
import Elegant.Layered.OrthogonalityFacts
import Elegant.Layered.SwimlanePinPointOrthogonalityProof
import ElegantGeometry.Validator

set_option autoImplicit false

/-! The swimlane adapter transports layered family validity through
`Layered.LaneBands.pinLanes`. A successful layout supplies lane nesting and
layered admission, from which `swimlane_endsPremise_of_admitted` derives the
executed route-end disjunction needed by `swimlane_endsOld_of_premise`.
The former same-band-or-kink condition fails on `endsSplitWitnessG2G` and
`endsSplitWitnessG2Loose`: both have a two-point route with equal cross-axis
endpoint coordinates but different band shifts.

Layered admission and base C5 also give the loose-route above-box bound,
which supplies victim clearance for `pinBands_c6_executed_closed`. -/
namespace Elegant
namespace Kinds

open Elegant.Layered.LaneBands
open Elegant.Layered

/-- Lane admission soundness: the executable `Swimlane.nestedInLaneB` check
implies `NestedInLane`. The guarded `Swimlane.layout` discharges the check,
so the former `admit` seam is derived, not travelled. -/
theorem nestedInLaneB_spec {boxes : List ModelBox}
    (h : Swimlane.nestedInLaneB boxes = true) :
    NestedInLane boxes := by
  intro b hbmem hpar
  have hall : (b.parent == "" ||
      (lanesOf boxes).any fun lane => inLane boxes b.id lane) = true :=
    List.all_eq_true.mp h b hbmem
  rw [Bool.or_eq_true] at hall
  rcases hall with htop | hlane
  · have heq : b.parent = "" := beq_iff_eq.mp htop
    exact absurd heq hpar
  · obtain ⟨lane, hlm, hin⟩ := List.any_eq_true.mp hlane
    exact ⟨lane, hlm, hin⟩

/-- Executed scene ids match the model box ids (from `layoutFamily_ids`;
the swimlane input carries model boxes verbatim). -/
private theorem swimPin_idsEq {m : Model} {base : Layered.FamilyResult}
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base) :
    base.scene.boxes.map (·.id) = m.boxes.map (·.id) := by
  have h1 := (Layered.layoutFamily_ids hfam).1
  have heq : (Swimlane.input m).boxes = m.boxes := rfl
  rw [heq] at h1
  exact h1

/-- Executed scene route ids match the model route ids. -/
private theorem swimPin_routesEq {m : Model} {base : Layered.FamilyResult}
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base) :
    base.scene.routes.map (·.id) = m.routes.map (·.id) := by
  have h2 := (Layered.layoutFamily_ids hfam).2
  have heq : (Swimlane.input m).routes = m.routes := rfl
  rw [heq] at h2
  exact h2

/-- Executed scene boxes have nonempty ids by layered admission. -/
private theorem swimPin_sceneNe {m : Model} {base : Layered.FamilyResult}
    (hne : ∀ b ∈ m.boxes, b.id ≠ "")
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base)
    {b : Box} (hb : b ∈ base.scene.boxes) : b.id ≠ "" := by
  have hmem : b.id ∈ base.scene.boxes.map (·.id) :=
    List.mem_map.mpr ⟨b, hb, rfl⟩
  rw [swimPin_idsEq hfam] at hmem
  obtain ⟨mb, hmb, hid⟩ := List.mem_map.mp hmem
  have hne := hne mb hmb
  rw [hid] at hne
  exact hne

/-- The `find?` endpoint form (`hEndsBox`) from the membership facts. -/
private theorem swimPin_endsBox {_m : Model} {base : Layered.FamilyResult}
    (hends : ∀ rt ∈ base.scene.routes,
      (∃ fb ∈ base.scene.boxes, fb.id = rt.fromId) ∧
        ∃ tb ∈ base.scene.boxes, tb.id = rt.toId)
    {rt : Route} (hrt : rt ∈ base.scene.routes) :
    (base.scene.boxes.find? (fun b => b.id == rt.fromId)).isSome = true ∧
      (base.scene.boxes.find? (fun b => b.id == rt.toId)).isSome = true := by
  obtain ⟨hfrom, hto⟩ := hends rt hrt
  obtain ⟨fb, hfb, hfid⟩ := hfrom
  obtain ⟨tb, htb, htid⟩ := hto
  have hbeqF : (fun b : Box => b.id == rt.fromId) fb = true :=
    beq_iff_eq.mpr hfid
  have hbeqT : (fun b : Box => b.id == rt.toId) tb = true :=
    beq_iff_eq.mpr htid
  refine ⟨?_, ?_⟩
  · exact List.find?_isSome.mpr ⟨fb, hfb, beq_iff_eq.mpr hfid⟩
  · exact List.find?_isSome.mpr ⟨tb, htb, beq_iff_eq.mpr htid⟩

/-- Route endpoints name scene boxes, from base C5: the endpoint boundary
lookups give `box? = some` for both ends, hence membership and id equality.
This closes the former `endsBox` seam; no record field remains. -/
private theorem swimPin_endsBox_of_c5 {base : Layered.FamilyResult}
    (hC5 : Validator.C5 base.scene.layoutDump) :
    ∀ rt ∈ base.scene.routes,
      (∃ fb ∈ base.scene.boxes, fb.id = rt.fromId) ∧
        ∃ tb ∈ base.scene.boxes, tb.id = rt.toId := by
  intro rt hrt
  have hmem : rt ∈ base.scene.layoutDump.routes := hrt
  obtain ⟨p, q, fb, tb, _, _, hfb, htb, _, _⟩ := hC5 rt hmem
  unfold LayoutDump.box? at hfb htb
  have hmemFb : fb ∈ base.scene.boxes :=
    List.mem_of_find?_eq_some hfb
  have hmemTb : tb ∈ base.scene.boxes :=
    List.mem_of_find?_eq_some htb
  exact ⟨⟨fb, hmemFb,
    beq_iff_eq.mp (List.find?_some (p := fun b : Box => b.id == rt.fromId) (a := fb) hfb)⟩,
    ⟨tb, hmemTb,
    beq_iff_eq.mp (List.find?_some (p := fun b : Box => b.id == rt.toId) (a := tb) htb)⟩⟩

/-- Input cleanliness for the executed scene: nonempty ids plus box/route
id disjointness, from the layered guard and family id transport. -/
private theorem swimPin_clean {m : Model} {base : Layered.FamilyResult}
    (hne : ∀ b ∈ m.boxes, b.id ≠ "")
    (hdisj : Layered.PipelineImpl.BoxRouteIdsDisjoint (Swimlane.input m))
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base) :
    LaneInputIdsClean base.scene := by
  have hSceneNe : ∀ b ∈ base.scene.boxes, b.id ≠ "" :=
    fun b hb => swimPin_sceneNe hne hfam hb
  refine ⟨hSceneNe, ?_⟩
  intro b hb rt hrt hcon
  have hbM : b.id ∈ (Swimlane.input m).boxes.map (·.id) := by
    have hmem : b.id ∈ base.scene.boxes.map (·.id) :=
      List.mem_map.mpr ⟨b, hb, rfl⟩
    rw [swimPin_idsEq hfam] at hmem
    exact hmem
  have hrM : rt.id ∈ (Swimlane.input m).routes.map (·.id) := by
    have hmem : rt.id ∈ base.scene.routes.map (·.id) :=
      List.mem_map.mpr ⟨rt, hrt, rfl⟩
    rw [swimPin_routesEq hfam] at hmem
    exact hmem
  have hnot := hdisj b.id hbM
  rw [hcon] at hnot
  exact hnot hrM

/-- Model parent links are valid: every parent is `""` or a model box id
(via the public parent induction over `WellFormed`). -/
private theorem swimPin_parentMem {m : Model} (hwf : WellFormed m)
    {b : ModelBox} (hb : b ∈ m.boxes) :
    b.parent = "" ∨ b.parent ∈ m.boxes.map (·.id) :=
  Elegant.parent_induction m hwf
    (fun id => id = "" ∨ id ∈ m.boxes.map (·.id)) (Or.inl rfl)
    (fun b hb _ => Or.inr (List.mem_map.mpr ⟨b, hb, rfl⟩)) b hb

/-- Scene shape for the executed scene: nonempty ids plus valid parent
links, from the family parent mirror and model parent validity. -/
private theorem swimPin_shape {m : Model} {base : Layered.FamilyResult}
    (hwf : WellFormed m)
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base)
    (hne : ∀ b ∈ m.boxes, b.id ≠ "") :
    LaneSceneShape base.scene := by
  have hSceneNe : ∀ b ∈ base.scene.boxes, b.id ≠ "" :=
    fun b hb => swimPin_sceneNe hne hfam hb
  refine ⟨hSceneNe, ?_⟩
  have hmirror := Layered.PipelineImpl.layoutFamily_scene_parents hfam
    (Layered.layoutFamily_wellFormed hfam)
  intro sb hsb
  obtain ⟨mb, hmb, _hid, hpar⟩ := hmirror sb hsb
  have hpm := swimPin_parentMem hwf (m := m) hmb
  rw [hpar]
  rcases hpm with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [swimPin_idsEq hfam]; exact h)

/-- Executed scene box-id nodup from model nodup via the id transport. -/
private theorem swimPin_sceneNodup {m : Model} {base : Layered.FamilyResult}
    (hwf : WellFormed m)
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base) :
    (base.scene.boxes.map (·.id)).Nodup := by
  have h := Model.boxIds_nodup hwf
  rw [swimPin_idsEq hfam]
  exact h

/-- Executed scene route-id nodup from model nodup via the id transport. -/
private theorem swimPin_routeNodup {m : Model} {base : Layered.FamilyResult}
    (hwf : WellFormed m)
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base) :
    (base.scene.routes.map (·.id)).Nodup := by
  have h := Model.routeIds_nodup hwf
  rw [swimPin_routesEq hfam]
  exact h

/-- Executed box coverage from lane admission. -/
private theorem swimPin_cover {m : Model} {base : Layered.FamilyResult}
    (hadm : NestedInLane m.boxes)
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base)
    (sp : Spacing) (hsp : spacingOf m.options.profile = .ok sp) :
    PinBoxCoverage m.boxes base.scene (Axis.ofDirection m.options.direction) sp :=
  swimlane_pinBoxCoverage hfam hsp hadm

/-- Executed pin setup from lane admission plus model health. -/
private theorem swimPin_setup {m : Model} {base : Layered.FamilyResult}
    (hadm : NestedInLane m.boxes) (hne : ∀ b ∈ m.boxes, b.id ≠ "")
    (hwf : WellFormed m)
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base)
    (sp : Spacing) (hsp : spacingOf m.options.profile = .ok sp) :
    PinSetup base.scene
      (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes)) :=
  swimlane_pinSetup_closed hfam hsp hadm hwf hne

/-- Executed scene parents from lane admission plus model health. -/
private theorem swimPin_parents {m : Model} {base : Layered.FamilyResult}
    (hadm : NestedInLane m.boxes) (hne : ∀ b ∈ m.boxes, b.id ≠ "")
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base)
    (sp : Spacing) (hsp : spacingOf m.options.profile = .ok sp) :
    PinSceneParents m.boxes base.scene
      (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes)) := by
  have h := Layered.PipelineImpl.swimlane_pinSceneParents
    (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
      (lanesOf m.boxes))
    hfam hsp hadm rfl hne
  exact h

/-- Gap clearance for the executed pin, via the closed gap theorem. -/
private theorem swimPin_gap {m : Model} {base : Layered.FamilyResult}
    {pinned : Scene} {sp : Spacing}
    (hadm : NestedInLane m.boxes) (hne : ∀ b ∈ m.boxes, b.id ≠ "")
    (hwf : WellFormed m)
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base)
    (hC3 : Validator.C3 base.scene.layoutDump)
    (hsp : spacingOf m.options.profile = .ok sp)
    (hpin : pinBands m.boxes m.options base.scene = .ok pinned) :
    GapClear (Axis.ofDirection m.options.direction)
      (laneFrames (Axis.ofDirection m.options.direction)
        (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes)) base.scene)
      pinned.layoutDump := by
  have hNoEmpty : ∀ b ∈ base.scene.boxes, b.id ≠ "" :=
    fun b hb => swimPin_sceneNe hne hfam hb
  have hsNodup := swimPin_sceneNodup hwf hfam
  have hBoxesNodup := Model.boxIds_nodup hwf
  have hShape := swimPin_shape hwf hfam hne
  have hcover := swimPin_cover hadm hfam sp hsp
  have hParents := swimPin_parents hadm hne hfam sp hsp
  exact pinBands_gapClear_closed hNoEmpty hsNodup hBoxesNodup hne
    hC3 hShape sp hsp hcover hParents hpin

/-- Frame fit for the executed pin, via the closed fit theorem. -/
private theorem swimPin_fit {m : Model} {base : Layered.FamilyResult}
    {pinned : Scene} {sp : Spacing}
    (hne : ∀ b ∈ m.boxes, b.id ≠ "") (hwf : WellFormed m)
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base)
    (hsp : spacingOf m.options.profile = .ok sp)
    (hpin : pinBands m.boxes m.options base.scene = .ok pinned) :
    FramesFit (Axis.ofDirection m.options.direction)
      (laneFrames (Axis.ofDirection m.options.direction)
        (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes)) base.scene)
      pinned.layoutDump := by
  have hNoEmpty : ∀ b ∈ base.scene.boxes, b.id ≠ "" :=
    fun b hb => swimPin_sceneNe hne hfam hb
  have hsNodup := swimPin_sceneNodup hwf hfam
  have hBoxesNodup := Model.boxIds_nodup hwf
  exact pinBands_framesFit hNoEmpty hBoxesNodup hne hsNodup hpin sp hsp

/-- Nonnegative frame lengths for the executed pin, via the closed length
transport over the proved executed-box positivity. -/
private theorem swimPin_len {m : Model} {base : Layered.FamilyResult}
    {pinned : Scene} {sp : Spacing}
    (hne : ∀ b ∈ m.boxes, b.id ≠ "")
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base)
    (hsp : spacingOf m.options.profile = .ok sp)
    (hpin : pinBands m.boxes m.options base.scene = .ok pinned) :
    ∀ f ∈ laneFrames (Axis.ofDirection m.options.direction)
      (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes)) base.scene, 0 ≤ f.length := by
  have hNoEmpty : ∀ b ∈ base.scene.boxes, b.id ≠ "" :=
    fun b hb => swimPin_sceneNe hne hfam hb
  have hNonneg := swimlane_boxNonneg hfam
  exact pinBands_framesLenNonneg hNonneg hNoEmpty hpin sp hsp

/-- Pinned exclusive positivity, via the closed positivity transport over
the proved executed-box positivity. -/
private theorem swimPin_pos {m : Model} {base : Layered.FamilyResult}
    {pinned : Scene}
    (hne : ∀ b ∈ m.boxes, b.id ≠ "")
    (hwf : WellFormed m)
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base)
    (hpin : pinBands m.boxes m.options base.scene = .ok pinned) :
    ExclusivePositive pinned.layoutDump := by
  have hNoEmpty : ∀ b ∈ base.scene.boxes, b.id ≠ "" :=
    fun b hb => swimPin_sceneNe hne hfam hb
  have hsNodup := swimPin_sceneNodup hwf hfam
  have hBoxesNodup := Model.boxIds_nodup hwf
  have hPosS := swimlane_basePos hfam
  exact pinBands_exclusivePositive hPosS hNoEmpty hBoxesNodup hne
    hsNodup hpin

/-- The pin preserves boundary endpoints on admitted swimlane runs. -/
private theorem swimPin_endsOld {m : Model} {base : Layered.FamilyResult}
    {r : Scene}
    (hadm : NestedInLane m.boxes)
    (hadmitted : Layered.layeredAdmissibleB (Swimlane.input m) = true)
    (hne : ∀ b ∈ m.boxes, b.id ≠ "") (hwf : WellFormed m)
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base)
    (hC5 : Validator.C5 base.scene.layoutDump)
    (hlanes : lanesOf m.boxes ≠ [])
    (hpin : pinBands m.boxes m.options base.scene = .ok r) :
    ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      EndsOnOld (Axis.ofDirection m.options.direction)
        (laneFrames (Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes)) base.scene)
        r.layoutDump := by
  have hrouteNodup := swimPin_routeNodup hwf hfam
  have hnodupB := swimPin_sceneNodup hwf hfam
  have hNoEmpty : ∀ b ∈ base.scene.boxes, b.id ≠ "" :=
    fun b hb => swimPin_sceneNe hne hfam hb
  have hModelClean : (m.boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ m.boxes, b.id ≠ "" :=
    ⟨Model.boxIds_nodup hwf, hne⟩
  have hEnds := SwimlaneEndsExecuted.swimlane_endsPremise_of_admitted hadm hadmitted
  exact SwimlaneEndsCutover.swimlane_endsOld_of_premise hC5 hlanes hrouteNodup
    hnodupB hNoEmpty (hEnds base hfam) findRouteEndsPin_holds hModelClean hpin

/-- The executed kept-clear bundle follows from the base validity and pin setup. -/
private theorem swimPin_kept {m : Model} {base : Layered.FamilyResult}
    (hadm : NestedInLane m.boxes) (hne : ∀ b ∈ m.boxes, b.id ≠ "")
    (hwf : WellFormed m)
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base)
    (hbase : HardConstraints base.scene.layoutDump)
    (sp : Spacing) (hsp : spacingOf m.options.profile = .ok sp)
    (s1 : Scene)
    (happ : applyPin (buildPin (Axis.ofDirection m.options.direction)
        (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes)) base.scene)
        (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes)) base.scene = .ok s1) :
    PinKeptClearExecuted (Axis.ofDirection m.options.direction)
      (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes)) base.scene s1 m.boxes sp := by
  have hcover := swimPin_cover hadm hfam sp hsp
  have hends := swimPin_endsBox_of_c5 hbase.2.2.2.2.1
  have hsetup := swimPin_setup hadm hne hwf hfam sp hsp
  have hParents := swimPin_parents hadm hne hfam sp hsp
  have hrouteNodup := swimPin_routeNodup hwf hfam
  have hsNodup := swimPin_sceneNodup hwf hfam
  have hBoxesNodup := Model.boxIds_nodup hwf
  have hnn := spacing_of_nonneg hsp
  exact ⟨rfl, happ, hbase, hcover, hends, hsetup, hParents, hrouteNodup,
    hsNodup, hBoxesNodup, hne, hnn⟩

/-- C6 after the executed pin, using the loose-route above-box bound. -/
private theorem swimPin_c6mid {m : Model} {base : Layered.FamilyResult}
    {pinned : Scene}
    (hadm : NestedInLane m.boxes)
    (hne : ∀ b ∈ m.boxes, b.id ≠ "") (hwf : WellFormed m)
    (hfam : Layered.layoutFamily (Swimlane.input m) m.options = .ok base)
    (hbase : HardConstraints base.scene.layoutDump)
    (hpin : pinBands m.boxes m.options base.scene = .ok pinned) :
    Validator.C6 pinned.layoutDump := by
  have hkept : ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      ∀ (s1 : Scene),
        applyPin (buildPin (Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes)) base.scene)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes)) base.scene = .ok s1 →
        PinKeptClearExecuted (Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes)) base.scene s1 m.boxes sp :=
    fun sp hsp s1 happ => swimPin_kept hadm hne hwf hfam hbase sp hsp s1 happ
  exact pinBands_c6_executed_closed hfam hpin hbase hkept (fun sp hsp _ _ =>
    swimlane_pinLooseRouteAboveLaneBox (sp := sp) hfam hne hbase.2.2.2.2.1 hsp)

/-- A successful swimlane layout satisfies the hard constraints. -/
theorem swimlane_valid
    {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (_hlim : WithinLimits m)
    (h : Swimlane.layout m = .ok result) :
    HardConstraints result.scene.layoutDump := by
  obtain ⟨base, pinned, hfam, hpinLanes, hdump⟩ := Swimlane.layout_dump h
  have hn := Swimlane.layout_nested h
  have ha := Swimlane.layout_admissible h
  have hadm : NestedInLane m.boxes := nestedInLaneB_spec hn
  have hspec := Layered.layeredAdmissibleB_spec ha m.options
  obtain ⟨hids, hdisj, hfix, -⟩ := hspec
  have hne : ∀ b ∈ m.boxes, b.id ≠ "" := hids
  have hbase : HardConstraints base.scene.layoutDump :=
    Layered.PipelineImpl.layoutFamily_valid_of_seams hids hfix hdisj hfam
  have hclean := swimPin_clean hne hdisj hfam
  have hshape := swimPin_shape hwf hfam hne
  have hBoxesNodup := Model.boxIds_nodup hwf
  have hsNodup := swimPin_sceneNodup hwf hfam
  have hNoEmpty : ∀ b ∈ base.scene.boxes, b.id ≠ "" :=
    fun b hb => swimPin_sceneNe hne hfam hb
  have hrouteNodup := swimPin_routeNodup hwf hfam
  have hcov : ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      PinBoxCoverage m.boxes base.scene (Axis.ofDirection m.options.direction) sp :=
    fun sp hsp => swimPin_cover hadm hfam sp hsp
  have hsetup : ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      PinSetup base.scene
        (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes)) :=
    fun sp hsp => swimPin_setup hadm hne hwf hfam sp hsp
  have hEndsBox : ∀ rt ∈ base.scene.routes,
      (base.scene.boxes.find? (fun b => b.id == rt.fromId)).isSome = true ∧
        (base.scene.boxes.find? (fun b => b.id == rt.toId)).isSome = true :=
    fun rt hrt => swimPin_endsBox (_m := m) (swimPin_endsBox_of_c5 hbase.2.2.2.2.1) hrt
  have hFit : ∀ (pinned : Scene), pinBands m.boxes m.options base.scene = .ok pinned →
      ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      FramesFit (Axis.ofDirection m.options.direction)
        (laneFrames (Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes)) base.scene)
        pinned.layoutDump :=
    fun pinned hpin sp hsp => swimPin_fit hne hwf hfam hsp hpin
  have hGap : ∀ (pinned : Scene), pinBands m.boxes m.options base.scene = .ok pinned →
      ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      GapClear (Axis.ofDirection m.options.direction)
        (laneFrames (Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes)) base.scene)
        pinned.layoutDump :=
    fun pinned hpin sp hsp => swimPin_gap hadm hne hwf hfam hbase.2.2.1 hsp hpin
  have hPos : ∀ (pinned : Scene), pinBands m.boxes m.options base.scene = .ok pinned →
      ExclusivePositive pinned.layoutDump :=
    fun pinned hpin => swimPin_pos hne hwf hfam hpin
  have hLen : ∀ (pinned : Scene), pinBands m.boxes m.options base.scene = .ok pinned →
      ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      ∀ f ∈ laneFrames (Axis.ofDirection m.options.direction)
        (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes)) base.scene, 0 ≤ f.length :=
    fun pinned hpin sp hsp => swimPin_len hne hfam hsp hpin
  have hParents : ∀ sp : Spacing, ∀ bands : List Band,
      spacingOf m.options.profile = .ok sp →
      bands = layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes) →
      PinSceneParents m.boxes base.scene bands := by
    intro sp bands hsp hb
    have hP := swimPin_parents hadm hne hfam sp hsp
    rw [hb]
    exact hP
  have hC1 : Validator.C1 pinned.layoutDump :=
    pinLanes_c1 hbase.1 hpinLanes
  have hC2 : Validator.C2 pinned.layoutDump :=
    pinLanes_c2 hcov hBoxesNodup hne hsetup hbase.2.1 hpinLanes
  have hC3 : Validator.C3 pinned.layoutDump :=
    pinLanes_c3 hcov hsNodup hBoxesNodup hne hbase.2.2.1 hsetup hpinLanes
  have hC4 : Validator.C4 pinned.layoutDump :=
    pinLanes_c4 hbase.2.2.2.1 hrouteNodup hcov hEndsBox findRouteOrthoPin_holds
      hpinLanes
  have hC5 : Validator.C5 pinned.layoutDump := by
    by_cases hlanes : lanesOf m.boxes = []
    · have hno : pinLanes m.boxes m.options base.scene = .ok base.scene :=
        pinLanes_no_lanes hlanes
      have heq : pinned = base.scene := Except.ok.inj (hpinLanes.symm.trans hno)
      subst heq
      exact hbase.2.2.2.2.1
    · have hEndsOld : ∀ (pinned : Scene),
          pinBands m.boxes m.options base.scene = .ok pinned →
          ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
          EndsOnOld (Axis.ofDirection m.options.direction)
            (laneFrames (Axis.ofDirection m.options.direction)
              (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
                (lanesOf m.boxes)) base.scene)
            pinned.layoutDump :=
        fun pinned hpin sp hsp =>
          swimPin_endsOld hadm ha hne hwf hfam hbase.2.2.2.2.1 hlanes hpin sp hsp
      exact pinLanes_c5 hbase.2.2.2.2.1 hEndsOld hFit hpinLanes
  have hC6 : Validator.C6 pinned.layoutDump := by
    by_cases hlanes : lanesOf m.boxes = []
    · have hno : pinLanes m.boxes m.options base.scene = .ok base.scene :=
        pinLanes_no_lanes hlanes
      have heq : pinned = base.scene := Except.ok.inj (hpinLanes.symm.trans hno)
      subst heq
      exact hbase.2.2.2.2.2.1
    · obtain ⟨sp, mid, hsp, hpinBands, hatt⟩ := pinLanes_spec hlanes hpinLanes
      have hC6mid := swimPin_c6mid hadm hne hwf hfam hbase hpinBands
      have hBaseOrtho : ∀ rt ∈ base.scene.routes,
          Polyline.isOrthogonal rt.points = true :=
        Layered.PipelineImpl.layoutRecursive_routes_orthogonal
          ((Swimlane.input m).boxes.length + 1) (Swimlane.input m) m.options base
          (Layered.layoutFamily_geometry_ok hfam)
      have hOrtho : ∀ rt ∈ mid.layoutDump.routes,
          Polyline.isOrthogonal rt.points = true := by
        rw [(pinBands_layoutDump (r := mid)).2.1]
        exact pinBands_points_orthogonal hBaseOrtho hpinBands
      have hGapMid := swimPin_gap hadm hne hwf hfam hbase.2.2.1 hsp hpinBands
      have hPosMid := swimPin_pos hne hwf hfam hpinBands
      have hFitMid := swimPin_fit hne hwf hfam hsp hpinBands
      have hLenMid := swimPin_len hne hfam hsp hpinBands
      exact attachLaneEnds_c6 hC6mid hOrtho hGapMid hPosMid hFitMid hLenMid hatt
  have hC7 : Validator.C7 pinned.layoutDump :=
    pinLanes_c7 hpinLanes hbase.2.2.2.2.2.2.1 hclean hshape
  have hC8a : Validator.C8a pinned.layoutDump :=
    pinLanes_c8a hbase.2.2.2.2.2.2.2.1 hBoxesNodup hne hsNodup hNoEmpty
      hcov hParents hpinLanes
  have hC8b : Validator.C8b pinned.layoutDump :=
    pinLanes_c8b hpinLanes hbase.2.2.2.2.2.2.2.2
  have hfinal : HardConstraints pinned.layoutDump :=
    ⟨hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8a, hC8b⟩
  rw [hdump]
  exact hfinal

end Kinds
end Elegant

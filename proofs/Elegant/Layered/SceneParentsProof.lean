import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ExpandChildC2Facts
import Elegant.Layered.RecursiveFit
import Elegant.Layered.LaneBandsCoverageProof
import Elegant.Kinds.Swimlane
import Elegant.DumpLaminar
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Validator
open LaneBands

/-- (A) The layered family copies model parents into the scene: every scene
box of a successful `layoutFamily` carries the id and parent pointer of a
source input box. Short corollary of the proved recursion mirror
`layoutRecursive_scene_box_parent` via `layoutFamily_geometry_ok`; the
`WellFormed` premise supplies the id nodup the induction needs. -/
theorem layoutFamily_scene_parents {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamily inp o = .ok res)
    (hwf : WellFormed (inputModel inp o)) :
    ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  have hnodup : (inp.boxes.map (·.id)).Nodup := by
    have h := Model.boxIds_nodup hwf
    simpa [inputModel] using h
  exact layoutRecursive_scene_box_parent _ _ _ _ hnodup (layoutFamily_geometry_ok h)

/-- Every model box has a scene box with the same id. -/
private theorem sceneBoxOfId {boxes : List ModelBox} {d : LayoutDump}
    (hids : d.boxes.map (·.id) = boxes.map (·.id))
    {mb : ModelBox} (hmb : mb ∈ boxes) :
    ∃ sb ∈ d.boxes, sb.id = mb.id := by
  have hmem : mb.id ∈ d.boxes.map (·.id) := by
    rw [hids]
    exact List.mem_map.mpr ⟨mb, hmb, rfl⟩
  obtain ⟨sb, hsb, hEq⟩ := List.mem_map.mp hmem
  exact ⟨sb, hsb, hEq⟩

/-- A scene box's parent is the parent of the model box with the same id. -/
private theorem sceneParentEq {boxes : List ModelBox} {d : LayoutDump}
    (hnodup : (boxes.map (·.id)).Nodup)
    (hmirror : ∀ sb ∈ d.boxes, ∃ mb ∈ boxes, mb.id = sb.id ∧ sb.parent = mb.parent)
    {sb : Box} (hsb : sb ∈ d.boxes) {mb : ModelBox} (hmb : mb ∈ boxes)
    (h : sb.id = mb.id) : sb.parent = mb.parent := by
  obtain ⟨mb', hmb', hid, hpar⟩ := hmirror sb hsb
  have heq : mb' = mb := eq_of_mem_id hnodup hmb' hmb (hid.trans h)
  rw [heq] at hpar
  exact hpar

/-- With no empty model id, no scene box is named `""`. -/
private theorem sceneIdsNe {boxes : List ModelBox} {d : LayoutDump}
    (hids : d.boxes.map (·.id) = boxes.map (·.id))
    (hne : ∀ mb ∈ boxes, mb.id ≠ "")
    {b : Box} (hb : b ∈ d.boxes) : b.id ≠ "" := by
  intro hcon
  have hmem : b.id ∈ boxes.map (·.id) := by
    rw [← hids]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  obtain ⟨mb, hmb, hmid⟩ := List.mem_map.mp hmem
  exact hne mb hmb (hmid.trans hcon)

/-- A `layLanes` band is a `laneBand` for some lane. -/
private theorem layLanes_mem_laneBand {boxes : List ModelBox} {s : Scene}
    {axis : LaneBands.Axis} {sp : Spacing} (lanes : List String) (start : Int)
    (band : Band) (h : band ∈ layLanes boxes s axis sp lanes start) :
    ∃ lane start', band = laneBand boxes s axis sp lane start' := by
  induction lanes generalizing start band with
  | nil => simp [layLanes] at h
  | cons hd tl ih =>
    have heq : layLanes boxes s axis sp (hd :: tl) start =
        laneBand boxes s axis sp hd start ::
          layLanes boxes s axis sp tl (start + (laneBand boxes s axis sp hd start).thickness) := by
      simp only [layLanes]
    rw [heq, List.mem_cons] at h
    rcases h with rfl | hmem
    · exact ⟨hd, start, rfl⟩
    · obtain ⟨lane, start', hb⟩ := ih _ _ hmem
      exact ⟨lane, start', hb⟩

/-- Membership in a lane band means `inLane` holds for that lane. -/
private theorem laneBand_mem_inLane_of {boxes : List ModelBox} {s : Scene}
    {axis : LaneBands.Axis} {sp : Spacing} {lane id : String} {start : Int}
    (hmem : id ∈ (laneBand boxes s axis sp lane start).members) :
    inLane boxes id lane = true := by
  unfold laneBand at hmem
  simp only at hmem
  obtain ⟨mb, hmb, hid⟩ := List.mem_map.mp hmem
  obtain ⟨hmbmem, hpred⟩ := List.mem_filter.mp hmb
  have htrue : inLane boxes mb.id lane = true := by
    simpa using hpred
  rw [hid] at htrue
  exact htrue

private theorem looseBand_id' {boxes : List ModelBox} {s : Scene} {axis : LaneBands.Axis}
    {sp : Spacing} {loose : List String} {start : Int} :
    (looseBand boxes s axis sp loose start).id = "" := by
  unfold looseBand
  split <;> rfl

/-- The `laneOf` parent chain reaches the lane in the scene dump: every step
of the model chain is mirrored by scene parents, so the lane is the member
itself or one of its scene ancestors. The `K` fuel generalizes the ancestor
walk so the cons tail matches the induction hypothesis exactly; the
`n ≤ K + 1` slack absorbs the one-step offset. -/
private theorem lane_chain {boxes : List ModelBox} {d : LayoutDump} {lane : String}
    (hnodup : (boxes.map (·.id)).Nodup)
    (hids : d.boxes.map (·.id) = boxes.map (·.id))
    (hmirror : ∀ sb ∈ d.boxes, ∃ mb ∈ boxes, mb.id = sb.id ∧ sb.parent = mb.parent) :
    ∀ (n K : Nat) (id : String),
      laneOfAux boxes n id = some (lane, true) → n ≤ K + 1 →
      id = lane ∨ lane ∈ LayoutDump.ancestors.go d K id := by
  have hW1 : (d.boxes.map (·.id)).Nodup := by rw [hids]; exact hnodup
  intro n
  induction n with
  | zero =>
    intro K id h _
    simp only [laneOfAux] at h
    cases h
  | succ n ih =>
    intro K id h hle
    simp only [laneOfAux] at h
    cases hfind : boxes.find? (fun b => b.id == id) with
    | none =>
      simp only [hfind] at h
      cases h
    | some b =>
      simp only [hfind] at h
      have hbid : b.id = id := by
        simpa only [beq_iff_eq] using List.find?_some hfind
      by_cases hpar : b.parent = ""
      · have hcond : (((b.parent == "") = true)) := beq_iff_eq.mpr hpar
        rw [ite_eq_left hcond] at h
        have hid : id = lane := by
          have hpair : (id, b.role == .group) = (lane, true) := by simpa using h
          simpa using congrArg Prod.fst hpair
        exact Or.inl hid
      · have hnc : ¬ (((b.parent == "") = true)) :=
          fun he => hpar (beq_iff_eq.mp he)
        rw [ite_eq_right hnc] at h
        have hbmem : b ∈ boxes := List.mem_of_find?_eq_some hfind
        obtain ⟨sb, hsb, hsbid⟩ := sceneBoxOfId hids hbmem
        have hsbpar : sb.parent = b.parent :=
          sceneParentEq hnodup hmirror hsb hbmem hsbid
        have hsid : sb.id = id := hsbid.trans hbid
        have hbox : d.box? id = some sb := by
          have hfb := Elegant.findBox_eq_self hW1 hsb
          rw [hsid] at hfb
          exact hfb
        cases K with
        | zero =>
          have hn0 : n = 0 := by omega
          subst hn0
          simp only [laneOfAux] at h
          cases h
        | succ K' =>
          have hle' : n ≤ K' + 1 := by omega
          have hgo : LayoutDump.ancestors.go d (K' + 1) id =
              b.parent :: LayoutDump.ancestors.go d K' b.parent := by
            simp only [LayoutDump.ancestors.go, hbox, hsbpar]
            rw [ite_eq_right hpar]
          rcases ih K' b.parent h hle' with h1 | h1
          · subst h1
            exact Or.inr (by rw [hgo]; exact List.mem_cons.mpr (Or.inl rfl))
          · exact Or.inr (by rw [hgo]; exact List.mem_cons.mpr (Or.inr h1))

/-- (B) Pinned scene parents for an executed swimlane layout. The statement
restates `PinSceneParents` (`LaneBandsApplyPinKeptClearProof`) inline:
conjunct 1 is (A) restricted to boxes with a nonempty model parent;
conjunct 2 puts every present band frame at-or-above each member along the
scene-parent mirror of the model `laneOf` chain. The nonempty-id premise is
a genuine seam: `modelWellFormed` does not reject `""` ids, and the
presence-guarded loose band is false without it (witness
`SceneParentsTProbe.mEmptyId`: band `""` with members `["", "x"]`, frame
`""` present, `x` not below `""`). It holds on every executed swimlane
layout probed. -/
theorem swimlane_pinSceneParents {m : Model} {base : FamilyResult} {sp : Spacing}
    (bands : List Band)
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (_hsp : spacingOf m.options.profile = .ok sp)
    (_hadm : NestedInLane m.boxes)
    (hbands : bands =
      layBands m.boxes base.scene (LaneBands.Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes))
    (hne : ∀ mb ∈ m.boxes, mb.id ≠ "") :
    (∀ mb ∈ m.boxes, mb.parent ≠ "" → ∀ sb ∈ base.scene.boxes, sb.id = mb.id →
      sb.parent = mb.parent) ∧
    (∀ band ∈ bands, (∃ b ∈ base.scene.boxes, b.id = band.id) →
      ∀ mid ∈ band.members, mid = band.id ∨
        band.id ∈ base.scene.layoutDump.ancestors mid) := by
  have hboxes : (Kinds.Swimlane.input m).boxes = m.boxes := rfl
  have hwf := layoutFamily_wellFormed hfam
  have hnodup : (m.boxes.map (·.id)).Nodup := by
    have h := Model.boxIds_nodup hwf
    rw [← hboxes]
    simpa [inputModel] using h
  have hmirror0 := layoutFamily_scene_parents hfam hwf
  rw [hboxes] at hmirror0
  have hids0 := (layoutFamily_ids hfam).1
  rw [hboxes] at hids0
  have hdump : base.scene.layoutDump.boxes = base.scene.boxes := rfl
  have hmirror : ∀ sb ∈ base.scene.layoutDump.boxes, ∃ mb ∈ m.boxes,
      mb.id = sb.id ∧ sb.parent = mb.parent := by
    rw [hdump]
    exact hmirror0
  have hids : base.scene.layoutDump.boxes.map (·.id) = m.boxes.map (·.id) := by
    rw [hdump]
    exact hids0
  refine ⟨?_, ?_⟩
  · intro mb hmb hpar sb hsb hsid
    exact sceneParentEq hnodup hmirror hsb hmb hsid
  · intro band hband hframe mid hmid
    rw [hbands] at hband
    have hlen : base.scene.layoutDump.boxes.length = m.boxes.length := by
      have h := congrArg List.length hids
      simpa using h
    by_cases hf : (looseNodes m.boxes).isEmpty = false
    · rw [layBands_append m.boxes base.scene (LaneBands.Axis.ofDirection m.options.direction)
        sp (lanesOf m.boxes) hf] at hband
      rcases List.mem_append.mp hband with hmem | hmem
      · obtain ⟨lane, start', rfl⟩ := layLanes_mem_laneBand _ _ _ hmem
        have hmem' : mid ∈ (laneBand m.boxes base.scene
            (LaneBands.Axis.ofDirection m.options.direction) sp lane start').members := hmid
        have hin : inLane m.boxes mid lane = true := laneBand_mem_inLane_of hmem'
        have hlaneOf : laneOf m.boxes mid = some (lane, true) := by
          unfold inLane at hin
          cases h : laneOf m.boxes mid with
          | none =>
            simp [h] at hin
          | some p =>
            obtain ⟨found, isGroup⟩ := p
            simp only [h, Bool.and_eq_true, beq_iff_eq] at hin
            obtain ⟨hg, he⟩ := hin
            rw [he, hg]
        have haux : laneOfAux m.boxes (m.boxes.length + 1) mid =
            some (lane, true) := hlaneOf
        have hle : m.boxes.length + 1 ≤ base.scene.layoutDump.boxes.length + 1 := by
          omega
        have hc := lane_chain hnodup hids hmirror _ _ mid haux hle
        have hfin : mid = lane ∨
            lane ∈ LayoutDump.ancestors.go base.scene.layoutDump
              base.scene.layoutDump.boxes.length mid := hc
        rw [laneBand_id] at ⊢
        exact hfin
      · obtain rfl := List.mem_singleton.mp hmem
        rw [looseBand_id'] at hframe ⊢
        obtain ⟨b, hb, hid⟩ := hframe
        exact absurd hid (sceneIdsNe hids hne hb)
    · have hnil : looseNodes m.boxes = [] := by
        revert hf
        cases hbb : looseNodes m.boxes with
        | nil => intro _; rfl
        | cons hd tl =>
          intro hf
          have hcon : (hd :: tl).isEmpty = false := rfl
          exact absurd hcon hf
      have heq : layBands m.boxes base.scene (LaneBands.Axis.ofDirection m.options.direction)
          sp (lanesOf m.boxes) =
          layLanes m.boxes base.scene (LaneBands.Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes)
            (firstLaneStart base.scene (lanesOf m.boxes)
              (LaneBands.Axis.ofDirection m.options.direction)) := by
        have h0 : (([] : List String).isEmpty) = true := rfl
        simp only [layBands, hnil, h0, ↓reduceIte]
      rw [heq] at hband
      obtain ⟨lane, start', rfl⟩ := layLanes_mem_laneBand _ _ _ hband
      have hmem' : mid ∈ (laneBand m.boxes base.scene
          (LaneBands.Axis.ofDirection m.options.direction) sp lane start').members := hmid
      have hin : inLane m.boxes mid lane = true := laneBand_mem_inLane_of hmem'
      have hlaneOf : laneOf m.boxes mid = some (lane, true) := by
        unfold inLane at hin
        cases h : laneOf m.boxes mid with
        | none =>
          simp [h] at hin
        | some p =>
          obtain ⟨found, isGroup⟩ := p
          simp only [h, Bool.and_eq_true, beq_iff_eq] at hin
          obtain ⟨hg, he⟩ := hin
          rw [he, hg]
      have haux : laneOfAux m.boxes (m.boxes.length + 1) mid =
          some (lane, true) := hlaneOf
      have hle : m.boxes.length + 1 ≤ base.scene.layoutDump.boxes.length + 1 := by
        omega
      have hc := lane_chain hnodup hids hmirror _ _ mid haux hle
      have hfin : mid = lane ∨
          lane ∈ LayoutDump.ancestors.go base.scene.layoutDump
            base.scene.layoutDump.boxes.length mid := hc
      rw [laneBand_id] at ⊢
      exact hfin

end PipelineImpl
end Layered
end Elegant

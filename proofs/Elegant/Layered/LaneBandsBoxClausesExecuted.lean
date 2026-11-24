import Elegant.Layered.LaneBandsBoxClausesProof
import Elegant.Layered.LaneBandsCoverageProof
import Elegant.Layered.ExpandChildC2Facts
import Elegant.Layered.ExpandChildContainment
import ElegantGeometry.Validator

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Elegant
namespace Layered
namespace LaneBands

/-- Executed-setup residual for the swimlane pin: scene-model id/parent/exclusive
mirror, nonempty model ids, and the three band-shift/membership facts that
`PinSetup` needs. Parent mirror is now also derived from
`PipelineImpl.layoutRecursive_scene_box_parent` via `layoutFamily_geometry_ok`;
exclusive mirror is proved below by the same recursion shape. This def is kept
for the band facts while they are discharged; `hne` is already explicit. -/
def PinSetupResidual (m : Model) (s : Scene) (axis : Axis) (sp : Spacing) : Prop :=
  (∀ b ∈ s.boxes, ∃ mb ∈ m.boxes, mb.id = b.id ∧ b.parent = mb.parent ∧ b.exclusive = mb.exclusive)
  ∧ (∀ mb ∈ m.boxes, mb.id ≠ "")
  ∧ (∀ b ∈ s.boxes, b.parent ≠ "" → ∀ q ∈ s.boxes, q.id = b.parent →
      bandShift (layBands m.boxes s axis sp (lanesOf m.boxes)) b.id =
      bandShift (layBands m.boxes s axis sp (lanesOf m.boxes)) q.id)
  ∧ (∀ b ∈ s.boxes, ∀ c ∈ s.boxes, b.parent = c.parent → b.exclusive = true → c.exclusive = true →
      bandShift (layBands m.boxes s axis sp (lanesOf m.boxes)) b.id =
      bandShift (layBands m.boxes s axis sp (lanesOf m.boxes)) c.id)
  ∧ (∀ b ∈ s.boxes, ∀ q ∈ s.boxes, ∀ Q ∈ layBands m.boxes s axis sp (lanesOf m.boxes),
      b.parent = q.id → Q.id = q.id → Q.id ≠ "" →
      b.id ∈ Q.members ∧
        bandShift (layBands m.boxes s axis sp (lanesOf m.boxes)) b.id = Q.shift)

/-- Copy of the lane-frame witness: a lane id names a top-level group. -/
theorem exec_lanesOf_mem {boxes : List ModelBox} {lane : String}
    (h : lane ∈ lanesOf boxes) :
    ∃ mb ∈ boxes, mb.role = .group ∧ mb.parent = "" ∧ mb.id = lane := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, hpred⟩ := List.mem_filter.mp hx
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hrole, hpar⟩ := hpred
  exact ⟨x, hxb, beq_iff_eq.mp hrole, beq_iff_eq.mp hpar, rfl⟩

/-- Copy of the loose-band id fact. -/
theorem exec_looseBand_id (boxes : List ModelBox) (s : Scene) (axis : Axis)
    (sp : Spacing) (loose : List String) (start : Int) :
    (looseBand boxes s axis sp loose start).id = "" := by
  unfold looseBand
  split <;> rfl

/-- Copy of the nodup `find?` self fact for model boxes. -/
theorem exec_modelFind_self {boxes : List ModelBox} (hn : (boxes.map (·.id)).Nodup)
    {x : ModelBox} (hx : x ∈ boxes) : boxes.find? (fun b => b.id == x.id) = some x := by
  induction boxes with
  | nil => simp at hx
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hfresh, hrest⟩ := hn
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · have hne : first.id ≠ x.id := by
        intro heq
        exact hfresh (List.mem_map.mpr ⟨x, hx, heq.symm⟩)
      have hfind : (first.id == x.id) = false := beq_eq_false_iff_ne.mpr hne
      simp [List.find?, hfind, ih hrest hx]

/-- Copy of the `layLanes` member-lane fact. -/
theorem exec_layLanes_mem_lane {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lanes : List String} {start : Int} {band : Band}
    (hmem : band ∈ layLanes boxes s axis sp lanes start) :
    ∃ lane ∈ lanes, ∃ st : Int, band = laneBand boxes s axis sp lane st := by
  induction lanes generalizing start with
  | nil => simp [layLanes] at hmem
  | cons lane rest ih =>
    simp only [layLanes] at hmem
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact ⟨lane, List.mem_cons.mpr (Or.inl rfl), start, rfl⟩
    · obtain ⟨l, hl, st, rfl⟩ := ih hmem
      exact ⟨l, List.mem_cons.mpr (Or.inr hl), st, rfl⟩

/-- Copy of the `layBands` split fact. -/
theorem exec_layBands_mem_cases {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lanes : List String} {band : Band}
    (hmem : band ∈ layBands boxes s axis sp lanes) :
    band ∈ layLanes boxes s axis sp lanes (firstLaneStart s lanes axis) ∨
      band = looseBand boxes s axis sp (looseNodes boxes)
        (firstLaneStart s lanes axis + ((layLanes boxes s axis sp lanes
          (firstLaneStart s lanes axis)).map (·.thickness)).sum) := by
  unfold layBands at hmem
  simp only at hmem
  by_cases hl : (looseNodes boxes).isEmpty = true
  · simp only [hl, ↓reduceIte] at hmem
    exact Or.inl hmem
  · simp only [hl, ↓reduceIte, Bool.false_eq_true] at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact Or.inl hmem
    · rw [List.mem_singleton] at hmem
      exact Or.inr hmem

/-- Copy of `layLanes` id projection. -/
theorem exec_layLanes_ids (boxes : List ModelBox) (s : Scene) (axis : Axis)
    (sp : Spacing) (lanes : List String) (start : Int) :
    ((layLanes boxes s axis sp lanes start).map (·.id)) = lanes := by
  induction lanes generalizing start with
  | nil => rfl
  | cons lane rest ih =>
    have h : layLanes boxes s axis sp (lane :: rest) start =
        laneBand boxes s axis sp lane start ::
          layLanes boxes s axis sp rest
            (start + (laneBand boxes s axis sp lane start).thickness) := rfl
    have hid : (laneBand boxes s axis sp lane start).id = lane := rfl
    rw [h, List.map_cons, ih, hid]

/-- Band covering predicate as a proposition. -/
def exec_bandCovers (band : Band) (id : String) : Prop :=
  band.id = id ∨ id ∈ band.members

/-- Covering bands satisfy the `bandShift` predicate. -/
theorem exec_bandShift_pred_true {band : Band} {id : String}
    (h : exec_bandCovers band id) : (band.id == id || band.members.contains id) = true := by
  rcases h with hEq | hmem
  · simp [hEq]
  · simp [List.contains_eq_mem, hmem]

/-- Non-covering bands fail the `bandShift` predicate. -/
theorem exec_bandShift_pred_false {band : Band} {id : String}
    (h : ¬ exec_bandCovers band id) :
    (band.id == id || band.members.contains id) = false := by
  have h1 : band.id ≠ id := by
    intro heq
    exact h (Or.inl heq)
  have h2 : id ∉ band.members := by
    intro hmem
    exact h (Or.inr hmem)
  simp [beq_eq_false_iff_ne.mpr h1, List.contains_eq_mem, h2]

/-- `bandShift` returns the unique covering band's shift. -/
theorem exec_bandShift_eq {bands : List Band} {id : String} {band : Band}
    (hmem : band ∈ bands) (hcov : exec_bandCovers band id)
    (hUniq : ∀ b1 ∈ bands, ∀ b2 ∈ bands,
      exec_bandCovers b1 id → exec_bandCovers b2 id → b1 = b2) :
    bandShift bands id = band.shift := by
  induction bands with
  | nil => simp at hmem
  | cons hd bs ih =>
    rw [List.mem_cons] at hmem
    rcases hmem with hEq | hmem
    · have hcovHd : exec_bandCovers hd id := hEq ▸ hcov
      have hfind : (hd :: bs).find? (fun b => b.id == id || b.members.contains id) =
          some hd := by simp only [List.find?_cons, exec_bandShift_pred_true hcovHd]
      have hShiftEq : hd.shift = band.shift := by
        have h := congrArg Band.shift hEq
        exact h.symm
      unfold bandShift
      rw [hfind]
      simp [hShiftEq]
    · by_cases hc : exec_bandCovers hd id
      · have heq : hd = band := hUniq hd (List.mem_cons.mpr (Or.inl rfl)) band
          (List.mem_cons.mpr (Or.inr hmem)) hc hcov
        have hfind : (hd :: bs).find? (fun b => b.id == id || b.members.contains id) =
            some hd := by simp only [List.find?_cons, exec_bandShift_pred_true hc]
        have hShiftEq : hd.shift = band.shift := by rw [heq]
        unfold bandShift
        rw [hfind]
        simp [hShiftEq]
      · have hfindFalse : (hd.id == id || hd.members.contains id) = false :=
          exec_bandShift_pred_false hc
        have hfindEq : (hd :: bs).find? (fun b => b.id == id || b.members.contains id) =
            bs.find? (fun b => b.id == id || b.members.contains id) := by
          simp only [List.find?_cons, hfindFalse]
        have hUniqTail : ∀ b1 ∈ bs, ∀ b2 ∈ bs,
            exec_bandCovers b1 id → exec_bandCovers b2 id → b1 = b2 := by
          intro b1 hb1 b2 hb2 hc1 hc2
          exact hUniq b1 (List.mem_cons.mpr (Or.inr hb1)) b2
            (List.mem_cons.mpr (Or.inr hb2)) hc1 hc2
        have ih' := ih hmem hUniqTail
        unfold bandShift
        rw [hfindEq]
        exact ih'

/-- Two lanes containing the same box coincide. -/
theorem exec_inLane_unique {boxes : List ModelBox} {id lane1 lane2 : String}
    (h1 : inLane boxes id lane1 = true) (h2 : inLane boxes id lane2 = true) :
    lane1 = lane2 := by
  unfold inLane at h1 h2
  cases h : laneOf boxes id with
  | none => simp [h] at h1
  | some p =>
    cases p with
    | mk found isGroup =>
      simp only [h, Bool.and_eq_true, beq_iff_eq] at h1 h2
      obtain ⟨hg1, e1⟩ := h1
      obtain ⟨hg2, e2⟩ := h2
      rw [← e1, ← e2]

/-- Membership in a lane band means `inLane` holds. -/
theorem exec_laneBand_mem_inLane {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lane id : String} {start : Int}
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

/-- A lane band member in another lane's band forces the lanes equal. -/
theorem exec_laneBand_mem_unique {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lane1 lane2 : String} {start1 start2 : Int} {id : String}
    (h1 : id ∈ (laneBand boxes s axis sp lane1 start1).members)
    (h2 : id ∈ (laneBand boxes s axis sp lane2 start2).members) :
    lane1 = lane2 := by
  exact exec_inLane_unique (exec_laneBand_mem_inLane h1) (exec_laneBand_mem_inLane h2)

/-- A loose node is in no lane. -/
theorem exec_loose_not_inLane {boxes : List ModelBox} (hn : (boxes.map (·.id)).Nodup)
    {id lane : String} (hmem : id ∈ looseNodes boxes) :
    inLane boxes id lane = false := by
  unfold looseNodes at hmem
  obtain ⟨mb, hmb, hid⟩ := List.mem_map.mp hmem
  obtain ⟨hmbmem, hpred⟩ := List.mem_filter.mp hmb
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hpar', hrole'⟩ := hpred
  have hpar : mb.parent = "" := beq_iff_eq.mp hpar'
  have hrole : mb.role = .node := beq_iff_eq.mp hrole'
  have heq : mb.id = id := hid
  have hfind : boxes.find? (fun b => b.id == id) = some mb := by
    have hx : mb ∈ boxes := hmbmem
    rw [← heq]
    exact exec_modelFind_self hn hx
  simp [inLane, laneOf, laneOfAux, hfind, hpar, hrole]

/-- Loose members are in no lane band. -/
theorem exec_loose_disjoint {boxes : List ModelBox} (hn : (boxes.map (fun b => b.id)).Nodup)
    {s : Scene} {axis : Axis} {sp : Spacing} {lane : String} {start : Int} {id : String}
    (hloose : id ∈ looseNodes boxes)
    (hlane : id ∈ (laneBand boxes s axis sp lane start).members) : False := by
  have hfalse : inLane boxes id lane = false := exec_loose_not_inLane hn hloose
  have htrue : inLane boxes id lane = true := exec_laneBand_mem_inLane hlane
  rw [hfalse] at htrue
  cases htrue

/-- Lane ids inherit nodup from model ids. -/
theorem exec_lanesOf_nodup {boxes : List ModelBox} :
    (boxes.map (fun b => b.id)).Nodup → (lanesOf boxes).Nodup := by
  induction boxes with
  | nil => intro _; simp [lanesOf]
  | cons b rest ih =>
    intro h
    have htail : (rest.map (fun b => b.id)).Nodup := (List.nodup_cons.mp h).2
    have hrest := ih htail
    have hnot : b.id ∉ rest.map (fun b => b.id) := (List.nodup_cons.mp h).1
    by_cases hp : (b.role == .group && b.parent == "") = true
    · have hne : b.id ∉ ((rest.filter fun b => b.role == .group && b.parent == "").map
          (fun b => b.id)) := by
        intro hmem
        obtain ⟨x, hxm, hidx⟩ := List.mem_map.mp hmem
        obtain ⟨hx, _⟩ := List.mem_filter.mp hxm
        have hmem' : x.id ∈ rest.map (fun b => b.id) := List.mem_map.mpr ⟨x, hx, rfl⟩
        rw [hidx] at hmem'
        exact hnot hmem'
      have heq : lanesOf (b :: rest) = b.id ::
          ((rest.filter fun b => b.role == .group && b.parent == "").map (fun b => b.id)) := by
        simp [lanesOf, hp]
      rw [heq]
      exact List.nodup_cons.mpr ⟨hne, hrest⟩
    · have hpF : (b.role == .group && b.parent == "") = false := by
        cases he : (b.role == .group && b.parent == "") with
        | true => exact absurd he hp
        | false => rfl
      have heq : lanesOf (b :: rest) =
          ((rest.filter fun b => b.role == .group && b.parent == "").map (fun b => b.id)) := by
        simp [lanesOf, hpF]
      rw [heq]
      exact hrest

/-- `layBands` ids are nodup when lanes are. -/
theorem exec_layBands_ids_nodup (boxes : List ModelBox) (s : Scene)
    (axis : Axis) (sp : Spacing) (lanes : List String)
    (hLanes : lanes.Nodup) (hNe : "" ∉ lanes) :
    (((layBands boxes s axis sp lanes).map (·.id)).Nodup) := by
  have hlay : layBands boxes s axis sp lanes =
      let start := firstLaneStart s lanes axis
      let bands := layLanes boxes s axis sp lanes start
      let loose := looseNodes boxes
      if loose.isEmpty then bands
      else bands ++ [looseBand boxes s axis sp loose
        (start + (bands.map (·.thickness)).sum)] := rfl
  rw [hlay]
  by_cases hempty : (looseNodes boxes).isEmpty = true
  · simp only [hempty, ↓reduceIte]
    rw [exec_layLanes_ids]
    exact hLanes
  · have hemptyF : (looseNodes boxes).isEmpty = false := by
      cases hb : (looseNodes boxes).isEmpty with
      | true => exact absurd hb hempty
      | false => rfl
    simp only [hemptyF]
    rw [ite_eq_right Bool.false_ne_true, List.map_append, exec_layLanes_ids]
    have hlo : ∀ (t : Int),
        (([looseBand boxes s axis sp (looseNodes boxes) t].map (·.id))) = [""] := by
      intro t
      simp [exec_looseBand_id]
    rw [hlo, List.nodup_append]
    refine ⟨hLanes, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    intro heq
    exact hNe (heq ▸ ha)

/-- Bands with nodup ids are unique by id. -/
theorem exec_band_unique {bands : List Band} :
    (bands.map (·.id)).Nodup → ∀ {b₁ b₂ : Band}, b₁ ∈ bands → b₂ ∈ bands →
      b₁.id = b₂.id → b₁ = b₂ := by
  induction bands with
  | nil => intro h b₁ b₂ h₁ h₂ heq; simp at h₁
  | cons b rest ih =>
    intro h b₁ b₂ h₁ h₂ heq
    have hnd := List.nodup_cons.mp h
    simp only [List.mem_cons] at h₁ h₂
    rcases h₁ with rfl | h₁
    · rcases h₂ with rfl | h₂
      · rfl
      · exfalso
        have hmem : b₂.id ∈ rest.map (·.id) := List.mem_map.mpr ⟨b₂, h₂, rfl⟩
        rw [← heq] at hmem
        exact hnd.1 hmem
    · rcases h₂ with rfl | h₂
      · exfalso
        have hmem : b₁.id ∈ rest.map (·.id) := List.mem_map.mpr ⟨b₁, h₁, rfl⟩
        rw [heq] at hmem
        exact hnd.1 hmem
      · exact ih hnd.2 h₁ h₂ heq

/-- A lane is in its own lane. -/
theorem exec_inLane_self {boxes : List ModelBox} (hNodup : (boxes.map (fun b => b.id)).Nodup)
    {lane : String} (hlane : lane ∈ lanesOf boxes) : inLane boxes lane lane = true := by
  obtain ⟨mb, hmbMem, hmbRole, hmbPar, hmbId⟩ := exec_lanesOf_mem hlane
  have hfind : boxes.find? (fun b => b.id == lane) = some mb := by
    have hEq : (fun b : ModelBox => b.id == lane) = (fun b : ModelBox => b.id == mb.id) := by
      funext b
      rw [hmbId]
    rw [hEq]
    exact exec_modelFind_self hNodup hmbMem
  unfold inLane laneOf laneOfAux
  rw [hfind]
  simp [hmbPar, hmbRole]

/-- Empty id is in no lane list. -/
theorem exec_empty_not_mem_lanes {boxes : List ModelBox} (hne : ∀ mb ∈ boxes, mb.id ≠ "")
    : "" ∉ lanesOf boxes := by
  intro hmem
  obtain ⟨mb, hmbMem, _hmbRole, _hmbPar, hmbId⟩ := exec_lanesOf_mem hmem
  exact hne mb hmbMem hmbId

/-- `find?` for the empty id is none when ids are nonempty. -/
theorem exec_find_empty_none {boxes : List ModelBox} (hne : ∀ mb ∈ boxes, mb.id ≠ "")
    : boxes.find? (fun b => b.id == "") = none := by
  induction boxes with
  | nil => rfl
  | cons b rest ih =>
    have hneB : b.id ≠ "" := hne b (List.mem_cons.mpr (Or.inl rfl))
    have hfalse : (b.id == "") = false := beq_eq_false_iff_ne.mpr hneB
    have hneRest : ∀ mb ∈ rest, mb.id ≠ "" := fun mb hmem => hne mb (List.mem_cons.mpr (Or.inr hmem))
    simp [hfalse, ih hneRest]

/-- A lane id is a member of its own lane band. -/
theorem exec_lane_self_mem {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing}
    (hNodup : (boxes.map (·.id)).Nodup)
    {lane : String} (hlane : lane ∈ lanesOf boxes) (st : Int) :
    lane ∈ (laneBand boxes s axis sp lane st).members := by
  obtain ⟨mb, hmbMem, _hmbRole, _hmbPar, hmbId⟩ := exec_lanesOf_mem hlane
  have hIn : inLane boxes lane lane = true := exec_inLane_self hNodup hlane
  have hFilt : mb ∈ (boxes.filter fun b => inLane boxes b.id lane) := by
    rw [List.mem_filter]
    refine ⟨hmbMem, ?_⟩
    have hEq : inLane boxes mb.id lane = inLane boxes lane lane := by rw [hmbId]
    rw [hEq, hIn]
  have hMemMap : lane ∈ ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id) := by
    exact List.mem_map.mpr ⟨mb, hFilt, hmbId⟩
  have hEqMem : (laneBand boxes s axis sp lane st).members =
      ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id) := rfl
  rw [hEqMem]
  exact hMemMap

/-- At most one band covers a nonempty id. -/
theorem exec_cover_unique {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing}
    (hNodup : (boxes.map (·.id)).Nodup)
    (hne : ∀ mb ∈ boxes, mb.id ≠ "")
    {id : String} (hneId : id ≠ "")
    {b1 b2 : Band} (hm1 : b1 ∈ layBands boxes s axis sp (lanesOf boxes))
    (hm2 : b2 ∈ layBands boxes s axis sp (lanesOf boxes))
    (hcov1 : exec_bandCovers b1 id) (hcov2 : exec_bandCovers b2 id) : b1 = b2 := by
  have hLanesNodup : (lanesOf boxes).Nodup := exec_lanesOf_nodup hNodup
  have hEmptyNotMem : "" ∉ lanesOf boxes := exec_empty_not_mem_lanes hne
  have hBandsNodup : ((layBands boxes s axis sp (lanesOf boxes)).map (·.id)).Nodup :=
    exec_layBands_ids_nodup boxes s axis sp (lanesOf boxes) hLanesNodup hEmptyNotMem
  have hCases1 := exec_layBands_mem_cases (hmem := hm1)
  have hCases2 := exec_layBands_mem_cases (hmem := hm2)
  rcases hCases1 with hLane1 | hLoose1
  · rcases hCases2 with hLane2 | hLoose2
    · obtain ⟨lane1, hlane1Mem, st1, rfl⟩ := exec_layLanes_mem_lane hLane1
      obtain ⟨lane2, hlane2Mem, st2, rfl⟩ := exec_layLanes_mem_lane hLane2
      have hIn1 : inLane boxes id lane1 = true := by
        rcases hcov1 with hEq1 | hMem1
        · have hId1 : (laneBand boxes s axis sp lane1 st1).id = lane1 := rfl
          rw [hId1] at hEq1
          rw [← hEq1]
          exact exec_inLane_self hNodup hlane1Mem
        · exact exec_laneBand_mem_inLane hMem1
      have hIn2 : inLane boxes id lane2 = true := by
        rcases hcov2 with hEq2 | hMem2
        · have hId2 : (laneBand boxes s axis sp lane2 st2).id = lane2 := rfl
          rw [hId2] at hEq2
          rw [← hEq2]
          exact exec_inLane_self hNodup hlane2Mem
        · exact exec_laneBand_mem_inLane hMem2
      have hLaneEq : lane1 = lane2 := exec_inLane_unique hIn1 hIn2
      have hIdEq : (laneBand boxes s axis sp lane1 st1).id = (laneBand boxes s axis sp lane2 st2).id := by
        have h1 : (laneBand boxes s axis sp lane1 st1).id = lane1 := rfl
        have h2 : (laneBand boxes s axis sp lane2 st2).id = lane2 := rfl
        rw [h1, h2, hLaneEq]
      exact exec_band_unique hBandsNodup hm1 hm2 hIdEq
    · obtain ⟨lane1, hlane1Mem, st1, hBand1Eq⟩ := exec_layLanes_mem_lane hLane1
      have hLaneMem1 : id ∈ (laneBand boxes s axis sp lane1 st1).members := by
        rw [hBand1Eq] at hcov1
        rcases hcov1 with hEq1 | hMem1
        · have hId1 : (laneBand boxes s axis sp lane1 st1).id = lane1 := rfl
          rw [hId1] at hEq1
          have hlaneId : id ∈ lanesOf boxes := hEq1 ▸ hlane1Mem
          rw [hEq1]
          exact exec_lane_self_mem hNodup hlaneId st1
        · exact hMem1
      have hLooseMem : id ∈ looseNodes boxes := by
        rw [hLoose2] at hcov2
        have hLooseId := exec_looseBand_id boxes s axis sp (looseNodes boxes)
          (firstLaneStart s (lanesOf boxes) axis + ((layLanes boxes s axis sp (lanesOf boxes)
            (firstLaneStart s (lanesOf boxes) axis)).map (·.thickness)).sum)
        have hMemEq : (looseBand boxes s axis sp (looseNodes boxes)
          (firstLaneStart s (lanesOf boxes) axis + ((layLanes boxes s axis sp (lanesOf boxes)
            (firstLaneStart s (lanesOf boxes) axis)).map (·.thickness)).sum)).members =
            looseNodes boxes := by
          unfold looseBand
          split <;> rfl
        rcases hcov2 with hEq2 | hMem2
        · rw [hLooseId] at hEq2
          exact absurd hEq2.symm hneId
        · rw [hMemEq] at hMem2
          exact hMem2
      exact absurd hLaneMem1 (fun h => exec_loose_disjoint hNodup hLooseMem h)
  · rcases hCases2 with hLane2 | hLoose2
    · have hLooseMem : id ∈ looseNodes boxes := by
        rw [hLoose1] at hcov1
        have hLooseId := exec_looseBand_id boxes s axis sp (looseNodes boxes)
          (firstLaneStart s (lanesOf boxes) axis + ((layLanes boxes s axis sp (lanesOf boxes)
            (firstLaneStart s (lanesOf boxes) axis)).map (·.thickness)).sum)
        have hMemEq : (looseBand boxes s axis sp (looseNodes boxes)
          (firstLaneStart s (lanesOf boxes) axis + ((layLanes boxes s axis sp (lanesOf boxes)
            (firstLaneStart s (lanesOf boxes) axis)).map (·.thickness)).sum)).members =
            looseNodes boxes := by
          unfold looseBand
          split <;> rfl
        rcases hcov1 with hEq1 | hMem1
        · rw [hLooseId] at hEq1
          exact absurd hEq1.symm hneId
        · rw [hMemEq] at hMem1
          exact hMem1
      obtain ⟨lane2, hlane2Mem, st2, hBand2Eq⟩ := exec_layLanes_mem_lane hLane2
      have hLaneMem2 : id ∈ (laneBand boxes s axis sp lane2 st2).members := by
        rw [hBand2Eq] at hcov2
        rcases hcov2 with hEq2 | hMem2
        · have hId2 : (laneBand boxes s axis sp lane2 st2).id = lane2 := rfl
          rw [hId2] at hEq2
          have hlaneId2 : id ∈ lanesOf boxes := hEq2 ▸ hlane2Mem
          rw [hEq2]
          exact exec_lane_self_mem hNodup hlaneId2 st2
        · exact hMem2
      exact absurd hLaneMem2 (fun h => exec_loose_disjoint hNodup hLooseMem h)
    · exact hLoose1.trans hLoose2.symm


/-- One-step stability of `laneOfAux`: sufficient fuel gives the same root. -/
private theorem exec_laneOfAux_stable {boxes : List ModelBox}
    (hne : ∀ mb ∈ boxes, mb.id ≠ "")
    : ∀ (n : Nat) (id : String), ParentReaches boxes n id →
      laneOfAux boxes n id = laneOfAux boxes (n + 1) id := by
  intro n
  induction n with
  | zero =>
    intro id hReach
    by_cases hid : id = ""
    · subst hid
      have hnone := exec_find_empty_none hne
      simp [laneOfAux, hnone]
    · have hF : ParentReaches boxes 0 id = False := by
        simp [ParentReaches, hid]
      rw [hF] at hReach
      exact False.elim hReach
  | succ n ih =>
    intro id hReach
    by_cases hid : id = ""
    · subst hid
      have hnone := exec_find_empty_none hne
      simp [laneOfAux, hnone]
    · have hPR : ∃ b, boxes.find? (fun b => b.id == id) = some b ∧ ParentReaches boxes n b.parent := by
        unfold ParentReaches at hReach
        simpa [hid] using hReach
      obtain ⟨b, hfind, hReachPar⟩ := hPR
      by_cases hpar : b.parent = ""
      · have h1 : laneOfAux boxes (n + 1) id = some (id, b.role == .group) := by
          simp [laneOfAux, hfind, hpar]
        have h2 : laneOfAux boxes (n + 1 + 1) id = some (id, b.role == .group) := by
          simp [laneOfAux, hfind, hpar]
        rw [h1, h2]
      · have hparB : (b.parent == "") = false := beq_eq_false_iff_ne.mpr hpar
        have h1 : laneOfAux boxes (n + 1) id = laneOfAux boxes n b.parent := by
          simp [laneOfAux, hfind, hparB]
        have h2 : laneOfAux boxes (n + 1 + 1) id = laneOfAux boxes (n + 1) b.parent := by
          simp [laneOfAux, hfind, hparB]
        rw [h1, h2]
        exact ih b.parent hReachPar

/-- A child shares its parent's `laneOf` root. -/
theorem exec_laneOf_parent_eq {boxes : List ModelBox}
    (hne : ∀ mb ∈ boxes, mb.id ≠ "")
    (hNodup : (boxes.map (·.id)).Nodup)
    {mb mq : ModelBox} (hmbmem : mb ∈ boxes) (hmqmem : mq ∈ boxes)
    (hpar : mb.parent = mq.id)
    (hReach : ParentReaches boxes boxes.length mb.parent) :
    laneOf boxes mb.id = laneOf boxes mq.id := by
  have hMqNe : mq.id ≠ "" := hne mq hmqmem
  have hMbNe : mb.parent ≠ "" := by rw [hpar]; exact hMqNe
  have hfindMb : boxes.find? (fun b => b.id == mb.id) = some mb :=
    exec_modelFind_self hNodup hmbmem
  have hunfoldMb : laneOfAux boxes (boxes.length + 1) mb.id = laneOfAux boxes boxes.length mq.id := by
    have hNeB : (mb.parent == "") = false := by
      rw [hpar]
      exact beq_eq_false_iff_ne.mpr hMqNe
    have h1 : laneOfAux boxes (boxes.length + 1) mb.id = laneOfAux boxes boxes.length mb.parent := by
      simp [laneOfAux, hfindMb, hNeB]
    rw [h1, hpar]
  have hLaneMb : laneOf boxes mb.id = laneOfAux boxes boxes.length mq.id := by
    unfold laneOf
    exact hunfoldMb
  have hStab := exec_laneOfAux_stable hne boxes.length mq.id (hpar ▸ hReach)
  have hLaneMq : laneOf boxes mq.id = laneOfAux boxes (boxes.length + 1) mq.id := rfl
  rw [hLaneMb, hLaneMq]
  exact hStab

/-- A child shares every `inLane` test with its parent. -/
theorem exec_inLane_parent_eq {boxes : List ModelBox}
    (hne : ∀ mb ∈ boxes, mb.id ≠ "")
    (hNodup : (boxes.map (·.id)).Nodup)
    {mb mq : ModelBox} (hmbmem : mb ∈ boxes) (hmqmem : mq ∈ boxes)
    (hpar : mb.parent = mq.id)
    (hReach : ParentReaches boxes boxes.length mb.parent) (lane : String) :
    inLane boxes mb.id lane = inLane boxes mq.id lane := by
  have hEq := exec_laneOf_parent_eq hne hNodup hmbmem hmqmem hpar hReach
  unfold inLane
  rw [hEq]

/-- Local copy of `nodup_filter_map`: filtering preserves `map` nodup. -/
private theorem exec_nodup_filter_map {α β : Type} (p : α → Bool) (f : α → β) :
    ∀ l : List α, (l.map f).Nodup → ((l.filter p).map f).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a l ih =>
    intro h
    by_cases hp : p a = true
    · rw [show (a :: l).filter p = a :: l.filter p from by simp [hp]]
      refine List.nodup_cons.mpr ⟨?_, ih ((List.nodup_cons.mp h).2)⟩
      intro hc
      obtain ⟨b, hbmem, hbf⟩ := List.mem_map.mp hc
      obtain ⟨hbIn, _hbP⟩ := List.mem_filter.mp hbmem
      exact (List.nodup_cons.mp h).1 (List.mem_map.mpr ⟨b, hbIn, hbf⟩)
    · rw [show (a :: l).filter p = l.filter p from by simp [hp]]
      exact ih ((List.nodup_cons.mp h).2)

/-- Parent mirror for an executed swimlane layout, derived from the proved
recursion mirror via the geometry projection. -/
theorem exec_parent_mirror_of_family {m : Model} {base : FamilyResult}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hNodup : (m.boxes.map (·.id)).Nodup) :
    ∀ cb ∈ base.scene.boxes, ∃ sb ∈ m.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  have hrec := layoutFamily_geometry_ok hfam
  have hmir := PipelineImpl.layoutRecursive_scene_box_parent _ _ _ _ hNodup hrec
  intro cb hcb
  obtain ⟨sb, hsbmem, hsbid, hsbpar⟩ := hmir cb hcb
  exact ⟨sb, hsbmem, hsbid, hsbpar⟩

/-- Local copy: `embedBox` keeps the box id. -/
private theorem exec_embed_id {g : String} {dx dy : Int} {box b : Box}
    (h : PipelineImpl.embedBox g dx dy box = b) : b.id = box.id := by
  have h' := congrArg Box.id h
  simp only [PipelineImpl.embedBox] at h'
  exact h'.symm

/-- Local copy: `embedBox` keeps the exclusive flag. -/
private theorem exec_embed_exclusive {g : String} {dx dy : Int} {box b : Box}
    (h : PipelineImpl.embedBox g dx dy box = b) : b.exclusive = box.exclusive := by
  have h' := congrArg Box.exclusive h
  simp only [PipelineImpl.embedBox] at h'
  exact h'.symm

private theorem exec_select_spec {inp : Input} (keep : ModelBox → Bool) (root : String)
    {b : ModelBox} (hb : b ∈ (PipelineImpl.selectInput inp keep root).boxes) :
    ∃ m ∈ inp.boxes, keep m = true ∧ b.id = m.id ∧ b.exclusive = m.exclusive ∧
      b.parent = (if m.parent == root then "" else m.parent) := by
  unfold PipelineImpl.selectInput at hb
  dsimp only at hb
  obtain ⟨q, hq, hbq⟩ := List.mem_map.mp hb
  obtain ⟨hqzip, hkq⟩ := List.mem_filter.mp hq
  have hmem : q.1 ∈ inp.boxes := List.fst_mem_of_mem_zipIdx hqzip
  refine ⟨q.1, hmem, hkq, ?_, ?_, ?_⟩
  · rw [← hbq]; split <;> rfl
  · rw [← hbq]; split <;> rfl
  · rw [← hbq]; split <;> rfl
/-- Leaf exclusive mirror: `sceneOf` copies id and exclusive verbatim. -/
private theorem exec_scene_exclusive_leaf {inp : Input} {o : Options} {res : FamilyResult}
    (h : PipelineImpl.layout inp o = .ok res) :
    ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.exclusive = sb.exclusive := by
  unfold PipelineImpl.layout at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨_, _, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨_, _, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨_, _, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨_, _, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨acc, _, h⟩ := PipelineImpl.bind_ok h
  obtain ⟨acc, _, h⟩ := PipelineImpl.bind_ok h
  split at h
  · simp at h
  · have hok := Except.ok.inj h
    subst hok
    simp only [PipelineImpl.sceneOf]
    intro cb hcb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcb
    exact ⟨q.1, List.fst_mem_of_mem_zipIdx hq, rfl, rfl⟩

/-- Exclusive mirror through the recursion, same shape as the parent theorem. -/
private theorem exec_layoutRecursive_exclusive :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      (inp.boxes.map (·.id)).Nodup →
      PipelineImpl.layoutRecursive fuel inp o = .ok res →
      ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.exclusive = sb.exclusive := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res _hnodup h
    exact exec_scene_exclusive_leaf h
  | succ fuel ih =>
    intro inp o res hnodup h
    rcases PipelineImpl.layoutRecursive_succ h with ⟨_, hlayout⟩ |
      ⟨group, _hg, _P, _titleHeight, child, parent, a, b, c, hchild, hparent, hexpand⟩
    · exact exec_scene_exclusive_leaf hlayout
    · have hselNodup : ∀ (keep : ModelBox → Bool) (root : String),
          ((PipelineImpl.selectInput inp keep root).boxes.map (·.id)).Nodup := by
        intro keep root
        rw [PipelineImpl.selectInput_box_ids]
        exact exec_nodup_filter_map keep (·.id) inp.boxes hnodup
      have hchildNodup : ((PipelineImpl.selectInput inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map
            (·.id)).Nodup := hselNodup _ _
      have hparentNodup : (({ PipelineImpl.selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := a, fixedChildren := b, fixedAreas := c } : Input).boxes.map
            (·.id)).Nodup := by
        show ((PipelineImpl.selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
            (·.id)).Nodup
        rw [PipelineImpl.selectInput_box_ids]
        exact exec_nodup_filter_map _ _ _ hnodup
      have hchildExcl := ih _ _ _ hchildNodup hchild
      have hparentExcl := ih _ _ _ hparentNodup hparent
      obtain ⟨_frame, _metric', _titleLines', _lines, dx, dy, _hframe, _hmetric',
        _htitle', _hlines', _hdx, _hdy, _hcanvas, hboxes⟩ :=
        PipelineImpl.expandChild_sources hexpand
      intro cb hcb
      rw [hboxes] at hcb
      obtain ⟨_model, _hmodelmem, hfind⟩ := List.mem_filterMap.mp hcb
      have hcbItems : cb ∈ (child.scene.boxes.map (PipelineImpl.embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hfind
      rcases List.mem_append.mp hcbItems with hbc | hbp
      · obtain ⟨cbb, hcbbmem, hEmbed⟩ := List.mem_map.mp hbc
        obtain ⟨sb, hsbmem, hsbid, hsbexcl⟩ := hchildExcl cbb hcbbmem
        obtain ⟨m, hmmem, hkeep, hmsbid, hmsexcl, _hmspar⟩ :=
          exec_select_spec (fun box => Compound.inside inp.boxes group.id box.id) group.id hsbmem
        refine ⟨m, hmmem, ?_, ?_⟩
        · have hcid : cbb.id = cb.id := (exec_embed_id hEmbed).symm
          exact hmsbid.symm.trans (hsbid.trans hcid)
        · have hcexcl : cbb.exclusive = cb.exclusive := (exec_embed_exclusive hEmbed).symm
          exact hcexcl.symm.trans (hsbexcl.trans hmsexcl)
      · obtain ⟨sb, hsbmem, hsbid, hsbexcl⟩ := hparentExcl cb hbp
        obtain ⟨m, _hmmem, _hkeep, hmsbid, hmsexcl, _hmspar⟩ :=
          exec_select_spec (fun box => !Compound.inside inp.boxes group.id box.id) "" hsbmem
        refine ⟨m, _hmmem, ?_, ?_⟩
        · exact hmsbid.symm.trans hsbid
        · exact hsbexcl.trans hmsexcl

/-- Exclusive mirror for an executed swimlane layout. -/
theorem exec_exclusive_mirror_of_family {m : Model} {base : FamilyResult}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hNodup : (m.boxes.map (·.id)).Nodup) :
    ∀ cb ∈ base.scene.boxes, ∃ sb ∈ m.boxes, sb.id = cb.id ∧ cb.exclusive = sb.exclusive := by
  have hrec := layoutFamily_geometry_ok hfam
  have hmir := exec_layoutRecursive_exclusive _ _ _ _ hNodup hrec
  intro cb hcb
  obtain ⟨sb, hsbmem, hsbid, hsbexcl⟩ := hmir cb hcb
  exact ⟨sb, hsbmem, hsbid, hsbexcl⟩

/-- Parent-child bands agree on an executed swimlane layout. -/
theorem exec_parShift {m : Model} {base : FamilyResult} {sp : Spacing}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hadm : NestedInLane m.boxes)
    (hwf : WellFormed m)
    (hne : ∀ mb ∈ m.boxes, mb.id ≠ "") :
    ∀ b ∈ base.scene.boxes, b.parent ≠ "" → ∀ q ∈ base.scene.boxes, q.id = b.parent →
      bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) b.id =
      bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) q.id := by
  intro b hb hBne q hq hqId
  have hNodup : (m.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hParMirror := exec_parent_mirror_of_family hfam hNodup
  obtain ⟨mb, hmbmem, hmbid, hmbpar⟩ := hParMirror b hb
  obtain ⟨mq, hmqmem, hmqid, _hmqpar⟩ := hParMirror q hq
  have hbNe : b.id ≠ "" := by rw [← hmbid]; exact hne mb hmbmem
  have hqNe : q.id ≠ "" := by rw [← hmqid]; exact hne mq hmqmem
  have hMbParEq : mb.parent = mq.id := by rw [← hmbpar, ← hqId, ← hmqid]
  have hMqNe : mq.id ≠ "" := hne mq hmqmem
  have hMbNe : mb.parent ≠ "" := by rw [hMbParEq]; exact hMqNe
  have hWfAll := (wellFormed_iff m).mp hwf
  have hReachAll : ∀ b ∈ m.boxes, ParentReaches m.boxes m.boxes.length b.parent := hWfAll.2.2.2.1
  have hReach : ParentReaches m.boxes m.boxes.length mb.parent := hReachAll mb hmbmem
  obtain ⟨lane, hlaneMem, hMbIn⟩ := hadm mb hmbmem hMbNe
  have hMqIn : inLane m.boxes mq.id lane = true := by
    have hEq := exec_inLane_parent_eq hne hNodup hmbmem hmqmem hMbParEq hReach lane
    rw [← hEq]
    exact hMbIn
  have hLanesIds : ((layLanes m.boxes base.scene (Axis.ofDirection m.options.direction) sp
      (lanesOf m.boxes) (firstLaneStart base.scene (lanesOf m.boxes)
        (Axis.ofDirection m.options.direction))).map (·.id)) = lanesOf m.boxes := by
    exact exec_layLanes_ids m.boxes base.scene (Axis.ofDirection m.options.direction) sp
      (lanesOf m.boxes) (firstLaneStart base.scene (lanesOf m.boxes)
        (Axis.ofDirection m.options.direction))
  have hLaneMemMap : lane ∈ ((layLanes m.boxes base.scene (Axis.ofDirection m.options.direction) sp
      (lanesOf m.boxes) (firstLaneStart base.scene (lanesOf m.boxes)
        (Axis.ofDirection m.options.direction))).map (·.id)) := by
    rw [hLanesIds]
    exact hlaneMem
  obtain ⟨Qlay, hQlayMem, hQlayId⟩ := List.mem_map.mp hLaneMemMap
  have hQlayBands : Qlay ∈ layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
      (lanesOf m.boxes) := layLanes_subset_layBands hQlayMem
  obtain ⟨laneQ, _hlaneQMem, stQ, hQeq⟩ := exec_layLanes_mem_lane hQlayMem
  have hQidLane : Qlay.id = laneQ := by rw [hQeq]; rfl
  have hLaneQeq : laneQ = lane := by
    have h1 : Qlay.id = lane := by rw [hQlayId]
    rw [hQidLane] at h1
    exact h1
  rw [hLaneQeq] at hQeq
  have hMbMemBand : mb.id ∈ (laneBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp lane stQ).members := by
    have hFilt : mb ∈ (m.boxes.filter fun b => inLane m.boxes b.id lane) := by
      rw [List.mem_filter]
      exact ⟨hmbmem, hMbIn⟩
    have hMap : mb.id ∈ ((m.boxes.filter fun b => inLane m.boxes b.id lane).map fun b => b.id) :=
      List.mem_map.mpr ⟨mb, hFilt, rfl⟩
    have hEqMem : (laneBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp lane stQ).members =
        ((m.boxes.filter fun b => inLane m.boxes b.id lane).map fun b => b.id) := rfl
    rw [hEqMem]
    exact hMap
  have hMqMemBand : mq.id ∈ (laneBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp lane stQ).members := by
    have hFilt : mq ∈ (m.boxes.filter fun b => inLane m.boxes b.id lane) := by
      rw [List.mem_filter]
      exact ⟨hmqmem, hMqIn⟩
    have hMap : mq.id ∈ ((m.boxes.filter fun b => inLane m.boxes b.id lane).map fun b => b.id) :=
      List.mem_map.mpr ⟨mq, hFilt, rfl⟩
    have hEqMem : (laneBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp lane stQ).members =
        ((m.boxes.filter fun b => inLane m.boxes b.id lane).map fun b => b.id) := rfl
    rw [hEqMem]
    exact hMap
  have hQeqBand : Qlay = laneBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp lane stQ := hQeq
  have hBcov : exec_bandCovers Qlay b.id := by
    rw [hQeqBand]
    refine Or.inr ?_
    have hEqId : b.id = mb.id := hmbid.symm
    rw [hEqId]
    exact hMbMemBand
  have hQcov : exec_bandCovers Qlay q.id := by
    rw [hQeqBand]
    refine Or.inr ?_
    have hEqId : q.id = mq.id := hmqid.symm
    rw [hEqId]
    exact hMqMemBand
  have hUb : ∀ b1 ∈ layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes),
      ∀ b2 ∈ layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes),
      exec_bandCovers b1 b.id → exec_bandCovers b2 b.id → b1 = b2 :=
    fun b1 hb1 b2 hb2 h1 h2 => exec_cover_unique hNodup hne hbNe hb1 hb2 h1 h2
  have hUq : ∀ b1 ∈ layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes),
      ∀ b2 ∈ layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes),
      exec_bandCovers b1 q.id → exec_bandCovers b2 q.id → b1 = b2 :=
    fun b1 hb1 b2 hb2 h1 h2 => exec_cover_unique hNodup hne hqNe hb1 hb2 h1 h2
  have hShiftB := exec_bandShift_eq hQlayBands hBcov hUb
  have hShiftQ := exec_bandShift_eq hQlayBands hQcov hUq
  rw [hShiftB, hShiftQ]

/-- `PinSetup` for an executed swimlane layout, conditional on the executed
residual. Parent/exclusive mirrors are now proved; `hne` is explicit. The
band shifts/membership are still the residual while they are discharged. -/
theorem swimlane_pinSetup {m : Model} {base : FamilyResult} {sp : Spacing}
    (_hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (_hsp : spacingOf m.options.profile = .ok sp)
    (_hadm : NestedInLane m.boxes)
    (hwf : WellFormed m)
    (hne : ∀ mb ∈ m.boxes, mb.id ≠ "")
    (hres : PinSetupResidual m base.scene (Axis.ofDirection m.options.direction) sp) :
    PinSetup base.scene
      (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) := by
  obtain ⟨_hMirror, _hNeRes, hParShift, hSibShift, hParMember⟩ := hres
  have hNodup : (m.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hParMirror := exec_parent_mirror_of_family _hfam hNodup
  have hExclMirror := exec_exclusive_mirror_of_family _hfam hNodup
  refine ⟨hParShift, hSibShift, ?_, ?_, hParMember⟩
  · intro b hb hband
    obtain ⟨band, hbandMem, hbid, hneBand⟩ := hband
    have hCases := exec_layBands_mem_cases (hmem := hbandMem)
    rcases hCases with hLane | hLoose
    · obtain ⟨lane, hlaneMem, st, hbandEq⟩ := exec_layLanes_mem_lane hLane
      have hLaneId : (laneBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp lane st).id = lane := rfl
      have hbidLane : b.id = lane := by
        rw [hbandEq] at hbid
        rw [hLaneId] at hbid
        exact hbid.symm
      obtain ⟨mbLane, hmbLaneMem, hmbLaneRole, hmbLanePar, hmbLaneId⟩ :=
        exec_lanesOf_mem hlaneMem
      obtain ⟨mbPar, hmbParMem, hmbParId, hmbParPar⟩ := hParMirror b hb
      obtain ⟨mbExcl, hmbExclMem, hmbExclId, hmbExclExcl⟩ := hExclMirror b hb
      have hfindPar : m.boxes.find? (fun b => b.id == mbPar.id) = some mbPar :=
        exec_modelFind_self hNodup hmbParMem
      have hfindLane : m.boxes.find? (fun b => b.id == mbLane.id) = some mbLane :=
        exec_modelFind_self hNodup hmbLaneMem
      have hIdsEq : mbPar.id = mbLane.id := by
        rw [hmbParId, hmbLaneId, hbidLane]
      have hPredEq : (fun b : ModelBox => b.id == mbPar.id) = (fun b : ModelBox => b.id == mbLane.id) := by
        funext x
        rw [hIdsEq]
      rw [hPredEq] at hfindPar
      have hSomeEq : some mbPar = some mbLane := hfindPar.symm.trans hfindLane
      have hEq : mbPar = mbLane := by simpa using hSomeEq
      have hMbParEmpty : mbPar.parent = "" := by
        rw [hEq]
        exact hmbLanePar
      have hRoleGroup : mbPar.role = .group := by
        rw [hEq]
        exact hmbLaneRole
      have hExclFalse : mbPar.exclusive = false := by
        have hWf := (wellFormed_iff m).mp hwf
        exact hWf.2.2.2.2.2.2 mbPar hmbParMem hRoleGroup
      have hBParEmpty : b.parent = "" := by
        rw [hmbParPar]
        exact hMbParEmpty
      have hEqExcl : mbPar = mbExcl := by
        have hfindExcl : m.boxes.find? (fun b => b.id == mbExcl.id) = some mbExcl :=
          exec_modelFind_self hNodup hmbExclMem
        have hIdsEq2 : mbExcl.id = mbLane.id := by
          rw [hmbExclId, hmbLaneId, hbidLane]
        have hPredEq2 : (fun b : ModelBox => b.id == mbExcl.id) = (fun b : ModelBox => b.id == mbLane.id) := by
          funext x
          rw [hIdsEq2]
        rw [hPredEq2] at hfindExcl
        have hEq2 : mbExcl = mbLane := by simpa using hfindExcl.symm.trans hfindLane
        exact hEq.trans hEq2.symm
      have hBExclFalse : b.exclusive = false := by
        have h1 : b.exclusive = mbExcl.exclusive := hmbExclExcl
        have h2 : mbExcl.exclusive = mbPar.exclusive := by rw [← hEqExcl]
        rw [h1, h2]
        exact hExclFalse
      exact ⟨hBParEmpty, hBExclFalse⟩
    · exfalso
      have hLooseId := exec_looseBand_id m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (looseNodes m.boxes)
        (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction) +
          ((layLanes m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)
            (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction))).map
            (·.thickness)).sum)
      rw [hLoose, hLooseId] at hneBand
      exact hneBand rfl
  · intro b hb
    obtain ⟨mb, hmbMem, hmbId, _hmbPar⟩ := hParMirror b hb
    have hMNe := hne mb hmbMem
    rw [hmbId] at hMNe
    exact hMNe

/-- C2 survives the pin on an executed swimlane layout. -/
theorem swimlane_pinBands_c2 {m : Model} {base : FamilyResult} {sp : Spacing} {r : Scene}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hsp : spacingOf m.options.profile = .ok sp)
    (hadm : NestedInLane m.boxes)
    (hwf : WellFormed m)
    (hne : ∀ mb ∈ m.boxes, mb.id ≠ "")
    (hres : PinSetupResidual m base.scene (Axis.ofDirection m.options.direction) sp)
    (hC2 : Validator.C2 base.scene.layoutDump)
    (hpin : pinBands m.boxes m.options base.scene = .ok r) :
    Validator.C2 r.layoutDump := by
  have hcover := swimlane_pinBoxCoverage hfam hsp hadm
  have hBoxesNodup : (m.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hsetup := swimlane_pinSetup hfam hsp hadm hwf hne hres
  exact pinBands_c2' hcover hBoxesNodup hne hsetup rfl hsp hC2 hpin

/-- C3 survives the pin on an executed swimlane layout. -/
theorem swimlane_pinBands_c3 {m : Model} {base : FamilyResult} {sp : Spacing} {r : Scene}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hsp : spacingOf m.options.profile = .ok sp)
    (hadm : NestedInLane m.boxes)
    (hwf : WellFormed m)
    (hne : ∀ mb ∈ m.boxes, mb.id ≠ "")
    (hres : PinSetupResidual m base.scene (Axis.ofDirection m.options.direction) sp)
    (hC3 : Validator.C3 base.scene.layoutDump)
    (hpin : pinBands m.boxes m.options base.scene = .ok r) :
    Validator.C3 r.layoutDump := by
  have hcover := swimlane_pinBoxCoverage hfam hsp hadm
  have hBoxesNodup : (m.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hsetup := swimlane_pinSetup hfam hsp hadm hwf hne hres
  have hids := layoutFamily_ids hfam
  have hEq : base.scene.boxes.map (·.id) = m.boxes.map (·.id) := by
    have h1 := hids.1
    have hInp : (Kinds.Swimlane.input m).boxes = m.boxes := rfl
    rw [hInp] at h1
    exact h1
  have hsNodup : (base.scene.boxes.map (·.id)).Nodup := hEq ▸ hBoxesNodup
  exact pinBands_c3' hcover hsNodup hBoxesNodup hne hC3 hsetup rfl hsp hpin

end LaneBands
end Layered
end Elegant

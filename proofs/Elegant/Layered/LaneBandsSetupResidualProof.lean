import Elegant.Layered.LaneBandsBoxClausesExecuted

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Elegant
namespace Layered
namespace LaneBands

theorem exec_combined_mirror_of_family {m : Model} {base : FamilyResult}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hNodup : (m.boxes.map (fun b => b.id)).Nodup) :
    ∀ b ∈ base.scene.boxes, ∃ mb ∈ m.boxes,
      mb.id = b.id ∧ b.parent = mb.parent ∧ b.exclusive = mb.exclusive := by
  intro b hb
  have hParMirror := exec_parent_mirror_of_family hfam hNodup
  have hExclMirror := exec_exclusive_mirror_of_family hfam hNodup
  obtain ⟨mp, hmpmem, hmpid, hmppar⟩ := hParMirror b hb
  obtain ⟨me, hmemem, hmeid, hmeexcl⟩ := hExclMirror b hb
  have hIdsEq : mp.id = me.id := by rw [hmpid, hmeid]
  have hPredEq : (fun b : ModelBox => b.id == mp.id) = (fun b : ModelBox => b.id == me.id) := by
    funext x
    rw [hIdsEq]
  have hfindPar : m.boxes.find? (fun b => b.id == mp.id) = some mp :=
    exec_modelFind_self hNodup hmpmem
  have hfindExcl : m.boxes.find? (fun b => b.id == me.id) = some me :=
    exec_modelFind_self hNodup hmemem
  rw [hPredEq] at hfindPar
  have hSomeEq : some mp = some me := hfindPar.symm.trans hfindExcl
  have hEq : mp = me := by simpa using hSomeEq
  refine ⟨mp, hmpmem, hmpid, hmppar, ?_⟩
  rw [hEq]
  exact hmeexcl

theorem exec_sibShift {m : Model} {base : FamilyResult} {sp : Spacing}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hadm : NestedInLane m.boxes)
    (hwf : WellFormed m)
    (hne : ∀ mb ∈ m.boxes, mb.id ≠ "") :
    ∀ b ∈ base.scene.boxes, ∀ c ∈ base.scene.boxes,
      b.parent = c.parent → b.exclusive = true → c.exclusive = true →
      bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) b.id =
      bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) c.id := by
  intro b hb c hc hParEq hBex hCex
  have hNodup : (m.boxes.map (fun b => b.id)).Nodup := Model.boxIds_nodup hwf
  have hComb := exec_combined_mirror_of_family hfam hNodup
  obtain ⟨mb, hmbmem, hmbid, hmbpar, hmbexcl⟩ := hComb b hb
  obtain ⟨mc, hmcmem, hmcid, hmcpar, hmcexcl⟩ := hComb c hc
  have hbNe : b.id ≠ "" := by rw [← hmbid]; exact hne mb hmbmem
  have hcNe : c.id ≠ "" := by rw [← hmcid]; exact hne mc hmcmem
  have hMbTrue : mb.exclusive = true := hmbexcl.symm.trans hBex
  have hMcTrue : mc.exclusive = true := hmcexcl.symm.trans hCex
  have hParModel : mb.parent = mc.parent := hmbpar.symm.trans (hParEq.trans hmcpar)
  by_cases hEmpty : mb.parent = ""
  · have hMcEmpty : mc.parent = "" := hParModel.symm.trans hEmpty
    have hWf := (wellFormed_iff m).mp hwf
    have hGroupRule : ∀ x ∈ m.boxes, x.role = .group → x.exclusive = false :=
      hWf.2.2.2.2.2.2
    have hMbRole : mb.role = .node := by
      cases hr : mb.role with
      | group =>
        exfalso
        have hf := hGroupRule mb hmbmem hr
        exact Bool.false_ne_true (hf.symm.trans hMbTrue)
      | node => rfl
    have hMcRole : mc.role = .node := by
      cases hr : mc.role with
      | group =>
        exfalso
        have hf := hGroupRule mc hmcmem hr
        exact Bool.false_ne_true (hf.symm.trans hMcTrue)
      | node => rfl
    have hMbLoose : mb.id ∈ looseNodes m.boxes :=
      mem_looseNodes_of_node hEmpty hMbRole hmbmem
    have hMcLoose : mc.id ∈ looseNodes m.boxes :=
      mem_looseNodes_of_node hMcEmpty hMcRole hmcmem
    have hemptyNe : looseNodes m.boxes ≠ [] := by
      intro hcon
      simp [hcon] at hMbLoose
    have hf : (looseNodes m.boxes).isEmpty = false := by
      revert hemptyNe
      cases hbb : looseNodes m.boxes with
      | nil => intro hcon; exact absurd rfl hcon
      | cons hd tl => intro _; rfl
    have hlay := layBands_append m.boxes base.scene (Axis.ofDirection m.options.direction) sp
      (lanesOf m.boxes) hf
    have hBLmem : looseBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (looseNodes m.boxes)
        (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction) +
          ((layLanes m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)
            (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction))).map
            (fun b => b.thickness)).sum) ∈
        layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes) := by
      rw [hlay]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    have hMbInBL : mb.id ∈ (looseBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (looseNodes m.boxes)
        (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction) +
          ((layLanes m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)
            (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction))).map
            (fun b => b.thickness)).sum)).members := by
      rw [looseBand_members]
      exact hMbLoose
    have hMcInBL : mc.id ∈ (looseBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (looseNodes m.boxes)
        (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction) +
          ((layLanes m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)
            (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction))).map
            (fun b => b.thickness)).sum)).members := by
      rw [looseBand_members]
      exact hMcLoose
    have hBmemBL : b.id ∈ (looseBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (looseNodes m.boxes)
        (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction) +
          ((layLanes m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)
            (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction))).map
            (fun b => b.thickness)).sum)).members := by
      have hEqId : b.id = mb.id := hmbid.symm
      rw [hEqId]
      exact hMbInBL
    have hCmemBL : c.id ∈ (looseBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (looseNodes m.boxes)
        (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction) +
          ((layLanes m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)
            (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction))).map
            (fun b => b.thickness)).sum)).members := by
      have hEqId : c.id = mc.id := hmcid.symm
      rw [hEqId]
      exact hMcInBL
    have hBcov : exec_bandCovers (looseBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (looseNodes m.boxes)
        (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction) +
          ((layLanes m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)
            (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction))).map
            (fun b => b.thickness)).sum)) b.id := Or.inr hBmemBL
    have hCcov : exec_bandCovers (looseBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (looseNodes m.boxes)
        (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction) +
          ((layLanes m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)
            (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction))).map
            (fun b => b.thickness)).sum)) c.id := Or.inr hCmemBL
    have hUbB : ∀ b1 ∈ layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes), ∀ b2 ∈ layBands m.boxes base.scene
        (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes),
        exec_bandCovers b1 b.id → exec_bandCovers b2 b.id → b1 = b2 :=
      fun b1 hb1 b2 hb2 h1 h2 => exec_cover_unique hNodup hne hbNe hb1 hb2 h1 h2
    have hUbC : ∀ b1 ∈ layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes), ∀ b2 ∈ layBands m.boxes base.scene
        (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes),
        exec_bandCovers b1 c.id → exec_bandCovers b2 c.id → b1 = b2 :=
      fun b1 hb1 b2 hb2 h1 h2 => exec_cover_unique hNodup hne hcNe hb1 hb2 h1 h2
    have hShiftB := exec_bandShift_eq hBLmem hBcov hUbB
    have hShiftC := exec_bandShift_eq hBLmem hCcov hUbC
    rw [hShiftB, hShiftC]
  · have hWfAll := (wellFormed_iff m).mp hwf
    have hReachAll : ∀ x ∈ m.boxes, ParentReaches m.boxes m.boxes.length x.parent :=
      hWfAll.2.2.2.1
    have hReachMb : ParentReaches m.boxes m.boxes.length mb.parent :=
      hReachAll mb hmbmem
    have hMpWit : ∃ mp ∈ m.boxes, mp.id = mb.parent := by
      cases hLen : m.boxes.length with
      | zero =>
        have hNil : m.boxes = [] := List.length_eq_zero_iff.mp hLen
        rw [hNil] at hmbmem
        exact False.elim (List.not_mem_nil hmbmem)
      | succ n =>
        have hReach' : ParentReaches m.boxes (n + 1) mb.parent := hLen ▸ hReachMb
        have hNePar : ¬ mb.parent = "" := hEmpty
        have hPR : ∃ b, m.boxes.find? (fun b => b.id == mb.parent) = some b ∧
            ParentReaches m.boxes n b.parent := by
          unfold ParentReaches at hReach'
          simpa [hNePar] using hReach'
        obtain ⟨mp, hfindMp, _hReachMp⟩ := hPR
        have hmpmem : mp ∈ m.boxes := List.mem_of_find?_eq_some hfindMp
        have hmpid : mp.id = mb.parent := by simpa using List.find?_some hfindMp
        exact ⟨mp, hmpmem, hmpid⟩
    obtain ⟨mp, hmpmem, hmpid⟩ := hMpWit
    have hModelParMb : mb.parent = mp.id := hmpid.symm
    have hModelParMc : mc.parent = mp.id := hParModel.symm.trans hModelParMb
    obtain ⟨lane1, hlane1Mem, hMbIn1⟩ := hadm mb hmbmem hEmpty
    have hEqMb : inLane m.boxes mb.id lane1 = inLane m.boxes mp.id lane1 :=
      exec_inLane_parent_eq hne hNodup hmbmem hmpmem hModelParMb hReachMb lane1
    have hMpIn1 : inLane m.boxes mp.id lane1 = true := by
      rw [← hEqMb]
      exact hMbIn1
    have hReachMc : ParentReaches m.boxes m.boxes.length mc.parent :=
      hParModel ▸ hReachMb
    have hEqMc : inLane m.boxes mc.id lane1 = inLane m.boxes mp.id lane1 :=
      exec_inLane_parent_eq hne hNodup hmcmem hmpmem hModelParMc hReachMc lane1
    have hMcIn1 : inLane m.boxes mc.id lane1 = true := by
      rw [hEqMc]
      exact hMpIn1
    have hLanesIds : ((layLanes m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes) (firstLaneStart base.scene (lanesOf m.boxes)
        (Axis.ofDirection m.options.direction))).map (fun b => b.id)) = lanesOf m.boxes := by
      exact exec_layLanes_ids m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes) (firstLaneStart base.scene (lanesOf m.boxes)
        (Axis.ofDirection m.options.direction))
    have hLaneMemMap : lane1 ∈ ((layLanes m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes) (firstLaneStart base.scene (lanesOf m.boxes)
        (Axis.ofDirection m.options.direction))).map (fun b => b.id)) := by
      rw [hLanesIds]
      exact hlane1Mem
    obtain ⟨Qlay, hQlayMem, hQlayId⟩ := List.mem_map.mp hLaneMemMap
    have hQlayBands : Qlay ∈ layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes) := layLanes_subset_layBands hQlayMem
    obtain ⟨laneQ, _hlaneQMem, stQ, hQeq⟩ := exec_layLanes_mem_lane hQlayMem
    have hQidLane : Qlay.id = laneQ := by rw [hQeq]; rfl
    have hLaneQeq : laneQ = lane1 := by
      have h1 : Qlay.id = lane1 := hQlayId
      rw [hQidLane] at h1
      exact h1
    rw [hLaneQeq] at hQeq
    have hMbMemBand : mb.id ∈ (laneBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        lane1 stQ).members := by
      have hFilt : mb ∈ (m.boxes.filter fun b => inLane m.boxes b.id lane1) := by
        rw [List.mem_filter]
        exact ⟨hmbmem, hMbIn1⟩
      have hMap : mb.id ∈ ((m.boxes.filter fun b => inLane m.boxes b.id lane1).map
          fun b => b.id) :=
        List.mem_map.mpr ⟨mb, hFilt, rfl⟩
      have hEqMem : (laneBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          lane1 stQ).members =
          ((m.boxes.filter fun b => inLane m.boxes b.id lane1).map fun b => b.id) := rfl
      rw [hEqMem]
      exact hMap
    have hMcMemBand : mc.id ∈ (laneBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        lane1 stQ).members := by
      have hFilt : mc ∈ (m.boxes.filter fun b => inLane m.boxes b.id lane1) := by
        rw [List.mem_filter]
        exact ⟨hmcmem, hMcIn1⟩
      have hMap : mc.id ∈ ((m.boxes.filter fun b => inLane m.boxes b.id lane1).map
          fun b => b.id) :=
        List.mem_map.mpr ⟨mc, hFilt, rfl⟩
      have hEqMem : (laneBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          lane1 stQ).members =
          ((m.boxes.filter fun b => inLane m.boxes b.id lane1).map fun b => b.id) := rfl
      rw [hEqMem]
      exact hMap
    have hQeqBand : Qlay = laneBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        lane1 stQ := hQeq
    have hBcov : exec_bandCovers Qlay b.id := by
      rw [hQeqBand]
      refine Or.inr ?_
      have hEqId : b.id = mb.id := hmbid.symm
      rw [hEqId]
      exact hMbMemBand
    have hCcov : exec_bandCovers Qlay c.id := by
      rw [hQeqBand]
      refine Or.inr ?_
      have hEqId : c.id = mc.id := hmcid.symm
      rw [hEqId]
      exact hMcMemBand
    have hUbB : ∀ b1 ∈ layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes), ∀ b2 ∈ layBands m.boxes base.scene
        (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes),
        exec_bandCovers b1 b.id → exec_bandCovers b2 b.id → b1 = b2 :=
      fun b1 hb1 b2 hb2 h1 h2 => exec_cover_unique hNodup hne hbNe hb1 hb2 h1 h2
    have hUbC : ∀ b1 ∈ layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes), ∀ b2 ∈ layBands m.boxes base.scene
        (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes),
        exec_bandCovers b1 c.id → exec_bandCovers b2 c.id → b1 = b2 :=
      fun b1 hb1 b2 hb2 h1 h2 => exec_cover_unique hNodup hne hcNe hb1 hb2 h1 h2
    have hShiftB := exec_bandShift_eq hQlayBands hBcov hUbB
    have hShiftC := exec_bandShift_eq hQlayBands hCcov hUbC
    rw [hShiftB, hShiftC]

theorem exec_parMember {m : Model} {base : FamilyResult} {sp : Spacing}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (_hadm : NestedInLane m.boxes)
    (hwf : WellFormed m)
    (hne : ∀ mb ∈ m.boxes, mb.id ≠ "") :
    ∀ b ∈ base.scene.boxes, ∀ q ∈ base.scene.boxes,
      ∀ Q ∈ layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes),
      b.parent = q.id → Q.id = q.id → Q.id ≠ "" →
      b.id ∈ Q.members ∧
        bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes)) b.id = Q.shift := by
  intro b hb q hq Q hQmem hParEq hQid hQne
  have hNodup : (m.boxes.map (fun b => b.id)).Nodup := Model.boxIds_nodup hwf
  have hComb := exec_combined_mirror_of_family hfam hNodup
  obtain ⟨mb, hmbmem, hmbid, hmbpar, _hmbexcl⟩ := hComb b hb
  obtain ⟨mq, hmqmem, hmqid, _hmqpar, _hmqexcl⟩ := hComb q hq
  have hbNe : b.id ≠ "" := by rw [← hmbid]; exact hne mb hmbmem
  have hModelPar : mb.parent = mq.id := hmbpar.symm.trans (hParEq.trans hmqid.symm)
  have hQidMq : Q.id = mq.id := hQid.trans hmqid.symm
  have hWfAll := (wellFormed_iff m).mp hwf
  have hReachAll : ∀ x ∈ m.boxes, ParentReaches m.boxes m.boxes.length x.parent :=
    hWfAll.2.2.2.1
  have hReachMb : ParentReaches m.boxes m.boxes.length mb.parent :=
    hReachAll mb hmbmem
  have hCases := exec_layBands_mem_cases (hmem := hQmem)
  rcases hCases with hLane | hLoose
  · obtain ⟨lane, hlaneMem, st, hQeq⟩ := exec_layLanes_mem_lane hLane
    have hQidLane : Q.id = lane := by rw [hQeq]; rfl
    have hLaneMq : lane = mq.id := hQidLane.symm.trans hQidMq
    have hMqLaneMem : mq.id ∈ lanesOf m.boxes := hLaneMq ▸ hlaneMem
    have hSelf : inLane m.boxes mq.id mq.id = true :=
      exec_inLane_self hNodup hMqLaneMem
    have hMqInLane : inLane m.boxes mq.id lane = true := by
      rw [hLaneMq]
      exact hSelf
    have hEq : inLane m.boxes mb.id lane = inLane m.boxes mq.id lane :=
      exec_inLane_parent_eq hne hNodup hmbmem hmqmem hModelPar hReachMb lane
    have hMbInLane : inLane m.boxes mb.id lane = true := by
      rw [hEq]
      exact hMqInLane
    have hMbMemBand : mb.id ∈ (laneBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        lane st).members := by
      have hFilt : mb ∈ (m.boxes.filter fun b => inLane m.boxes b.id lane) := by
        rw [List.mem_filter]
        exact ⟨hmbmem, hMbInLane⟩
      have hMap : mb.id ∈ ((m.boxes.filter fun b => inLane m.boxes b.id lane).map
          fun b => b.id) :=
        List.mem_map.mpr ⟨mb, hFilt, rfl⟩
      have hEqMem : (laneBand m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          lane st).members =
          ((m.boxes.filter fun b => inLane m.boxes b.id lane).map fun b => b.id) := rfl
      rw [hEqMem]
      exact hMap
    have hBMem : b.id ∈ Q.members := by
      rw [hQeq]
      have hEqId : b.id = mb.id := hmbid.symm
      rw [hEqId]
      exact hMbMemBand
    have hBcov : exec_bandCovers Q b.id := Or.inr hBMem
    have hUniq : ∀ b1 ∈ layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes), ∀ b2 ∈ layBands m.boxes base.scene
        (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes),
        exec_bandCovers b1 b.id → exec_bandCovers b2 b.id → b1 = b2 :=
      fun b1 hb1 b2 hb2 h1 h2 => exec_cover_unique hNodup hne hbNe hb1 hb2 h1 h2
    have hShift := exec_bandShift_eq hQmem hBcov hUniq
    exact ⟨hBMem, hShift⟩
  · exfalso
    have hLooseId := exec_looseBand_id m.boxes base.scene (Axis.ofDirection m.options.direction) sp
      (looseNodes m.boxes)
      (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction) +
        ((layLanes m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)
          (firstLaneStart base.scene (lanesOf m.boxes) (Axis.ofDirection m.options.direction))).map
          (fun b => b.thickness)).sum)
    rw [hLoose, hLooseId] at hQne
    exact hQne rfl

theorem swimlane_pinSetup_closed {m : Model} {base : FamilyResult} {sp : Spacing}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hsp : spacingOf m.options.profile = .ok sp)
    (hadm : NestedInLane m.boxes)
    (hwf : WellFormed m)
    (hne : ∀ mb ∈ m.boxes, mb.id ≠ "") :
    PinSetup base.scene
      (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) := by
  have hNodup : (m.boxes.map (fun b => b.id)).Nodup := Model.boxIds_nodup hwf
  have hPar := exec_parShift (sp := sp) hfam hadm hwf hne
  have hSib := exec_sibShift (sp := sp) hfam hadm hwf hne
  have hMem := exec_parMember (sp := sp) hfam hadm hwf hne
  have hMirror : ∀ b ∈ base.scene.boxes, ∃ mb ∈ m.boxes,
      mb.id = b.id ∧ b.parent = mb.parent ∧ b.exclusive = mb.exclusive :=
    exec_combined_mirror_of_family hfam hNodup
  have hres : PinSetupResidual m base.scene (Axis.ofDirection m.options.direction) sp :=
    ⟨hMirror, hne, hPar, hSib, hMem⟩
  exact swimlane_pinSetup hfam hsp hadm hwf hne hres

theorem swimlane_pinBands_c2_closed {m : Model} {base : FamilyResult} {sp : Spacing} {r : Scene}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hsp : spacingOf m.options.profile = .ok sp)
    (hadm : NestedInLane m.boxes)
    (hwf : WellFormed m)
    (hne : ∀ mb ∈ m.boxes, mb.id ≠ "")
    (hC2 : Validator.C2 base.scene.layoutDump)
    (hpin : pinBands m.boxes m.options base.scene = .ok r) :
    Validator.C2 r.layoutDump := by
  have hcover := swimlane_pinBoxCoverage hfam hsp hadm
  have hBoxesNodup : (m.boxes.map (fun b => b.id)).Nodup := Model.boxIds_nodup hwf
  have hsetup := swimlane_pinSetup_closed hfam hsp hadm hwf hne
  exact pinBands_c2' hcover hBoxesNodup hne hsetup rfl hsp hC2 hpin

theorem swimlane_pinBands_c3_closed {m : Model} {base : FamilyResult} {sp : Spacing} {r : Scene}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hsp : spacingOf m.options.profile = .ok sp)
    (hadm : NestedInLane m.boxes)
    (hwf : WellFormed m)
    (hne : ∀ mb ∈ m.boxes, mb.id ≠ "")
    (hC3 : Validator.C3 base.scene.layoutDump)
    (hpin : pinBands m.boxes m.options base.scene = .ok r) :
    Validator.C3 r.layoutDump := by
  have hcover := swimlane_pinBoxCoverage hfam hsp hadm
  have hBoxesNodup : (m.boxes.map (fun b => b.id)).Nodup := Model.boxIds_nodup hwf
  have hsetup := swimlane_pinSetup_closed hfam hsp hadm hwf hne
  have hids := layoutFamily_ids hfam
  have hEq : base.scene.boxes.map (fun b => b.id) = m.boxes.map (fun b => b.id) := by
    have h1 := hids.1
    have hInp : (Kinds.Swimlane.input m).boxes = m.boxes := rfl
    rw [hInp] at h1
    exact h1
  have hsNodup : (base.scene.boxes.map (fun b => b.id)).Nodup := hEq ▸ hBoxesNodup
  exact pinBands_c3' hcover hsNodup hBoxesNodup hne hC3 hsetup rfl hsp hpin

end LaneBands
end Layered
end Elegant

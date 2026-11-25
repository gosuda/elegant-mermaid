import Elegant.Layered.LaneEndsPinEnds

set_option autoImplicit false

/-! Pin-phase closure for `pinBands_ends`.

Plan: `pinBands_ends` (in `LaneEndsPinEnds`) composes five phase facts.
Three are proved there (`Restore`, `Relocate`, `Grow`). This module proves
the remaining two (`ApplyPin`, `Reroute`) and closes the composition.
Truth-first probes live in `proofs/wip/Probe/LaneEndsPinPhasesProbe.lean`.
Initial state keeps the two open phases as explicit hypotheses; they are
discharged one by one into `lepePhaseApplyPin_holds` and
`lepePhaseReroute_holds` below. -/

namespace Elegant
namespace Layered
namespace LaneBands

private theorem lpp_bind {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β} {y : β} (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by cases x with | error e => simp [Bind.bind, Except.bind] at h | ok a => exact ⟨a, rfl, h⟩

private theorem lpp_find?_ex {α : Type} (p : α → Bool) (l : List α) (h : ∃ a, a ∈ l ∧ p a = true) : ∃ a, l.find? p = some a := by
  induction l with
  | nil => obtain ⟨a, ha, _⟩ := h; cases ha
  | cons x xs ih =>
    obtain ⟨a, ha, hp⟩ := h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rw [List.find?_cons]
      cases hpx : p a with
      | true => exact ⟨a, rfl⟩
      | false => rw [hpx] at hp; cases hp
    · obtain ⟨b, hb⟩ := ih ⟨a, ha', hp⟩
      rw [List.find?_cons]
      cases hpx : p x with
      | true => exact ⟨x, rfl⟩
      | false => exact ⟨b, hb⟩

private theorem lpp_nodup_map_inj {α β : Type} [BEq β] [LawfulBEq β] (g : α → β) {l : List α} (h : (l.map g).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hgx : g x = g y) : x = y := by
  induction l with
  | nil => cases hx
  | cons z zs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨hnot, htail⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exfalso
        apply hnot
        rw [List.mem_map]
        exact ⟨y, hy', hgx.symm⟩
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exfalso
        apply hnot
        rw [List.mem_map]
        exact ⟨x, hx', hgx⟩
      · exact ih htail hx' hy'

private theorem lpp_find?_idx {α : Type} (p : α → Bool) : ∀ (l : List α) (a : α), l.find? p = some a → ∃ j : Nat, l[j]? = some a ∧ p a = true ∧ ∀ k, k < j → ∀ y, l[k]? = some y → p y = false := by
  intro l
  induction l with
  | nil => intro a h; simp at h
  | cons x xs ih =>
    intro a h
    rw [List.find?_cons] at h
    cases hpx : p x with
    | true =>
      simp [hpx] at h
      subst h
      refine ⟨0, rfl, hpx, ?_⟩
      intro k hk _ _
      simp at hk
    | false =>
      simp [hpx] at h
      obtain ⟨j, hjget, hjp, hj4⟩ := ih a h
      refine ⟨j + 1, ?_, hjp, ?_⟩
      · rw [List.getElem?_cons_succ]
        exact hjget
      · intro k hk y hy
        cases k with
        | zero =>
          rw [List.getElem?_cons_zero] at hy
          cases hy
          exact hpx
        | succ k' =>
          rw [List.getElem?_cons_succ] at hy
          exact hj4 k' (by omega) _ hy

private theorem lpp_frame_mem {axis : Axis} {bands : List Band} {s : Scene} {f : LaneFrame} (hf : f ∈ laneFrames axis bands s) : ∃ band ∈ bands, ∃ b ∈ s.boxes, band.id = f.id ∧ f.near = axis.start b.rect + band.shift - band.start ∧ f.length = axis.length b.rect ∧ s.boxes.find? (fun b => b.id == band.id) = some b := by
  unfold laneFrames at hf
  obtain ⟨band, hband, hfb⟩ := List.mem_filterMap.mp hf
  cases hfind : s.boxes.find? (fun b => b.id == band.id) with
  | none => simp [hfind] at hfb
  | some b =>
    simp [hfind] at hfb
    subst hfb
    exact ⟨band, hband, b, List.mem_of_find?_eq_some hfind, rfl, rfl, rfl, hfind⟩

private theorem lpp_lanesOf_mem {boxes : List ModelBox} {lane : String} (h : lane ∈ lanesOf boxes) : ∃ mb ∈ boxes, mb.role = .group ∧ mb.parent = "" ∧ mb.id = lane := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, hpred⟩ := List.mem_filter.mp hx
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hrole, hpar⟩ := hpred
  exact ⟨x, hxb, beq_iff_eq.mp hrole, beq_iff_eq.mp hpar, rfl⟩

private theorem lpp_inLane_self {boxes : List ModelBox} (hn : (boxes.map (fun b => b.id)).Nodup) {lane : String} (hl : lane ∈ lanesOf boxes) : inLane boxes lane lane = true := by
  obtain ⟨mb, hmbMem, hmbRole, hmbPar, hmbId⟩ := lpp_lanesOf_mem hl
  have hfind : boxes.find? (fun b => b.id == lane) = some mb := by
    have hEq : (fun b : ModelBox => b.id == lane) = (fun b : ModelBox => b.id == mb.id) := by
      funext b
      rw [hmbId]
    rw [hEq]
    exact modelFind?_eq_self hn hmbMem
  unfold inLane laneOf laneOfAux
  rw [hfind]
  simp [hmbPar, hmbRole]

private theorem lpp_layLanes_ids (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing) (lanes : List String) (start : Int) : (layLanes boxes s axis sp lanes start).map (fun b => b.id) = lanes := by
  induction lanes generalizing start with
  | nil => rfl
  | cons lane rest ih =>
    have hhead : (laneBand boxes s axis sp lane start).id = lane := rfl
    simp only [layLanes, List.map_cons, hhead, ih]

private theorem lpp_lanes_ne_empty {boxes : List ModelBox} (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") {lane : String} (h : lane ∈ lanesOf boxes) : lane ≠ "" := by
  obtain ⟨x, hxb, _, _, rfl⟩ := lpp_lanesOf_mem h
  exact hModelNoEmpty x hxb

private theorem lpp_loose_id {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} {loose : List String} {start : Int} : (looseBand boxes s axis sp loose start).id = "" := by
  unfold looseBand
  split <;> rfl

private theorem lpp_replace_other {axis : Axis} {band₂ : Band} {s s' : Scene} (h : replaceFrame axis band₂ s = .ok s') {b : Box} (hbin : b ∈ s.boxes) (hne : b.id ≠ band₂.id) : b ∈ s'.boxes := by
  unfold replaceFrame at h
  cases hfind : s.boxes.findIdx? (fun b => b.id == band₂.id) with
  | none =>
    simp only [hfind, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hbin
  | some index =>
    obtain ⟨hi, hpred, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
    simp only [hfind] at h
    cases hstart : Measure.checkedI32 band₂.start with
    | error e => simp [hstart, Bind.bind, Except.bind] at h
    | ok sv =>
      simp only [hstart, Bind.bind, Except.bind] at h
      cases hthick : Measure.checkedI32 band₂.thickness with
      | error e => simp [hthick] at h
      | ok tv =>
        simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hbin
        have hkid : (s.boxes[k]).id ≠ band₂.id := hne
        have hidx : (s.boxes[index]'hi).id = band₂.id := beq_iff_eq.mp hpred
        have hne' : k ≠ index := by
          intro hkk
          subst hkk
          exact hkid hidx
        have hlen : k < (s.boxes.mapIdx fun j b => if j = index then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b).length := by
          simpa using hk
        have heq : (s.boxes.mapIdx fun j b => if j = index then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b)[k]'hlen = s.boxes[k] := by
          rw [List.getElem_mapIdx]
          simp [hne']
        rw [← heq]
        exact List.getElem_mem hlen

private theorem lpp_fold_other {axis : Axis} {bands : List Band} {shifted pinned : Scene} {b : Box} (hbin : b ∈ shifted.boxes) (hne : ∀ bd ∈ bands, bd.id ≠ b.id) (hfold : bands.foldlM (fun scene band => replaceFrame axis band scene) shifted = .ok pinned) : b ∈ pinned.boxes := by
  induction bands generalizing shifted with
  | nil =>
    have he : pinned = shifted := by
      simpa only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] using hfold.symm
    subst he
    exact hbin
  | cons hd rest ih =>
    rw [List.foldlM_cons] at hfold
    obtain ⟨mid, hmid, hrest⟩ := lpp_bind hfold
    have hneHd : b.id ≠ hd.id := Ne.symm (hne hd (List.mem_cons.mpr (Or.inl rfl)))
    have hmid' : b ∈ mid.boxes := lpp_replace_other hmid hbin hneHd
    exact ih hmid' (fun bd hbd => hne bd (List.mem_cons.mpr (Or.inr hbd))) hrest

private theorem lpp_replaceFrame_rank {axis : Axis} {band : Band} {s s' : Scene} (h : replaceFrame axis band s = .ok s') {b' : Box} (hb' : b' ∈ s'.boxes) : ∃ b ∈ s.boxes, b'.id = b.id ∧ axis.other.start b'.rect = axis.other.start b.rect ∧ axis.other.length b'.rect = axis.other.length b.rect := by
  unfold replaceFrame at h
  cases hfind : s.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    simp only [hfind, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨b', hb', rfl, rfl, rfl⟩
  | some idx =>
    obtain ⟨hi, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
    simp only [hfind] at h
    cases hstart : Measure.checkedI32 band.start with
    | error e => simp [hstart, Bind.bind, Except.bind] at h
    | ok sv =>
      simp only [hstart, Bind.bind, Except.bind] at h
      cases hthick : Measure.checkedI32 band.thickness with
      | error e => simp [hthick] at h
      | ok tv =>
        simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at h
        rw [← h] at hb'
        simp only at hb'
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hb'
        have hlen : (s.boxes.mapIdx fun j b => if j = idx then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b).length = s.boxes.length := List.length_mapIdx
        have hklen : k < s.boxes.length := by
          have hkk0 := (List.getElem?_eq_some_iff.mp hk).1
          omega
        have hbk : s.boxes[k]? = some s.boxes[k] := List.getElem?_eq_getElem hklen
        have hmap := List.getElem?_mapIdx (f := fun j b => if j = idx then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b) (l := s.boxes) (i := k)
        rw [hk, hbk] at hmap
        simp only [Option.map_some] at hmap
        by_cases hkk : k = idx
        · have hkk2 : idx = k := hkk.symm
          subst hkk2
          rw [ite_eq_left rfl] at hmap
          have hbeq := Option.some.inj hmap
          subst hbeq
          exact ⟨s.boxes[idx], List.mem_iff_getElem.mpr ⟨idx, hi, rfl⟩, rfl, (placeRect_other _ _ _).1, (placeRect_other _ _ _).2⟩
        · rw [ite_eq_right hkk] at hmap
          have hbeq : b' = s.boxes[k] := Option.some.inj hmap
          rw [hbeq]
          exact ⟨s.boxes[k], List.mem_iff_getElem.mpr ⟨k, hklen, rfl⟩, rfl, rfl, rfl⟩

private theorem lpp_fold_rank {axis : Axis} {bands : List Band} {shifted pinned : Scene} (hfold : bands.foldlM (fun scene band => replaceFrame axis band scene) shifted = .ok pinned) {b' : Box} (hb' : b' ∈ pinned.boxes) : ∃ b ∈ shifted.boxes, b'.id = b.id ∧ axis.other.start b'.rect = axis.other.start b.rect ∧ axis.other.length b'.rect = axis.other.length b.rect := by
  induction bands generalizing shifted with
  | nil =>
    have he : pinned = shifted := by
      simpa only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] using hfold.symm
    subst he
    exact ⟨b', hb', rfl, rfl, rfl⟩
  | cons hd rest ih =>
    rw [List.foldlM_cons] at hfold
    obtain ⟨mid, hmid, hrest⟩ := lpp_bind hfold
    obtain ⟨bm, hbmm, hidm, hr1m, hr2m⟩ := ih hrest
    obtain ⟨b, hbm, hidb, hr1b, hr2b⟩ := lpp_replaceFrame_rank hmid hbmm
    exact ⟨b, hbm, hidm.trans hidb, hr1m.trans hr1b, hr2m.trans hr2b⟩

private theorem lpp_layBands_ids_nodup {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} (hModelNodup : (boxes.map fun b => b.id).Nodup) (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") : ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup := by
  have hLaneIds : ((layLanes boxes s axis sp (lanesOf boxes) (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id) = lanesOf boxes := lpp_layLanes_ids _ _ _ _ _ _
  have hLaneNodup : ((layLanes boxes s axis sp (lanesOf boxes) (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id).Nodup := by
    rw [hLaneIds]
    exact lanesOf_nodup hModelNodup
  have hfresh : "" ∉ lanesOf boxes := fun hmem => lpp_lanes_ne_empty hModelNoEmpty hmem rfl
  unfold layBands
  by_cases hl : (looseNodes boxes).isEmpty = true
  · simp only [hl, ↓reduceIte]
    exact hLaneNodup
  · simp only [hl, ↓reduceIte, Bool.false_eq_true, List.map_append, hLaneIds]
    have hsing : ∀ S : Int, (([looseBand boxes s axis sp (looseNodes boxes) S].map fun b => b.id) = [""]) := by
      intro S
      simp only [List.map_cons, List.map_nil, lpp_loose_id]
    simp only [hsing]
    rw [List.nodup_append]
    refine ⟨?_, (by simp : ([""] : List String).Nodup), ?_⟩
    · exact lanesOf_nodup hModelNodup
    · intro a ha b hb hEq
      rw [List.mem_singleton] at hb
      subst hb
      exact lpp_lanes_ne_empty hModelNoEmpty ha hEq

private theorem lpp_lane_pinned {axis : Axis} {bands : List Band} {shifted pinned : Scene} (hfold : bands.foldlM (fun scene band => replaceFrame axis band scene) shifted = .ok pinned) (hnodup : (bands.map fun b => b.id).Nodup) (hshiftNodup : (shifted.boxes.map (·.id)).Nodup) {band : Band} (hband : band ∈ bands) {b0 : Box} (hb0 : b0 ∈ shifted.boxes) (hid0 : b0.id = band.id) : ∃ bp ∈ pinned.boxes, bp.id = band.id ∧ axis.start bp.rect = band.start ∧ axis.length bp.rect = band.thickness ∧ axis.other.start bp.rect = axis.other.start b0.rect ∧ axis.other.length bp.rect = axis.other.length b0.rect := by
  induction bands generalizing shifted with
  | nil => cases hband
  | cons hd rest ih =>
    rw [List.foldlM_cons] at hfold
    obtain ⟨mid, hmid, hrest⟩ := lpp_bind hfold
    rw [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnot, htail⟩ := hnodup
    rcases List.mem_cons.mp hband with rfl | hmem
    · obtain ⟨bm, hbmm, hidm, hstartm, hlenm⟩ := replaceFrame_places_lane hmid ⟨b0, hb0, hid0⟩
      obtain ⟨bpre, hbprem, hidprem, hr1pre, hr2pre⟩ := lpp_replaceFrame_rank hmid hbmm
      have hidpre0 : bpre.id = b0.id := hidprem.symm.trans (hidm.trans hid0.symm)
      have hpreEq : bpre = b0 := lpp_nodup_map_inj (·.id) hshiftNodup hbprem hb0 hidpre0
      have hr1 : axis.other.start bm.rect = axis.other.start b0.rect := by rw [hpreEq] at hr1pre; exact hr1pre
      have hr2 : axis.other.length bm.rect = axis.other.length b0.rect := by rw [hpreEq] at hr2pre; exact hr2pre
      have hneRest : ∀ bd ∈ rest, bd.id ≠ bm.id := by
        intro bd hbd heq
        apply hnot
        rw [List.mem_map]
        exact ⟨bd, hbd, heq.trans hidm⟩
      have hbmPin : bm ∈ pinned.boxes := lpp_fold_other hbmm hneRest hrest
      exact ⟨bm, hbmPin, hidm, hstartm, hlenm, hr1, hr2⟩
    · have hneHd : b0.id ≠ hd.id := by
        intro heq
        apply hnot
        rw [List.mem_map]
        exact ⟨band, hmem, hid0.symm.trans heq⟩
      have hb0mid : b0 ∈ mid.boxes := lpp_replace_other hmid hb0 hneHd
      have hmidNodup : (mid.boxes.map (·.id)).Nodup := by
        obtain ⟨hidMap, _, _, _⟩ := replaceFrame_boxes_maps hmid
        rw [hidMap]
        exact hshiftNodup
      exact ih hrest htail hmidNodup hmem hb0mid

private theorem lpp_loose_members {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} {loose : List String} {start : Int} : (looseBand boxes s axis sp loose start).members = loose := by
  unfold looseBand
  split <;> rfl

private theorem lpp_cover_unique_lane {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} (hModelNodup : (boxes.map fun b => b.id).Nodup) (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") (hIdsNodup : ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup) {bands : List Band} (hbands : bands = layBands boxes s axis sp (lanesOf boxes)) {id : String} (hidLane : id ∈ lanesOf boxes) {b1 : Band} (hm1 : b1 ∈ bands) (hc1 : bandCovers b1 id) {b2 : Band} (hm2 : b2 ∈ bands) (hc2 : bandCovers b2 id) : b1 = b2 := by
  have hIdsNodupB : (bands.map fun b => b.id).Nodup := by rw [hbands]; exact hIdsNodup
  have hmemEq : ∀ b ∈ bands, ∀ c ∈ bands, b.id = c.id → b = c := fun b hb c hc heq => lpp_nodup_map_inj (·.id) hIdsNodupB hb hc heq
  have hSelf : inLane boxes id id = true := lpp_inLane_self hModelNodup hidLane
  have hidNe : id ≠ "" := lpp_lanes_ne_empty hModelNoEmpty hidLane
  have hC1 := layBands_mem_cases (hmem := hbands ▸ hm1)
  have hC2 := layBands_mem_cases (hmem := hbands ▸ hm2)
  have hc1' : b1.id = id ∨ id ∈ b1.members := hc1
  have hc2' : b2.id = id ∨ id ∈ b2.members := hc2
  rcases hC1 with hLane1 | hLoose1
  · rcases hC2 with hLane2 | hLoose2
    · obtain ⟨lane1, _, st1, rfl⟩ := layLanes_mem_lane hLane1
      obtain ⟨lane2, _, st2, rfl⟩ := layLanes_mem_lane hLane2
      have e1 : (laneBand boxes s axis sp lane1 st1).id = lane1 := rfl
      have e2 : (laneBand boxes s axis sp lane2 st2).id = lane2 := rfl
      rcases hc1' with hEq1 | hMem1
      · rcases hc2' with hEq2 | hMem2
        · exact hmemEq _ hm1 _ hm2 (hEq1.trans hEq2.symm)
        · have hIn2 : inLane boxes id lane2 = true := laneBand_mem_inLane hMem2
          have hEq : lane2 = id := inLane_unique hIn2 hSelf
          exact hmemEq _ hm1 _ hm2 (hEq1.trans (e2.trans hEq).symm)
      · rcases hc2' with hEq2 | hMem2
        · have hIn1 : inLane boxes id lane1 = true := laneBand_mem_inLane hMem1
          have hEq : lane1 = id := inLane_unique hIn1 hSelf
          exact hmemEq _ hm1 _ hm2 ((e1.trans hEq).trans hEq2.symm)
        · have hIn1 : inLane boxes id lane1 = true := laneBand_mem_inLane hMem1
          have hIn2 : inLane boxes id lane2 = true := laneBand_mem_inLane hMem2
          have hEq : lane1 = lane2 := inLane_unique hIn1 hIn2
          exact hmemEq _ hm1 _ hm2 ((e1.trans hEq).trans e2.symm)
    · exfalso
      rw [hLoose2] at hc2'
      rcases hc2' with hEq2 | hMem2
      · rw [lpp_loose_id] at hEq2
        exact hidNe hEq2.symm
      · have hMemLoose : id ∈ looseNodes boxes := by
          rw [lpp_loose_members] at hMem2
          exact hMem2
        have hContra := loose_not_inLane hModelNodup hMemLoose (lane := id)
        rw [hSelf] at hContra
        exact Bool.noConfusion hContra
  · exfalso
    rw [hLoose1] at hc1'
    rcases hc1' with hEq1 | hMem1
    · rw [lpp_loose_id] at hEq1
      exact hidNe hEq1.symm
    · have hMemLoose : id ∈ looseNodes boxes := by
        rw [lpp_loose_members] at hMem1
        exact hMem1
      have hContra := loose_not_inLane hModelNodup hMemLoose (lane := id)
      rw [hSelf] at hContra
      exact Bool.noConfusion hContra
private theorem lpp_bandShift_lane {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} {bands : List Band} (hbands : bands = layBands boxes s axis sp (lanesOf boxes)) (hModelNodup : (boxes.map fun b => b.id).Nodup) (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") {band : Band} (hband : band ∈ bands) (hne : band.id ≠ "") : bandShift bands band.id = band.shift := by
  have hIdsNodup : ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup := lpp_layBands_ids_nodup hModelNodup hModelNoEmpty
  have hLaneMem : band.id ∈ lanesOf boxes := by
    have hC := layBands_mem_cases (hmem := hbands ▸ hband)
    rcases hC with hL | hO
    · exact layLanes_id_mem hL
    · exfalso
      have hid : band.id = "" := by
        rw [hO, lpp_loose_id]
      exact hne hid
  have hcov : bandCovers band band.id := Or.inl rfl
  have hUniq : ∀ b1 ∈ bands, ∀ b2 ∈ bands, bandCovers b1 band.id → bandCovers b2 band.id → b1 = b2 := fun b1 hb1 b2 hb2 hc1 hc2 => lpp_cover_unique_lane hModelNodup hModelNoEmpty hIdsNodup hbands hLaneMem hb1 hc1 hb2 hc2
  exact bandShift_eq hband hcov hUniq


private theorem lpp_lane_endRect_eq {axis : Axis} {band : Band} {bOrig bm bp : Box} {frames : List LaneFrame} {f : LaneFrame} (hfind : frames.find? (fun b_ => b_.id == bp.id) = some f) (hnear : f.near = axis.start bOrig.rect + band.shift - band.start) (hlen : f.length = axis.length bOrig.rect) (hbmRect : bm.rect = axis.withStart bOrig.rect (axis.start bOrig.rect + band.shift)) (hbpStart : axis.start bp.rect = band.start) (hrankS : axis.other.start bp.rect = axis.other.start bm.rect) (hrankL : axis.other.length bp.rect = axis.other.length bm.rect) (hrankBm : axis.other.start bm.rect = axis.other.start bOrig.rect) (hrankBmL : axis.other.length bm.rect = axis.other.length bOrig.rect) : endRect axis frames bp = bm.rect := by
  unfold endRect
  rw [hfind]
  dsimp only
  unfold oldFrame placeRect
  have hcross : axis.start bp.rect + f.near = axis.start bOrig.rect + band.shift := by
    rw [hbpStart, hnear]
    omega
  rw [hcross, hlen]
  cases axis with
  | x =>
    simp only [Axis.withStart, Axis.withLength, Axis.start, Axis.length, Axis.other] at hbmRect hrankS hrankL hrankBm hrankBmL ⊢
    rw [hbmRect, hrankS, hrankBm, hrankL, hrankBmL]
  | y =>
    simp only [Axis.withStart, Axis.withLength, Axis.start, Axis.length, Axis.other] at hbmRect hrankS hrankL hrankBm hrankBmL ⊢
    rw [hbmRect, hrankS, hrankBm, hrankL, hrankBmL]

private theorem lpp_laneFrames_ids_nodup {axis : Axis} {bands : List Band} {s : Scene} (hnodup : (bands.map fun b => b.id).Nodup) : ((laneFrames axis bands s).map fun f => f.id).Nodup := by
  induction bands with
  | nil =>
    simp only [laneFrames, List.filterMap_nil, List.map_nil]
    exact List.nodup_nil
  | cons hd rest ih =>
    unfold laneFrames at ih ⊢
    simp only [List.filterMap_cons] at ih ⊢
    rw [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnot, htail⟩ := hnodup
    cases hfind : s.boxes.find? (fun b => b.id == hd.id) with
    | none =>
      simp only [Option.map_none] at ih ⊢
      exact ih htail
    | some box =>
      simp only [Option.map_some] at ih ⊢
      have ih' := ih htail
      simp only [List.map_cons, List.nodup_cons] at ⊢
      refine ⟨?_, ih'⟩
      intro hcon
      have hmem : ∃ f ∈ (rest.filterMap fun b => (s.boxes.find? fun b_ => b_.id == b.id).map fun box => ({ id := b.id, near := axis.start box.rect + b.shift - b.start, length := axis.length box.rect } : LaneFrame)), f.id = hd.id := by
        obtain ⟨f, hfm, hid⟩ := List.mem_map.mp hcon
        exact ⟨f, hfm, hid⟩
      obtain ⟨f, hfm, hid⟩ := hmem
      obtain ⟨band, hband, _, _, hbid, _, _, _⟩ := lpp_frame_mem (s := s) (bands := rest) (f := f) hfm
      have hmap : band.id ∈ (rest.map fun b => b.id) := List.mem_map.mpr ⟨band, hband, rfl⟩
      rw [hbid, hid] at hmap
      exact hnot hmap

private theorem lpp_shifted_nonlane_box {axis : Axis} {bands : List Band} {s pinned : Scene} (happ : applyPin (buildPin axis bands s) bands s = .ok pinned) {bp : Box} (hb : bp ∈ pinned.boxes) (hnf : ∀ band ∈ bands, band.id ≠ bp.id) : ∃ b ∈ s.boxes, ∃ w, bp.id = b.id ∧ Measure.checkedI32 (axis.start b.rect + bandShift bands b.id) = .ok w ∧ bp.rect = axis.withStart b.rect w ∧ w = axis.start b.rect + bandShift bands b.id ∧ endRect axis (laneFrames axis bands s) bp = bp.rect := by
  obtain ⟨b, hbm, w, hid, hw, hrect, hval⟩ := applyPin_c5_box happ bp hb hnf
  have hfindNone : (laneFrames axis bands s).find? (fun b_ => b_.id == bp.id) = none := by
    cases hsome : (laneFrames axis bands s).find? (fun b_ => b_.id == bp.id) with
    | none => rfl
    | some f =>
      exfalso
      obtain ⟨j, _, hpred, _⟩ := lpp_find?_idx _ _ _ hsome
      have hfid : f.id = bp.id := beq_iff_eq.mp hpred
      obtain ⟨band, hband, _, _, hbid, _, _, _⟩ := lpp_frame_mem (List.mem_of_find?_eq_some hsome)
      have hEq : band.id = bp.id := hbid.trans hfid
      exact hnf band hband hEq
  have hEnd : endRect axis (laneFrames axis bands s) bp = bp.rect := by
    unfold endRect
    rw [hfindNone]
  have hDelta : (buildPin axis bands s).boxDelta b.id = bandShift bands b.id := buildPin_boxDelta b.id
  rw [hDelta] at hw hval
  exact ⟨b, hbm, w, hid, hw, hrect, hval, hEnd⟩

theorem pinBands_ends_closed {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hC5 : Validator.C5 s.layoutDump)
    (hlanes : lanesOf boxes ≠ [])
    (hrouteNodup : (s.routes.map (·.id)).Nodup)
    (hnodupB : (s.boxes.map (·.id)).Nodup)
    (hEnds : ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      ∀ rt ∈ s.routes,
        bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) rt.fromId =
        bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) rt.toId ∨
        ((Axis.ofDirection o.direction).point (rt.points.head?.getD ⟨0, 0⟩) ≠
          (Axis.ofDirection o.direction).point (rt.points.getLast?.getD ⟨0, 0⟩) ∧ 1 < rt.points.length))
    (hEndsPin : FindRouteEndsPin)
    (hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "")
    (hApply : ∀ (axis : Axis) (bands : List Band), lepePhaseApplyPin axis bands boxes s)
    (hReroute : ∀ (axis : Axis) (bands : List Band), lepePhaseReroute axis bands boxes o s)
    (h : pinBands boxes o s = .ok r) :
    ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      EndsOnOld (Axis.ofDirection o.direction)
        (laneFrames (Axis.ofDirection o.direction)
          (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
        r.layoutDump :=
  pinBands_ends hC5 hlanes hrouteNodup hnodupB hEnds hEndsPin hModelClean hApply hReroute h

end LaneBands
end Layered
end Elegant

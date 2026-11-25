import Elegant.Layered.LaneEndsPinPhaseApply

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

private theorem lft_lanesOf_mem {boxes : List ModelBox} {lane : String} (h : lane ∈ lanesOf boxes) : ∃ mb ∈ boxes, mb.role = .group ∧ mb.parent = "" ∧ mb.id = lane := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, hpred⟩ := List.mem_filter.mp hx
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hrole, hpar⟩ := hpred
  exact ⟨x, hxb, beq_iff_eq.mp hrole, beq_iff_eq.mp hpar, rfl⟩

private theorem lft_nodup_map_inj {α β : Type} [BEq β] [LawfulBEq β] (g : α → β) {l : List α} (h : (l.map g).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hgx : g x = g y) : x = y := by
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

private theorem lft_inLane_self {boxes : List ModelBox} (hn : (boxes.map (fun b => b.id)).Nodup) {lane : String} (hl : lane ∈ lanesOf boxes) : inLane boxes lane lane = true := by
  obtain ⟨mb, hmbMem, hmbRole, hmbPar, hmbId⟩ := lft_lanesOf_mem hl
  have hfind : boxes.find? (fun b => b.id == lane) = some mb := by
    have hEq : (fun b : ModelBox => b.id == lane) = (fun b : ModelBox => b.id == mb.id) := by
      funext b
      rw [hmbId]
    rw [hEq]
    exact modelFind?_eq_self hn hmbMem
  unfold inLane laneOf laneOfAux
  rw [hfind]
  simp [hmbPar, hmbRole]

private theorem lft_layLanes_ids (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing) (lanes : List String) (start : Int) : (layLanes boxes s axis sp lanes start).map (fun b => b.id) = lanes := by
  induction lanes generalizing start with
  | nil => rfl
  | cons lane rest ih =>
    have hhead : (laneBand boxes s axis sp lane start).id = lane := rfl
    simp only [layLanes, List.map_cons, hhead, ih]
private theorem lft_lanes_ne_empty {boxes : List ModelBox} (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") {lane : String} (h : lane ∈ lanesOf boxes) : lane ≠ "" := by
  obtain ⟨x, hxb, _, _, rfl⟩ := lft_lanesOf_mem h
  exact hModelNoEmpty x hxb

private theorem lft_loose_id_members {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} {loose : List String} {start : Int} : (looseBand boxes s axis sp loose start).id = "" ∧ (looseBand boxes s axis sp loose start).members = loose := by
  unfold looseBand
  split <;> exact ⟨rfl, rfl⟩

private theorem lft_layBands_ids_nodup {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} (hModelNodup : (boxes.map fun b => b.id).Nodup) (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") : ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup := by
  have hLaneIds : ((layLanes boxes s axis sp (lanesOf boxes) (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id) = lanesOf boxes := lft_layLanes_ids _ _ _ _ _ _
  have hLaneNodup : ((layLanes boxes s axis sp (lanesOf boxes) (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id).Nodup := by
    rw [hLaneIds]
    exact lanesOf_nodup hModelNodup
  have hfresh : "" ∉ lanesOf boxes := fun hmem => lft_lanes_ne_empty hModelNoEmpty hmem rfl
  unfold layBands
  by_cases hl : (looseNodes boxes).isEmpty = true
  · simp only [hl, ↓reduceIte]
    exact hLaneNodup
  · simp only [hl, ↓reduceIte, Bool.false_eq_true, List.map_append, hLaneIds]
    have hsing : ∀ S : Int, (([looseBand boxes s axis sp (looseNodes boxes) S].map fun b => b.id) = [""]) := by
      intro S
      simp only [List.map_cons, List.map_nil, (lft_loose_id_members (boxes := boxes)).1]
    simp only [hsing]
    rw [List.nodup_append]
    refine ⟨?_, (by simp : ([""] : List String).Nodup), ?_⟩
    · exact lanesOf_nodup hModelNodup
    · intro a ha b hb hEq
      rw [List.mem_singleton] at hb
      subst hb
      exact lft_lanes_ne_empty hModelNoEmpty ha hEq

private theorem lft_cover_unique_lane {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} (hModelNodup : (boxes.map fun b => b.id).Nodup) (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") (hIdsNodup : ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup) {bands : List Band} (hbands : bands = layBands boxes s axis sp (lanesOf boxes)) {id : String} (hidLane : id ∈ lanesOf boxes) {b1 : Band} (hm1 : b1 ∈ bands) (hc1 : bandCovers b1 id) {b2 : Band} (hm2 : b2 ∈ bands) (hc2 : bandCovers b2 id) : b1 = b2 := by
  have hIdsNodupB : (bands.map fun b => b.id).Nodup := by rw [hbands]; exact hIdsNodup
  have hmemEq : ∀ b ∈ bands, ∀ c ∈ bands, b.id = c.id → b = c := fun b hb c hc heq => lft_nodup_map_inj (·.id) hIdsNodupB hb hc heq
  have hSelf : inLane boxes id id = true := lft_inLane_self hModelNodup hidLane
  have hidNe : id ≠ "" := lft_lanes_ne_empty hModelNoEmpty hidLane
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
      · rw [(lft_loose_id_members).1] at hEq2
        exact hidNe hEq2.symm
      · have hMemLoose : id ∈ looseNodes boxes := by
          rw [(lft_loose_id_members).2] at hMem2
          exact hMem2
        have hContra := loose_not_inLane hModelNodup hMemLoose (lane := id)
        rw [hSelf] at hContra
        exact Bool.noConfusion hContra
  · exfalso
    rw [hLoose1] at hc1'
    rcases hc1' with hEq1 | hMem1
    · rw [(lft_loose_id_members).1] at hEq1
      exact hidNe hEq1.symm
    · have hMemLoose : id ∈ looseNodes boxes := by
        rw [(lft_loose_id_members).2] at hMem1
        exact hMem1
      have hContra := loose_not_inLane hModelNodup hMemLoose (lane := id)
      rw [hSelf] at hContra
      exact Bool.noConfusion hContra

private theorem lft_bandShift_lane {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} {bands : List Band} (hbands : bands = layBands boxes s axis sp (lanesOf boxes)) (hModelNodup : (boxes.map fun b => b.id).Nodup) (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") {band : Band} (hband : band ∈ bands) (hne : band.id ≠ "") : bandShift bands band.id = band.shift := by
  have hIdsNodup : ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup := lft_layBands_ids_nodup hModelNodup hModelNoEmpty
  have hLaneMem : band.id ∈ lanesOf boxes := by
    have hC := layBands_mem_cases (hmem := hbands ▸ hband)
    rcases hC with hL | hO
    · exact layLanes_id_mem hL
    · exfalso
      have hid : band.id = "" := by
        rw [hO, (lft_loose_id_members).1]
      exact hne hid
  have hcov : bandCovers band band.id := Or.inl rfl
  have hUniq : ∀ b1 ∈ bands, ∀ b2 ∈ bands, bandCovers b1 band.id → bandCovers b2 band.id → b1 = b2 := fun b1 hb1 b2 hb2 hc1 hc2 => lft_cover_unique_lane hModelNodup hModelNoEmpty hIdsNodup hbands hLaneMem hb1 hc1 hb2 hc2
  exact bandShift_eq hband hcov hUniq
private theorem lft_bind {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β} {y : β} (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem lft_find?_ex {α : Type} (p : α → Bool) (l : List α) (a : α) (hm : a ∈ l) (hp : p a = true) : ∃ b, l.find? p = some b := by
  have hex : ∃ x, x ∈ l ∧ p x = true := ⟨a, hm, hp⟩
  have h := (List.find?_isSome).mpr hex
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
  exact ⟨b, hb⟩

private theorem lft_findIdx_lookup {α : Type} (l : List α) (p : α → Bool) (j : Nat) (h : l.findIdx? p = some j) : ∃ x, l[j]? = some x ∧ p x = true := by
  induction l generalizing j with
  | nil => rw [List.findIdx?_nil] at h; exact absurd h (by simp)
  | cons y ys ih =>
    rw [List.findIdx?_cons] at h
    cases hp : p y with
    | true =>
      simp only [hp, ↓reduceIte, Option.some.injEq] at h
      cases j with
      | zero => exact ⟨y, rfl, hp⟩
      | succ j' => exact absurd h (by simp)
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      cases j with
      | zero => exact absurd h (by simp)
      | succ j' =>
        cases hv : ys.findIdx? p with
        | none => rw [hv] at h; simp at h
        | some k =>
          rw [hv, Option.map_some, Option.some.injEq] at h
          have hjk : j' = k := by omega
          obtain ⟨x, hx, hpx⟩ := ih k hv
          exact ⟨x, by simp only [hjk]; simpa using hx, hpx⟩

private theorem lft_mapIdx_kept_get (place : Rect → Rect) (idx : Nat) : ∀ (l : List Box) (n k : Nat), k + n ≠ idx → ∀ (b : Box), l[k]? = some b → (l.mapIdx fun j b => if j + n = idx then ({ b with rect := place b.rect } : Box) else b)[k]? = some b := by
  intro l
  induction l with
  | nil =>
    intro n k hk b hbk
    have hlt := (List.getElem?_eq_some_iff.mp hbk).1
    simp at hlt
  | cons head tail ih =>
    intro n k hk b hbk
    cases k with
    | zero =>
      have hhead : head = b := by
        rw [List.getElem?_cons_zero] at hbk
        exact Option.some.inj hbk
      subst hhead
      rw [List.mapIdx_cons, List.getElem?_cons_zero]
      show (if 0 + n = idx then ({ head with rect := place head.rect } : Box) else head) = some head
      rw [ite_eq_right hk]
    | succ k' =>
      rw [List.mapIdx_cons] at ⊢
      rw [List.getElem?_cons_succ] at hbk
      rw [List.getElem?_cons_succ] at ⊢
      show ((tail.mapIdx fun i b => if i + 1 + n = idx then ({ b with rect := place b.rect } : Box) else b)[k']? = some b)
      have heq : (fun i b => if i + 1 + n = idx then ({ b with rect := place b.rect } : Box) else b) =
          (fun j b => if j + (n + 1) = idx then ({ b with rect := place b.rect } : Box) else b) := by
        funext j b
        have h : j + 1 + n = j + (n + 1) := by omega
        rw [h]
      rw [heq]
      exact ih (n + 1) k' (by omega) b hbk
private theorem lft_replaceFrame_kept {axis : Axis} {band : Band} {s s' : Scene} (h : replaceFrame axis band s = .ok s') (b : Box) (hb : b ∈ s.boxes) (hne : b.id ≠ band.id) : ∃ b' ∈ s'.boxes, b'.id = b.id ∧ b'.rect = b.rect ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive := by
  unfold replaceFrame at h
  cases hfind : s.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    simp only [hfind, Pure.pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨b, hb, rfl, rfl, rfl, rfl, rfl⟩
  | some idx =>
    simp only [hfind] at h
    cases hstart : Measure.checkedI32 band.start with
    | error e => simp [hstart, Bind.bind, Except.bind] at h
    | ok start =>
      simp only [hstart, Bind.bind, Except.bind] at h
      cases hthick : Measure.checkedI32 band.thickness with
      | error e => simp [hthick] at h
      | ok thickness =>
        simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hb
        have hkk : k + 0 ≠ idx := by
          intro hkk
          have hkz : k = idx := by omega
          rw [hkz] at hk
          obtain ⟨x, hx, hpx⟩ := lft_findIdx_lookup s.boxes _ idx hfind
          rw [hk] at hx
          have hbx : b = x := Option.some.inj hx
          have hbe : b.id = band.id := by rw [hbx]; exact beq_iff_eq.mp hpx
          exact hne hbe
        have hkept := lft_mapIdx_kept_get (placeRect axis start thickness) idx s.boxes 0 k hkk b hk
        have hmem : b ∈ s'.boxes := by
          rw [← h]
          exact List.mem_iff_getElem?.mpr ⟨k, hkept⟩
        exact ⟨b, hmem, rfl, rfl, rfl, rfl, rfl⟩

private theorem lft_getElem?_inj {α : Type} : ∀ (l : List α), l.Nodup → ∀ {i j : Nat} {b : α}, l[i]? = some b → l[j]? = some b → i = j := by
  intro l
  induction l with
  | nil =>
    intro h i j b hi hj
    simp at hi
  | cons head tail ih =>
    intro h i j b hi hj
    rw [List.nodup_cons] at h
    obtain ⟨hnot, htail⟩ := h
    cases i with
    | zero =>
      have hhead : head = b := by
        rw [List.getElem?_cons_zero] at hi
        exact Option.some.inj hi
      cases j with
      | zero => rfl
      | succ j' =>
        exfalso
        rw [List.getElem?_cons_succ] at hj
        have hmem : b ∈ tail := List.mem_iff_getElem?.mpr ⟨j', hj⟩
        rw [← hhead] at hmem
        exact hnot hmem
    | succ i' =>
      cases j with
      | zero =>
        have hhead : head = b := by
          rw [List.getElem?_cons_zero] at hj
          exact Option.some.inj hj
        exfalso
        rw [List.getElem?_cons_succ] at hi
        have hmem : b ∈ tail := List.mem_iff_getElem?.mpr ⟨i', hi⟩
        rw [← hhead] at hmem
        exact hnot hmem
      | succ j' =>
        rw [List.getElem?_cons_succ] at hi hj
        exact congrArg Nat.succ (ih htail hi hj)

private theorem lft_box_find_self {l : List Box} (h : (l.map (·.id)).Nodup) {b : Box} (hb : b ∈ l) : l.find? (fun x => x.id == b.id) = some b := by
  induction l with
  | nil => simp at hb
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    obtain ⟨hfresh, hrest⟩ := h
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · simp
    · have hne : first.id ≠ b.id := by
        intro heq
        exact hfresh (List.mem_map.mpr ⟨b, hb, heq.symm⟩)
      have hfind : (first.id == b.id) = false := beq_eq_false_iff_ne.mpr hne
      simp [List.find?, hfind, ih hrest hb]

private theorem lft_boxDelta_lane {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} {bands : List Band} (hbands : bands = layBands boxes s axis sp (lanesOf boxes)) (hModelNodup : (boxes.map fun b => b.id).Nodup) (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") {band : Band} (hmem : band ∈ bands) (hne : band.id ≠ "") : (buildPin axis bands s).boxDelta band.id = band.shift := by
  have hIdsNodup : ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup := lft_layBands_ids_nodup hModelNodup hModelNoEmpty
  have hLaneMem : band.id ∈ lanesOf boxes := by
    have hC := layBands_mem_cases (hmem := hbands ▸ hmem)
    rcases hC with hL | hO
    · exact layLanes_id_mem hL
    · exfalso
      have hid : band.id = "" := by rw [hO, (lft_loose_id_members).1]
      exact hne hid
  have hexp : ∀ {b : Band}, b ∈ bands → ∀ {p : String × Int}, p ∈ (b.id, b.shift) :: b.members.map (fun m => (m, b.shift)) → p.2 = b.shift := by
    intro b _ p hp
    simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨m, _, hmp⟩
    · rfl
    · exact (congrArg Prod.snd hmp).symm
  have hflat : (buildPin axis bands s).boxes = bands.flatMap fun b => (b.id, b.shift) :: b.members.map fun m => (m, b.shift) := rfl
  have hmemPin : (band.id, band.shift) ∈ (buildPin axis bands s).boxes := by
    rw [hflat, List.mem_flatMap]
    exact ⟨band, hmem, List.mem_cons_self⟩
  obtain ⟨p, hp⟩ := lft_find?_ex (fun e : String × Int => e.1 == band.id) _ (band.id, band.shift) hmemPin (beq_self_eq_true band.id)
  have hpred : (p.1 == band.id) = true := by
    have h := List.find?_some hp
    simpa using h
  have hpid : p.1 = band.id := beq_iff_eq.mp hpred
  have hpmem : p ∈ (buildPin axis bands s).boxes := List.mem_of_find?_eq_some hp
  rw [hflat, List.mem_flatMap] at hpmem
  obtain ⟨b, hbmem, hbp⟩ := hpmem
  have hpexp : p.2 = b.shift := hexp hbmem hbp
  have hcov : bandCovers b band.id := by
    simp only [List.mem_cons, List.mem_map] at hbp
    rcases hbp with rfl | ⟨m, hmmem, hmp⟩
    · exact Or.inl (beq_iff_eq.mp (by simpa using hpred))
    · have h1 : m = p.1 := congrArg Prod.fst hmp
      have hm : m = band.id := h1.trans hpid
      exact Or.inr (by rw [← hm]; exact hmmem)
  have heq : b = band := lft_cover_unique_lane hModelNodup hModelNoEmpty hIdsNodup hbands hLaneMem hbmem hcov hmem (Or.inl rfl)
  have hdelta : (buildPin axis bands s).boxDelta band.id = p.2 := by
    unfold Pin.boxDelta
    rw [hp]
    rfl
  rw [hdelta, hpexp, heq]
private theorem lft_shifted_of_mem {s : Scene} {pin : Pin} {axis : Axis} {shifted : List Box} (hmap : s.boxes.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant (pin.boxDelta b.id)).rect axis b.rect } : Except LayoutError Box)) = .ok shifted) {b0 : Box} (hb0 : b0 ∈ s.boxes) : ∃ bs ∈ shifted, bs.id = b0.id ∧ bs.parent = b0.parent ∧ ∃ w, Measure.checkedI32 (axis.start b0.rect + pin.boxDelta b0.id) = .ok w ∧ bs.rect = axis.withStart b0.rect w ∧ w = axis.start b0.rect + pin.boxDelta b0.id := by
  obtain ⟨i, hi, hbi⟩ := List.mem_iff_getElem.mp hb0
  have hspec := mapM_except_spec _ s.boxes shifted hmap
  have hlen : shifted.length = s.boxes.length := hspec.1
  obtain ⟨a, b, ha, hb, hab⟩ := hspec.2 i hi (by omega)
  have hag : s.boxes[i]? = some s.boxes[i] := List.getElem?_eq_getElem hi
  have haE : a = b0 := (Option.some.inj (ha.symm.trans hag)).trans hbi
  obtain ⟨hid, hpar, _, _, w, hw, hrect, hval⟩ := pinShiftBox_ok hab
  rw [haE] at hid hpar hw hrect hval
  exact ⟨b, List.mem_iff_getElem?.mpr ⟨i, hb⟩, hid, hpar, w, hw, hrect, hval⟩


private theorem lft_replaceFrame_places {axis : Axis} {band : Band} {s s' : Scene} (h : replaceFrame axis band s = .ok s') (hnodup : (s.boxes.map (·.id)).Nodup) {b : Box} (hb : b ∈ s.boxes) (hid : b.id = band.id) : ∃ b' ∈ s'.boxes, b'.id = band.id ∧ b'.rect = placeRect axis band.start band.thickness b.rect ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive := by
  unfold replaceFrame at h
  cases hfind : s.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    exfalso
    have hnone := List.findIdx?_eq_none_iff.mp hfind b hb
    simp [hid] at hnone
  | some idx =>
    simp only [hfind] at h
    cases hstart : Measure.checkedI32 band.start with
    | error e => simp [hstart, Bind.bind, Except.bind] at h
    | ok start =>
      simp only [hstart, Bind.bind, Except.bind] at h
      cases hthick : Measure.checkedI32 band.thickness with
      | error e => simp [hthick] at h
      | ok thickness =>
        simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at h
        have hs' : start = band.start := checkedI32_ok hstart
        have ht' : thickness = band.thickness := checkedI32_ok hthick
        subst hs'
        subst ht'
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hb
        obtain ⟨x, hx, hpx⟩ := lft_findIdx_lookup s.boxes _ idx hfind
        have hxid : x.id = band.id := beq_iff_eq.mp hpx
        have hmemx : x ∈ s.boxes := List.mem_iff_getElem?.mpr ⟨idx, hx⟩
        have hidb : x.id = b.id := by rw [hxid, hid]
        have hbx : b = x := lft_nodup_map_inj (·.id) hnodup hb hmemx hidb.symm
        have hxb : x = b := hbx.symm
        rw [hxb] at hx
        have hkk : ((s.boxes.map (·.id))[k]? = some b.id) := by
          have e := List.getElem?_map (f := (·.id)) (l := s.boxes) (i := k)
          rw [hk] at e
          simpa using e
        have hxx : ((s.boxes.map (·.id))[idx]? = some b.id) := by
          have e := List.getElem?_map (f := (·.id)) (l := s.boxes) (i := idx)
          rw [hx] at e
          simpa using e
        have hki : k = idx := lft_getElem?_inj _ hnodup hkk hxx
        subst hki
        have hmap := List.getElem?_mapIdx (f := fun j b => if j = k then ({ b with rect := (placeRect axis band.start band.thickness) b.rect } : Box) else b) (l := s.boxes) (i := k)
        rw [hk] at hmap
        have hmap2 : (s.boxes.mapIdx fun j b => if j = k then ({ b with rect := (placeRect axis band.start band.thickness) b.rect } : Box) else b)[k]? = some { b with rect := (placeRect axis band.start band.thickness) b.rect } := by
          simpa using hmap
        have hmem : { b with rect := (placeRect axis band.start band.thickness) b.rect } ∈ s'.boxes := by
          rw [← h]
          exact List.mem_iff_getElem?.mpr ⟨k, hmap2⟩
        exact ⟨_, hmem, hid, rfl, rfl, rfl, rfl⟩

private theorem lft_foldKeptBox (bands : List Band) (axis : Axis) (s : Scene) : ∀ (s' : Scene), bands.foldlM (fun scene band => replaceFrame axis band scene) s = .ok s' → ∀ b ∈ s.boxes, (∀ band ∈ bands, band.id ≠ b.id) → ∃ b' ∈ s'.boxes, b'.id = b.id ∧ b'.rect = b.rect ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive := by
  induction bands generalizing s with
  | nil =>
    intro s' h b hb _
    simp only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨b, hb, rfl, rfl, rfl, rfl, rfl⟩
  | cons band rest ih =>
    intro s' h b hb hnf
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := lft_bind h
    have hband : b.id ≠ band.id := Ne.symm (hnf band List.mem_cons_self)
    obtain ⟨bm, hbmm, hidm, hrectm, hparm, hrolem, hexclm⟩ :=
      lft_replaceFrame_kept hmid b hb hband
    have hrest' : ∀ band' ∈ rest, band'.id ≠ bm.id := by
      intro band' hmem
      rw [hidm]
      exact hnf band' (List.mem_cons_of_mem band hmem)
    obtain ⟨b', hb', hid', hrect', hpar', hrole', hexcl'⟩ :=
      ih mid s' hrest bm hbmm hrest'
    exact ⟨b', hb', hid'.trans hidm, hrect'.trans hrectm, hpar'.trans hparm,
      hrole'.trans hrolem, hexcl'.trans hexclm⟩

private theorem lft_fold_places {axis : Axis} {bands : List Band} (s : Scene) : ∀ (s' : Scene), bands.foldlM (fun scene band => replaceFrame axis band scene) s = .ok s' → (bands.map fun b => b.id).Nodup → (s.boxes.map (·.id)).Nodup → ∀ {band : Band}, band ∈ bands → ∀ {b : Box}, b ∈ s.boxes → b.id = band.id → ∃ b' ∈ s'.boxes, b'.id = band.id ∧ b'.rect = placeRect axis band.start band.thickness b.rect ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive := by
  induction bands generalizing s with
  | nil =>
    intro s' h _ _ band hmem _ _ _
    simp at hmem
  | cons hd rest ih =>
    intro s' h hIds hnodup band hmem b hb hid
    rw [List.map_cons, List.nodup_cons] at hIds
    obtain ⟨hhead, htail⟩ := hIds
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := lft_bind h
    have hnodupMid : (mid.boxes.map (·.id)).Nodup := by
      have hm := replaceFrame_boxes_maps hmid
      rw [hm.1]
      exact hnodup
    by_cases hRest : band ∈ rest
    · have hne : b.id ≠ hd.id := by
        intro hcon
        apply hhead
        rw [← hcon, hid]
        exact List.mem_map.mpr ⟨band, hRest, rfl⟩
      obtain ⟨bm, hbmm, hidm, hrectm, hparm, hrolem, hexclm⟩ :=
        lft_replaceFrame_kept hmid b hb hne
      have hidm' : bm.id = band.id := hidm.trans hid
      obtain ⟨b', hb', hid', hrect', hpar', hrole', hexcl'⟩ :=
        ih mid s' hrest htail hnodupMid hRest hbmm hidm'
      exact ⟨b', hb', hid', by rw [hrect', hrectm], hpar'.trans hparm,
        hrole'.trans hrolem, hexcl'.trans hexclm⟩
    · have hbandHd : band = hd := by
        rcases List.mem_cons.mp hmem with h | h
        · exact h
        · exact absurd h hRest
      subst hbandHd
      obtain ⟨bm, hbmm, hidm, hrectm, hparm, hrolem, hexclm⟩ :=
        lft_replaceFrame_places hmid hnodup hb hid
      have hkeep : ∀ band' ∈ rest, band'.id ≠ bm.id := by
        intro band' hmem'
        rw [hidm]
        intro hcon
        apply hhead
        rw [← hcon]
        exact List.mem_map.mpr ⟨band', hmem', rfl⟩
      obtain ⟨b', hb', hid', hrect', hpar', hrole', hexcl'⟩ :=
        lft_foldKeptBox rest axis mid s' hrest bm hbmm hkeep
      exact ⟨b', hb', hid'.trans hidm, hrect'.trans hrectm, hpar'.trans hparm,
        hrole'.trans hrolem, hexcl'.trans hexclm⟩
private theorem lft_frame_find {axis : Axis} {bands : List Band} {s : Scene} (hIdsNodup : (bands.map fun b => b.id).Nodup) (hnodupB : (s.boxes.map (·.id)).Nodup) {band : Band} (hmem : band ∈ bands) {b0 : Box} (hb0 : b0 ∈ s.boxes) (hid0 : b0.id = band.id) {bp : Box} (hpid : bp.id = band.id) : (laneFrames axis bands s).find? (fun f => f.id == bp.id) = some ⟨band.id, axis.start b0.rect + band.shift - band.start, axis.length b0.rect⟩ := by
  have hfindB : s.boxes.find? (fun b => b.id == band.id) = some b0 := by
    rw [← hid0]
    exact lft_box_find_self hnodupB hb0
  have hFmem : (⟨band.id, axis.start b0.rect + band.shift - band.start, axis.length b0.rect⟩ : LaneFrame) ∈ laneFrames axis bands s := by
    unfold laneFrames
    apply List.mem_filterMap.mpr
    refine ⟨band, hmem, ?_⟩
    simp [hfindB]
  have hFpred : ((fun f : LaneFrame => f.id == bp.id) ⟨band.id, axis.start b0.rect + band.shift - band.start, axis.length b0.rect⟩) = true := by
    show ((band.id == bp.id) = true)
    rw [hpid.symm]
    exact beq_self_eq_true _
  obtain ⟨g, hg⟩ := lft_find?_ex (fun f : LaneFrame => f.id == bp.id) _ _ hFmem hFpred
  have hgmem : g ∈ laneFrames axis bands s := List.mem_of_find?_eq_some hg
  have hgId : g.id = bp.id := by
    have h := List.find?_some hg
    simpa using h
  obtain ⟨band', hband', hgb⟩ := List.mem_filterMap.mp hgmem
  cases hfb : s.boxes.find? (fun b => b.id == band'.id) with
  | none => simp [hfb] at hgb
  | some b' =>
    simp only [hfb, Option.map_some, Option.some.injEq] at hgb
    subst hgb
    have hbb : band'.id = band.id := hgId.trans hpid
    have hbeq : band' = band := lft_nodup_map_inj (·.id) hIdsNodup hband' hmem hbb
    rw [hbeq] at hfb
    have hb0' : b' = b0 := Option.some.inj (hfb.symm.trans hfindB)
    rw [hbeq, hb0'] at hg
    exact hg

private theorem lft_endRect_eq {axis : Axis} {bands : List Band} {s : Scene} (hIdsNodup : (bands.map fun b => b.id).Nodup) (hnodupB : (s.boxes.map (·.id)).Nodup) {band : Band} (hmem : band ∈ bands) {b0 : Box} (hb0 : b0 ∈ s.boxes) (hid0 : b0.id = band.id) {bp : Box} (hbpRect : bp.rect = placeRect axis band.start band.thickness b0.rect) (hpid : bp.id = band.id) : axis.start bp.rect = band.start ∧ axis.length bp.rect = band.thickness ∧ endRect axis (laneFrames axis bands s) bp = axis.withStart b0.rect (axis.start b0.rect + band.shift) := by
  have hFr := lft_frame_find (axis := axis) hIdsNodup hnodupB hmem hb0 hid0 hpid
  have hstart : axis.start bp.rect = band.start := by
    rw [hbpRect]
    cases axis <;> simp [placeRect, Axis.start, Axis.withStart, Axis.withLength]
  have hlen : axis.length bp.rect = band.thickness := by
    rw [hbpRect]
    cases axis <;> simp [placeRect, Axis.length, Axis.withStart, Axis.withLength]
  have hsum : band.start + (axis.start b0.rect + band.shift - band.start) = axis.start b0.rect + band.shift := by omega
  refine ⟨hstart, hlen, ?_⟩
  simp only [endRect, hFr, oldFrame]
  rw [hstart, hbpRect, hsum]
  cases axis <;> simp [placeRect, Axis.start, Axis.length, Axis.withStart, Axis.withLength]

theorem lppaFrameTransportResidual_holds {boxes : List ModelBox} {o : Options} {s : Scene} : lppaFrameTransportResidual boxes o s := by
  intro sp _hsp hModelClean hnodupB pinned happ band hmem hne b0 hb0 hid0 bp hbp hpid
  obtain ⟨hModelNodup, hModelNoEmpty⟩ := hModelClean
  have hIdsNodup : ((layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)).map fun b => b.id).Nodup := lft_layBands_ids_nodup hModelNodup hModelNoEmpty
  obtain ⟨shifted, shiftedLabels, shiftedRoutes, shiftedItems, hboxes, _, _, _, hfold⟩ := applyPin_shifted happ
  obtain ⟨bs, hbsmem, hbsid, _hbspar, w, _hw, hbsrect, hbsval⟩ := lft_shifted_of_mem hboxes hb0
  have hdelta : (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).boxDelta b0.id = band.shift := by
    rw [hid0]
    exact lft_boxDelta_lane rfl hModelNodup hModelNoEmpty hmem hne
  rw [hdelta] at hbsval
  rw [hbsval] at hbsrect
  have hbsid' : bs.id = band.id := hbsid.trans hid0
  have hnodupShift : (shifted.map (·.id)).Nodup := by
    have hm := pinShiftBoxes_maps _ _ _ _ hboxes
    have e2 : shifted.map (·.id) = s.boxes.map (·.id) := hm.2.1
    rw [e2]
    exact hnodupB
  have hbsmemRec : bs ∈ { s with boxes := shifted, labels := shiftedLabels, routes := shiftedRoutes, items := shiftedItems }.boxes := hbsmem
  obtain ⟨bpf, hbfmem, hbfid, hbfrect, _, _, _⟩ :=
    lft_fold_places _ pinned hfold hIdsNodup hnodupShift hmem hbsmemRec hbsid'
  have hnodupPinned : (pinned.boxes.map (·.id)).Nodup := by
    have hf := foldReplaceFrame_all _ _ _ pinned hfold
    have hm := pinShiftBoxes_maps _ _ _ _ hboxes
    have e1 : pinned.boxes.map (·.id) = shifted.map (·.id) := hf.2.1
    have e2 : shifted.map (·.id) = s.boxes.map (·.id) := hm.2.1
    rw [e1, e2]
    exact hnodupB
  have hbeq : bpf = bp := lft_nodup_map_inj (·.id) hnodupPinned hbfmem hbp (hbfid.trans hpid.symm)
  rw [hbeq] at hbfrect hbfid
  have hsw : placeRect (Axis.ofDirection o.direction) band.start band.thickness ((Axis.ofDirection o.direction).withStart b0.rect ((Axis.ofDirection o.direction).start b0.rect + band.shift)) = placeRect (Axis.ofDirection o.direction) band.start band.thickness b0.rect := by
    cases (Axis.ofDirection o.direction) <;> rfl
  have hbpRect : bp.rect = placeRect (Axis.ofDirection o.direction) band.start band.thickness b0.rect := by
    have e : bp.rect = placeRect (Axis.ofDirection o.direction) band.start band.thickness ((Axis.ofDirection o.direction).withStart b0.rect ((Axis.ofDirection o.direction).start b0.rect + band.shift)) := by
      rw [hbsrect] at hbfrect
      exact hbfrect
    rw [hsw] at e
    exact e
  exact lft_endRect_eq hIdsNodup hnodupB hmem hb0 hid0 hbpRect hpid
theorem lepePhaseApplyPinExec_closed {boxes : List ModelBox} {o : Options} {s : Scene} : lepePhaseApplyPinExec boxes o s := by
  exact lepePhaseApplyPinExec_holds lppaFrameTransportResidual_holds


end LaneBands





end Layered
end Elegant

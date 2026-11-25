import Elegant.Layered.LaneEndsPinEnds
import Elegant.Layered.LaneEndsPinPhases
import Elegant.Layered.LaneBandsRouteClausesProof
import Elegant.Layered.LaneBandsFrameClause
import Elegant.Layered.LaneBandsPhaseFacts
import Elegant.Layered.LaneBandsClearance
import Elegant.Layered.LaneBandsRouteClauses

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

private theorem lppa_lanesOf_mem {boxes : List ModelBox} {lane : String} (h : lane ∈ lanesOf boxes) : ∃ mb ∈ boxes, mb.role = .group ∧ mb.parent = "" ∧ mb.id = lane := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, hpred⟩ := List.mem_filter.mp hx
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hrole, hpar⟩ := hpred
  exact ⟨x, hxb, beq_iff_eq.mp hrole, beq_iff_eq.mp hpar, rfl⟩

private theorem lppa_nodup_map_inj {α β : Type} [BEq β] [LawfulBEq β] (g : α → β) {l : List α} (h : (l.map g).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hgx : g x = g y) : x = y := by
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
private theorem lppa_inLane_self {boxes : List ModelBox} (hn : (boxes.map (fun b => b.id)).Nodup) {lane : String} (hl : lane ∈ lanesOf boxes) : inLane boxes lane lane = true := by
  obtain ⟨mb, hmbMem, hmbRole, hmbPar, hmbId⟩ := lppa_lanesOf_mem hl
  have hfind : boxes.find? (fun b => b.id == lane) = some mb := by
    have hEq : (fun b : ModelBox => b.id == lane) = (fun b : ModelBox => b.id == mb.id) := by
      funext b
      rw [hmbId]
    rw [hEq]
    exact modelFind?_eq_self hn hmbMem
  unfold inLane laneOf laneOfAux
  rw [hfind]
  simp [hmbPar, hmbRole]


private theorem lppa_layLanes_ids (boxes : List ModelBox) (s : Scene) (axis : Axis) (sp : Spacing) (lanes : List String) (start : Int) : (layLanes boxes s axis sp lanes start).map (fun b => b.id) = lanes := by
  induction lanes generalizing start with
  | nil => rfl
  | cons lane rest ih =>
    have hhead : (laneBand boxes s axis sp lane start).id = lane := rfl
    simp only [layLanes, List.map_cons, hhead, ih]

private theorem lppa_lanes_ne_empty {boxes : List ModelBox} (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") {lane : String} (h : lane ∈ lanesOf boxes) : lane ≠ "" := by
  obtain ⟨x, hxb, _, _, rfl⟩ := lppa_lanesOf_mem h
  exact hModelNoEmpty x hxb

private theorem lppa_loose_id {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} {loose : List String} {start : Int} : (looseBand boxes s axis sp loose start).id = "" := by
  unfold looseBand
  split <;> rfl

private theorem lppa_loose_members {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} {loose : List String} {start : Int} : (looseBand boxes s axis sp loose start).members = loose := by
  unfold looseBand
  split <;> rfl

private theorem lppa_layBands_ids_nodup {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} (hModelNodup : (boxes.map fun b => b.id).Nodup) (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") : ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup := by
  have hLaneIds : ((layLanes boxes s axis sp (lanesOf boxes) (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id) = lanesOf boxes := lppa_layLanes_ids _ _ _ _ _ _
  have hLaneNodup : ((layLanes boxes s axis sp (lanesOf boxes) (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id).Nodup := by
    rw [hLaneIds]
    exact lanesOf_nodup hModelNodup
  have hfresh : "" ∉ lanesOf boxes := fun hmem => lppa_lanes_ne_empty hModelNoEmpty hmem rfl
  unfold layBands
  by_cases hl : (looseNodes boxes).isEmpty = true
  · simp only [hl, ↓reduceIte]
    exact hLaneNodup
  · simp only [hl, ↓reduceIte, Bool.false_eq_true, List.map_append, hLaneIds]
    have hsing : ∀ S : Int, (([looseBand boxes s axis sp (looseNodes boxes) S].map fun b => b.id) = [""]) := by
      intro S
      simp only [List.map_cons, List.map_nil, lppa_loose_id]
    simp only [hsing]
    rw [List.nodup_append]
    refine ⟨?_, (by simp : ([""] : List String).Nodup), ?_⟩
    · exact lanesOf_nodup hModelNodup
    · intro a ha b hb hEq
      rw [List.mem_singleton] at hb
      subst hb
      exact lppa_lanes_ne_empty hModelNoEmpty ha hEq

private theorem lppa_cover_unique_lane {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} (hModelNodup : (boxes.map fun b => b.id).Nodup) (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") (hIdsNodup : ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup) {bands : List Band} (hbands : bands = layBands boxes s axis sp (lanesOf boxes)) {id : String} (hidLane : id ∈ lanesOf boxes) {b1 : Band} (hm1 : b1 ∈ bands) (hc1 : bandCovers b1 id) {b2 : Band} (hm2 : b2 ∈ bands) (hc2 : bandCovers b2 id) : b1 = b2 := by
  have hIdsNodupB : (bands.map fun b => b.id).Nodup := by rw [hbands]; exact hIdsNodup
  have hmemEq : ∀ b ∈ bands, ∀ c ∈ bands, b.id = c.id → b = c := fun b hb c hc heq => lppa_nodup_map_inj (·.id) hIdsNodupB hb hc heq
  have hSelf : inLane boxes id id = true := lppa_inLane_self hModelNodup hidLane
  have hidNe : id ≠ "" := lppa_lanes_ne_empty hModelNoEmpty hidLane
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
      · rw [lppa_loose_id] at hEq2
        exact hidNe hEq2.symm
      · have hMemLoose : id ∈ looseNodes boxes := by
          rw [lppa_loose_members] at hMem2
          exact hMem2
        have hContra := loose_not_inLane hModelNodup hMemLoose (lane := id)
        rw [hSelf] at hContra
        exact Bool.noConfusion hContra
  · exfalso
    rw [hLoose1] at hc1'
    rcases hc1' with hEq1 | hMem1
    · rw [lppa_loose_id] at hEq1
      exact hidNe hEq1.symm
    · have hMemLoose : id ∈ looseNodes boxes := by
        rw [lppa_loose_members] at hMem1
        exact hMem1
      have hContra := loose_not_inLane hModelNodup hMemLoose (lane := id)
      rw [hSelf] at hContra
      exact Bool.noConfusion hContra

private theorem lppa_bandShift_lane {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} {bands : List Band} (hbands : bands = layBands boxes s axis sp (lanesOf boxes)) (hModelNodup : (boxes.map fun b => b.id).Nodup) (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") {band : Band} (hband : band ∈ bands) (hne : band.id ≠ "") : bandShift bands band.id = band.shift := by
  have hIdsNodup : ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup := lppa_layBands_ids_nodup hModelNodup hModelNoEmpty
  have hLaneMem : band.id ∈ lanesOf boxes := by
    have hC := layBands_mem_cases (hmem := hbands ▸ hband)
    rcases hC with hL | hO
    · exact layLanes_id_mem hL
    · exfalso
      have hid : band.id = "" := by
        rw [hO, lppa_loose_id]
      exact hne hid
  have hcov : bandCovers band band.id := Or.inl rfl
  have hUniq : ∀ b1 ∈ bands, ∀ b2 ∈ bands, bandCovers b1 band.id → bandCovers b2 band.id → b1 = b2 := fun b1 hb1 b2 hb2 hc1 hc2 => lppa_cover_unique_lane hModelNodup hModelNoEmpty hIdsNodup hbands hLaneMem hb1 hc1 hb2 hc2
  exact bandShift_eq hband hcov hUniq

private theorem lppa_bind {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β} {y : β} (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩


private theorem lppa_mapM_point_head {m : Move} {axis : Axis} : ∀ (ps qs : List Point), ps.mapM (m.point axis) = .ok qs → ∀ p, ps.head? = some p → ∃ q, qs.head? = some q ∧ m.point axis p = .ok q := by
  intro ps
  induction ps with
  | nil => intro qs _ p hp; simp at hp
  | cons x xs ih =>
    intro qs h p hp
    rw [List.mapM_cons] at h
    obtain ⟨x', hx', h⟩ := lppa_bind h
    obtain ⟨rest', hrest, hrfl⟩ := lppa_bind h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
    subst hrfl
    have hpx : x = p := by simpa using hp
    subst hpx
    exact ⟨x', rfl, hx'⟩

private theorem lppa_mapM_point_getLast {m : Move} {axis : Axis} : ∀ (ps qs : List Point), ps.mapM (m.point axis) = .ok qs → ∀ p, ps.getLast? = some p → ∃ q, qs.getLast? = some q ∧ m.point axis p = .ok q := by
  intro ps
  induction ps with
  | nil => intro qs _ p hp; simp at hp
  | cons x rest ih =>
    intro qs h p hp
    rw [List.mapM_cons] at h
    obtain ⟨x', hx', h⟩ := lppa_bind h
    obtain ⟨rest', hrest, hrfl⟩ := lppa_bind h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
    subst hrfl
    cases rest with
    | nil =>
      simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at hrest
      subst hrest
      have hpx : p = x := by
        have hgl : (x :: []).getLast? = some x := rfl
        rw [hgl] at hp
        exact (Option.some.inj hp).symm
      subst hpx
      exact ⟨x', rfl, hx'⟩
    | cons y ys =>
      obtain ⟨q, hq, hfun⟩ := ih rest' hrest p hp
      refine ⟨q, ?_, hfun⟩
      rw [List.getLast?_cons, hq]
      rfl

private theorem lppa_find?_ex {α : Type} (p : α → Bool) (l : List α) (a : α) (hm : a ∈ l) (hp : p a = true) : ∃ b, l.find? p = some b := by
  have hex : ∃ x, x ∈ l ∧ p x = true := ⟨a, hm, hp⟩
  have h := (List.find?_isSome).mpr hex
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
  exact ⟨b, hb⟩

def lepePhaseApplyPinExec (boxes : List ModelBox) (o : Options) (s : Scene) : Prop :=
  ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
    ∀ (_hC5 : Validator.C5 s.layoutDump)
      (_hrouteNodup : (s.routes.map (·.id)).Nodup)
      (_hnodupB : (s.boxes.map (·.id)).Nodup)
      (_hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
      (_hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "")
      (_hEnds : ∀ rt ∈ s.routes,
        bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) rt.fromId =
        bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) rt.toId ∨
          ((Axis.ofDirection o.direction).point (rt.points.head?.getD ⟨0, 0⟩) ≠
            (Axis.ofDirection o.direction).point (rt.points.getLast?.getD ⟨0, 0⟩) ∧ 1 < rt.points.length))
      {pinned : Scene}
      (_happ : applyPin (buildPin (Axis.ofDirection o.direction)
        (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
        (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s = .ok pinned),
    EndsOnOld (Axis.ofDirection o.direction)
      (laneFrames (Axis.ofDirection o.direction)
        (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
      pinned.layoutDump

def lppaBandShiftResidual (boxes : List ModelBox) (o : Options) (s : Scene) : Prop :=
  ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
    ∀ (_hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "")
      {band : Band} (_hmem : band ∈ layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)),
      band.id ≠ "" →
      bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) band.id = band.shift
private theorem lppa_frame_mem {axis : Axis} {bands : List Band} {s : Scene} {f : LaneFrame} (hf : f ∈ laneFrames axis bands s) : ∃ band ∈ bands, ∃ b ∈ s.boxes, band.id = f.id ∧ f.near = axis.start b.rect + band.shift - band.start ∧ f.length = axis.length b.rect ∧ s.boxes.find? (fun b => b.id == band.id) = some b := by
  unfold laneFrames at hf
  obtain ⟨band, hband, hfb⟩ := List.mem_filterMap.mp hf
  cases hfind : s.boxes.find? (fun b => b.id == band.id) with
  | none => simp [hfind] at hfb
  | some b =>
    simp [hfind] at hfb
    subst hfb
    exact ⟨band, hband, b, List.mem_of_find?_eq_some hfind, rfl, rfl, rfl, hfind⟩

private theorem lppa_shifted_points {axis : Axis} {d : RouteDelta} {p q : Point} {ps qs : List Point} (hmap : ps.mapM ((routeMove d).point axis) = .ok qs) (hp : ps.head? = some p) (hq : ps.getLast? = some q) (hfirst : d.first = axis.point p) (hlast : d.last = axis.point q) (hEndsD : d.fromDelta = d.toDelta ∨ (axis.point p ≠ axis.point q ∧ 1 < ps.length)) : ∃ qP qQ : Point, qs.head? = some qP ∧ qs.getLast? = some qQ ∧ qP = axis.withPoint p (axis.point p + d.fromDelta) ∧ qQ = axis.withPoint q (axis.point q + d.toDelta) := by
  obtain ⟨qP, hqPhead, hqPfun⟩ := lppa_mapM_point_head _ _ hmap p hp
  obtain ⟨wP, hwP, hqPeq, _⟩ := movePoint_ok hqPfun
  have hoffP : (routeMove d).offset (axis.point p) = d.fromDelta := by
    have hpl : axis.point p = d.first := hfirst.symm
    unfold routeMove
    by_cases heqd : d.fromDelta = d.toDelta
    · simp [heqd, Move.offset]
    · simp [heqd, hpl, Move.offset]
  have hwPeq : wP = axis.point p + d.fromDelta := by
    have happEq : (routeMove d).apply (axis.point p) = Measure.checkedI32 (axis.point p + d.fromDelta) := by
      simp [Move.apply, hoffP]
    rw [happEq] at hwP
    exact checked_value hwP
  have hqPEq : qP = axis.withPoint p (axis.point p + d.fromDelta) := by
    rw [hqPeq, hwPeq]
  obtain ⟨qQ, hqQlast, hqQfun⟩ := lppa_mapM_point_getLast _ _ hmap q hq
  obtain ⟨wQ, hwQ, hqQeq, _⟩ := movePoint_ok hqQfun
  have hoffQ : (routeMove d).offset (axis.point q) = d.toDelta := by
    have hql : axis.point q = d.last := hlast.symm
    rcases hEndsD with heq | ⟨hne, _⟩
    · have heqd : d.fromDelta = d.toDelta := heq
      unfold routeMove
      simp [heqd, Move.offset]
    · have hne' : d.last ≠ d.first := by
        rw [hlast, hfirst]
        exact Ne.symm hne
      unfold routeMove
      by_cases heqd : d.fromDelta = d.toDelta
      · simp [heqd, Move.offset]
      · simp [heqd, hql, hne', Move.offset]
  have hwQeq : wQ = axis.point q + d.toDelta := by
    have happEq : (routeMove d).apply (axis.point q) = Measure.checkedI32 (axis.point q + d.toDelta) := by
      simp [Move.apply, hoffQ]
    rw [happEq] at hwQ
    exact checked_value hwQ
  have hqQEq : qQ = axis.withPoint q (axis.point q + d.toDelta) := by
    rw [hqQeq, hwQeq]
  exact ⟨qP, qQ, hqPhead, hqQlast, hqPEq, hqQEq⟩

def lppaFrameTransportResidual (boxes : List ModelBox) (o : Options) (s : Scene) : Prop :=
  ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
    ∀ (_hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "")
      (_hnodupB : (s.boxes.map (·.id)).Nodup)
      {pinned : Scene}
      (_happ : applyPin (buildPin (Axis.ofDirection o.direction)
        (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
        (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s = .ok pinned)
      {band : Band} (_hmem : band ∈ layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes))
      (_hne : band.id ≠ "")
      {b0 : Box} (_hb0 : b0 ∈ s.boxes) (_hid0 : b0.id = band.id)
      {bp : Box} (_hbp : bp ∈ pinned.boxes) (_hpid : bp.id = band.id),
    (Axis.ofDirection o.direction).start bp.rect = band.start ∧
      (Axis.ofDirection o.direction).length bp.rect = band.thickness ∧
      endRect (Axis.ofDirection o.direction)
        (laneFrames (Axis.ofDirection o.direction)
          (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) bp =
        (Axis.ofDirection o.direction).withStart b0.rect
          ((Axis.ofDirection o.direction).start b0.rect + band.shift)

private theorem lppaBandShiftResidual_holds {boxes : List ModelBox} {o : Options} {s : Scene} : lppaBandShiftResidual boxes o s := by
  intro sp _ hModelClean band hmem hne
  exact lppa_bandShift_lane rfl hModelClean.1 hModelClean.2 hmem hne
private theorem lppa_endRect_for_endpoint {boxes : List ModelBox} {o : Options} {s pinned : Scene} {sp : Spacing} (hsp : spacingOf o.profile = .ok sp) (hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "") (hnodupB : (s.boxes.map (·.id)).Nodup) (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "") (hFrame : lppaFrameTransportResidual boxes o s) (happ : applyPin (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s = .ok pinned) {eid : String} {b0 : Box} (hb0 : b0 ∈ s.boxes) (hid0 : b0.id = eid) {bp : Box} (hbp : bp ∈ pinned.boxes) (hpid : bp.id = eid) {delta : Int} (hdelta : delta = bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) eid) : endRect (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) bp = (Axis.ofDirection o.direction).withStart b0.rect ((Axis.ofDirection o.direction).start b0.rect + delta) := by
  by_cases hFr : ∃ band ∈ layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes), band.id = eid ∧ band.id ≠ ""
  · obtain ⟨band, hmem, hid, hne⟩ := hFr
    have hshift := lppaBandShiftResidual_holds (boxes := boxes) (o := o) (s := s) sp hsp hModelClean hmem hne
    have hdeltaEq : delta = band.shift := by rw [hdelta, ← hid]; exact hshift
    have hid0' : b0.id = band.id := hid0.trans hid.symm
    have hpid' : bp.id = band.id := hpid.trans hid.symm
    have hfr := hFrame sp hsp hModelClean hnodupB happ hmem hne hb0 hid0' hbp hpid'
    obtain ⟨_, _, hend⟩ := hfr
    rw [hdeltaEq]
    exact hend
  · have hneEid : eid ≠ "" := by rw [← hid0]; exact hNoEmpty b0 hb0
    have hnf : ∀ band ∈ layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes), band.id ≠ eid := by
      intro band hmem heq
      apply hFr
      exact ⟨band, hmem, heq, by rw [heq]; exact hneEid⟩
    have hnf' : ∀ band ∈ layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes), band.id ≠ bp.id := by
      intro band hmem heq
      exact hnf band hmem (heq.trans hpid)
    obtain ⟨b, hbmem, w, hidb, hw, hrectb, hval⟩ := applyPin_c5_box happ bp hbp hnf'
    have hbEq : b = b0 := lppa_nodup_map_inj (·.id) hnodupB hbmem hb0 (hidb.symm.trans (hpid.trans hid0.symm))
    have hax : (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).axis = Axis.ofDirection o.direction := rfl
    have hboxDelta : (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).boxDelta b.id = bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) b.id := buildPin_boxDelta b.id
    have hbid : b.id = eid := hidb.symm.trans hpid
    have hwEq : w = (Axis.ofDirection o.direction).start b0.rect + delta := by
      rw [hax] at hval
      rw [hbEq] at hval hboxDelta hbid
      rw [hval, hboxDelta, hbid, ← hdelta]
    have hbpEq : bp.rect = (Axis.ofDirection o.direction).withStart b0.rect ((Axis.ofDirection o.direction).start b0.rect + delta) := by
      rw [hax] at hrectb
      rw [hbEq] at hrectb
      rw [hrectb, hwEq]
    have hfindNone : (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).find? (fun b_ => b_.id == bp.id) = none := by
      cases hsome : (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).find? (fun b_ => b_.id == bp.id) with
      | none => rfl
      | some f =>
        exfalso
        obtain ⟨band, hband, _, _, hbidf, _, _, _⟩ := lppa_frame_mem (List.mem_of_find?_eq_some hsome)
        have hpred : ((fun b_ : LaneFrame => b_.id == bp.id) f) = true := by
          have h := List.find?_some hsome
          simpa using h
        have hfid : f.id = bp.id := beq_iff_eq.mp hpred
        have heq : band.id = eid := by rw [hbidf, hfid, hpid]
        exact hnf band hband heq
    have hend : endRect (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) bp = bp.rect := by
      unfold endRect
      rw [hfindNone]
    rw [hend, hbpEq]



theorem lepePhaseApplyPinExec_holds {boxes : List ModelBox} {o : Options} {s : Scene} (hFrame : lppaFrameTransportResidual boxes o s) : lepePhaseApplyPinExec boxes o s := by
  intro sp hsp hC5 hrouteNodup hnodupB hNoEmpty hModelClean hEnds pinned happ
  intro rP hrP
  have hrPm : rP ∈ pinned.routes := hrP
  obtain ⟨i, hiP, rfl⟩ := List.mem_iff_getElem.mp hrPm
  have hlenMap := applyPin_routes_length_map (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s pinned happ
  have hlen : pinned.routes.length = s.routes.length := by
    have h := congrArg List.length hlenMap
    simpa using h
  have hiS : i < s.routes.length := by omega
  have hP : pinned.routes[i]? = some pinned.routes[i] := List.getElem?_eq_some_iff.mpr ⟨hiP, rfl⟩
  have hB : s.routes[i]? = some s.routes[i] := List.getElem?_eq_some_iff.mpr ⟨hiS, rfl⟩
  have hrBmem : s.routes[i] ∈ s.routes := List.mem_iff_getElem.mpr ⟨i, hiS, rfl⟩
  obtain ⟨hid, hfrom, hto, _, hmapOr⟩ := applyPin_c4_map happ hiP hiS hP hB
  have hrBD : s.routes[i] ∈ s.layoutDump.routes := hrBmem
  obtain ⟨p, q, fb0, tb0, hp, hq, hfb0, htb0, hb1, hb2⟩ := hC5 s.routes[i] hrBD
  have hax : (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).axis = Axis.ofDirection o.direction := rfl
  have hfb0M : fb0 ∈ s.boxes := List.mem_of_find?_eq_some hfb0
  have htb0M : tb0 ∈ s.boxes := List.mem_of_find?_eq_some htb0
  have hpredF : (fb0.id == s.routes[i].fromId) = true := by have h := List.find?_some hfb0; simpa using h
  have hpredT : (tb0.id == s.routes[i].toId) = true := by have h := List.find?_some htb0; simpa using h
  have hfb0id : fb0.id = s.routes[i].fromId := beq_iff_eq.mp hpredF
  have htb0id : tb0.id = s.routes[i].toId := beq_iff_eq.mp hpredT
  have hgd0 : s.routes[i].points.head?.getD ⟨0, 0⟩ = p := by simp only [hp, Option.getD_some]
  have hgd1 : s.routes[i].points.getLast?.getD ⟨0, 0⟩ = q := by simp only [hq, Option.getD_some]
  have hEndsD0 := hEnds s.routes[i] hrBmem
  rw [hgd0, hgd1] at hEndsD0
  rcases hmapOr with ⟨hnone, _⟩ | ⟨d, hd, hmap⟩
  · have hmem : (⟨s.routes[i].id, bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s.routes[i].fromId, bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s.routes[i].toId, (Axis.ofDirection o.direction).point p, (Axis.ofDirection o.direction).point q⟩ : RouteDelta) ∈ s.routes.filterMap fun r => match r.points.head?, r.points.getLast? with | some f, some l => some ⟨r.id, bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) r.fromId, bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) r.toId, (Axis.ofDirection o.direction).point f, (Axis.ofDirection o.direction).point l⟩ | _, _ => none := by
      apply List.mem_filterMap.mpr
      exact ⟨s.routes[i], hrBmem, by simp only [hp, hq]⟩
    obtain ⟨dd, hdd⟩ := lppa_find?_ex (fun d : RouteDelta => d.id == s.routes[i].id) _ _ hmem (beq_self_eq_true _)
    have hdd' : (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).route s.routes[i].id = some dd := hdd
    rw [hid] at hnone
    rw [hdd'] at hnone
    cases hnone
  · have hd' : (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).route s.routes[i].id = some d := hid ▸ hd
    obtain ⟨hfd, htd, hfirst, hlast⟩ := c4c5_route_deltas hrBmem hrouteNodup hd'
    rw [hgd0] at hfirst
    rw [hgd1] at hlast
    rw [hax] at hmap
    have hEndsD : d.fromDelta = d.toDelta ∨ ((Axis.ofDirection o.direction).point p ≠ (Axis.ofDirection o.direction).point q ∧ 1 < s.routes[i].points.length) := by
      rcases hEndsD0 with heq | ⟨hne, hlen2⟩
      · left
        rw [hfd, htd]
        exact heq
      · right
        exact ⟨hne, hlen2⟩
    obtain ⟨qP, qQ, hqPhead, hqQlast, hqPEq, hqQEq⟩ := lppa_shifted_points hmap hp hq hfirst hlast hEndsD
    have hpbFex : ∃ bx ∈ s.boxes, bx.id = pinned.routes[i].fromId := ⟨fb0, hfb0M, by rw [hfb0id, ← hfrom]⟩
    have hpbTex : ∃ bx ∈ s.boxes, bx.id = pinned.routes[i].toId := ⟨tb0, htb0M, by rw [htb0id, ← hto]⟩
    have hsomeF := c4c5_pinned_box_some happ pinned.routes[i].fromId hpbFex
    have hsomeT := c4c5_pinned_box_some happ pinned.routes[i].toId hpbTex
    obtain ⟨bpF, hbpF⟩ := Option.isSome_iff_exists.mp hsomeF
    obtain ⟨bpT, hbpT⟩ := Option.isSome_iff_exists.mp hsomeT
    have hbpFM : bpF ∈ pinned.boxes := List.mem_of_find?_eq_some hbpF
    have hbpTM : bpT ∈ pinned.boxes := List.mem_of_find?_eq_some hbpT
    have hpredBF : (bpF.id == pinned.routes[i].fromId) = true := by have h := List.find?_some hbpF; simpa using h
    have hpredBT : (bpT.id == pinned.routes[i].toId) = true := by have h := List.find?_some hbpT; simpa using h
    have hbpFid : bpF.id = pinned.routes[i].fromId := beq_iff_eq.mp hpredBF
    have hbpTid : bpT.id = pinned.routes[i].toId := beq_iff_eq.mp hpredBT
    have hfromId : fb0.id = pinned.routes[i].fromId := by rw [hfb0id, hfrom]
    have htoId : tb0.id = pinned.routes[i].toId := by rw [htb0id, hto]
    have hdeltaF : d.fromDelta = bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) fb0.id := by rw [hfromId, hfrom, hfd]
    have hdeltaT : d.toDelta = bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) tb0.id := by rw [htoId, hto, htd]
    have hendF := lppa_endRect_for_endpoint hsp hModelClean hnodupB hNoEmpty hFrame happ hfb0M hfromId hbpFM hbpFid (hfromId ▸ hdeltaF)
    have hendT := lppa_endRect_for_endpoint hsp hModelClean hnodupB hNoEmpty hFrame happ htb0M htoId hbpTM hbpTid (htoId ▸ hdeltaT)
    have hbP : Validator.onBoundary qP (endRect (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) bpF) := by
      rw [hqPEq, hendF]
      exact (onBoundary_crossShift).mpr hb1
    have hbQ : Validator.onBoundary qQ (endRect (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) bpT) := by
      rw [hqQEq, hendT]
      exact (onBoundary_crossShift).mpr hb2
    have hfindF : pinned.layoutDump.box? pinned.routes[i].fromId = some bpF := by unfold LayoutDump.box?; exact hbpF
    have hfindT : pinned.layoutDump.box? pinned.routes[i].toId = some bpT := by unfold LayoutDump.box?; exact hbpT
    exact ⟨qP, qQ, bpF, bpT, hqPhead, hqQlast, hfindF, hfindT, hbP, hbQ⟩

end LaneBands
end Layered
end Elegant

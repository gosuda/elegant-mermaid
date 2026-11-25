import Elegant.Layered.LaneEndsPinRerouteFresh
import Elegant.Layered.LaneEndsPinExec
import Elegant.Layered.LaneEndsPinFrameTransport

set_option autoImplicit false

/-! Reroute ends boundary for executed paired runs.

Unpaired `lepeRerouteEndsBdryExec` (all `r` with all `old`) is false:
two-route witness in `proofs/wip/Probe/LaneRerouteEndsBdryTProbe.lean`
(`t_crossBdryBool` is `false`, `t_pairedBdryBool` is `true` on the same
scene: routes `e1 : a -> b`, `e2 : b -> a`; cross pair `r = e1`,
`old = e2` rebuilds `ends.source` from `e2` head shifted by `e1`
delta, off `e1` end rect). The reroute consumer only needs zip-paired
routes (`c4c5_reroute_mem` pairs `(r, old)` with shared ids), so this
module proves the paired true form below and closes both finals from
it. Base `C5` puts old ends on old rects; apply transport shifts end
rects by the band delta; `onBoundary_crossShift` moves boundary along.
-/

namespace Elegant
namespace Layered
namespace LaneBands

/-- Paired true form of the reroute ends boundary: `r` and `old` share
endpoint ids (what `c4c5_reroute_mem` plus zip sameness supply). -/
def lepeRerouteEndsBdryPairedExec (boxes : List ModelBox) (o : Options) (s : Scene) : Prop :=
  ∀ (sp : Spacing) (_hsp : spacingOf o.profile = .ok sp)
    (_hnodupB : (s.boxes.map (·.id)).Nodup)
    (_hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "")
    (_hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    {pinned : Scene}
    (_happ : applyPin (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s = .ok pinned)
    (_hC5 : Validator.C5 s.layoutDump)
    {r old : Route} (_hold : old ∈ s.routes)
    (_hpair : r.fromId = old.fromId ∧ r.toId = old.toId)
    {fb tb : Box}
    (_hfb : pinned.boxes.find? (fun b => b.id == r.fromId) = some fb)
    (_htb : pinned.boxes.find? (fun b => b.id == r.toId) = some tb)
    {ends : RouteEnds}
    (_hends : routeEnds (Axis.ofDirection o.direction) sp (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) fb tb old.points = .ok ends),
  ∃ fbp tbp : Box,
    pinned.layoutDump.box? r.fromId = some fbp ∧ pinned.layoutDump.box? r.toId = some tbp ∧
    Validator.onBoundary ends.source (endRect (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) fbp) ∧
    Validator.onBoundary ends.target (endRect (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) tbp)

private theorem lrb_nodup_map_inj {α β : Type} [BEq β] [LawfulBEq β] (g : α → β)
    {l : List α} (h : (l.map g).Nodup) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (hgx : g x = g y) : x = y := by
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

private theorem lrb_lanesOf_mem {boxes : List ModelBox} {lane : String}
    (h : lane ∈ lanesOf boxes) :
    ∃ mb ∈ boxes, mb.role = .group ∧ mb.parent = "" ∧ mb.id = lane := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, hpred⟩ := List.mem_filter.mp hx
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hrole, hpar⟩ := hpred
  exact ⟨x, hxb, beq_iff_eq.mp hrole, beq_iff_eq.mp hpar, rfl⟩

private theorem lrb_inLane_self {boxes : List ModelBox}
    (hn : (boxes.map (fun b => b.id)).Nodup) {lane : String}
    (hl : lane ∈ lanesOf boxes) : inLane boxes lane lane = true := by
  obtain ⟨mb, hmbMem, hmbRole, hmbPar, hmbId⟩ := lrb_lanesOf_mem hl
  have hfind : boxes.find? (fun b => b.id == lane) = some mb := by
    have hEq : (fun b : ModelBox => b.id == lane) = (fun b : ModelBox => b.id == mb.id) := by
      funext b
      rw [hmbId]
    rw [hEq]
    exact modelFind?_eq_self hn hmbMem
  unfold inLane laneOf laneOfAux
  rw [hfind]
  simp [hmbPar, hmbRole]

private theorem lrb_lanes_ne_empty {boxes : List ModelBox}
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") {lane : String}
    (h : lane ∈ lanesOf boxes) : lane ≠ "" := by
  obtain ⟨x, hxb, _, _, rfl⟩ := lrb_lanesOf_mem h
  exact hModelNoEmpty x hxb

private theorem lrb_layLanes_ids (boxes : List ModelBox) (s : Scene) (axis : Axis)
    (sp : Spacing) (lanes : List String) (start : Int) :
    (layLanes boxes s axis sp lanes start).map (fun b => b.id) = lanes := by
  induction lanes generalizing start with
  | nil => rfl
  | cons lane rest ih =>
    have hhead : (laneBand boxes s axis sp lane start).id = lane := rfl
    simp only [layLanes, List.map_cons, hhead, ih]

private theorem lrb_layBands_ids_nodup {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} (hModelNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") :
    ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup := by
  have hLaneIds : ((layLanes boxes s axis sp (lanesOf boxes) (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id) = lanesOf boxes :=
    lrb_layLanes_ids _ _ _ _ _ _
  have hLaneNodup : ((layLanes boxes s axis sp (lanesOf boxes) (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id).Nodup := by
    rw [hLaneIds]
    exact lanesOf_nodup hModelNodup
  have hfresh : "" ∉ lanesOf boxes := fun hmem => lrb_lanes_ne_empty hModelNoEmpty hmem rfl
  unfold layBands
  by_cases hl : (looseNodes boxes).isEmpty = true
  · simp only [hl, ↓reduceIte]
    exact hLaneNodup
  · simp only [hl, ↓reduceIte, Bool.false_eq_true, List.map_append, hLaneIds]
    have hsing : ∀ S : Int, (([looseBand boxes s axis sp (looseNodes boxes) S].map fun b => b.id) = [""]) := by
      intro S
      simp only [List.map_cons, List.map_nil]
      have hid : (looseBand boxes s axis sp (looseNodes boxes) S).id = "" := by
        unfold looseBand
        split <;> rfl
      simp only [hid]
    simp only [hsing]
    rw [List.nodup_append]
    refine ⟨?_, (by simp : ([""] : List String).Nodup), ?_⟩
    · exact lanesOf_nodup hModelNodup
    · intro a ha b hb hEq
      rw [List.mem_singleton] at hb
      subst hb
      exact lrb_lanes_ne_empty hModelNoEmpty ha hEq
private theorem lrb_cover_unique_lane {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} (hModelNodup : (boxes.map fun b => b.id).Nodup) (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") (hIdsNodup : ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup) {bands : List Band} (hbands : bands = layBands boxes s axis sp (lanesOf boxes)) {id : String} (hidLane : id ∈ lanesOf boxes) {b1 : Band} (hm1 : b1 ∈ bands) (hc1 : bandCovers b1 id) {b2 : Band} (hm2 : b2 ∈ bands) (hc2 : bandCovers b2 id) : b1 = b2 := by
  have hIdsNodupB : (bands.map fun b => b.id).Nodup := by rw [hbands]; exact hIdsNodup
  have hmemEq : ∀ b ∈ bands, ∀ c ∈ bands, b.id = c.id → b = c := fun b hb c hc heq => lrb_nodup_map_inj (·.id) hIdsNodupB hb hc heq
  have hSelf : inLane boxes id id = true := lrb_inLane_self hModelNodup hidLane
  have hidNe : id ≠ "" := lrb_lanes_ne_empty hModelNoEmpty hidLane
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
      · have hEqLoose : (looseBand boxes s axis sp (looseNodes boxes) (firstLaneStart s (lanesOf boxes) axis + ((layLanes boxes s axis sp (lanesOf boxes) (firstLaneStart s (lanesOf boxes) axis)).map (·.thickness)).sum)).id = "" := by
          unfold looseBand
          split <;> rfl
        rw [hEqLoose] at hEq2
        exact hidNe hEq2.symm
      · have hMemLoose : id ∈ looseNodes boxes := by
          have hmemEq2 : (looseBand boxes s axis sp (looseNodes boxes) (firstLaneStart s (lanesOf boxes) axis + ((layLanes boxes s axis sp (lanesOf boxes) (firstLaneStart s (lanesOf boxes) axis)).map (·.thickness)).sum)).members = looseNodes boxes := by
            unfold looseBand
            split <;> rfl
          rw [hmemEq2] at hMem2
          exact hMem2
        have hContra := loose_not_inLane hModelNodup hMemLoose (lane := id)
        rw [hSelf] at hContra
        exact Bool.noConfusion hContra
  · exfalso
    rw [hLoose1] at hc1'
    rcases hc1' with hEq1 | hMem1
    · have hEqLoose : (looseBand boxes s axis sp (looseNodes boxes) (firstLaneStart s (lanesOf boxes) axis + ((layLanes boxes s axis sp (lanesOf boxes) (firstLaneStart s (lanesOf boxes) axis)).map (·.thickness)).sum)).id = "" := by
        unfold looseBand
        split <;> rfl
      rw [hEqLoose] at hEq1
      exact hidNe hEq1.symm
    · have hMemLoose : id ∈ looseNodes boxes := by
        have hmemEq1 : (looseBand boxes s axis sp (looseNodes boxes) (firstLaneStart s (lanesOf boxes) axis + ((layLanes boxes s axis sp (lanesOf boxes) (firstLaneStart s (lanesOf boxes) axis)).map (·.thickness)).sum)).members = looseNodes boxes := by
          unfold looseBand
          split <;> rfl
        rw [hmemEq1] at hMem1
        exact hMem1
      have hContra := loose_not_inLane hModelNodup hMemLoose (lane := id)
      rw [hSelf] at hContra
      exact Bool.noConfusion hContra

private theorem lrb_bandShift_lane {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing} {bands : List Band} (hbands : bands = layBands boxes s axis sp (lanesOf boxes)) (hModelNodup : (boxes.map fun b => b.id).Nodup) (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") {band : Band} (hband : band ∈ bands) (hne : band.id ≠ "") : bandShift bands band.id = band.shift := by
  have hIdsNodup : ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup := lrb_layBands_ids_nodup hModelNodup hModelNoEmpty
  have hLaneMem : band.id ∈ lanesOf boxes := by
    have hC := layBands_mem_cases (hmem := hbands ▸ hband)
    rcases hC with hL | hO
    · exact layLanes_id_mem hL
    · exfalso
      have hid : band.id = "" := by
        have hEqLoose : (looseBand boxes s axis sp (looseNodes boxes) (firstLaneStart s (lanesOf boxes) axis + ((layLanes boxes s axis sp (lanesOf boxes) (firstLaneStart s (lanesOf boxes) axis)).map (·.thickness)).sum)).id = "" := by
          unfold looseBand
          split <;> rfl
        rw [hO, hEqLoose]
      exact hne hid
  have hcov : bandCovers band band.id := Or.inl rfl
  have hUniq : ∀ b1 ∈ bands, ∀ b2 ∈ bands, bandCovers b1 band.id → bandCovers b2 band.id → b1 = b2 := fun b1 hb1 b2 hb2 hc1 hc2 => lrb_cover_unique_lane hModelNodup hModelNoEmpty hIdsNodup hbands hLaneMem hb1 hc1 hb2 hc2
  exact bandShift_eq hband hcov hUniq
private theorem lrb_bind {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β} {y : β} (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem lrb_headD_of_head {α : Type} [Inhabited α] {l : List α} {p d : α} (h : l.head? = some p) : l.headD d = p := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    have hx : x = p := by simpa using h
    show x = p
    exact hx

private theorem lrb_frame_mem {axis : Axis} {bands : List Band} {s : Scene} {f : LaneFrame} (hf : f ∈ laneFrames axis bands s) : ∃ band ∈ bands, ∃ b ∈ s.boxes, band.id = f.id ∧ f.near = axis.start b.rect + band.shift - band.start ∧ f.length = axis.length b.rect ∧ s.boxes.find? (fun b => b.id == band.id) = some b := by
  unfold laneFrames at hf
  obtain ⟨band, hband, hfb⟩ := List.mem_filterMap.mp hf
  cases hfind : s.boxes.find? (fun b => b.id == band.id) with
  | none => simp [hfind] at hfb
  | some b =>
    simp [hfind] at hfb
    subst hfb
    exact ⟨band, hband, b, List.mem_of_find?_eq_some hfind, rfl, rfl, rfl, hfind⟩

private theorem lrb_endRect_for_endpoint {boxes : List ModelBox} {o : Options} {s pinned : Scene} {sp : Spacing} (hsp : spacingOf o.profile = .ok sp) (hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "") (hnodupB : (s.boxes.map (·.id)).Nodup) (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "") (hFrame : lppaFrameTransportResidual boxes o s) (happ : applyPin (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s = .ok pinned) {eid : String} {b0 : Box} (hb0 : b0 ∈ s.boxes) (hid0 : b0.id = eid) {bp : Box} (hbp : bp ∈ pinned.boxes) (hpid : bp.id = eid) {delta : Int} (hdelta : delta = bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) eid) : endRect (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) bp = (Axis.ofDirection o.direction).withStart b0.rect ((Axis.ofDirection o.direction).start b0.rect + delta) := by
  by_cases hFr : ∃ band ∈ layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes), band.id = eid ∧ band.id ≠ ""
  · obtain ⟨band, hmem, hid, hne⟩ := hFr
    have hshift := lrb_bandShift_lane (bands := layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) rfl hModelClean.1 hModelClean.2 hmem hne
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
    have hbEq : b = b0 := lrb_nodup_map_inj (·.id) hnodupB hbmem hb0 (hidb.symm.trans (hpid.trans hid0.symm))
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
        obtain ⟨band, hband, _, _, hbidf, _, _, _⟩ := lrb_frame_mem (List.mem_of_find?_eq_some hsome)
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
theorem lepeRerouteEndsBdryPairedExec_holds {boxes : List ModelBox} {o : Options} {s : Scene} : lepeRerouteEndsBdryPairedExec boxes o s := by
  intro sp hsp hnodupB hModelClean hNoEmpty pinned happ hC5 r old hold hpair fb tb hfb htb ends hends
  have holdD : old ∈ s.layoutDump.routes := hold
  obtain ⟨p, q, fb0, tb0, hp, hq, hfb0, htb0, hb1, hb2⟩ := hC5 old holdD
  have hfb0F : s.boxes.find? (fun b => b.id == old.fromId) = some fb0 := hfb0
  have htb0F : s.boxes.find? (fun b => b.id == old.toId) = some tb0 := htb0
  have hpredF : ((fun b : Box => b.id == r.fromId) fb) = true := by
    have h := List.find?_some hfb
    simpa using h
  have hfbid : fb.id = r.fromId := beq_iff_eq.mp hpredF
  have hpredT : ((fun b : Box => b.id == r.toId) tb) = true := by
    have h := List.find?_some htb
    simpa using h
  have htbId : tb.id = r.toId := beq_iff_eq.mp hpredT
  have hpredF0 : ((fun b : Box => b.id == old.fromId) fb0) = true := by
    have h := List.find?_some hfb0F
    simpa using h
  have hfb0id : fb0.id = old.fromId := beq_iff_eq.mp hpredF0
  have hpredT0 : ((fun b : Box => b.id == old.toId) tb0) = true := by
    have h := List.find?_some htb0F
    simpa using h
  have htb0id : tb0.id = old.toId := beq_iff_eq.mp hpredT0
  obtain ⟨src, hsrc, h1⟩ := lrb_bind hends
  obtain ⟨tgt, htgt, h2⟩ := lrb_bind h1
  dsimp only at h2
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h2
  have hhd : old.points.headD ⟨0, 0⟩ = p := lrb_headD_of_head hp
  have hgd : old.points.getLast?.getD ⟨0, 0⟩ = q := by simp only [hq, Option.getD_some]
  unfold shiftedPoint at hsrc
  obtain ⟨wS, hwS, hrflS⟩ := lrb_bind hsrc
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrflS
  have hwSeq : wS = (Axis.ofDirection o.direction).point (old.points.headD ⟨0, 0⟩) + (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).boxDelta fb.id :=
    checked_value hwS
  have hsrcPt : ends.source = (Axis.ofDirection o.direction).withPoint p ((Axis.ofDirection o.direction).point p + (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).boxDelta fb.id) := by
    have hES : ends.source = src := by rw [← h2]
    rw [hES, ← hrflS, hhd, hwSeq, hhd]
  unfold shiftedPoint at htgt
  obtain ⟨wT, hwT, hrflT⟩ := lrb_bind htgt
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrflT
  have hwTeq : wT = (Axis.ofDirection o.direction).point (old.points.getLast?.getD ⟨0, 0⟩) + (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).boxDelta tb.id :=
    checked_value hwT
  have htgtPt : ends.target = (Axis.ofDirection o.direction).withPoint q ((Axis.ofDirection o.direction).point q + (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).boxDelta tb.id) := by
    have hET : ends.target = tgt := by rw [← h2]
    rw [hET, ← hrflT, hgd, hwTeq, hgd]
  have hfbmem : fb ∈ pinned.boxes := List.mem_of_find?_eq_some hfb
  have htbmem : tb ∈ pinned.boxes := List.mem_of_find?_eq_some htb
  have hfb0mem : fb0 ∈ s.boxes := List.mem_of_find?_eq_some hfb0F
  have htb0mem : tb0 ∈ s.boxes := List.mem_of_find?_eq_some htb0F
  have hfb0eid : fb0.id = r.fromId := hfb0id.trans hpair.1.symm
  have htb0eid : tb0.id = r.toId := htb0id.trans hpair.2.symm
  have hdeltaF : (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).boxDelta fb.id = bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) r.fromId := by
    rw [← hfbid]
    exact buildPin_boxDelta fb.id
  have hdeltaT : (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s).boxDelta tb.id = bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) r.toId := by
    rw [← htbId]
    exact buildPin_boxDelta tb.id
  have hendF := lrb_endRect_for_endpoint (boxes := boxes) (o := o) (s := s) (pinned := pinned) (sp := sp) hsp hModelClean hnodupB hNoEmpty lppaFrameTransportResidual_holds happ hfb0mem hfb0eid hfbmem hfbid hdeltaF
  have hendT := lrb_endRect_for_endpoint (boxes := boxes) (o := o) (s := s) (pinned := pinned) (sp := sp) hsp hModelClean hnodupB hNoEmpty lppaFrameTransportResidual_holds happ htb0mem htb0eid htbmem htbId hdeltaT
  have hbS : Validator.onBoundary ends.source (endRect (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) fb) := by
    rw [hsrcPt, hendF]
    exact (onBoundary_crossShift).mpr hb1
  have hbT : Validator.onBoundary ends.target (endRect (Axis.ofDirection o.direction) (laneFrames (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) tb) := by
    rw [htgtPt, hendT]
    exact (onBoundary_crossShift).mpr hb2
  have hfindF : pinned.layoutDump.box? r.fromId = some fb := by
    unfold LayoutDump.box?
    exact hfb
  have hfindT : pinned.layoutDump.box? r.toId = some tb := by
    unfold LayoutDump.box?
    exact htb
  exact ⟨fb, tb, hfindF, hfindT, hbS, hbT⟩
theorem lepePhaseRerouteExec_final {boxes : List ModelBox} {o : Options} {s : Scene} (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "") : lepePhaseRerouteExec boxes o s := by
  intro sp hsp hnodupB hModelClean hEndsPin pinned routed happ hEndsOld hC5 hroute
  have hboxesEq : routed.boxes = pinned.boxes := (rerouteBands_frame hroute).1
  have hdumpEq : routed.layoutDump.boxes = pinned.layoutDump.boxes := hboxesEq
  have happEq : ∀ (k : Nat) (hkP : k < pinned.routes.length) (hkO : k < s.routes.length)
      {rP rB : Route}, pinned.routes[k]? = some rP → s.routes[k]? = some rB →
      rP.id = rB.id ∧ rP.fromId = rB.fromId ∧ rP.toId = rB.toId := by
    intro k hkP hkO rP rB hPk hOk
    obtain ⟨hid, hfrom, hto, _, _⟩ := applyPin_c4_map happ hkP hkO hPk hOk
    exact ⟨hid, hfrom, hto⟩
  intro r' hr'
  obtain ⟨r, hrmem, old, holdmem, hpair, hid, hfrom, hto, horthEq, hcase⟩ :=
    c4c5_reroute_mem _ _ _ _ _ _ _ _ hroute r' hr'
  rcases hcase with ⟨hptsEq, _⟩ | ⟨fi, ti, fb, tb, ends, obs, pts, hfi, hti, hfb, htb, hends, hobs, hfind, hptsPts⟩
  · obtain ⟨p, q, fbp, tbp, hp, hq, hfbp, htbp, hb1, hb2⟩ := hEndsOld r hrmem
    refine ⟨p, q, fbp, tbp, ?_, ?_, ?_, ?_, hb1, hb2⟩
    · rw [hptsEq]; exact hp
    · rw [hptsEq]; exact hq
    · unfold LayoutDump.box?
      rw [hdumpEq, hfrom]; exact hfbp
    · unfold LayoutDump.box?
      rw [hdumpEq, hto]; exact htbp
  · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hpair
    obtain ⟨hkR, hkO⟩ := getElem?_zip_iff.mp hk
    have hkRL : k < pinned.routes.length := (List.getElem?_eq_some_iff.mp hkR).1
    have hkOL : k < s.routes.length := (List.getElem?_eq_some_iff.mp hkO).1
    obtain ⟨_, hfrEq, htoEq⟩ := happEq k hkRL hkOL hkR hkO
    obtain ⟨fbp, tbp, hfbp, htbp, hbs, hbt⟩ :=
      lepeRerouteEndsBdryPairedExec_holds (boxes := boxes) (o := o) (s := s) sp hsp hnodupB hModelClean hNoEmpty happ hC5 holdmem ⟨hfrEq, htoEq⟩ hfb htb hends
    obtain ⟨hhead, hlast⟩ :=
      hEndsPin (Axis.ofDirection o.direction) sp (buildPin (Axis.ofDirection o.direction) (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s) fb tb old.points ends obs (LayoutConst.rank_gap.get o.profile) pts hends hfind
    refine ⟨ends.source, ends.target, fbp, tbp, ?_, ?_, ?_, ?_, hbs, hbt⟩
    · rw [hptsPts]; exact hhead
    · rw [hptsPts]; exact hlast
    · unfold LayoutDump.box?
      rw [hdumpEq, hfrom]; exact hfbp
    · unfold LayoutDump.box?
      rw [hdumpEq, hto]; exact htbp

theorem pinBands_ends_exec_final {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hC5 : Validator.C5 s.layoutDump)
    (hlanes : lanesOf boxes ≠ [])
    (hrouteNodup : (s.routes.map (·.id)).Nodup)
    (hnodupB : (s.boxes.map (·.id)).Nodup)
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (hEnds : ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      ∀ rt ∈ s.routes,
        bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) rt.fromId =
        bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) rt.toId ∨
        ((Axis.ofDirection o.direction).point (rt.points.head?.getD ⟨0, 0⟩) ≠
          (Axis.ofDirection o.direction).point (rt.points.getLast?.getD ⟨0, 0⟩) ∧ 1 < rt.points.length))
    (hEndsPin : FindRouteEndsPin)
    (hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "")
    (h : pinBands boxes o s = .ok r) :
    ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      EndsOnOld (Axis.ofDirection o.direction)
        (laneFrames (Axis.ofDirection o.direction)
          (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
        r.layoutDump := by
  exact pinBands_ends_exec hC5 hlanes hrouteNodup hnodupB hNoEmpty hEnds hEndsPin
    hModelClean lepePhaseApplyPinExec_closed (lepePhaseRerouteExec_final hNoEmpty) h
end LaneBands
end Layered
end Elegant

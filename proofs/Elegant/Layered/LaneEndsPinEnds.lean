import Elegant.Layered.LaneEndsClauses
import Elegant.Layered.LaneBandsPhaseFacts
import Elegant.Layered.LaneBandsRouteClauses
import Elegant.Layered.LaneBandsRouteClausesProof
import Elegant.Layered.LaneBandsFrameClause

set_option autoImplicit false

/-! Ends of pinned routes lie on their old frames.

`pinBands_ends` replaces the `hNoBandEnds` premise of `pinBands_c5`: after
`pinBands`, every route end lies on its end box boundary, or its end box is a
lane frame and the end lies on the old frame rect `endRect`. It is proved as a
composition of one named fact per phase of `pinBands`: band shift with frame
replacement (`lepePhaseApplyPin`), cross-band rerouting (`lepePhaseReroute`),
origin restoration (`lepePhaseRestore`), label relocation (`lepePhaseRelocate`)
and canvas growth (`lepePhaseGrow`). Undischarged phases stay as explicit
hypotheses of the main theorem until they are proved one by one. -/

namespace Elegant
namespace Layered
namespace LaneBands

/-- Binding step of an `Except` computation (local copy). -/
private theorem lepe_bind {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- Phase fact: `applyPin` (band shift plus frame replacement) takes ends to
the old frames. -/
def lepePhaseApplyPin (axis : Axis) (bands : List Band) (boxes : List ModelBox)
    (s : Scene) : Prop :=
  ∀ (_hC5 : Validator.C5 s.layoutDump)
    (_hrouteNodup : (s.routes.map (·.id)).Nodup)
    (_hnodupB : (s.boxes.map (·.id)).Nodup)
    (_hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "")
    (_hEnds : ∀ rt ∈ s.routes,
      bandShift bands rt.fromId = bandShift bands rt.toId ∨
        (axis.point (rt.points.head?.getD ⟨0, 0⟩) ≠
          axis.point (rt.points.getLast?.getD ⟨0, 0⟩) ∧ 1 < rt.points.length))
    (sp : Spacing)
    (_hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    {pinned : Scene}
    (_happ : applyPin (buildPin axis bands s) bands s = .ok pinned),
    EndsOnOld axis (laneFrames axis bands s) pinned.layoutDump

/-- Phase fact: `rerouteBands` keeps ends on the old frames; rebuilt
cross-band routes start from the band-shifted base ends. -/
def lepePhaseReroute (axis : Axis) (bands : List Band) (boxes : List ModelBox)
    (o : Options) (s : Scene) : Prop :=
  ∀ (_hnodupB : (s.boxes.map (·.id)).Nodup)
    (_hModelClean : (boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ boxes, b.id ≠ "")
    (_hEndsPin : FindRouteEndsPin)
    (sp : Spacing)
    (_hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    {pinned routed : Scene}
    (_happ : applyPin (buildPin axis bands s) bands s = .ok pinned)
    (_hEndsOld : EndsOnOld axis (laneFrames axis bands s) pinned.layoutDump)
    (_hC5 : Validator.C5 s.layoutDump)
    (_hroute : rerouteBands axis sp (LayoutConst.rank_gap.get o.profile) bands
      (buildPin axis bands s) s.routes pinned = .ok routed),
    EndsOnOld axis (laneFrames axis bands s) routed.layoutDump

/-- Phase fact: `restoreOrigin` moves everything by one vector. -/
def lepePhaseRestore : Prop :=
  ∀ {axis : Axis} {frames : List LaneFrame} {s s' : Scene}
    (_h : restoreOrigin axis s = .ok s')
    (_hnodupB : (s.boxes.map (·.id)).Nodup)
    (_hE : EndsOnOld axis frames s.layoutDump),
    EndsOnOld axis frames s'.layoutDump

/-- Phase fact: `relocateLabels` leaves boxes and routes alone. -/
def lepePhaseRelocate : Prop :=
  ∀ {axis : Axis} {frames : List LaneFrame} {s : Scene} {strip : Int}
    (_hE : EndsOnOld axis frames s.layoutDump),
    EndsOnOld axis frames (relocateLabels axis strip s).layoutDump

/-- Phase fact: `growCanvas` leaves boxes and routes alone. -/
def lepePhaseGrow : Prop :=
  ∀ {axis : Axis} {frames : List LaneFrame} {canvas : Size} {s s' : Scene}
    (_h : growCanvas axis canvas s = .ok s')
    (_hE : EndsOnOld axis frames s.layoutDump),
    EndsOnOld axis frames s'.layoutDump



/-- `relocateLabels` preserves `EndsOnOld`: boxes and routes are untouched. -/
private theorem lepePhaseRelocate_holds : lepePhaseRelocate := by
  intro axis frames s strip hE r hr
  have hrS : r ∈ s.layoutDump.routes := hr
  obtain ⟨p, q, fb, tb, hp, hq, hfb, htb, hb1, hb2⟩ := hE r hrS
  exact ⟨p, q, fb, tb, hp, hq, hfb, htb, hb1, hb2⟩

/-- `growCanvas` preserves `EndsOnOld`: boxes and routes are untouched. -/
private theorem lepePhaseGrow_holds : lepePhaseGrow := by
  intro axis frames canvas s s' h hE r hr
  obtain ⟨hb, hrEq, _⟩ := growCanvas_frame h
  have hdB : s'.layoutDump.boxes = s.layoutDump.boxes := hb
  have hdR : s'.layoutDump.routes = s.layoutDump.routes := hrEq
  have hrS : r ∈ s.layoutDump.routes := by rw [← hdR]; exact hr
  obtain ⟨p, q, fb, tb, hp, hq, hfb, htb, hb1, hb2⟩ := hE r hrS
  have hfb' : s'.layoutDump.box? r.fromId = some fb := by
    unfold LayoutDump.box?
    rw [hdB]
    exact hfb
  have htb' : s'.layoutDump.box? r.toId = some tb := by
    unfold LayoutDump.box?
    rw [hdB]
    exact htb
  exact ⟨p, q, fb, tb, hp, hq, hfb', htb', hb1, hb2⟩

/-- A satisfying member gives a `find?` witness. -/
private theorem lepe_find?_ex {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∃ a, a ∈ l ∧ p a = true) →
      ∃ a, l.find? p = some a := by
  intro l
  induction l with
  | nil => intro ⟨a, ha, _⟩; cases ha
  | cons x xs ih =>
    intro ⟨a, ha, hp⟩
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

/-- Injectivity on a nodup image list. -/
private theorem lepe_nodup_map_inj {α β : Type} [BEq β] [LawfulBEq β] (g : α → β)
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
/-- First index carrying a satisfying element, with all earlier failing. -/
private theorem lepe_find?_idx {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), l.find? p = some a →
      ∃ j : Nat, l[j]? = some a ∧ p a = true ∧
        ∀ k, k < j → ∀ y, l[k]? = some y → p y = false := by
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

/-- Every emitted frame comes from a band with a found scene box. -/
private theorem lepe_frame_mem {axis : Axis} {bands : List Band} {s : Scene}
    {f : LaneFrame} (hf : f ∈ laneFrames axis bands s) :
    ∃ band ∈ bands, ∃ b ∈ s.boxes, band.id = f.id ∧
      f.near = axis.start b.rect + band.shift - band.start ∧
      f.length = axis.length b.rect ∧
      s.boxes.find? (fun b => b.id == band.id) = some b := by
  unfold laneFrames at hf
  obtain ⟨band, hband, hfb⟩ := List.mem_filterMap.mp hf
  cases hfind : s.boxes.find? (fun b => b.id == band.id) with
  | none => simp [hfind] at hfb
  | some b =>
    simp [hfind] at hfb
    subst hfb
    exact ⟨band, hband, b, List.mem_of_find?_eq_some hfind, rfl, rfl, rfl, hfind⟩

/-- A lane is witnessed by a group model box with no parent. -/
private theorem lepe_lanesOf_mem {boxes : List ModelBox} {lane : String}
    (h : lane ∈ lanesOf boxes) :
    ∃ mb ∈ boxes, mb.role = .group ∧ mb.parent = "" ∧ mb.id = lane := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, hpred⟩ := List.mem_filter.mp hx
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hrole, hpar⟩ := hpred
  exact ⟨x, hxb, beq_iff_eq.mp hrole, beq_iff_eq.mp hpar, rfl⟩

/-- A lane is in its own lane, under model nodup. -/
private theorem lepe_inLane_self {boxes : List ModelBox}
    (hn : (boxes.map (fun b => b.id)).Nodup) {lane : String}
    (hl : lane ∈ lanesOf boxes) : inLane boxes lane lane = true := by
  obtain ⟨mb, hmbMem, hmbRole, hmbPar, hmbId⟩ := lepe_lanesOf_mem hl
  have hfind : boxes.find? (fun b => b.id == lane) = some mb := by
    have hEq : (fun b : ModelBox => b.id == lane) = (fun b : ModelBox => b.id == mb.id) := by
      funext b
      rw [hmbId]
    rw [hEq]
    exact modelFind?_eq_self hn hmbMem
  unfold inLane laneOf laneOfAux
  rw [hfind]
  simp [hmbPar, hmbRole]

/-- `layLanes` ids are exactly the lane list. -/
private theorem lepe_layLanes_ids (boxes : List ModelBox) (s : Scene) (axis : Axis)
    (sp : Spacing) (lanes : List String) (start : Int) :
    (layLanes boxes s axis sp lanes start).map (fun b => b.id) = lanes := by
  induction lanes generalizing start with
  | nil => rfl
  | cons lane rest ih =>
    have hhead : (laneBand boxes s axis sp lane start).id = lane := rfl
    simp only [layLanes, List.map_cons, hhead, ih]

/-- Lane ids are nonempty model ids. -/
private theorem lepe_lanes_ne_empty {boxes : List ModelBox}
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") {lane : String}
    (h : lane ∈ lanesOf boxes) : lane ≠ "" := by
  obtain ⟨x, hxb, _, _, rfl⟩ := lepe_lanesOf_mem h
  exact hModelNoEmpty x hxb

/-- The loose band id is always empty. -/
private theorem lepe_loose_id {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {loose : List String} {start : Int} :
    (looseBand boxes s axis sp loose start).id = "" := by
  unfold looseBand
  split <;> rfl
/-- A box whose id differs from the replaced band survives `replaceFrame`. -/
private theorem lepe_replace_other {axis : Axis} {band₂ : Band} {s s' : Scene}
    (h : replaceFrame axis band₂ s = .ok s')
    {b : Box} (hbin : b ∈ s.boxes) (hne : b.id ≠ band₂.id) :
    b ∈ s'.boxes := by
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
        have hlen : k < (s.boxes.mapIdx fun j b =>
            if j = index then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b).length := by
          simpa using hk
        have heq : (s.boxes.mapIdx fun j b =>
            if j = index then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b)[k]'hlen =
            s.boxes[k] := by
          rw [List.getElem_mapIdx]
          simp [hne']
        rw [← heq]
        exact List.getElem_mem hlen


/-- A non-target box survives a whole `replaceFrame` fold. -/
private theorem lepe_fold_other {axis : Axis} {bands : List Band} {shifted pinned : Scene}
    {b : Box} (hbin : b ∈ shifted.boxes)
    (hne : ∀ bd ∈ bands, bd.id ≠ b.id)
    (hfold : bands.foldlM (fun scene band => replaceFrame axis band scene) shifted = .ok pinned) :
    b ∈ pinned.boxes := by
  induction bands generalizing shifted with
  | nil =>
    have he : pinned = shifted := by
      simpa only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] using hfold.symm
    subst he
    exact hbin
  | cons hd rest ih =>
    rw [List.foldlM_cons] at hfold
    obtain ⟨mid, hmid, hrest⟩ := lepe_bind hfold
    have hneHd : b.id ≠ hd.id := Ne.symm (hne hd (List.mem_cons.mpr (Or.inl rfl)))
    have hmid' : b ∈ mid.boxes := lepe_replace_other hmid hbin hneHd
    exact ih hmid' (fun bd hbd => hne bd (List.mem_cons.mpr (Or.inr hbd))) hrest

/-- One `replaceFrame` keeps every box's rank, with a same-id pre-image. -/
private theorem lepe_replaceFrame_rank {axis : Axis} {band : Band} {s s' : Scene}
    (h : replaceFrame axis band s = .ok s')
    {b' : Box} (hb' : b' ∈ s'.boxes) :
    ∃ b ∈ s.boxes, b'.id = b.id ∧
      axis.other.start b'.rect = axis.other.start b.rect ∧
      axis.other.length b'.rect = axis.other.length b.rect := by
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
        have hlen : (s.boxes.mapIdx fun j b =>
            if j = idx then ({ b with rect := placeRect axis sv tv b.rect } : Box)
            else b).length = s.boxes.length := List.length_mapIdx
        have hklen : k < s.boxes.length := by
          have hkk0 := (List.getElem?_eq_some_iff.mp hk).1
          omega
        have hbk : s.boxes[k]? = some s.boxes[k] := List.getElem?_eq_getElem hklen
        have hmap := List.getElem?_mapIdx (f := fun j b =>
            if j = idx then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b)
            (l := s.boxes) (i := k)
        rw [hk, hbk] at hmap
        simp only [Option.map_some] at hmap
        by_cases hkk : k = idx
        · have hkk2 : idx = k := hkk.symm
          subst hkk2
          rw [ite_eq_left rfl] at hmap
          have hbeq := Option.some.inj hmap
          subst hbeq
          exact ⟨s.boxes[idx], List.mem_iff_getElem.mpr ⟨idx, hi, rfl⟩, rfl,
            (placeRect_other _ _ _).1, (placeRect_other _ _ _).2⟩
        · rw [ite_eq_right hkk] at hmap
          have hbeq : b' = s.boxes[k] := Option.some.inj hmap
          rw [hbeq]
          exact ⟨s.boxes[k], List.mem_iff_getElem.mpr ⟨k, hklen, rfl⟩, rfl, rfl, rfl⟩

/-- A fold keeps every box's rank, with a same-id pre-image. -/
private theorem lepe_fold_rank {axis : Axis} {bands : List Band} {shifted pinned : Scene}
    (hfold : bands.foldlM (fun scene band => replaceFrame axis band scene) shifted = .ok pinned)
    {b' : Box} (hb' : b' ∈ pinned.boxes) :
    ∃ b ∈ shifted.boxes, b'.id = b.id ∧
      axis.other.start b'.rect = axis.other.start b.rect ∧
      axis.other.length b'.rect = axis.other.length b.rect := by
  induction bands generalizing shifted with
  | nil =>
    have he : pinned = shifted := by
      simpa only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] using hfold.symm
    subst he
    exact ⟨b', hb', rfl, rfl, rfl⟩
  | cons hd rest ih =>
    rw [List.foldlM_cons] at hfold
    obtain ⟨mid, hmid, hrest⟩ := lepe_bind hfold
    obtain ⟨bm, hbmm, hidm, hr1m, hr2m⟩ := ih hrest
    obtain ⟨b, hbm, hidb, hr1b, hr2b⟩ := lepe_replaceFrame_rank hmid hbmm
    exact ⟨b, hbm, hidm.trans hidb, hr1m.trans hr1b, hr2m.trans hr2b⟩

/-- `layBands` ids are nodup when model ids are nodup and nonempty. -/
private theorem lepe_layBands_ids_nodup {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing}
    (hModelNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") :
    ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup := by
  have hLaneIds : ((layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id) =
      lanesOf boxes :=
    lepe_layLanes_ids _ _ _ _ _ _
  have hLaneNodup : ((layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id).Nodup := by
    rw [hLaneIds]
    exact lanesOf_nodup hModelNodup
  have hfresh : "" ∉ lanesOf boxes :=
    fun hmem => lepe_lanes_ne_empty hModelNoEmpty hmem rfl
  unfold layBands
  by_cases hl : (looseNodes boxes).isEmpty = true
  · simp only [hl, ↓reduceIte]
    exact hLaneNodup
  · simp only [hl, ↓reduceIte, Bool.false_eq_true, List.map_append, hLaneIds]
    have hsing : ∀ S : Int, (([looseBand boxes s axis sp (looseNodes boxes) S].map
        fun b => b.id) = [""]) := by
      intro S
      simp only [List.map_cons, List.map_nil, lepe_loose_id]
    simp only [hsing]
    rw [List.nodup_append]
    refine ⟨?_, (by simp : ([""] : List String).Nodup), ?_⟩
    · exact lanesOf_nodup hModelNodup
    · intro a ha b hb hEq
      rw [List.mem_singleton] at hb
      subst hb
      exact lepe_lanes_ne_empty hModelNoEmpty ha hEq


/-- Box correspondence through a uniform shift, with `find?` and rect. -/
private theorem lepe_shiftAll_boxIdx {axis : Axis} {delta : Int} {s : Scene}
    {boxes : List Box}
    (hboxes : s.boxes.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant delta).rect axis b.rect } : Except LayoutError Box)) = .ok boxes)
    (hnodupB : (s.boxes.map (·.id)).Nodup)
    {id : String} {fb : Box} (hfb : s.boxes.find? (fun b => b.id == id) = some fb) :
    ∃ b0', (boxes.find? fun b => b.id == id) = some b0' ∧ b0'.id = fb.id ∧
      b0'.rect = axis.withStart fb.rect (axis.start fb.rect + delta) := by
  have hfbM : fb ∈ s.boxes := List.mem_of_find?_eq_some hfb
  have hspecB := mapM_except_spec _ s.boxes boxes hboxes
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hfbM
  have hjL : j < s.boxes.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjB : j < boxes.length := by have := hspecB.1; omega
  obtain ⟨b0, b0', hb0, hb0', hfb0⟩ := hspecB.2 j hjL hjB
  have hb0e : b0 = fb := Option.some.inj (hb0.symm.trans hj)
  have hnodupB' : (boxes.map (·.id)).Nodup := by
    have hid : boxes.map (·.id) = s.boxes.map (·.id) :=
      (shiftBoxes_maps s.boxes axis delta boxes hboxes).2.1
    rw [hid]
    exact hnodupB
  obtain ⟨hid0, _, _, _, w0, hw0, hrect0, hval0⟩ := shiftBox_ok hfb0
  have hb0'mem : b0' ∈ boxes := List.mem_iff_getElem?.mpr ⟨j, hb0'⟩
  obtain ⟨_, _, hjpred, _⟩ := lepe_find?_idx _ _ _ hfb
  have hfbid : fb.id = id := beq_iff_eq.mp hjpred
  have hidF : b0'.id = id := by rw [hb0e] at hid0; rw [hid0, hfbid]
  have hpredF : (fun b : Box => b.id == id) b0' = true := beq_iff_eq.mpr hidF
  obtain ⟨dF, hfindF0⟩ := lepe_find?_ex (fun b : Box => b.id == id) _ ⟨b0', hb0'mem, hpredF⟩
  have hdFeq : dF = b0' := by
    apply lepe_nodup_map_inj (·.id) hnodupB'
    · exact List.mem_of_find?_eq_some hfindF0
    · exact hb0'mem
    · obtain ⟨_, _, hjpred2, _⟩ := lepe_find?_idx _ _ _ hfindF0
      have h2 := beq_iff_eq.mp hjpred2
      rw [← hidF] at h2
      exact h2
  have hfindF : (boxes.find? fun b => b.id == id) = some b0' := by
    rw [← hdFeq]
    exact hfindF0
  have hrectF : b0'.rect = axis.withStart fb.rect (axis.start fb.rect + delta) := by
    rw [hb0e] at hrect0 hval0 hw0
    rw [hrect0, hval0]
  exact ⟨b0', hfindF, by rw [hidF, hfbid], hrectF⟩

/-- Route index correspondence through a uniform shift. -/
private theorem lepe_shiftAll_routeIdx {axis : Axis} {delta : Int} {s : Scene}
    {routes : List Route}
    (hroutes : s.routes.mapM (fun r : Route => (do pure { r with points := ← r.points.mapM ((Move.constant delta).point axis) } : Except LayoutError Route)) = .ok routes)
    {r' : Route} (hr' : r' ∈ routes) :
    ∃ r ∈ s.routes, r'.id = r.id ∧ r'.fromId = r.fromId ∧ r'.toId = r.toId ∧
      ∃ pts, r'.points = pts ∧
        r.points.mapM ((Move.constant delta).point axis) = .ok pts := by
  have hspecR := mapM_except_spec _ s.routes routes hroutes
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr'
  have hiL : i < routes.length := (List.getElem?_eq_some_iff.mp hi).1
  have hiS : i < s.routes.length := by omega
  obtain ⟨r, bR, haR, hbR, hfab⟩ := hspecR.2 i hiS hiL
  have hrBmem : r ∈ s.routes := List.mem_iff_getElem?.mpr ⟨i, haR⟩
  have hbRe : bR = r' := Option.some.inj (hbR.symm.trans hi)
  obtain ⟨pts, hpts, hrfl⟩ := lepe_bind hfab
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  refine ⟨r, hrBmem, ?_, ?_, ?_, pts, ?_, hpts⟩ <;> rw [← hbRe, ← hrfl]

/-- Last point through a `mapM` point move. -/
private theorem lepe_mapM_point_getLast {m : Move} {axis : Axis} :
    ∀ (ps qs : List Point), ps.mapM (m.point axis) = .ok qs →
      ∀ p, ps.getLast? = some p →
        ∃ q, qs.getLast? = some q ∧ m.point axis p = .ok q := by
  intro ps
  induction ps with
  | nil => intro qs _ p hp; simp at hp
  | cons x rest ih =>
    intro qs h p hp
    rw [List.mapM_cons] at h
    obtain ⟨x', hx', h⟩ := lepe_bind h
    obtain ⟨rest', hrest, hrfl⟩ := lepe_bind h
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

/-- Head point through a `mapM` point move. -/
private theorem lepe_mapM_point_head {m : Move} {axis : Axis} :
    ∀ (ps qs : List Point), ps.mapM (m.point axis) = .ok qs →
      ∀ p, ps.head? = some p →
        ∃ q, qs.head? = some q ∧ m.point axis p = .ok q := by
  intro ps
  induction ps with
  | nil => intro qs _ p hp; simp at hp
  | cons x xs ih =>
    intro qs h p hp
    rw [List.mapM_cons] at h
    obtain ⟨x', hx', h⟩ := lepe_bind h
    obtain ⟨rest', hrest, hrfl⟩ := lepe_bind h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
    subst hrfl
    have hpx : x = p := by simpa using hp
    subst hpx
    exact ⟨x', rfl, hx'⟩

/-- A uniform cross shift commutes with `endRect`. -/
private theorem lepe_endRect_shift {axis : Axis} {frames : List LaneFrame}
    {b b' : Box} {delta : Int}
    (hrect : b'.rect = axis.withStart b.rect (axis.start b.rect + delta))
    (hid : b'.id = b.id) :
    endRect axis frames b' =
      axis.withStart (endRect axis frames b)
        (axis.start (endRect axis frames b) + delta) := by
  have hfind : (frames.find? fun b_ => b_.id == b'.id) =
      frames.find? fun b_ => b_.id == b.id := by rw [hid]
  unfold endRect
  rw [hfind]
  cases hf : frames.find? (fun b_ => b_.id == b.id) with
  | none =>
    exact hrect
  | some f =>
    cases axis with
    | x =>
      have hx : b'.rect.x = b.rect.x + delta := by rw [hrect]; rfl
      have hy : b'.rect.y = b.rect.y := by rw [hrect]; rfl
      have hw : b'.rect.w = b.rect.w := by rw [hrect]; rfl
      have hh : b'.rect.h = b.rect.h := by rw [hrect]; rfl
      simp only [oldFrame, placeRect, Axis.withStart, Axis.withLength,
        Axis.start, hx, hy, hw, hh]
      congr 1 <;> omega
    | y =>
      have hx : b'.rect.x = b.rect.x := by rw [hrect]; rfl
      have hy : b'.rect.y = b.rect.y + delta := by rw [hrect]; rfl
      have hw : b'.rect.w = b.rect.w := by rw [hrect]; rfl
      have hh : b'.rect.h = b.rect.h := by rw [hrect]; rfl
      simp only [oldFrame, placeRect, Axis.withStart, Axis.withLength,
        Axis.start, hx, hy, hw, hh]
      congr 1 <;> omega




/-- A uniform shift preserves `EndsOnOld`. -/
private theorem lepe_shiftAll_ends {axis : Axis} {delta : Int} {s s' : Scene}
    {frames : List LaneFrame}
    (h : shiftAll axis delta s = .ok s')
    (hnodupB : (s.boxes.map (·.id)).Nodup)
    (hE : EndsOnOld axis frames s.layoutDump) :
    EndsOnOld axis frames s'.layoutDump := by
  unfold shiftAll at h
  obtain ⟨boxes, hboxes, h1⟩ := lepe_bind h
  obtain ⟨labels, hlabels, h2⟩ := lepe_bind h1
  obtain ⟨routes, hroutes, h3⟩ := lepe_bind h2
  obtain ⟨items, hitems, h4⟩ := lepe_bind h3
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h4
  subst h4
  intro r' hr'
  have hrM : r' ∈ routes := hr'
  obtain ⟨r, hrBmem, hrid, hrfrom, hrto, pts, hptsR, hpts⟩ :=
    lepe_shiftAll_routeIdx hroutes hrM
  have hrS : r ∈ s.layoutDump.routes := hrBmem
  obtain ⟨p, q, fb, tb, hp, hq, hfb, htb, hb1, hb2⟩ := hE r hrS
  obtain ⟨qP, hqPhead, hqPfun⟩ := lepe_mapM_point_head _ _ hpts p hp
  obtain ⟨wP, hwP, hqPeq, _⟩ := movePoint_ok hqPfun
  have hwPeq : wP = axis.point p + delta := by
    have happEq : (Move.constant delta).apply (axis.point p) =
        Measure.checkedI32 (axis.point p + delta) := by simp [Move.apply, Move.offset]
    rw [happEq] at hwP
    exact checked_value hwP
  have hqPEq : qP = axis.withPoint p (axis.point p + delta) := by rw [hqPeq, hwPeq]
  obtain ⟨qQ, hqQlast, hqQfun⟩ := lepe_mapM_point_getLast _ _ hpts q hq
  obtain ⟨wQ, hwQ, hqQeq, _⟩ := movePoint_ok hqQfun
  have hwQeq : wQ = axis.point q + delta := by
    have happEq : (Move.constant delta).apply (axis.point q) =
        Measure.checkedI32 (axis.point q + delta) := by simp [Move.apply, Move.offset]
    rw [happEq] at hwQ
    exact checked_value hwQ
  have hqQEq : qQ = axis.withPoint q (axis.point q + delta) := by rw [hqQeq, hwQeq]
  have hfb' : s.boxes.find? (fun b => b.id == r.fromId) = some fb := hfb
  have htb' : s.boxes.find? (fun b => b.id == r.toId) = some tb := htb
  obtain ⟨b0', hfindF, hidF, hrectF⟩ := lepe_shiftAll_boxIdx hboxes hnodupB hfb'
  obtain ⟨b1', hfindT, hidT, hrectT⟩ := lepe_shiftAll_boxIdx hboxes hnodupB htb'
  have hendF : endRect axis frames b0' =
      axis.withStart (endRect axis frames fb)
        (axis.start (endRect axis frames fb) + delta) :=
    lepe_endRect_shift hrectF hidF
  have hendT : endRect axis frames b1' =
      axis.withStart (endRect axis frames tb)
        (axis.start (endRect axis frames tb) + delta) :=
    lepe_endRect_shift hrectT hidT
  have hbP : Validator.onBoundary qP (endRect axis frames b0') := by
    rw [hqPEq, hendF]
    exact (onBoundary_crossShift).mpr hb1
  have hbQ : Validator.onBoundary qQ (endRect axis frames b1') := by
    rw [hqQEq, hendT]
    exact (onBoundary_crossShift).mpr hb2
  have hfindF' : (boxes.find? fun b => b.id == r'.fromId) = some b0' := by
    rw [hrfrom]; exact hfindF
  have hfindT' : (boxes.find? fun b => b.id == r'.toId) = some b1' := by
    rw [hrto]; exact hfindT
  have hhead : r'.points.head? = some qP := by rw [hptsR]; exact hqPhead
  have hlast : r'.points.getLast? = some qQ := by rw [hptsR]; exact hqQlast
  exact ⟨qP, qQ, b0', b1', hhead, hlast, hfindF', hfindT', hbP, hbQ⟩
/-- `restoreOrigin` preserves `EndsOnOld`: it either leaves the scene or shifts it. -/
private theorem lepePhaseRestore_holds : lepePhaseRestore := by
  intro axis frames s s' h hnodupB hE
  obtain rfl | ⟨delta, _, hshift⟩ := restoreOrigin_cases h
  · exact hE
  · exact lepe_shiftAll_ends hshift hnodupB hE

/-- After `pinBands`, every route end lies on its end box boundary, or on the
old frame when the end box is a lane frame. This replaces the `hNoBandEnds`
premise of `pinBands_c5`. -/
theorem pinBands_ends {boxes : List ModelBox} {o : Options} {s r : Scene}
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
    (hApply : ∀ (axis : Axis) (bands : List Band),
      lepePhaseApplyPin axis bands boxes s)
    (hReroute : ∀ (axis : Axis) (bands : List Band),
      lepePhaseReroute axis bands boxes o s)

    (h : pinBands boxes o s = .ok r) :
    ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      EndsOnOld (Axis.ofDirection o.direction)
        (laneFrames (Axis.ofDirection o.direction)
          (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
        r.layoutDump := by
  obtain ⟨sp, axis, bands, pinned, routed, origin, strip, stripScene,
    hsp, haxis, hbands, happ, hroute, horig, hstrip, hstripEq, hgrow⟩ :=
    pinBands_spec hlanes h
  have hEnds' : ∀ rt ∈ s.routes,
      bandShift bands rt.fromId = bandShift bands rt.toId ∨
        (axis.point (rt.points.head?.getD ⟨0, 0⟩) ≠
          axis.point (rt.points.getLast?.getD ⟨0, 0⟩) ∧ 1 < rt.points.length) := by
    intro rt hr
    have h2 := hEnds sp hsp rt hr
    rw [← haxis, ← hbands] at h2
    exact h2
  intro sp' hsp'
  have hspEq : sp' = sp := Except.ok.inj (hsp'.symm.trans hsp)
  rw [hspEq]
  have hpin := hApply axis bands hC5 hrouteNodup hnodupB hModelClean hEnds' sp
    hbands happ
  have hrouted := hReroute axis bands hnodupB hModelClean hEndsPin sp hbands
    happ hpin hC5 hroute
  obtain ⟨shiftedBoxes, _, _, _, hboxes, _, _, _, hfold⟩ := applyPin_shifted happ
  have hid1 : shiftedBoxes.map (·.id) = s.boxes.map (·.id) :=
    (pinShiftBoxes_maps _ _ _ _ hboxes).2.1
  have hid2 : pinned.boxes.map (·.id) = shiftedBoxes.map (·.id) :=
    (foldReplaceFrame_all _ _ _ _ hfold).2.1
  have hrr : routed.boxes = pinned.boxes := (rerouteBands_frame hroute).1
  have hnodupRouted : (routed.boxes.map (·.id)).Nodup := by
    rw [hrr, hid2, hid1]
    exact hnodupB
  have horigE := lepePhaseRestore_holds horig hnodupRouted hrouted
  have hstripE : EndsOnOld axis (laneFrames axis bands s) stripScene.layoutDump := by
    rw [hstripEq]
    exact lepePhaseRelocate_holds horigE
  have hfinal := lepePhaseGrow_holds hgrow hstripE
  rw [hbands, haxis] at hfinal
  exact hfinal

end LaneBands
end Layered
end Elegant

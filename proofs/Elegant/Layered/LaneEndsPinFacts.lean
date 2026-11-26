import Elegant.Layered.LaneEndsClauses
import Elegant.Layered.LaneBandsPhaseFacts
import Elegant.Layered.LaneBandsRouteClauses
import Elegant.Layered.LaneBandsRouteClausesProof
import Elegant.Layered.LaneBandsFindRouteFactsProof
import Elegant.Layered.LaneBandsFrameClause
import Elegant.Layered.LaneBandsLabelClauses
import Elegant.Layered.LaneBandsClearance
import Elegant.Layered.LaneBandsBoxClausesProof

set_option autoImplicit false

/-! Facts about the scene after `pinBands` (before `attachLaneEnds`).

Design items 10-12 (`swimlane-lane-loop-fix-design.md` section 5): `pinBands`
establishes `FramesFit` (every lane frame sits inside its stretched box),
`GapClear` (the strip between an old and a new frame side holds no exclusive
box interior) and `ExclusivePositive` (exclusive boxes keep positive size).
Item 9 (`pinBands_ends`) replaces the `hNoBandEnds` premise of `pinBands_c5`
with an `EndsOnOld` conclusion; it keeps one narrow single-function residual
about `bandShift` on lane ids (see `pinBands_ends`). -/

namespace Elegant
namespace Layered
namespace LaneBands

/-- Bind decomposition for `Except`. -/
private theorem lepf_bind {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- Membership from `find?` (core wrapper for uniform use). -/
private theorem lepf_found_mem {α : Type} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : a ∈ l :=
  List.mem_of_find?_eq_some h

/-- The `find?` predicate holds at the found element (core wrapper). -/
private theorem lepf_found_true {α : Type} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : p a = true :=
  List.find?_some h

/-- Injectivity on a nodup image list. -/
private theorem lepf_nodup_eq {α β : Type} [BEq β] [LawfulBEq β] (g : α → β)
    {l : List α} (h : (l.map g).Nodup) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (e : g x = g y) : x = y := by
  induction l with
  | nil => cases hx
  | cons z zs ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    obtain ⟨hfresh, hrest⟩ := h
    rw [List.mem_cons] at hx hy
    rcases hx with hxz | hx
    · rcases hy with hyz | hy
      · rw [hxz, hyz]
      · exfalso
        have hm : g x ∈ zs.map g := List.mem_map.mpr ⟨y, hy, e.symm⟩
        rw [hxz] at hm
        exact hfresh hm
    · rcases hy with hyz | hy
      · exfalso
        have hm : g z ∈ zs.map g := List.mem_map.mpr ⟨x, hx, e.trans (congrArg g hyz)⟩
        exact hfresh hm
      · exact ih hrest hx hy

/-- Cross length is unchanged by a cross start move. -/
private theorem lepf_length_withStart {axis : Axis} {r : Rect} {w : Int} :
    axis.length (axis.withStart r w) = axis.length r := by
  cases axis <;> rfl

/-- Rank coordinates are unchanged by a cross start move. -/
private theorem lepf_rank_withStart {axis : Axis} {r : Rect} {w : Int} :
    axis.other.start (axis.withStart r w) = axis.other.start r ∧
      axis.other.length (axis.withStart r w) = axis.other.length r := by
  cases axis <;> constructor <;> rfl

/-- Rank coordinate of a point is unchanged by a cross move. -/
private theorem lepf_rank_withPoint {axis : Axis} {p : Point} {v : Int} :
    axis.other.point (axis.withPoint p v) = axis.other.point p := by
  cases axis <;> rfl

/-- Rank coordinates are unchanged by `placeRect`. -/
private theorem lepf_rank_placeRect {axis : Axis} {start thickness : Int} {r : Rect} :
    axis.other.start (placeRect axis start thickness r) = axis.other.start r ∧
      axis.other.length (placeRect axis start thickness r) = axis.other.length r := by
  cases axis <;> unfold placeRect Axis.withStart Axis.withLength Axis.start
    Axis.length Axis.other <;> constructor <;> rfl

/-- Every emitted frame comes from a band with a found scene box. -/
private theorem lepf_frame_mem {axis : Axis} {bands : List Band} {s : Scene}
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
    exact ⟨band, hband, b, lepf_found_mem hfind, rfl, rfl, rfl, hfind⟩

/-- A band of `layBands` is a lane band or the trailing loose band. -/
private theorem lepf_band_cases {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lanes : List String} {band : Band}
    (hmem : band ∈ layBands boxes s axis sp lanes) :
    (∃ lane ∈ lanes, ∃ st : Int, band = laneBand boxes s axis sp lane st) ∨
      band = looseBand boxes s axis sp (looseNodes boxes)
        (firstLaneStart s lanes axis + ((layLanes boxes s axis sp lanes
          (firstLaneStart s lanes axis)).map (fun b => b.thickness)).sum) := by
  obtain hmem | rfl := layBands_mem_cases hmem
  · obtain ⟨lane, hl, st, rfl⟩ := layLanes_mem_lane hmem
    exact Or.inl ⟨lane, hl, st, rfl⟩
  · exact Or.inr rfl

/-- The loose band id is always empty. -/
private theorem lepf_loose_id {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {loose : List String} {start : Int} :
    (looseBand boxes s axis sp loose start).id = "" := by
  unfold looseBand
  split <;> rfl

/-- A lane's model box has group role and no parent. -/
private theorem lepf_lanesOf_mem {boxes : List ModelBox} {lane : String}
    (h : lane ∈ lanesOf boxes) :
    ∃ mb ∈ boxes, mb.role = .group ∧ mb.parent = "" ∧ mb.id = lane := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, hpred⟩ := List.mem_filter.mp hx
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hrole, hpar⟩ := hpred
  exact ⟨x, hxb, beq_iff_eq.mp hrole, beq_iff_eq.mp hpar, rfl⟩

/-- A lane is in its own lane (`inLane`), under model nodup. -/
private theorem lepf_inLane_self {boxes : List ModelBox}
    (hn : (boxes.map (fun b => b.id)).Nodup) {lane : String}
    (hl : lane ∈ lanesOf boxes) : inLane boxes lane lane = true := by
  obtain ⟨mb, hmbMem, hmbRole, hmbPar, hmbId⟩ := lepf_lanesOf_mem hl
  have hfind : boxes.find? (fun b => b.id == lane) = some mb := by
    have hEq : (fun b : ModelBox => b.id == lane) = (fun b : ModelBox => b.id == mb.id) := by
      funext b
      rw [hmbId]
    rw [hEq]
    exact modelFind?_eq_self hn hmbMem
  unfold inLane laneOf laneOfAux
  rw [hfind]
  simp [hmbPar, hmbRole]

/-- A lane id is a member of its own lane band, under model nodup. -/
private theorem lepf_self_mem {boxes : List ModelBox}
    (hn : (boxes.map (fun b => b.id)).Nodup) {s : Scene} {axis : Axis}
    {sp : Spacing} {lane : String} {st : Int}
    (hl : lane ∈ lanesOf boxes) :
    lane ∈ (laneBand boxes s axis sp lane st).members := by
  have hIn : inLane boxes lane lane = true := lepf_inLane_self hn hl
  obtain ⟨mb, hmbMem, _, _, hmbId⟩ := lepf_lanesOf_mem hl
  have hFilt : mb ∈ (boxes.filter fun b => inLane boxes b.id lane) := by
    rw [List.mem_filter]
    refine ⟨hmbMem, ?_⟩
    have hEq : inLane boxes mb.id lane = inLane boxes lane lane := by rw [hmbId]
    rw [hEq, hIn]
  have hMemMap : lane ∈ ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id) :=
    List.mem_map.mpr ⟨mb, hFilt, hmbId⟩
  have hEqMem : (laneBand boxes s axis sp lane st).members =
      ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id) := rfl
  rw [hEqMem]
  exact hMemMap

/-- Existence from a filtered membership. -/
private theorem lepf_find?_ex {α : Type} (p : α → Bool) (l : List α) (a : α)
    (hm : a ∈ l) (hp : p a = true) : ∃ b, l.find? p = some b := by
  have hex : ∃ x, x ∈ l ∧ p x := ⟨a, hm, hp⟩
  have h := (List.find?_isSome).mpr hex
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
  exact ⟨b, hb⟩

/-- `find?` by id transports across an id-preserving box list change. -/
private theorem lepf_find_congr {l₁ l₂ : List Box} (hid : l₁.map (·.id) = l₂.map (·.id))
     (_hn : (l₂.map (·.id)).Nodup) {id : String} {b₁ : Box}
     (h₁ : l₁.find? (fun b => b.id == id) = some b₁) :
     ∃ b₂, l₂.find? (fun b => b.id == id) = some b₂ ∧ b₂.id = b₁.id := by
  have hmem : b₁ ∈ l₁ := lepf_found_mem h₁
  have hid₁ : b₁.id = id :=
    beq_iff_eq.mp (List.find?_some (p := fun b : Box => b.id == id) h₁)
  have hmap : b₁.id ∈ l₂.map (·.id) := by
    rw [← hid]
    exact List.mem_map.mpr ⟨b₁, hmem, rfl⟩
  obtain ⟨b₂, hmem₂, hid₂⟩ := List.mem_map.mp hmap
  have hpred₂ : (fun b : Box => b.id == id) b₂ = true := by
    show (b₂.id == id) = true
    rw [hid₂, hid₁]
    exact beq_self_eq_true id
  obtain ⟨b₂', hb₂'⟩ := lepf_find?_ex (fun b : Box => b.id == id) l₂ b₂ hmem₂ hpred₂
  have hlastid : b₂'.id = id :=
    beq_iff_eq.mp (List.find?_some (p := fun b : Box => b.id == id) hb₂')
  exact ⟨b₂', hb₂', by rw [hlastid, hid₁]⟩

/-- Membership transport through a uniform cross-shift box map. -/
private theorem lepf_shiftMap_mem {axis : Axis} {D : Box → Int} (l : List Box) :
    ∀ (l' : List Box),
    l.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant (D b)).rect axis b.rect } : Except LayoutError Box)) = .ok l' →
    ∀ b' ∈ l', ∃ b ∈ l, b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧
      b'.exclusive = b.exclusive ∧
      b'.rect = axis.withStart b.rect (axis.start b.rect + D b) ∧
      Axis.length axis b'.rect = Axis.length axis b.rect ∧
      axis.other.start b'.rect = axis.other.start b.rect ∧
      axis.other.length b'.rect = axis.other.length b.rect := by
  induction l with
  | nil =>
    intro l' h b' hb'
    have he : l' = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    simp at hb'
  | cons head tail ih =>
    intro l' h b' hb'
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := lepf_bind h
    obtain ⟨rest, hrest, h⟩ := lepf_bind h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    simp only [List.mem_cons] at hb'
    rcases hb' with rfl | hmem
    · obtain ⟨rect, hrect, hrfl⟩ := lepf_bind hfirst
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
      subst hrfl
      obtain ⟨w, hw, hrectEq, hval⟩ := moveConstant_rect_value hrect
      refine ⟨head, List.mem_cons.mpr (Or.inl rfl), rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · rw [hrectEq, hval]
      · rw [hrectEq, lepf_length_withStart]
      · rw [hrectEq]
        exact (lepf_rank_withStart (axis := axis) (r := head.rect) (w := w)).1
      · rw [hrectEq]
        exact (lepf_rank_withStart (axis := axis) (r := head.rect) (w := w)).2
    · obtain ⟨b, hbin, hid, hpar, hrole, hexcl, heq, hlen, hr1, hr2⟩ := ih _ hrest _ hmem
      exact ⟨b, List.mem_cons.mpr (Or.inr hbin), hid, hpar, hrole, hexcl, heq, hlen, hr1, hr2⟩

/-- Membership transport through `shiftAll`. -/
private theorem lepf_shiftAll_mem {axis : Axis} {delta : Int} {s s' : Scene}
    (h : shiftAll axis delta s = .ok s') :
    ∀ b' ∈ s'.boxes, ∃ b ∈ s.boxes, b'.id = b.id ∧ b'.parent = b.parent ∧
      b'.role = b.role ∧ b'.exclusive = b.exclusive ∧
      b'.rect = axis.withStart b.rect (axis.start b.rect + delta) ∧
      Axis.length axis b'.rect = Axis.length axis b.rect ∧
      axis.other.start b'.rect = axis.other.start b.rect ∧
      axis.other.length b'.rect = axis.other.length b.rect := by
  unfold shiftAll at h
  obtain ⟨boxes, hboxes, h⟩ := lepf_bind h
  obtain ⟨labels, hlabels, h⟩ := lepf_bind h
  obtain ⟨routes, hroutes, h⟩ := lepf_bind h
  obtain ⟨items, _hitems, h⟩ := lepf_bind h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  intro b' hb'
  obtain ⟨b, hbin, hid, hpar, hrole, hexcl, heq, hlen, hr1, hr2⟩ :=
    lepf_shiftMap_mem s.boxes boxes hboxes b' hb'
  exact ⟨b, hbin, hid, hpar, hrole, hexcl, heq, hlen, hr1, hr2⟩

/-- A box whose id differs from the replaced band survives `replaceFrame`. -/
private theorem lepf_replace_other {axis : Axis} {band₂ : Band} {s s' : Scene}
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
    obtain ⟨hi, hpred, _hfirst⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
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
private theorem lepf_fold_other {axis : Axis} {bands : List Band} {shifted pinned : Scene}
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
    obtain ⟨mid, hmid, hrest⟩ := lepf_bind hfold
    have hneHd : b.id ≠ hd.id := Ne.symm (hne hd (List.mem_cons.mpr (Or.inl rfl)))
    have hmid' : b ∈ mid.boxes := lepf_replace_other hmid hbin hneHd
    exact ih hmid' (fun bd hbd => hne bd (List.mem_cons.mpr (Or.inr hbd))) hrest

/-- The target lane box is placed by the fold over its band. -/
private theorem lepf_fold_places {axis : Axis} {bands : List Band} {shifted pinned : Scene}
    {band : Band} (hnodup : (bands.map (·.id)).Nodup) (hmem : band ∈ bands)
    (hfold : bands.foldlM (fun scene b => replaceFrame axis b scene) shifted = .ok pinned)
    (hb : ∃ b ∈ shifted.boxes, b.id = band.id) :
    ∃ b ∈ pinned.boxes, b.id = band.id ∧ axis.start b.rect = band.start ∧
      axis.length b.rect = band.thickness := by
  induction bands generalizing shifted with
  | nil => simp at hmem
  | cons hd rest ih =>
    rw [List.foldlM_cons] at hfold
    obtain ⟨mid, hmid, hrest⟩ := lepf_bind hfold
    rw [List.mem_cons] at hmem
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hfresh, hrestnd⟩ := hnodup
    rcases hmem with rfl | hmem
    · obtain ⟨b, hbin, hplace⟩ := replaceFrame_places_lane
        (axis := axis) (band := band) (s := shifted) (s' := mid) hmid hb
      obtain ⟨hFid, hFstart, hFlen⟩ := hplace
      have hne : ∀ bd ∈ rest, bd.id ≠ b.id := by
        intro bd hbd
        intro heq
        have hmem : band.id ∈ rest.map (·.id) :=
          List.mem_map.mpr ⟨bd, hbd, by rw [heq, hFid]⟩
        exact hfresh hmem
      have hkeep : b ∈ pinned.boxes :=
        lepf_fold_other (bands := rest) hbin hne hrest
      exact ⟨b, hkeep, hFid, hFstart, hFlen⟩
    · obtain ⟨b, hbin, hbid⟩ := hb
      have hneHd : b.id ≠ hd.id := by
        intro heq
        have hhd : hd.id ∈ rest.map (·.id) := by
          have hmemid : band.id ∈ rest.map (·.id) :=
            List.mem_map.mpr ⟨band, hmem, rfl⟩
          rw [← hbid, heq] at hmemid
          exact hmemid
        exact hfresh hhd
      have hmid' : b ∈ mid.boxes := lepf_replace_other hmid hbin hneHd
      exact ih hrestnd hmem hrest ⟨b, hmid', hbid⟩

/-- `layLanes` ids are exactly the lane list. -/
private theorem lepf_layLanes_ids (boxes : List ModelBox) (s : Scene) (axis : Axis)
    (sp : Spacing) (lanes : List String) (start : Int) :
    (layLanes boxes s axis sp lanes start).map (fun b => b.id) = lanes := by
  induction lanes generalizing start with
  | nil => rfl
  | cons lane rest ih =>
    have hhead : (laneBand boxes s axis sp lane start).id = lane := rfl
    simp only [layLanes, List.map_cons, hhead, ih]

/-- Lane ids are nonempty model ids. -/
private theorem lepf_lanes_ne_empty {boxes : List ModelBox}
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") {lane : String}
    (h : lane ∈ lanesOf boxes) : lane ≠ "" := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, _⟩ := List.mem_filter.mp hx
  exact hModelNoEmpty x hxb

/-- `layBands` ids are nodup when model ids are nodup and nonempty. -/
private theorem lepf_layBands_ids_nodup {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing}
    (hModelNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") :
    ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup := by
  have hLaneIds : ((layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id) =
      lanesOf boxes :=
    lepf_layLanes_ids _ _ _ _ _ _
  have hLaneNodup : ((layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id).Nodup := by
    rw [hLaneIds]
    exact lanesOf_nodup hModelNodup
  have hfresh : "" ∉ lanesOf boxes :=
    fun hmem => lepf_lanes_ne_empty hModelNoEmpty hmem rfl
  unfold layBands
  by_cases hl : (looseNodes boxes).isEmpty = true
  · simp only [hl, ↓reduceIte]
    exact hLaneNodup
  · simp only [hl, ↓reduceIte, Bool.false_eq_true, List.map_append, hLaneIds]
    have hsing : ∀ S : Int, (([looseBand boxes s axis sp (looseNodes boxes) S].map
        fun b => b.id) = [""]) := by
      intro S
      simp only [List.map_cons, List.map_nil, lepf_loose_id]
    simp only [hsing]
    rw [List.nodup_append]
    refine ⟨?_, (by simp : ([""] : List String).Nodup), ?_⟩
    · exact lanesOf_nodup hModelNodup
    · intro a ha b hb hEq
      rw [List.mem_singleton] at hb
      subst hb
      exact lepf_lanes_ne_empty hModelNoEmpty ha hEq

/-- A box whose id names no band survives a `replaceFrame` fold as the same element. -/
private theorem lepf_fold_untouched {axis : Axis} {bands : List Band} {shifted pinned : Scene}
    (hfold : bands.foldlM (fun scene band => replaceFrame axis band scene) shifted = .ok pinned)
    {b' : Box} (hb' : b' ∈ pinned.boxes) (hne : ∀ bd ∈ bands, bd.id ≠ b'.id) :
    b' ∈ shifted.boxes := by
  induction bands generalizing shifted with
  | nil =>
    have he : pinned = shifted := by
      simpa only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] using hfold.symm
    subst he
    exact hb'
  | cons hd rest ih =>
    rw [List.foldlM_cons] at hfold
    obtain ⟨mid, hmid, hrest⟩ := lepf_bind hfold
    have hbM : b' ∈ mid.boxes :=
      ih hrest (fun bd hbd => hne bd (List.mem_cons.mpr (Or.inr hbd)))
    have hneHd : hd.id ≠ b'.id := hne hd (List.mem_cons.mpr (Or.inl rfl))
    unfold replaceFrame at hmid
    cases hfind : shifted.boxes.findIdx? (fun b => b.id == hd.id) with
    | none =>
      simp only [hfind, Pure.pure, Except.pure, Except.ok.injEq] at hmid
      subst hmid
      exact hbM
    | some index =>
      obtain ⟨hi, hpred, _hfirst⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
      simp only [hfind] at hmid
      cases hstart : Measure.checkedI32 hd.start with
      | error e => simp [hstart, Bind.bind, Except.bind] at hmid
      | ok sv =>
        simp only [hstart, Bind.bind, Except.bind] at hmid
        cases hthick : Measure.checkedI32 hd.thickness with
        | error e => simp [hthick] at hmid
        | ok tv =>
          simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at hmid
          subst hmid
          obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hbM
          have hidx : (shifted.boxes[index]'hi).id = hd.id := beq_iff_eq.mp hpred
          have hne' : k ≠ index := by
            intro hkk
            subst hkk
            apply hneHd
            have hpid : ((shifted.boxes.mapIdx fun j b =>
                if j = k then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b)[k]'hk).id
                = hd.id := by
              rw [List.getElem_mapIdx]
              simp [hidx]
            exact hpid.symm
          have hlen : k < (shifted.boxes.mapIdx fun j b =>
              if j = index then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b).length := by
            simpa using hk
          have hlenS : k < shifted.boxes.length := by
            have hml : (shifted.boxes.mapIdx fun j b =>
                if j = index then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b).length
                = shifted.boxes.length :=
              List.length_mapIdx
            omega
          have heq : (shifted.boxes.mapIdx fun j b =>
              if j = index then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b)[k]'hlen =
              shifted.boxes[k]'hlenS := by
            rw [List.getElem_mapIdx]
            simp [hne']
          show ((shifted.boxes.mapIdx fun j b =>
              if j = index then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b)[k]'hlen
              ∈ shifted.boxes)
          rw [heq]
          exact List.getElem_mem hlenS

/-- Under id nodup, `findIdx?` by band id returns the position of the box. -/
private theorem lepf_findIdx_of_mem {l : List Box} (hnodup : (l.map (·.id)).Nodup)
    {band : Band} {k : Nat} (hk : k < l.length) (hid : (l[k]'hk).id = band.id) :
    l.findIdx? (fun b => b.id == band.id) = some k := by
  cases hfind : l.findIdx? (fun b => b.id == band.id) with
  | none =>
    have hfalse : ((l[k]'hk).id == band.id) = false :=
      List.findIdx?_eq_none_iff.mp hfind _ (List.getElem_mem hk)
    rw [hid] at hfalse
    simp at hfalse
  | some index =>
    obtain ⟨hi, hpred, _hfirst⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
    have hidx : (l[index]'hi).id = band.id := beq_iff_eq.mp hpred
    have hi' : index < (l.map fun b => b.id).length := by simpa using hi
    have hk' : k < (l.map fun b => b.id).length := by simpa using hk
    have e : (l.map fun b => b.id)[index]'hi' = (l.map fun b => b.id)[k]'hk' := by
      simp only [List.getElem_map]
      rw [hidx, hid]
    have hkk : index = k := List.Nodup.eq_of_getElem_eq hnodup hi' hk' e
    rw [← hkk]

/-- A found box is placed by `replaceFrame` with its own id, rank sizes and flag. -/
private theorem lepf_replace_found {axis : Axis} {band : Band} {shifted mid : Scene}
    (hmid : replaceFrame axis band shifted = .ok mid)
    {k : Nat} (hk : k < shifted.boxes.length)
    (hkd : shifted.boxes.findIdx? (fun b => b.id == band.id) = some k)
    {bS : Box} (hkart : shifted.boxes[k]'hk = bS) (hid : bS.id = band.id) :
    ∃ bM ∈ mid.boxes, bM.id = band.id ∧ bM.exclusive = bS.exclusive ∧
      axis.start bM.rect = band.start ∧ axis.length bM.rect = band.thickness ∧
      axis.other.start bM.rect = axis.other.start bS.rect ∧
      axis.other.length bM.rect = axis.other.length bS.rect := by
  unfold replaceFrame at hmid
  simp only [hkd] at hmid
  cases hstart : Measure.checkedI32 band.start with
  | error e => simp [hstart, Bind.bind, Except.bind] at hmid
  | ok sv =>
    simp only [hstart, Bind.bind, Except.bind] at hmid
    cases hthick : Measure.checkedI32 band.thickness with
    | error e => simp [hthick] at hmid
    | ok tv =>
      simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at hmid
      subst hmid
      have hlen : k < (shifted.boxes.mapIdx fun j b =>
          if j = k then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b).length := by
        simpa using hk
      have hsv : sv = band.start := checkedI32_ok hstart
      have htv : tv = band.thickness := checkedI32_ok hthick
      refine ⟨(shifted.boxes.mapIdx fun j b =>
          if j = k then ({ b with rect := placeRect axis sv tv b.rect } : Box) else b)[k]'hlen,
        List.getElem_mem hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.getElem_mapIdx, ↓reduceIte]
        show (shifted.boxes[k]'hk).id = band.id
        rw [hkart, hid]
      · simp only [List.getElem_mapIdx, ↓reduceIte]
        show (shifted.boxes[k]'hk).exclusive = bS.exclusive
        rw [hkart]
      · simp only [List.getElem_mapIdx, ↓reduceIte]
        show axis.start (placeRect axis sv tv (shifted.boxes[k]'hk).rect) = band.start
        have e1 : axis.start (placeRect axis sv tv (shifted.boxes[k]'hk).rect)
            = axis.start (axis.withStart (shifted.boxes[k]'hk).rect sv) := by
          unfold placeRect
          cases axis <;> rfl
        have e2 : axis.start (axis.withStart (shifted.boxes[k]'hk).rect sv) = sv := by
          cases axis <;> rfl
        rw [e1, e2, hsv]
      · simp only [List.getElem_mapIdx, ↓reduceIte]
        show axis.length (placeRect axis sv tv (shifted.boxes[k]'hk).rect) = band.thickness
        have e1 : axis.length (placeRect axis sv tv (shifted.boxes[k]'hk).rect)
            = axis.length (axis.withLength (axis.withStart (shifted.boxes[k]'hk).rect sv) tv) := rfl
        have e2 : axis.length (axis.withLength (axis.withStart (shifted.boxes[k]'hk).rect sv) tv)
            = tv := by
          cases axis <;> rfl
        rw [e1, e2, htv]
      · simp only [List.getElem_mapIdx, ↓reduceIte]
        show axis.other.start (placeRect axis sv tv (shifted.boxes[k]'hk).rect)
          = axis.other.start bS.rect
        rw [hkart]
        exact (lepf_rank_placeRect).1
      · simp only [List.getElem_mapIdx, ↓reduceIte]
        show axis.other.length (placeRect axis sv tv (shifted.boxes[k]'hk).rect)
          = axis.other.length bS.rect
        rw [hkart]
        exact (lepf_rank_placeRect).2

/-- A band-id box is placed by the fold, keeping its source rank sizes and flag. -/
private theorem lepf_fold_places_full {axis : Axis} {bands : List Band} {shifted pinned : Scene}
    (hBnodup : (bands.map (·.id)).Nodup)
    (hSnodup : (shifted.boxes.map (·.id)).Nodup)
    (hfold : bands.foldlM (fun scene band => replaceFrame axis band scene) shifted = .ok pinned)
    {band : Band} (hmem : band ∈ bands)
    {bS : Box} (hbS : bS ∈ shifted.boxes) (hid : bS.id = band.id) :
    ∃ b' ∈ pinned.boxes, b'.id = band.id ∧ b'.exclusive = bS.exclusive ∧
      axis.start b'.rect = band.start ∧ axis.length b'.rect = band.thickness ∧
      axis.other.start b'.rect = axis.other.start bS.rect ∧
      axis.other.length b'.rect = axis.other.length bS.rect := by
  induction bands generalizing shifted bS with
  | nil => simp at hmem
  | cons hd rest ih =>
    rw [List.foldlM_cons] at hfold
    obtain ⟨mid, hmid, hrest⟩ := lepf_bind hfold
    simp only [List.map_cons, List.nodup_cons] at hBnodup
    obtain ⟨hfresh, hrestnd⟩ := hBnodup
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · obtain ⟨k, hk, hkart⟩ := List.mem_iff_getElem.mp hbS
      have hkd := lepf_findIdx_of_mem hSnodup hk (by rw [hkart, hid])
      obtain ⟨bM, hbM, hMid, hMexcl, hMstart, hMlen, hMo1, hMo2⟩ :=
        lepf_replace_found hmid hk hkd hkart hid
      have hBcons : ((band :: rest).map (·.id)).Nodup :=
        List.nodup_cons.mpr ⟨hfresh, hrestnd⟩
      obtain ⟨bP, hbP, hPid, hPstart, hPlen⟩ :=
        lepf_fold_places hBcons (List.mem_cons.mpr (Or.inl rfl)) hfold ⟨bS, hbS, hid⟩
      have hneP : ∀ bd ∈ rest, bd.id ≠ bP.id := by
        intro bd hbd heq
        have hcon : band.id ∈ (rest.map fun b => b.id) :=
          List.mem_map.mpr ⟨bd, hbd, by rw [heq, hPid]⟩
        exact hfresh hcon
      have hbPm : bP ∈ mid.boxes := lepf_fold_untouched hrest hbP hneP
      have hMnodup : (mid.boxes.map (·.id)).Nodup := by
        have hmm := (replaceFrame_boxes_maps hmid).1
        rw [hmm]
        exact hSnodup
      have heq : bM = bP :=
        lepf_nodup_eq (fun b : Box => b.id) hMnodup hbM hbPm (hMid.trans hPid.symm)
      subst heq
      exact ⟨bM, hbP, hPid, hMexcl, hMstart, hMlen, hMo1, hMo2⟩
    · have hneHd : bS.id ≠ hd.id := by
        intro heq
        have hcon : hd.id ∈ (rest.map fun b => b.id) := by
          have hmemid : band.id ∈ (rest.map fun b => b.id) :=
            List.mem_map.mpr ⟨band, hmem, rfl⟩
          rw [← hid, heq] at hmemid
          exact hmemid
        exact hfresh hcon
      have hbM : bS ∈ mid.boxes := lepf_replace_other hmid hbS hneHd
      have hMnodup : (mid.boxes.map (·.id)).Nodup := by
        have hmm := (replaceFrame_boxes_maps hmid).1
        rw [hmm]
        exact hSnodup
      exact ih hrestnd hMnodup hrest hmem hbM hid

/-- Spacing titles and clearances are strictly positive on both profiles. -/
private theorem lepf_spacing_pos {p : Profile} {sp : Spacing}
    (h : spacingOf p = .ok sp) : 0 < sp.title ∧ 0 < sp.clear := by
  cases p with
  | vector =>
    unfold spacingOf LayoutConst.slot LayoutConst.line_h LayoutConst.cluster_pad
      LayoutConst.Pair.get at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨by decide, by decide⟩
  | cell =>
    unfold spacingOf LayoutConst.slot LayoutConst.line_h LayoutConst.cluster_pad
      LayoutConst.Pair.get at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨by decide, by decide⟩

/-- A uniform cross-shift keeps box sizes: every shifted box has a same-sized source. -/
private theorem lepf_shiftAll_sizes {axis : Axis} {delta : Int} {s s' : Scene}
    (h : shiftAll axis delta s = .ok s')
    {b' : Box} (hb' : b' ∈ s'.boxes) :
    ∃ b ∈ s.boxes, b.id = b'.id ∧ b.exclusive = b'.exclusive ∧
      b.rect.w = b'.rect.w ∧ b.rect.h = b'.rect.h := by
  obtain ⟨b, hbin, hid, _hpar, _hrole, hexcl, _hrect, hlen, _hr1, hr2⟩ :=
    lepf_shiftAll_mem h b' hb'
  refine ⟨b, hbin, hid.symm, hexcl.symm, ?_, ?_⟩
  · cases hax : axis with
    | x => rw [hax] at hlen hr2; exact hlen.symm
    | y => rw [hax] at hlen hr2; exact hr2.symm
  · cases hax : axis with
    | x => rw [hax] at hlen hr2; exact hr2.symm
    | y => rw [hax] at hlen hr2; exact hlen.symm

/-- A nonempty-id band is thick: lane bands add positive title and clearance. -/
private theorem lepf_lane_thick_pos {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {o : Options} {band : Band}
    (hmem : band ∈ layBands boxes s axis sp (lanesOf boxes))
    (hne : band.id ≠ "")
    (hsp : spacingOf o.profile = .ok sp) :
    0 < band.thickness := by
  obtain hband := lepf_band_cases hmem
  rcases hband with ⟨lane, _hlane, st, rfl⟩ | hloose
  · have htc := lepf_spacing_pos hsp
    have hform : (laneBand boxes s axis sp lane st).thickness = sp.title + 2 * sp.clear +
        (((bounds (contentValues boxes s axis lane
          ((boxes.filter fun b => inLane boxes b.id lane).map (·.id)))).getD (st, st)).2 -
        (((bounds (contentValues boxes s axis lane
          ((boxes.filter fun b => inLane boxes b.id lane).map (·.id)))).getD (st, st)).1)) := rfl
    rw [hform]
    cases hbe : bounds (contentValues boxes s axis lane
        ((boxes.filter fun b => inLane boxes b.id lane).map (·.id))) with
    | none => simp; all_goals omega
    | some p =>
      obtain ⟨lo, hi⟩ := p
      have hle := bounds_le hbe
      simp; all_goals omega
  · have hid0 : band.id = "" := by rw [hloose]; exact lepf_loose_id
    exact absurd hid0 hne

/-- Every exclusive box of the applyPin output is positive. -/
private theorem lepf_pinned0_positive {boxes : List ModelBox} {o : Options} {s : Scene}
    {axis : Axis} {sp : Spacing} {bands : List Band} {shifted p0 : Scene}
    (hPosS : ExclusivePositive s.layoutDump)
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (hShNodup : (shifted.boxes.map (·.id)).Nodup)
    (hPnodup : (p0.boxes.map (·.id)).Nodup)
    (hBnodup : (bands.map (·.id)).Nodup)
    (hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    (hsp : spacingOf o.profile = .ok sp)
    (hboxes : s.boxes.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant ((buildPin axis bands s).boxDelta b.id)).rect (buildPin axis bands s).axis b.rect } : Except LayoutError Box)) = .ok shifted.boxes)
    (hfold : bands.foldlM (fun scene band => replaceFrame (buildPin axis bands s).axis band scene) shifted = .ok p0) :
    ∀ bR ∈ p0.boxes, bR.exclusive = true → 0 < bR.rect.w ∧ 0 < bR.rect.h := by
  intro bR hbR hexcl
  have hpinAxis : (buildPin axis bands s).axis = axis := rfl
  rw [hpinAxis] at hboxes hfold
  by_cases hex : ∃ band ∈ bands, band.id = bR.id
  · obtain ⟨band, hmem, hid⟩ := hex
    have hmemid : band.id ∈ shifted.boxes.map (·.id) := by
      have h1 : bR.id ∈ p0.boxes.map (·.id) := List.mem_map.mpr ⟨bR, hbR, rfl⟩
      have h2 := (foldReplaceFrame_all bands axis _ _ hfold).2.1
      rw [h2, ← hid] at h1
      exact h1
    obtain ⟨bS, hbS, hSid⟩ := List.mem_map.mp hmemid
    obtain ⟨bP, hbP, hPid, hPexcl, _hPstart, hPlen, _hPo1, hPo2⟩ :=
      lepf_fold_places_full hBnodup hShNodup hfold hmem hbS hSid
    have heq : bR = bP :=
      lepf_nodup_eq (fun b : Box => b.id) hPnodup hbR hbP (by show bR.id = bP.id; rw [← hid, hPid])
    obtain ⟨b0, hb0, _h0id, _hp, _hr, h0excl, _hrect, _h0len, _ho1, h0o2⟩ :=
      lepf_shiftMap_mem s.boxes shifted.boxes hboxes bS hbS
    have hb0excl : b0.exclusive = true := by
      have hRtrue : bR.exclusive = true := hexcl
      rw [heq, hPexcl, h0excl] at hRtrue
      exact hRtrue
    have hpos := hPosS b0 hb0 hb0excl
    have hrank : 0 < axis.other.length bP.rect := by
      rw [hPo2, h0o2]
      cases axis with
      | x => exact hpos.2
      | y => exact hpos.1
    have hne : bR.id ≠ "" := by
      have hmem0 : bR.id ∈ s.boxes.map (·.id) := by
        have h1 : bR.id ∈ p0.boxes.map (·.id) := List.mem_map.mpr ⟨bR, hbR, rfl⟩
        have h2 := (foldReplaceFrame_all bands axis _ _ hfold).2.1
        have h3 := (pinShiftBoxes_maps s.boxes (buildPin axis bands s)
          (buildPin axis bands s).axis shifted.boxes hboxes).2.1
        rw [h2, h3] at h1
        exact h1
      intro heq0
      rw [heq0] at hmem0
      obtain ⟨b, hbin, hbid⟩ := List.mem_map.mp hmem0
      exact hNoEmpty b hbin hbid
    have hthick : 0 < band.thickness := by
      have hmemL : band ∈ layBands boxes s axis sp (lanesOf boxes) := by
        rw [← hbands]; exact hmem
      have hneB : band.id ≠ "" := by rw [hid]; exact hne
      exact lepf_lane_thick_pos hmemL hneB hsp
    have hcross : 0 < axis.length bP.rect := by rw [hPlen]; exact hthick
    have hSizes : 0 < bP.rect.w ∧ 0 < bP.rect.h := by
      cases hax : axis with
      | x => rw [hax] at hcross hrank; exact ⟨hcross, hrank⟩
      | y => rw [hax] at hcross hrank; exact ⟨hrank, hcross⟩
    rw [heq]
    exact hSizes
  · have hne : ∀ bd ∈ bands, bd.id ≠ bR.id := by
      intro bd hbd heq
      exact hex ⟨bd, hbd, heq⟩
    have hbS : bR ∈ shifted.boxes := lepf_fold_untouched hfold hbR hne
    obtain ⟨b0, hb0, _h0id, _hp, _hr, h0excl, _hrect, h0len, _ho1, h0o2⟩ :=
      lepf_shiftMap_mem s.boxes shifted.boxes hboxes bR hbS
    have hb0excl : b0.exclusive = true := by rw [← h0excl]; exact hexcl
    have hpos := hPosS b0 hb0 hb0excl
    have hW : 0 < bR.rect.w := by
      cases hax : axis with
      | x => rw [hax] at h0len; have hwEq : bR.rect.w = b0.rect.w := h0len; rw [hwEq]; exact hpos.1
      | y => rw [hax] at h0o2; have hwEq : bR.rect.w = b0.rect.w := h0o2; rw [hwEq]; exact hpos.1
    have hH : 0 < bR.rect.h := by
      cases hax : axis with
      | x => rw [hax] at h0o2; have hhEq : bR.rect.h = b0.rect.h := h0o2; rw [hhEq]; exact hpos.2
      | y => rw [hax] at h0len; have hhEq : bR.rect.h = b0.rect.h := h0len; rw [hhEq]; exact hpos.2
    exact ⟨hW, hH⟩

/-- Frames of `pinLanes` have ordered old cross ranges (discharges `hLen`). -/
theorem pinBands_framesLenNonneg {boxes : List ModelBox} {o : Options} {s pinned : Scene}
    (hBoxNonneg : ∀ b ∈ s.boxes, 0 ≤ (Axis.ofDirection o.direction).length b.rect)
    (_hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (_hpin : pinBands boxes o s = .ok pinned)
    (sp : Spacing) (_hsp : spacingOf o.profile = .ok sp) :
    ∀ f ∈ laneFrames (Axis.ofDirection o.direction)
      (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s, 0 ≤ f.length := by
  intro f hf
  obtain ⟨band, _hband, b, hbin, _hid, _hnear, hlen, _hfind⟩ := lepf_frame_mem hf
  rw [hlen]
  exact hBoxNonneg b hbin
/-- Pinned-to-applyPin length transport: every pinned box has a same-length source. -/
private theorem lepf_pin_length_trans {axis : Axis}
    {pinned stripScene origin routed p0 : Scene}
    (hgrowB : pinned.boxes = stripScene.boxes)
    (hstripB : stripScene.boxes = origin.boxes)
    (hrouteB : routed.boxes = p0.boxes)
    (horig : restoreOrigin axis routed = .ok origin) :
    ∀ fb ∈ pinned.boxes, ∃ bR ∈ p0.boxes, bR.id = fb.id ∧
      axis.length bR.rect = axis.length fb.rect := by
  intro fb hfb
  have h1 : fb ∈ origin.boxes := by
    rw [hgrowB, hstripB] at hfb
    exact hfb
  obtain hO | ⟨delta, _hpos, hshift⟩ := restoreOrigin_cases horig
  · rw [hO, hrouteB] at h1
    exact ⟨fb, h1, rfl, rfl⟩
  · obtain ⟨bS, hbS, hid, _hexcl, _hw, _hh, _hrect, hlen, _ho1, _ho2⟩ :=
      lepf_shiftAll_mem hshift fb h1
    rw [hrouteB] at hbS
    exact ⟨bS, hbS, hid.symm, hlen.symm⟩

/-- A lane member's old range sits inside its band: near/length arithmetic. -/
private theorem lepf_frame_fit_arith {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {o : Options} {lane : String} {st : Int} {box0 : Box}
    (hsp : spacingOf o.profile = .ok sp)
    (hmem : box0.id ∈ (laneBand boxes s axis sp lane st).members)
    (hfind : s.boxes.find? (fun b' => b'.id == box0.id) = some box0) :
    0 ≤ axis.start box0.rect + (laneBand boxes s axis sp lane st).shift -
      (laneBand boxes s axis sp lane st).start ∧
    axis.start box0.rect + (laneBand boxes s axis sp lane st).shift -
      (laneBand boxes s axis sp lane st).start + axis.length box0.rect ≤
      (laneBand boxes s axis sp lane st).thickness := by
  obtain ⟨ht, hc⟩ := spacing_of_nonneg hsp
  have hwithin := laneMember_within (ht := ht) (hc := hc) (hmem := hmem) (hfind := hfind)
  have h1 : (laneBand boxes s axis sp lane st).start ≤
      axis.start box0.rect + (laneBand boxes s axis sp lane st).shift := hwithin.1
  have h2 : axis.start box0.rect + axis.length box0.rect +
      (laneBand boxes s axis sp lane st).shift ≤
      (laneBand boxes s axis sp lane st).start +
        (laneBand boxes s axis sp lane st).thickness := hwithin.2
  omega


/-- Exclusive boxes keep positive sizes through `pinBands` (discharges `hPos`). -/
theorem pinBands_exclusivePositive {boxes : List ModelBox} {o : Options} {s pinned : Scene}
    (hPosS : ExclusivePositive s.layoutDump)
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (hBoxesNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "")
    (hsNodup : (s.boxes.map fun b => b.id).Nodup)
    (hpin : pinBands boxes o s = .ok pinned) :
    ExclusivePositive pinned.layoutDump := by
  intro b' hb' hexcl
  have hb0 : b' ∈ pinned.boxes := hb'
  by_cases hlanes : lanesOf boxes = []
  · have hno : pinBands boxes o s = .ok s := pinBands_no_lanes hlanes
    have heq : pinned = s := Except.ok.inj (hpin.symm.trans hno)
    subst heq
    exact hPosS b' hb0 hexcl
  · obtain ⟨sp, axis, bands, p0, routed, origin, strip, stripScene,
      hsp, _haxis, hbands, happ, hroute, horig, _hstrip, hstripEq, hgrow⟩ :=
      pinBands_spec hlanes hpin
    obtain ⟨shiftedBoxes, _sl, _sr, _si, hboxes, _hl, _hr, _hi, hfold⟩ :=
      applyPin_shifted happ
    have hShNodup : (shiftedBoxes.map (·.id)).Nodup := by
      have hmap := (pinShiftBoxes_maps s.boxes (buildPin axis bands s)
        (buildPin axis bands s).axis shiftedBoxes hboxes).2.1
      rw [hmap]
      exact hsNodup
    have hBnodup : (bands.map (·.id)).Nodup := by
      have hll := lepf_layBands_ids_nodup (boxes := boxes) (s := s) (axis := axis) (sp := sp)
        hBoxesNodup hModelNoEmpty
      rw [hbands]
      exact hll
    have hPnodup : (p0.boxes.map (·.id)).Nodup := by
      have hmap := (foldReplaceFrame_all bands (buildPin axis bands s).axis _ _ hfold).2.1
      rw [hmap]
      exact hShNodup
    have hgrowB : pinned.boxes = stripScene.boxes := (growCanvas_frame hgrow).1
    have hstripB : stripScene.boxes = origin.boxes := relocateLabels_boxes hstripEq
    have hrouteB : routed.boxes = p0.boxes := (rerouteBands_frame hroute).1
    obtain ⟨bR, hbR, _hRid, hRexcl, hRw, hRh⟩ :
        ∃ bR ∈ p0.boxes, bR.id = b'.id ∧ bR.exclusive = b'.exclusive ∧
        bR.rect.w = b'.rect.w ∧ bR.rect.h = b'.rect.h := by
      have h1 : b' ∈ pinned.boxes := hb0
      rw [hgrowB, hstripB] at h1
      obtain hO | ⟨delta, _hpos, hshift⟩ := restoreOrigin_cases horig
      · rw [hO, hrouteB] at h1
        exact ⟨b', h1, rfl, rfl, rfl, rfl⟩
      · obtain ⟨bS, hbS, hid, hexclS, hw, hh⟩ := lepf_shiftAll_sizes hshift h1
        rw [hrouteB] at hbS
        exact ⟨bS, hbS, hid, hexclS, hw, hh⟩
    have hRexcl : bR.exclusive = true := by rw [hRexcl]; exact hexcl
    have hRpos :=
      lepf_pinned0_positive hPosS hNoEmpty hShNodup hPnodup hBnodup hbands hsp
        hboxes hfold bR hbR hRexcl
    rw [← hRw, ← hRh]
    exact hRpos

/-- Each lane old range sits inside its stretched frame (discharges `hFit`). -/
theorem pinBands_framesFit {boxes : List ModelBox} {o : Options} {s pinned : Scene}
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (hBoxesNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "")
    (hsNodup : (s.boxes.map fun b => b.id).Nodup)
    (hpin : pinBands boxes o s = .ok pinned)
    (sp : Spacing) (hsp : spacingOf o.profile = .ok sp) :
    FramesFit (Axis.ofDirection o.direction)
      (laneFrames (Axis.ofDirection o.direction)
        (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
      pinned.layoutDump := by
  intro f hf fb hfb
  have hfb' : pinned.boxes.find? (fun b => b.id == f.id) = some fb := hfb
  have hfbmem : fb ∈ pinned.boxes := List.mem_of_find?_eq_some hfb'
  have hfbid : fb.id = f.id :=
    beq_iff_eq.mp (List.find?_some (p := fun b : Box => b.id == f.id) hfb')
  obtain ⟨band, hmem, box0, hbox0, hid, hnear, hlen, hfind⟩ := lepf_frame_mem hf
  have hfbBand : fb.id = band.id := by rw [hfbid, ← hid]
  obtain hband := lepf_band_cases hmem
  rcases hband with ⟨lane, hlane, st, hbandEq⟩ | hloose
  · have h0lane : box0.id = lane := by
      have heq := beq_iff_eq.mp (List.find?_some (p := fun b : Box => b.id == band.id) hfind)
      rw [hbandEq] at heq
      exact heq
    have hmem0 : box0.id ∈ (laneBand boxes s (Axis.ofDirection o.direction) sp lane st).members := by
      rw [h0lane]
      exact lepf_self_mem hBoxesNodup hlane
    have hfind0 : s.boxes.find? (fun b' => b'.id == box0.id) = some box0 := by
      have hbb0 : band.id = box0.id := by
        rw [hbandEq]
        exact h0lane.symm
      simpa only [hbb0] using hfind
    have harith := lepf_frame_fit_arith (hsp := hsp) (hmem := hmem0) (hfind := hfind0)
    by_cases hlanes : lanesOf boxes = []
    · rw [hlanes] at hlane
      simp at hlane
    · obtain ⟨sp', axis', bands, p0, routed, origin, strip, stripScene,
        _hsp', haxis, hbands, happ, hroute, horig, _hstrip, hstripEq, hgrow⟩ :=
        pinBands_spec hlanes hpin
      have hspeq : sp' = sp := Except.ok.inj (_hsp'.symm.trans hsp)
      rw [hspeq] at hbands hroute
      subst haxis
      have hpinAxis : (buildPin (Axis.ofDirection o.direction) bands s).axis =
          Axis.ofDirection o.direction := rfl
      obtain ⟨shiftedBoxes, _sl, _sr, _si, hboxes, _hl, _hr, _hi, hfold⟩ :=
        applyPin_shifted happ
      rw [hpinAxis] at hfold hboxes
      have hShNodup : (shiftedBoxes.map (·.id)).Nodup := by
        have hmap := (pinShiftBoxes_maps s.boxes (buildPin (Axis.ofDirection o.direction) bands s)
          (buildPin (Axis.ofDirection o.direction) bands s).axis shiftedBoxes hboxes).2.1
        rw [hmap]
        exact hsNodup
      have hBnodup : (bands.map (·.id)).Nodup := by
        have hll := lepf_layBands_ids_nodup (boxes := boxes) (s := s)
          (axis := Axis.ofDirection o.direction) (sp := sp) hBoxesNodup hModelNoEmpty
        rw [hbands]
        exact hll
      have hPnodup : (p0.boxes.map (·.id)).Nodup := by
        have hmap := (foldReplaceFrame_all bands (Axis.ofDirection o.direction) _ _ hfold).2.1
        rw [hmap]
        exact hShNodup
      have hgrowB : pinned.boxes = stripScene.boxes := (growCanvas_frame hgrow).1
      have hstripB : stripScene.boxes = origin.boxes := relocateLabels_boxes hstripEq
      have hrouteB : routed.boxes = p0.boxes := (rerouteBands_frame hroute).1
      obtain ⟨bR, hbR, hRid, hRlen⟩ :
          ∃ bR ∈ p0.boxes, bR.id = fb.id ∧
          (Axis.ofDirection o.direction).length bR.rect =
            (Axis.ofDirection o.direction).length fb.rect := by
        have h1 : fb ∈ pinned.boxes := hfbmem
        rw [hgrowB, hstripB] at h1
        obtain hO | ⟨delta, _hpos, hshift⟩ := restoreOrigin_cases horig
        · rw [hO, hrouteB] at h1
          exact ⟨fb, h1, rfl, rfl⟩
        · obtain ⟨bS, hbS, hidS, _he, _hw, _hh, _hr, hlenS, _ho1, _ho2⟩ :=
            lepf_shiftAll_mem hshift fb h1
          rw [hrouteB] at hbS
          exact ⟨bS, hbS, hidS.symm, hlenS.symm⟩
      have hRidB : bR.id = band.id := by rw [hRid, hfbid, hid.symm]
      rw [← hbands] at hmem
      have hmemid : band.id ∈ shiftedBoxes.map (·.id) := by
        have h1 : bR.id ∈ p0.boxes.map (·.id) := List.mem_map.mpr ⟨bR, hbR, rfl⟩
        have h2 := (foldReplaceFrame_all bands (Axis.ofDirection o.direction) _ _ hfold).2.1
        rw [h2, hRidB] at h1
        exact h1
      obtain ⟨bS, hbS, hSid⟩ := List.mem_map.mp hmemid
      obtain ⟨bP, _hbP, _hPid, _hPexcl, _hPstart, hPlen, _hPo1, _hPo2⟩ :=
        lepf_fold_places_full hBnodup hShNodup hfold hmem hbS hSid
      have heq : bR = bP :=
        lepf_nodup_eq (fun b : Box => b.id) hPnodup hbR _hbP
          (by show bR.id = bP.id; rw [hRidB, _hPid])
      have hFlen : (Axis.ofDirection o.direction).length fb.rect = band.thickness := by
        rw [← hRlen, heq]
        exact hPlen
      rw [hnear, hlen, hFlen, hbandEq]
      exact harith
  · have hid0 : band.id = "" := by rw [hloose]; exact lepf_loose_id
    have h0id : box0.id = "" := by
      have heq := beq_iff_eq.mp (List.find?_some (p := fun b : Box => b.id == band.id) hfind)
      rw [heq, hid0]
    exact absurd h0id (hNoEmpty box0 hbox0)

end LaneBands
end Layered
end Elegant

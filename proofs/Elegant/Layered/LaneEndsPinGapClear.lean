import Elegant.Layered.LaneEndsPinFacts
import Elegant.Layered.LaneEndsClauses
import Elegant.Layered.LaneBandsCoverage
import Elegant.Layered.LaneBandsLabelClauses
import Elegant.Layered.LaneBandsPhaseFacts
import Elegant.Layered.LaneBandsCoverageProof
import Elegant.Layered.LaneBandsBoxClausesExecuted
import Elegant.Layered.LaneBands

set_option autoImplicit false

/-! Gap clearance after `pinBands`: the strip between an old and a new frame
side holds no exclusive box interior. Members of the same lane sit inside the
old range through the base `C3` ancestor chain; other lanes are ordered off the
band by tiling; loose members start at or beyond the loose band. The shift of a
box equals the shift of its covering band (`LaneGapShiftCover`, supplied by the
swimlane assembly like `PinBoxCoverage`); ancestor containment is proved by
fuel induction on `ancestors.go` with generalization before induction. -/

namespace Elegant
namespace Layered
namespace LaneBands

/-- Bind decomposition for `Except`. -/
private theorem lgc_bind {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- Cross length is unchanged by a cross start move. -/
private theorem lgc_length_withStart {axis : Axis} {r : Rect} {w : Int} :
    axis.length (axis.withStart r w) = axis.length r := by
  cases axis <;> rfl

/-- Cross start of a cross start move is the new value. -/
private theorem lgc_start_withStart {axis : Axis} {r : Rect} {w : Int} :
    axis.start (axis.withStart r w) = w := by
  cases axis <;> rfl

/-- Rank coordinates are unchanged by a cross start move. -/
private theorem lgc_rank_withStart {axis : Axis} {r : Rect} {w : Int} :
    axis.other.start (axis.withStart r w) = axis.other.start r ∧
      axis.other.length (axis.withStart r w) = axis.other.length r := by
  cases axis <;> constructor <;> rfl

/-- Rank coordinates are unchanged by `placeRect`. -/
private theorem lgc_rank_placeRect {axis : Axis} {start thickness : Int} {r : Rect} :
    axis.other.start (placeRect axis start thickness r) =
      axis.other.start r ∧
      axis.other.length (placeRect axis start thickness r) =
        axis.other.length r := by
  cases axis <;> unfold placeRect Axis.withStart Axis.withLength Axis.start
    Axis.length Axis.other <;> constructor <;> rfl

/-- Membership transport through a uniform cross-shift box map. -/
private theorem lgc_shiftMap_mem {axis : Axis} {D : Box → Int} (l : List Box) :
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
    obtain ⟨first, hfirst, h⟩ := lgc_bind h
    obtain ⟨rest, hrest, h⟩ := lgc_bind h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    simp only [List.mem_cons] at hb'
    rcases hb' with rfl | hmem
    · obtain ⟨rect, hrect, hrfl⟩ := lgc_bind hfirst
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
      subst hrfl
      obtain ⟨w, hw, hrectEq, hval⟩ := moveConstant_rect_value hrect
      refine ⟨head, List.mem_cons.mpr (Or.inl rfl), rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · rw [hrectEq, hval]
      · rw [hrectEq, lgc_length_withStart]
      · rw [hrectEq]
        exact (lgc_rank_withStart (axis := axis) (r := head.rect) (w := w)).1
      · rw [hrectEq]
        exact (lgc_rank_withStart (axis := axis) (r := head.rect) (w := w)).2
    · obtain ⟨b, hbin, hid, hpar, hrole, hexcl, heq, hlen, hr1, hr2⟩ := ih _ hrest _ hmem
      exact ⟨b, List.mem_cons.mpr (Or.inr hbin), hid, hpar, hrole, hexcl, heq, hlen, hr1, hr2⟩

/-- Membership transport through `shiftAll`. -/
private theorem lgc_shiftAll_mem {axis : Axis} {delta : Int} {s s' : Scene}
    (h : shiftAll axis delta s = .ok s') :
    ∀ b' ∈ s'.boxes, ∃ b ∈ s.boxes, b'.id = b.id ∧ b'.parent = b.parent ∧
      b'.role = b.role ∧ b'.exclusive = b.exclusive ∧
      b'.rect = axis.withStart b.rect (axis.start b.rect + delta) ∧
      Axis.length axis b'.rect = Axis.length axis b.rect ∧
      axis.other.start b'.rect = axis.other.start b.rect ∧
      axis.other.length b'.rect = axis.other.length b.rect := by
  unfold shiftAll at h
  obtain ⟨boxes, hboxes, h⟩ := lgc_bind h
  obtain ⟨labels, hlabels, h⟩ := lgc_bind h
  obtain ⟨routes, hroutes, h⟩ := lgc_bind h
  obtain ⟨items, _hitems, h⟩ := lgc_bind h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  intro b' hb'
  exact lgc_shiftMap_mem s.boxes boxes hboxes b' hb'

/-- A box whose id differs from the replaced band survives `replaceFrame`. -/
private theorem lgc_replace_other {axis : Axis} {band₂ : Band} {s s' : Scene}
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
private theorem lgc_fold_other {axis : Axis} {bands : List Band} {shifted pinned : Scene}
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
    obtain ⟨mid, hmid, hrest⟩ := lgc_bind hfold
    have hneHd : b.id ≠ hd.id := Ne.symm (hne hd (List.mem_cons.mpr (Or.inl rfl)))
    have hmid' : b ∈ mid.boxes := lgc_replace_other hmid hbin hneHd
    exact ih hmid' (fun bd hbd => hne bd (List.mem_cons.mpr (Or.inr hbd))) hrest
/-- The target lane box is placed by the fold over its band. -/
private theorem lgc_fold_places {axis : Axis} {bands : List Band} {shifted pinned : Scene}
    {band : Band} (hnodup : (bands.map (·.id)).Nodup) (hmem : band ∈ bands)
    (hfold : bands.foldlM (fun scene b => replaceFrame axis b scene) shifted = .ok pinned)
    (hb : ∃ b ∈ shifted.boxes, b.id = band.id) :
    ∃ b ∈ pinned.boxes, b.id = band.id ∧ axis.start b.rect = band.start ∧
      axis.length b.rect = band.thickness := by
  induction bands generalizing shifted with
  | nil => simp at hmem
  | cons hd rest ih =>
    rw [List.foldlM_cons] at hfold
    obtain ⟨mid, hmid, hrest⟩ := lgc_bind hfold
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
        lgc_fold_other (bands := rest) hbin hne hrest
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
      have hmid' : b ∈ mid.boxes := lgc_replace_other hmid hbin hneHd
      exact ih hrestnd hmem hrest ⟨b, hmid', hbid⟩

/-- Every emitted frame comes from a band with a found scene box. -/
private theorem lgc_frame_mem {axis : Axis} {bands : List Band} {s : Scene}
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

/-- A band of `layBands` is a lane band or the trailing loose band. -/
private theorem lgc_band_cases {boxes : List ModelBox} {s : Scene} {axis : Axis}
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
private theorem lgc_loose_id {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {loose : List String} {start : Int} :
    (looseBand boxes s axis sp loose start).id = "" := by
  unfold looseBand
  split <;> rfl

/-- Every pair in a band chunk carries the band shift. -/
private theorem lgc_chunk_mem_snd (bid : String) (bshift : Int) (members : List String)
    (e : String × Int)
    (h : e ∈ ((bid, bshift) :: members.map fun m => (m, bshift))) : e.2 = bshift := by
  simp only [List.mem_cons, List.mem_map] at h
  rcases h with rfl | ⟨m, _, rfl⟩
  · rfl
  · rfl

/-- A band chunk lookup finds the shift exactly for covering ids. -/
private theorem lgc_chunk_find_map (bid : String) (bshift : Int) (members : List String)
    (id : String) :
    ((((bid, bshift) :: members.map fun m => (m, bshift)).find? (fun e => e.1 == id)).map (·.2)) =
      if bid == id || members.contains id then some bshift else none := by
  by_cases hbid : (bid == id) = true
  · have hfind : ((bid, bshift) :: members.map fun m => (m, bshift)).find? (fun e => e.1 == id) =
        some (bid, bshift) := by
        simp only [List.find?_cons, hbid]
    simp only [hfind, Option.map_some]
    have hcond : (bid == id || members.contains id) = true := by
      simp only [hbid, Bool.true_or]
    simp only [hcond, ite_true]
  · have hbidF : (bid == id) = false := by
      cases hb : (bid == id) with
      | true => exact absurd hb hbid
      | false => rfl
    by_cases hmem : members.contains id = true
    · have hcond : (bid == id || members.contains id) = true := by
        simp only [hbidF, hmem, Bool.or_true]
      simp only [hcond, ite_true]
      have hmem' : id ∈ members := List.contains_iff_mem.mp hmem
      have hin : (id, bshift) ∈ ((bid, bshift) :: members.map fun m => (m, bshift)) :=
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨id, hmem', rfl⟩)
      have hmeq : (((id, bshift)).1 == id) = true := beq_self_eq_true id
      have hne : (((bid, bshift) :: members.map fun m => (m, bshift)).find? (fun e => e.1 == id)) ≠
          none := by
        intro hnone
        have hcon := List.find?_eq_none.mp hnone _ hin
        exact hcon hmeq
      obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hne
      have hmemE : e ∈ ((bid, bshift) :: members.map fun m => (m, bshift)) :=
        List.mem_of_find?_eq_some he
      have hsnd := lgc_chunk_mem_snd bid bshift members e hmemE
      rw [he]
      simp only [Option.map_some, hsnd]
    · have hmemF : members.contains id = false := by
        cases hb : members.contains id with
        | true => exact absurd hb hmem
        | false => rfl
      have hcond : (bid == id || members.contains id) = false := by
        simp only [hbidF, hmemF, Bool.or_self]
      simp only [hcond]
      have hnone : ((bid, bshift) :: members.map fun m => (m, bshift)).find? (fun e => e.1 == id) =
          none := by
        rw [List.find?_eq_none]
        intro e he
        simp only [List.mem_cons, List.mem_map] at he
        rcases he with rfl | ⟨m, hm, rfl⟩
        · show ¬ (((bid, bshift).1 == id) = true)
          simp only [hbidF]
          exact Bool.false_ne_true
        · show ¬ (((m, bshift).1 == id) = true)
          have hme : m ≠ id := by
            intro hme
            subst hme
            have ht : members.contains m = true :=
              List.contains_iff_mem.mpr hm
            rw [ht] at hmemF
            exact Bool.noConfusion hmemF
          have hfalse : (m == id) = false := by
            cases hb : (m == id) with
            | true => exact absurd (beq_iff_eq.mp hb) hme
            | false => rfl
          simp only [hfalse]
          exact Bool.false_ne_true
      simp [hnone]

/-- The pin delta of an id is the band shift of its covering band. -/
private theorem lgc_pinBoxDelta_eq (axis : Axis) (bands : List Band) (s : Scene)
    (id : String) :
    (buildPin axis bands s).boxDelta id = bandShift bands id := by
  unfold buildPin Pin.boxDelta bandShift
  simp only
  induction bands with
  | nil => rfl
  | cons b rest ih =>
    rw [List.flatMap_cons, List.find?_append, Option.map_or]
    by_cases hcond : (b.id == id || b.members.contains id) = true
    · have hchunk : (((b.id, b.shift) :: b.members.map fun m => (m, b.shift)).find?
          (fun e => e.1 == id)).map (·.2) = some b.shift := by
        have hmap := lgc_chunk_find_map b.id b.shift b.members id
        simp only [hcond] at hmap
        exact hmap
      rw [hchunk, Option.some_or]
      have hfind : (b :: rest).find? (fun b => b.id == id || b.members.contains id) = some b := by
        simp only [List.find?_cons, hcond]
      simp only [hfind, Option.map_some, Option.getD_some]
    · have hcondF : (b.id == id || b.members.contains id) = false := by
        cases hb : (b.id == id || b.members.contains id) with
        | true => exact absurd hb hcond
        | false => rfl
      have hchunk : (((b.id, b.shift) :: b.members.map fun m => (m, b.shift)).find?
          (fun e => e.1 == id)).map (·.2) = none := by
        have hmap := lgc_chunk_find_map b.id b.shift b.members id
        simp only [hcondF] at hmap
        exact hmap
      rw [hchunk, Option.none_or]
      have hfind : (b :: rest).find? (fun b => b.id == id || b.members.contains id) =
          rest.find? (fun b => b.id == id || b.members.contains id) := by
        simp only [List.find?_cons, hcondF]
      rw [hfind]
      exact ih

/-- Injectivity on a nodup image list. -/
private theorem lgc_nodup_eq {α β : Type} [BEq β] [LawfulBEq β] (g : α → β)
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


/-- `layLanes` ids are exactly the lane list. -/
private theorem lgc_layLanes_ids (boxes : List ModelBox) (s : Scene) (axis : Axis)
    (sp : Spacing) (lanes : List String) (start : Int) :
    (layLanes boxes s axis sp lanes start).map (fun b => b.id) = lanes := by
  induction lanes generalizing start with
  | nil => rfl
  | cons lane rest ih =>
    have hhead : (laneBand boxes s axis sp lane start).id = lane := rfl
    simp only [layLanes, List.map_cons, hhead, ih]

/-- Lane ids are nonempty model ids. -/
private theorem lgc_lanes_ne_empty {boxes : List ModelBox}
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") {lane : String}
    (h : lane ∈ lanesOf boxes) : lane ≠ "" := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, _⟩ := List.mem_filter.mp hx
  exact hModelNoEmpty x hxb

/-- `layBands` ids are nodup when model ids are nodup and nonempty. -/
private theorem lgc_layBands_ids_nodup {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing}
    (hModelNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") :
    ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup := by
  have hLaneIds : ((layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id) =
      lanesOf boxes :=
    lgc_layLanes_ids _ _ _ _ _ _
  have hLaneNodup : ((layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id).Nodup := by
    rw [hLaneIds]
    exact lanesOf_nodup hModelNodup
  have hfresh : "" ∉ lanesOf boxes :=
    fun hmem => lgc_lanes_ne_empty hModelNoEmpty hmem rfl
  unfold layBands
  by_cases hl : (looseNodes boxes).isEmpty = true
  · simp only [hl, ↓reduceIte]
    exact hLaneNodup
  · simp only [hl, ↓reduceIte, Bool.false_eq_true, List.map_append, hLaneIds]
    have hsing : ∀ S : Int, (([looseBand boxes s axis sp (looseNodes boxes) S].map
        fun b => b.id) = [""]) := by
      intro S
      simp only [List.map_cons, List.map_nil, lgc_loose_id]
    simp only [hsing]
    rw [List.nodup_append]
    refine ⟨?_, (by simp : ([""] : List String).Nodup), ?_⟩
    · exact lanesOf_nodup hModelNodup
    · intro a ha b hb hEq
      rw [List.mem_singleton] at hb
      subst hb
      exact lgc_lanes_ne_empty hModelNoEmpty ha hEq

/-- Shift residual for gap clearance: every scene box moves by the shift of the
band that covers it. This has the shape of `PinBoxCoverage` (membership plus
the shift equation) and is supplied by the swimlane assembly for the executed
run, where it follows from the unique covering band; it is strictly narrower
than `GapClear`, which compares pinned frame intervals against every
exclusive box. -/
def LaneGapShiftCover (boxes : List ModelBox) (s : Scene) (axis : Axis)
    (sp : Spacing) : Prop :=
  ∀ b ∈ s.boxes, ∀ band ∈ layBands boxes s axis sp (lanesOf boxes),
    band.id = b.id ∨ b.id ∈ band.members →
    bandShift (layBands boxes s axis sp (lanesOf boxes)) b.id = band.shift

/-- An ancestor's frame contains the descendant's frame, from base `C3` and the
lane scene shape. Fuel induction on `ancestors.go` with every id-dependent
variable generalized before induction. -/
private theorem lgc_ancestor_contained {s : Scene}
    (hsNodup : (s.boxes.map fun b => b.id).Nodup)
    (hShape : LaneSceneShape s)
    (hC3 : Validator.C3 s.layoutDump)
    {x p : Box} (hx : x ∈ s.boxes) (hp : p ∈ s.boxes)
    (h : p.id ∈ s.layoutDump.ancestors x.id) : p.rect.Contained x.rect := by
  have key : ∀ fuel x, x ∈ s.boxes → ∀ p ∈ s.boxes,
      p.id ∈ LayoutDump.ancestors.go s.layoutDump fuel x.id →
        p.rect.Contained x.rect := by
    intro fuel
    induction fuel with
    | zero => intro x hx p hp hmem; simp [LayoutDump.ancestors.go] at hmem
    | succ fuel ih =>
      intro x hx p hp hmem
      have hxbox : s.layoutDump.box? x.id = some x :=
        sceneFind?_eq_self hsNodup hx
      by_cases hpar : x.parent = ""
      · simp [LayoutDump.ancestors.go, hxbox, hpar] at hmem
      · obtain ⟨pb, hbmem, hbpid⟩ : ∃ pb ∈ s.boxes, pb.id = x.parent := by
          have hparent : x.parent ∈ s.boxes.map (·.id) := by
            rcases hShape.2 x hx with he | hm
            · exact absurd he hpar
            · exact hm
          obtain ⟨b, hb, hbE⟩ := List.mem_map.mp hparent
          exact ⟨b, hb, hbE⟩
        have hpbbox : s.layoutDump.box? x.parent = some pb := by
          have hfind := sceneFind?_eq_self hsNodup hbmem
          rw [← hbpid]
          exact hfind
        simp only [LayoutDump.ancestors.go, hxbox, hpar, ↓reduceIte,
          List.mem_cons] at hmem
        rcases hmem with hpid | htail
        · have hpid' : p.id = x.parent := hpid
          have hppb : p = pb :=
            lgc_nodup_eq (fun b : Box => b.id) hsNodup hp hbmem
              (by rw [hbpid]; exact hpid')
          rw [hppb]
          exact hC3 x hx hpar pb hpbbox
        · have hgo : LayoutDump.ancestors.go s.layoutDump fuel x.parent =
              LayoutDump.ancestors.go s.layoutDump fuel pb.id := by rw [hbpid]
          rw [hgo] at htail
          have hinner := ih pb hbmem p hp htail
          have houter := hC3 x hx hpar pb hpbbox
          exact Rect.Contained.trans hinner houter
  have hgo : s.layoutDump.ancestors x.id =
      LayoutDump.ancestors.go s.layoutDump s.layoutDump.boxes.length x.id := rfl
  rw [hgo] at h
  exact key s.layoutDump.boxes.length x hx p hp h

/-- A lane's model box has group role and no parent. -/
private theorem lgc_lanesOf_mem {boxes : List ModelBox} {lane : String}
    (h : lane ∈ lanesOf boxes) :
    ∃ mb ∈ boxes, mb.role = .group ∧ mb.parent = "" ∧ mb.id = lane := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, hpred⟩ := List.mem_filter.mp hx
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hrole, hpar⟩ := hpred
  exact ⟨x, hxb, beq_iff_eq.mp hrole, beq_iff_eq.mp hpar, rfl⟩

/-- A lane is in its own lane (`inLane`), under model nodup. -/
private theorem lgc_inLane_self {boxes : List ModelBox}
    (hn : (boxes.map (fun b => b.id)).Nodup) {lane : String}
    (hl : lane ∈ lanesOf boxes) : inLane boxes lane lane = true := by
  obtain ⟨mb, hmbMem, hmbRole, hmbPar, hmbId⟩ := lgc_lanesOf_mem hl
  have hfind : boxes.find? (fun b => b.id == lane) = some mb := by
    have hEq : (fun b : ModelBox => b.id == lane) = (fun b => b.id == mb.id) := by
      funext b
      rw [hmbId]
    rw [hEq]
    exact modelFind?_eq_self hn hmbMem
  unfold inLane laneOf laneOfAux
  rw [hfind]
  simp [hmbPar, hmbRole]

/-- A lane id is a member of its own lane band, under model nodup. -/
private theorem lgc_self_mem {boxes : List ModelBox}
    (hn : (boxes.map (fun b => b.id)).Nodup) {s : Scene} {axis : Axis}
    {sp : Spacing} {lane : String} {st : Int}
    (hl : lane ∈ lanesOf boxes) :
    lane ∈ (laneBand boxes s axis sp lane st).members := by
  have hIn : inLane boxes lane lane = true := lgc_inLane_self hn hl
  obtain ⟨mb, hmbMem, _, _, hmbId⟩ := lgc_lanesOf_mem hl
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

/-- A box named like its nonempty band is a member of that band. -/
private theorem lgc_id_mem_of_nodup {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {bands : List Band} {band : Band} {b : Box}
    (hModelNodup : (boxes.map (fun b => b.id)).Nodup)
    (hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    (hbandMem : band ∈ bands) (hbandNe : band.id ≠ "")
    (hbid : b.id = band.id) : b.id ∈ band.members := by
  have hCases := layBands_mem_cases (boxes := boxes) (s := s) (axis := axis) (sp := sp)
    (lanes := lanesOf boxes) (band := band) (by rw [← hbands]; exact hbandMem)
  rcases hCases with hLane | hLoose
  · obtain ⟨lane, hlaneMem, st, rfl⟩ := layLanes_mem_lane hLane
    have hIn : inLane boxes lane lane = true := lgc_inLane_self hModelNodup hlaneMem
    have hMemMap : lane ∈ ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id) := by
      obtain ⟨mb, hmbMem, _, _, hmbId⟩ := lgc_lanesOf_mem hlaneMem
      have hFilt : mb ∈ (boxes.filter fun b => inLane boxes b.id lane) := by
        rw [List.mem_filter]
        refine ⟨hmbMem, ?_⟩
        have hEq : inLane boxes mb.id lane = inLane boxes lane lane := by rw [hmbId]
        rw [hEq, hIn]
      exact List.mem_map.mpr ⟨mb, hFilt, hmbId⟩
    have hEqMem : (laneBand boxes s axis sp lane st).members =
        ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id) := rfl
    have hMemMap2 : lane ∈ (laneBand boxes s axis sp lane st).members := by
      rw [hEqMem]
      exact hMemMap
    have hBandId : (laneBand boxes s axis sp lane st).id = lane := rfl
    have hBidLane : b.id = lane := by rw [hbid, hBandId]
    rw [hBidLane]
    exact hMemMap2
  · exfalso
    have hId : (looseBand boxes s axis sp (looseNodes boxes)
        (firstLaneStart s (lanesOf boxes) axis +
          (List.map (fun b => b.thickness)
            (layLanes boxes s axis sp (lanesOf boxes)
              (firstLaneStart s (lanesOf boxes) axis))).sum)).id = "" :=
      lgc_loose_id
    exact hbandNe (by rw [hLoose, hId])

/-- Thickness sums are non-negative. -/
private theorem lgc_sum_thickness_nonneg (bands : List Band)
    (h : ∀ b ∈ bands, 0 ≤ b.thickness) : 0 ≤ (bands.map fun b => b.thickness).sum := by
  induction bands with
  | nil => simp
  | cons hd tl ih =>
    have hhd : 0 ≤ hd.thickness := h hd (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ b ∈ tl, 0 ≤ b.thickness := by
      intro b hb
      exact h b (List.mem_cons.mpr (Or.inr hb))
    simp only [List.map_cons, List.sum_cons]
    have := ih htl
    omega

/-- Every band of a non-negative tiling ends at or before the tiling end. -/
private theorem lgc_tiled_end_le {start : Int} {bands : List Band}
    (h : Tiled start bands) (hnonneg : ∀ b ∈ bands, 0 ≤ b.thickness)
    {c : Band} (hmem : c ∈ bands) :
    c.start + c.thickness ≤ start + (bands.map fun b => b.thickness).sum := by
  induction bands generalizing start with
  | nil => simp at hmem
  | cons b bs ih =>
    obtain ⟨hstart, htail⟩ := h
    rw [List.mem_cons] at hmem
    have hbpos : 0 ≤ b.thickness := hnonneg b (List.mem_cons.mpr (Or.inl rfl))
    have htailNonneg : ∀ x ∈ bs, 0 ≤ x.thickness := by
      intro x hx
      exact hnonneg x (List.mem_cons.mpr (Or.inr hx))
    have hsumNonneg := lgc_sum_thickness_nonneg bs htailNonneg
    rcases hmem with rfl | hmem
    · simp only [List.map_cons, List.sum_cons]
      omega
    · have hle := ih (start := start + b.thickness) htail htailNonneg hmem
      simp only [List.map_cons, List.sum_cons] at hle ⊢
      omega

/-- Every lane band ends at or before the loose band start. -/
private theorem lgc_lane_end_le_loose {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} (ht : 0 ≤ sp.title) (hc : 0 ≤ sp.clear)
    {L : Band}
    (hmem : L ∈ layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis)) :
    L.start + L.thickness ≤ firstLaneStart s (lanesOf boxes) axis +
      (((layLanes boxes s axis sp (lanesOf boxes)
        (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.thickness)).sum := by
  exact lgc_tiled_end_le (layLanes_tiled boxes s axis sp (lanesOf boxes) _)
    (layLanes_thickness_nonneg boxes s axis sp (lanesOf boxes) _ ht hc) hmem

/-- Every box of a `replaceFrame` fold is either placed over its band or an
untouched shifted box. -/
private theorem lgc_fold_cases {axis : Axis} {bands : List Band} {shifted p0 : Scene}
    (hfold : bands.foldlM (fun scene band => replaceFrame axis band scene) shifted
      = .ok p0)
    {b' : Box} (hb' : b' ∈ p0.boxes) :
    (∃ band ∈ bands, b'.id = band.id ∧ axis.start b'.rect = band.start ∧
      axis.length b'.rect = band.thickness) ∨
    (b' ∈ shifted.boxes) := by
  induction bands generalizing shifted with
  | nil =>
    have he : p0 = shifted := by
      simpa only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq]
        using hfold.symm
    subst he
    exact Or.inr hb'
  | cons hd rest ih =>
    rw [List.foldlM_cons] at hfold
    obtain ⟨mid, hmid, hrest⟩ := lgc_bind hfold
    have hmid' := ih hrest
    rcases hmid' with ⟨band, hmem, hid, hstart, hlen⟩ | hmem
    · exact Or.inl ⟨band, List.mem_cons.mpr (Or.inr hmem), hid, hstart, hlen⟩
    · unfold replaceFrame at hmid
      cases hfind : shifted.boxes.findIdx? (fun b => b.id == hd.id) with
      | none =>
        simp only [hfind, Pure.pure, Except.pure, Except.ok.injEq] at hmid
        subst hmid
        exact Or.inr hmem
      | some index =>
        obtain ⟨hi, hpred, _hfirst⟩ :=
          List.findIdx?_eq_some_iff_getElem.mp hfind
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
            have hidx : (shifted.boxes[index]'hi).id = hd.id := beq_iff_eq.mp hpred
            obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hmem
            by_cases hkk : k = index
            · subst hkk
              have hsv : sv = hd.start := checkedI32_ok hstart
              have htv : tv = hd.thickness := checkedI32_ok hthick
              refine Or.inl ⟨hd, List.mem_cons.mpr (Or.inl rfl), ?_, ?_, ?_⟩
              · simp only [List.getElem_mapIdx, ↓reduceIte]
                show (shifted.boxes[k]'hi).id = hd.id
                exact hidx
              · simp only [List.getElem_mapIdx, ↓reduceIte]
                show axis.start (placeRect axis sv tv (shifted.boxes[k]'hi).rect)
                  = hd.start
                have e1 : axis.start (placeRect axis sv tv (shifted.boxes[k]'hi).rect)
                    = axis.start (axis.withStart (shifted.boxes[k]'hi).rect sv) := by
                  unfold placeRect
                  cases axis <;> rfl
                have e2 : axis.start (axis.withStart (shifted.boxes[k]'hi).rect sv)
                    = sv := by
                  cases axis <;> rfl
                rw [e1, e2, hsv]
              · simp only [List.getElem_mapIdx, ↓reduceIte]
                show axis.length (placeRect axis sv tv (shifted.boxes[k]'hi).rect)
                  = hd.thickness
                have e1 : axis.length (placeRect axis sv tv (shifted.boxes[k]'hi).rect)
                    = axis.length (axis.withLength
                      (axis.withStart (shifted.boxes[k]'hi).rect sv) tv) := rfl
                have e2 : axis.length (axis.withLength
                    (axis.withStart (shifted.boxes[k]'hi).rect sv) tv) = tv := by
                  cases axis <;> rfl
                rw [e1, e2, htv]
            · have hml : (shifted.boxes.mapIdx fun j b =>
                    if j = index then
                      ({ b with rect := placeRect axis sv tv b.rect } : Box) else b).length =
                    shifted.boxes.length := List.length_mapIdx
              have hlenS : k < shifted.boxes.length := hml ▸ hk
              have heq : (shifted.boxes.mapIdx fun j b =>
                  if j = index then
                    ({ b with rect := placeRect axis sv tv b.rect } : Box) else b)[k]'hk =
                  shifted.boxes[k]'hlenS := by
                rw [List.getElem_mapIdx]
                simp [hkk]
              rw [heq]
              exact Or.inr (List.getElem_mem hlenS)

/-- Every origin box is a routed box shifted by one shared delta. -/
private theorem lgc_origin_transport {axis : Axis} {routed origin : Scene}
    (horig : restoreOrigin axis routed = .ok origin) :
    ∃ D : Int, ∀ b' ∈ origin.boxes, ∃ b ∈ routed.boxes, b'.id = b.id ∧
      b'.exclusive = b.exclusive ∧
      b'.rect = axis.withStart b.rect (axis.start b.rect + D) ∧
      Axis.length axis b'.rect = Axis.length axis b.rect := by
  obtain hO | ⟨delta, _hpos, hshift⟩ := restoreOrigin_cases horig
  · refine ⟨0, fun b' hb' => ?_⟩
    rw [hO] at hb'
    have hws : axis.withStart b'.rect (axis.start b'.rect + 0) = b'.rect := by
      have e : axis.start b'.rect + 0 = axis.start b'.rect := by omega
      rw [e]
      cases axis <;> rfl
    exact ⟨b', hb', rfl, rfl, hws.symm, rfl⟩
  · refine ⟨delta, fun b' hb' => ?_⟩
    obtain ⟨b, hbin, hid, _hpar, _hrole, hexcl, heq, hlen, _hr1, _hr2⟩ :=
      lgc_shiftAll_mem hshift b' hb'
    exact ⟨b, hbin, hid, hexcl, heq, hlen⟩

/-- Every lane frame comes from a lane band with a same-named scene box. -/
private theorem lgc_frame_lane {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lanes : List String} {bands : List Band}
    (hbands : bands = layBands boxes s axis sp lanes)
    {f : LaneFrame} (hf : f ∈ laneFrames axis bands s)
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "") :
    ∃ lane ∈ lanes, ∃ st : Int, ∃ b0 ∈ s.boxes, ∃ band ∈ bands,
      band = laneBand boxes s axis sp lane st ∧ band.id = f.id ∧ b0.id = band.id ∧
      f.near = axis.start b0.rect + band.shift - band.start ∧
      f.length = axis.length b0.rect ∧ band.id ≠ "" := by
  obtain ⟨band, hmem, b0, hb0, hid, hnear, hlen, hfind⟩ := lgc_frame_mem hf
  have hid2 : b0.id = band.id :=
    beq_iff_eq.mp (List.find?_some (p := fun b : Box => b.id == band.id) hfind)
  have hcases := lgc_band_cases (boxes := boxes) (s := s) (axis := axis) (sp := sp)
    (lanes := lanes) (band := band) (by rw [← hbands]; exact hmem)
  rcases hcases with ⟨lane, hlane, st, rfl⟩ | hllo
  · exact ⟨lane, hlane, st, b0, hb0, _, hmem, rfl, hid, hid2, hnear, hlen,
      fun hcon => hNoEmpty b0 hb0 (hid2.trans hcon)⟩
  · have hid0 : band.id = "" := by rw [hllo]; exact lgc_loose_id
    exact absurd (hid2.trans hid0) (hNoEmpty b0 hb0)
/-- A same-band member sits inside the old frame range, through the base `C3`
ancestor chain. -/
private theorem lgc_same_band_clear {axis : Axis} {s : Scene}
    (hsNodup : (s.boxes.map fun b => b.id).Nodup)
    (hShape : LaneSceneShape s)
    (hC3 : Validator.C3 s.layoutDump)
    {f0 b0 : Box} (hf0 : f0 ∈ s.boxes) (hb0 : b0 ∈ s.boxes)
    (hanc : f0.id ∈ s.layoutDump.ancestors b0.id)
    {shift D lo hi bS bLen flen : Int}
    (hlo : lo = axis.start f0.rect + shift + D)
    (hhi : hi = lo + flen) (hflen : flen = axis.length f0.rect)
    (hbS : bS = axis.start b0.rect + shift + D)
    (hbLen : bLen = axis.length b0.rect) :
    lo ≤ bS ∧ bS + bLen ≤ hi := by
  have hcont := lgc_ancestor_contained hsNodup hShape hC3 hb0 hf0 hanc
  unfold Rect.Contained at hcont
  obtain ⟨hx1, hx2, hy1, hy2⟩ := hcont
  cases hax : axis with
  | x =>
    simp only [hax, Axis.start, Axis.length] at hlo hhi hflen hbS hbLen
    omega
  | y =>
    simp only [hax, Axis.start, Axis.length] at hlo hhi hflen hbS hbLen
    omega

/-- With no lanes there are no frames, so gap clearance holds vacuously. -/
private theorem lgc_gapClear_empty {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hlanes : lanesOf boxes = [])
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (hpin : pinBands boxes o s = .ok r)
    (sp : Spacing) (_hsp : spacingOf o.profile = .ok sp) :
    GapClear (Axis.ofDirection o.direction)
      (laneFrames (Axis.ofDirection o.direction)
        (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
      r.layoutDump := by
  have hr : r = s := by
    have hNo : pinBands boxes o s = .ok s := pinBands_no_lanes hlanes
    have := Except.ok.inj (hpin.symm.trans hNo)
    exact this
  rw [hr]
  intro f hf fb hfb b hb hexcl hne
  obtain ⟨band, hmem, b0, hb0, hid, hnear, hlen, hfind⟩ := lgc_frame_mem hf
  have hcases := lgc_band_cases (boxes := boxes) (s := s)
    (axis := Axis.ofDirection o.direction) (sp := sp) (lanes := lanesOf boxes)
    (band := band) hmem
  rcases hcases with ⟨lane, hlane, st, rfl⟩ | hllo
  · rw [hlanes] at hlane
    simp at hlane
  · have hid0 : band.id = "" := by rw [hllo]; exact lgc_loose_id
    have h0id : b0.id = "" := by
      have heq := beq_iff_eq.mp
        (List.find?_some (p := fun b : Box => b.id == band.id) hfind)
      rw [heq, hid0]
    exact absurd h0id (hNoEmpty b0 hb0)

/-- Pinned frame placement: a required frame sits over its band, shifted by the
shared restore delta. -/
private theorem lgc_frame_bundle {boxes : List ModelBox} {o : Options} {s r : Scene}
    {axis : Axis} {sp : Spacing} {bands : List Band} {p0 routed origin stripScene : Scene}
    {strip gap : Int} {bend : Int}
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (hsNodup : (s.boxes.map fun b => b.id).Nodup)
    (hBoxesNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "")
    (happ : applyPin (buildPin axis bands s) bands s = .ok p0)
    (hroute : rerouteBands axis sp bend bands (buildPin axis bands s) s.routes p0
      = .ok routed)
    (hgrow : growCanvas axis s.canvas stripScene = .ok r)
    (hstripEq : relocateLabels axis strip gap origin = .ok stripScene)
    (hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    (hpin : pinBands boxes o s = .ok r)
    (hsp : spacingOf o.profile = .ok sp)
    (haxis : axis = Axis.ofDirection o.direction)
    {D : Int}
    (hDtrans : ∀ b' ∈ origin.boxes, ∃ b ∈ routed.boxes, b'.id = b.id ∧
      b'.exclusive = b.exclusive ∧
      b'.rect = axis.withStart b.rect (axis.start b.rect + D) ∧
      Axis.length axis b'.rect = Axis.length axis b.rect)
    {f : LaneFrame} (hf : f ∈ laneFrames axis bands s)
    {fb : Box} (hfb : r.layoutDump.box? f.id = some fb) :
    ∃ Cb ∈ bands, ∃ f0 ∈ s.boxes,
      Cb.id = f.id ∧ f0.id = Cb.id ∧
      axis.start fb.rect = Cb.start + D ∧ axis.length fb.rect = Cb.thickness ∧
      f.near = axis.start f0.rect + Cb.shift - Cb.start ∧
      f.length = axis.length f0.rect ∧
      0 ≤ f.near ∧ f.near + f.length ≤ axis.length fb.rect ∧
      Cb ∈ layLanes boxes s axis sp (lanesOf boxes)
        (firstLaneStart s (lanesOf boxes) axis) ∧
      Cb.id ≠ "" := by
  have hf' : f ∈ laneFrames (Axis.ofDirection o.direction)
      (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s := by
    rw [← haxis, ← hbands]
    exact hf
  obtain ⟨lane, hlane, st, f0, hf0, Cb, hCbmem, hCbEq, hCbid, hf0id, hnear, hlen,
      hCbne⟩ := lgc_frame_lane hbands hf hNoEmpty
  have hpinAxis : (buildPin axis bands s).axis = axis := rfl
  obtain ⟨shiftedBoxes, _sl, _sr, _si, hboxes, _hl, _hr, _hi, hfold⟩ :=
    applyPin_shifted happ
  rw [hpinAxis] at hfold hboxes
  have hShNodup : (shiftedBoxes.map (·.id)).Nodup := by
    have hmap := (pinShiftBoxes_maps s.boxes (buildPin axis bands s)
      (buildPin axis bands s).axis shiftedBoxes hboxes).2.1
    rw [hmap]
    exact hsNodup
  have hBnodup : (bands.map (·.id)).Nodup := by
    have hll := lgc_layBands_ids_nodup (boxes := boxes) (s := s)
      (axis := axis) (sp := sp) hBoxesNodup hModelNoEmpty
    rw [hbands]
    exact hll
  have hPnodup : (p0.boxes.map (·.id)).Nodup := by
    have hmap := (foldReplaceFrame_all bands axis _ _ hfold).2.1
    rw [hmap]
    exact hShNodup
  have hShiftIds : shiftedBoxes.map (·.id) = s.boxes.map (·.id) :=
    (pinShiftBoxes_maps s.boxes (buildPin axis bands s) axis shiftedBoxes hboxes).2.1
  have hbS : ∃ bS ∈ shiftedBoxes, bS.id = Cb.id := by
    have hmem : Cb.id ∈ shiftedBoxes.map (·.id) := by
      rw [hShiftIds]
      exact List.mem_map.mpr ⟨f0, hf0, hf0id⟩
    obtain ⟨bS, hbS, hid⟩ := List.mem_map.mp hmem
    exact ⟨bS, hbS, hid⟩
  obtain ⟨bP, hbP, hPid, hPstart, hPlen⟩ :=
    lgc_fold_places hBnodup hCbmem hfold hbS
  have hFit := pinBands_framesFit hNoEmpty hBoxesNodup hModelNoEmpty hsNodup hpin sp hsp
  have hfit := hFit f hf' fb hfb
  have hgrowB : r.boxes = stripScene.boxes := (growCanvas_frame hgrow).1
  have hstripB : stripScene.boxes = origin.boxes := relocateLabels_boxes hstripEq
  have hrouteB : routed.boxes = p0.boxes := (rerouteBands_frame hroute).1
  have hfb' : r.boxes.find? (fun b => b.id == f.id) = some fb := hfb
  have hfbO : fb ∈ origin.boxes := by
    have hm : fb ∈ r.boxes := List.mem_of_find?_eq_some hfb'
    rw [hgrowB, hstripB] at hm
    exact hm
  obtain ⟨fR, hfRmem, hfid, _hexcl, hrect, hlenR⟩ := hDtrans fb hfbO
  have hfR0 : fR ∈ p0.boxes := by rw [← hrouteB]; exact hfRmem
  have hfbid : fb.id = f.id :=
    beq_iff_eq.mp (List.find?_some (p := fun b : Box => b.id == f.id) hfb')
  have heq : fR = bP :=
    lgc_nodup_eq (fun b : Box => b.id) hPnodup hfR0 hbP
      (by rw [← hfid, hfbid, ← hCbid, hPid])
  have hLay : Cb ∈ layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis) := by
    have hC := layBands_mem_cases (band := Cb) (by rw [← hbands]; exact hCbmem)
    rcases hC with hL | hO
    · exact hL
    · exfalso
      have hId : Cb.id = "" := by
        rw [hO]
        exact lgc_loose_id
      exact hCbne hId
  have hfit2 : f.near + f.length ≤ axis.length fb.rect := by
    rw [haxis]
    exact hfit.2
  refine ⟨Cb, hCbmem, f0, hf0, hCbid, hf0id, ?_, ?_, hnear, hlen, hfit.1,
    hfit2, hLay, hCbne⟩
  · have hS : axis.start fR.rect = Cb.start := by rw [heq]; exact hPstart
    rw [hrect, lgc_start_withStart] at ⊢
    omega
  · have hL : axis.length fR.rect = Cb.thickness := by rw [heq]; exact hPlen
    rw [hrect, lgc_length_withStart] at ⊢
    exact hL

/-- Pinned exclusive boxes are placed frames or shifted members. -/
private theorem lgc_box_bundle {boxes : List ModelBox} {_o : Options} {s r : Scene}
    {axis : Axis} {sp : Spacing} {bands : List Band} {p0 routed origin stripScene : Scene}
    {strip gap : Int} {bend : Int} {D : Int}
    (hcover : PinBoxCoverage boxes s axis sp)
    (hshift : LaneGapShiftCover boxes s axis sp)
    (happ : applyPin (buildPin axis bands s) bands s = .ok p0)
    (hroute : rerouteBands axis sp bend bands (buildPin axis bands s) s.routes p0
      = .ok routed)
    (hgrow : growCanvas axis s.canvas stripScene = .ok r)
    (hstripEq : relocateLabels axis strip gap origin = .ok stripScene)
    (hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    (hDtrans : ∀ b' ∈ origin.boxes, ∃ b ∈ routed.boxes, b'.id = b.id ∧
      b'.exclusive = b.exclusive ∧
      b'.rect = axis.withStart b.rect (axis.start b.rect + D) ∧
      Axis.length axis b'.rect = Axis.length axis b.rect)
    {b : Box} (hb : b ∈ r.boxes) (hexcl : b.exclusive = true) :
    (∃ Db ∈ bands, b.id = Db.id ∧ axis.start b.rect = Db.start + D ∧
      axis.length b.rect = Db.thickness) ∨
    (∃ b0 ∈ s.boxes, ∃ Db ∈ bands, (Db.id = b0.id ∨ b0.id ∈ Db.members) ∧
      b0.id = b.id ∧ b0.exclusive = true ∧
      axis.start b.rect = axis.start b0.rect + Db.shift + D ∧
      axis.length b.rect = axis.length b0.rect) := by
  obtain ⟨shiftedBoxes, _sl, _sr, _si, hboxes, _hl, _hr, _hi, hfold⟩ :=
    applyPin_shifted happ
  have hpinAxis : (buildPin axis bands s).axis = axis := rfl
  rw [hpinAxis] at hfold hboxes
  have hgrowB : r.boxes = stripScene.boxes := (growCanvas_frame hgrow).1
  have hstripB : stripScene.boxes = origin.boxes := relocateLabels_boxes hstripEq
  have hrouteB : routed.boxes = p0.boxes := (rerouteBands_frame hroute).1
  have hbO : b ∈ origin.boxes := by
    rw [hgrowB, hstripB] at hb
    exact hb
  obtain ⟨bR, hbRmem, hbid, hexclR, hrect, hlenR⟩ := hDtrans b hbO
  have hbR0 : bR ∈ p0.boxes := by rw [← hrouteB]; exact hbRmem
  have hexcl0 : bR.exclusive = true := by rw [← hexclR]; exact hexcl
  rcases lgc_fold_cases hfold hbR0 with ⟨Db, hDbmem, hidB, hstartB, hlenB⟩ | hshifted
  · refine Or.inl ⟨Db, hDbmem, ?_, ?_, ?_⟩
    · rw [hbid, hidB]
    · rw [hrect, lgc_start_withStart, hstartB]
    · rw [hrect, lgc_length_withStart, hlenB]
  · obtain ⟨b0, hb0mem, hid0, _hpar, _hrole, hexcl0', heq0, hlen0, _hr1, _hr2⟩ :=
      lgc_shiftMap_mem s.boxes shiftedBoxes hboxes bR hshifted
    have hst0 : axis.start bR.rect =
        axis.start b0.rect + (buildPin axis bands s).boxDelta b0.id := by
      rw [heq0, lgc_start_withStart]
    have hdelta : (buildPin axis bands s).boxDelta b0.id = bandShift bands b0.id :=
      lgc_pinBoxDelta_eq axis bands s b0.id
    obtain ⟨Db, hDbLay, hcov⟩ := hcover b0 hb0mem
    have hDbmem : Db ∈ bands := by rw [hbands]; exact hDbLay
    have hsh : bandShift bands b0.id = Db.shift := by
      rw [hbands]
      exact hshift b0 hb0mem Db hDbLay hcov
    refine Or.inr ⟨b0, hb0mem, Db, hDbmem, hcov, ?_, ?_, ?_, ?_⟩
    · exact hid0.symm.trans hbid.symm
    · rw [← hexcl0']; exact hexcl0
    · rw [hrect, lgc_start_withStart, hst0, hdelta, hsh]
    · rw [hrect, lgc_length_withStart, heq0, lgc_length_withStart]

/-- A member of a different band is off the old range: lane members by tiling,
loose members below the loose band under the lane bands. -/
private theorem lgc_gapClear_member_other {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} {bands : List Band}
    (hsNodup : (s.boxes.map fun b => b.id).Nodup)
    (hBoxesNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "")
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (ht : 0 ≤ sp.title) (hc : 0 ≤ sp.clear)
    (hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    (hTiled : Tiled (firstLaneStart s (lanesOf boxes) axis) bands)
    (hnonnegB : ∀ b ∈ bands, 0 ≤ b.thickness)
    {f : LaneFrame} {fb b b0 : Box} {Cb Db : Band} {D : Int}
    (hCbLay : Cb ∈ layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis))
    (hCbmem : Cb ∈ bands)
    (hS : axis.start fb.rect = Cb.start + D)
    (hF : axis.length fb.rect = Cb.thickness)
    (_hfit1 : 0 ≤ f.near) (_hfit2 : f.near + f.length ≤ axis.length fb.rect)
    (hb0mem : b0 ∈ s.boxes) (hDbmem : Db ∈ bands)
    (hcov : Db.id = b0.id ∨ b0.id ∈ Db.members)
    (hBs : axis.start b.rect = axis.start b0.rect + Db.shift + D)
    (hBl : axis.length b.rect = axis.length b0.rect)
    (hne2 : Cb ≠ Db) :
    (axis.start fb.rect + f.near ≤ axis.start b.rect ∧
      axis.start b.rect + axis.length b.rect ≤
      axis.start fb.rect + f.near + f.length) ∨
    axis.start b.rect + axis.length b.rect ≤ axis.start fb.rect ∨
    axis.start fb.rect + axis.length fb.rect ≤ axis.start b.rect := by
  have hfindB : s.boxes.find? (fun b' => b'.id == b0.id) = some b0 :=
    sceneFind?_eq_self hsNodup hb0mem
  have hDbCases := lgc_band_cases (boxes := boxes) (s := s) (axis := axis) (sp := sp)
    (lanes := lanesOf boxes) (band := Db) (by rw [← hbands]; exact hDbmem)
  rcases hDbCases with ⟨lane, hlane, st, rfl⟩ | hDbLoose
  · have hDbne : (laneBand boxes s axis sp lane st).id ≠ "" :=
      lgc_lanes_ne_empty hModelNoEmpty hlane
    have hmemB : b0.id ∈ (laneBand boxes s axis sp lane st).members := by
      rcases hcov with hEq | hMem
      · exact lgc_id_mem_of_nodup hBoxesNodup hbands hDbmem hDbne hEq.symm
      · exact hMem
    have hwithin := laneMember_within ht hc hmemB hfindB
    have hord := tiled_ordered hTiled hnonnegB hCbmem hDbmem hne2
    rcases hord with hle | hle
    · right; right; omega
    · right; left
      rw [hBs, hBl]
      omega
  · have hmemL : b0.id ∈ looseNodes boxes := by
      rcases hcov with hEq | hMem
      · exfalso
        have hDbId : Db.id = "" := by rw [hDbLoose]; exact lgc_loose_id
        exact hNoEmpty b0 hb0mem (hEq.symm.trans hDbId)
      · rw [hDbLoose, looseBand_members] at hMem
        exact hMem
    have hlower : Db.start ≤ axis.start b0.rect + Db.shift := by
      rw [hDbLoose]
      exact looseMember_lower hc hmemL hfindB
    have hL0 : Db.start = firstLaneStart s (lanesOf boxes) axis +
        (((layLanes boxes s axis sp (lanesOf boxes)
          (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.thickness)).sum := by
      rw [hDbLoose]
      exact looseBand_start _ _ _ _ _ _
    have hLend := lgc_lane_end_le_loose (boxes := boxes) (s := s)
      (axis := axis) (sp := sp) ht hc (L := Cb) hCbLay
    right; right
    omega

/-- Gap clearance at one frame, one exclusive box: placed frames by tiling,
same-band members through the ancestor chain, other members by band case. -/
private theorem lgc_gapClear_point {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} {bands : List Band}
    (hsNodup : (s.boxes.map fun b => b.id).Nodup)
    (hBoxesNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "")
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (hC3 : Validator.C3 s.layoutDump)
    (hShape : LaneSceneShape s)
    (ht : 0 ≤ sp.title) (hc : 0 ≤ sp.clear)
    (hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    (hTiled : Tiled (firstLaneStart s (lanesOf boxes) axis) bands)
    (hnonnegB : ∀ b ∈ bands, 0 ≤ b.thickness)
    (hParents : PinSceneParents boxes s bands)
    {f : LaneFrame} {fb b f0 : Box} {Cb : Band} {D : Int}
    (hCbmem : Cb ∈ bands)
    (hCbLay : Cb ∈ layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis))
    (hCbid : Cb.id = f.id) (hf0id : f0.id = Cb.id) (hf0 : f0 ∈ s.boxes)
    (hS : axis.start fb.rect = Cb.start + D)
    (hF : axis.length fb.rect = Cb.thickness)
    (hnear : f.near = axis.start f0.rect + Cb.shift - Cb.start)
    (hlen : f.length = axis.length f0.rect)
    (hfit1 : 0 ≤ f.near) (hfit2 : f.near + f.length ≤ axis.length fb.rect)
    (hCbne : Cb.id ≠ "")
    (hne : b.id ≠ f.id)
    (hFb : (∃ Db ∈ bands, b.id = Db.id ∧ axis.start b.rect = Db.start + D ∧
      axis.length b.rect = Db.thickness) ∨
      (∃ b0 ∈ s.boxes, ∃ Db ∈ bands, (Db.id = b0.id ∨ b0.id ∈ Db.members) ∧
        b0.id = b.id ∧
        axis.start b.rect = axis.start b0.rect + Db.shift + D ∧
        axis.length b.rect = axis.length b0.rect)) :
    (axis.start fb.rect + f.near ≤ axis.start b.rect ∧
      axis.start b.rect + axis.length b.rect ≤
      axis.start fb.rect + f.near + f.length) ∨
    axis.start b.rect + axis.length b.rect ≤ axis.start fb.rect ∨
    axis.start fb.rect + axis.length fb.rect ≤ axis.start b.rect := by
  rcases hFb with ⟨Db, hDbmem, hidB, hBsF, hBlF⟩ | ⟨b0, hb0mem, Db, hDbmem, hcov, hidB0, hBs, hBl⟩
  · by_cases hSame : Db = Cb
    · exfalso; exact hne (by rw [hidB, hSame, hCbid])
    · have hne2 : Cb ≠ Db := fun h => hSame h.symm
      have hord := tiled_ordered hTiled hnonnegB hCbmem hDbmem hne2
      rcases hord with hle | hle
      · right; right; omega
      · right; left; omega
  · by_cases hSame : Db = Cb
    · rw [hSame] at hcov hBs hDbmem
      have hneB : b0.id ≠ Cb.id := by
        intro hcon
        apply hne
        rw [← hidB0, hcon, hCbid]
      have hmemB : b0.id ∈ Cb.members := by
        rcases hcov with hEq | hMem
        · exact lgc_id_mem_of_nodup hBoxesNodup hbands hCbmem hCbne hEq.symm
        · exact hMem
      have hpar := hParents.2 Cb hCbmem ⟨f0, hf0, hf0id⟩ b0.id hmemB
      rcases hpar with hEq | hanc
      · exact absurd hEq hneB
      · rw [← hf0id] at hanc
        have hlo : axis.start fb.rect + f.near = axis.start f0.rect + Cb.shift + D := by
          omega
        have hhi : axis.start fb.rect + f.near + f.length
            = (axis.start fb.rect + f.near) + f.length := by omega
        have hinside := lgc_same_band_clear hsNodup hShape hC3 hf0 hb0mem hanc
          hlo hhi hlen hBs hBl
        exact Or.inl hinside
    · exact lgc_gapClear_member_other hsNodup hBoxesNodup hModelNoEmpty hNoEmpty ht hc
        hbands hTiled hnonnegB hCbLay hCbmem hS hF hfit1 hfit2 hb0mem hDbmem hcov
        hBs hBl (fun h => hSame h.symm)

/-- Gap clearance after `pinBands`: every out-of-scope exclusive box is inside
the old frame range or off the band. Same-band members sit inside through the
base `C3` ancestor chain; other lanes are ordered off by tiling; loose members
start at or beyond the loose band. The shift of a box equals the shift of its
covering band (`LaneGapShiftCover`), supplied by the swimlane assembly. -/
theorem pinBands_gapClear {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (hsNodup : (s.boxes.map fun b => b.id).Nodup)
    (hBoxesNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "")
    (hC3 : Validator.C3 s.layoutDump)
    (hShape : LaneSceneShape s)
    (sp : Spacing) (hsp : spacingOf o.profile = .ok sp)
    (hcover : PinBoxCoverage boxes s (Axis.ofDirection o.direction) sp)
    (hshift : LaneGapShiftCover boxes s (Axis.ofDirection o.direction) sp)
    (hParents : PinSceneParents boxes s
      (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)))
    (hpin : pinBands boxes o s = .ok r) :
    GapClear (Axis.ofDirection o.direction)
      (laneFrames (Axis.ofDirection o.direction)
        (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
      r.layoutDump := by
  by_cases hlanes : lanesOf boxes = []
  · exact lgc_gapClear_empty hlanes hNoEmpty hpin sp hsp
  · obtain ⟨sp', axis', bands, p0, routed, origin, strip, stripScene, hsp', haxis,
        hbands, happ, hroute, horig, _hstrip, hstripEq, hgrow⟩ :=
      pinBands_spec hlanes hpin
    have hspeq : sp' = sp := Except.ok.inj (hsp'.symm.trans hsp)
    subst sp'
    subst axis'
    obtain ⟨ht, hc⟩ := spacing_of_nonneg hsp
    have hTiled : Tiled (firstLaneStart s (lanesOf boxes) (Axis.ofDirection o.direction))
        bands := by
      rw [hbands]
      exact layBands_tiled boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)
    have hnonnegB : ∀ b ∈ bands, 0 ≤ b.thickness := by
      rw [hbands]
      exact layBands_thickness_nonneg boxes s (Axis.ofDirection o.direction) sp
        (lanesOf boxes) ht hc
    obtain ⟨D, hDtrans⟩ := lgc_origin_transport horig
    intro f hf fb hfb b hb hexcl hne
    have hb' : b ∈ r.boxes := hb
    rw [← hbands] at hf
    rw [← hbands] at hParents
    obtain ⟨Cb, hCbmem, f0, hf0, hCbid, hf0id, hS, hF, hnear, hlen, hfit1, hfit2,
        hCbLay, hCbne⟩ :=
      lgc_frame_bundle hNoEmpty hsNodup hBoxesNodup hModelNoEmpty happ hroute
        hgrow hstripEq hbands hpin hsp rfl hDtrans hf hfb
    obtain hB := lgc_box_bundle (_o := o) hcover hshift happ hroute hgrow hstripEq hbands
      hDtrans hb' hexcl
    have hB' : (∃ Db ∈ bands, b.id = Db.id ∧ (Axis.ofDirection o.direction).start b.rect = Db.start + D ∧
        (Axis.ofDirection o.direction).length b.rect = Db.thickness) ∨
      (∃ b0 ∈ s.boxes, ∃ Db ∈ bands, (Db.id = b0.id ∨ b0.id ∈ Db.members) ∧
        b0.id = b.id ∧ (Axis.ofDirection o.direction).start b.rect =
          (Axis.ofDirection o.direction).start b0.rect + Db.shift + D ∧
        (Axis.ofDirection o.direction).length b.rect = (Axis.ofDirection o.direction).length b0.rect) := by
      rcases hB with h | ⟨b0, hb0, Db, hDb, hcov, hid, _, hst, hlenB⟩
      · exact Or.inl h
      · exact Or.inr ⟨b0, hb0, Db, hDb, hcov, hid, hst, hlenB⟩
    exact lgc_gapClear_point hsNodup hBoxesNodup hModelNoEmpty hNoEmpty hC3 hShape ht hc
      hbands hTiled hnonnegB hParents hCbmem hCbLay hCbid hf0id hf0 hS hF hnear hlen
      hfit1 hfit2 hCbne hne hB'

/-- The shift residual holds on every executed run: a covered scene box moves
by its covering band's shift. Coverage of a nonempty id is unique
(`exec_cover_unique`), so `bandShift` returns that band's shift
(`exec_bandShift_eq`). -/
theorem pinBands_shift_cover {boxes : List ModelBox} {s : Scene} {axis : Axis} {sp : Spacing}
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (hBoxesNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") :
    LaneGapShiftCover boxes s axis sp := by
  intro b hb band hband hcov
  have hne : b.id ≠ "" := hNoEmpty b hb
  have hUniq : ∀ b1 ∈ layBands boxes s axis sp (lanesOf boxes),
      ∀ b2 ∈ layBands boxes s axis sp (lanesOf boxes),
      exec_bandCovers b1 b.id → exec_bandCovers b2 b.id → b1 = b2 :=
    fun b1 hb1 b2 hb2 hc1 hc2 => exec_cover_unique hBoxesNodup hModelNoEmpty hne hb1 hb2 hc1 hc2
  exact exec_bandShift_eq hband hcov hUniq

/-- Gap clearance with the shift residual discharged: the covering-band shift
fact is derived from model nodup, nonempty model ids, and nonempty scene ids,
so no separate shift premise remains. -/
theorem pinBands_gapClear_closed {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (hsNodup : (s.boxes.map fun b => b.id).Nodup)
    (hBoxesNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "")
    (hC3 : Validator.C3 s.layoutDump)
    (hShape : LaneSceneShape s)
    (sp : Spacing) (hsp : spacingOf o.profile = .ok sp)
    (hcover : PinBoxCoverage boxes s (Axis.ofDirection o.direction) sp)
    (hParents : PinSceneParents boxes s
      (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)))
    (hpin : pinBands boxes o s = .ok r) :
    GapClear (Axis.ofDirection o.direction)
      (laneFrames (Axis.ofDirection o.direction)
        (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
      r.layoutDump := by
  have hshift : LaneGapShiftCover boxes s (Axis.ofDirection o.direction) sp :=
    pinBands_shift_cover hNoEmpty hBoxesNodup hModelNoEmpty
  exact pinBands_gapClear hNoEmpty hsNodup hBoxesNodup hModelNoEmpty hC3 hShape sp hsp
    hcover hshift hParents hpin

end LaneBands
end Layered

end Elegant

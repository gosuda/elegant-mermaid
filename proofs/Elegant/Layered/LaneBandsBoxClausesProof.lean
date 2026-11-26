import Elegant.Layered.LaneBandsBoxClauses
import Elegant.Layered.LaneBandsCoverage
import Elegant.Layered.LaneBandsPhaseFacts
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

/-- Setup-phase facts for the executed lane layout: shift agreement for
parent-child and exclusive-sibling pairs, lane-frame top-level shape,
nonempty scene ids, and parent-band membership with its shift.

`PinBoxCoverage` alone does not determine how a parent and child (or two
exclusive siblings) move relative to each other, nor that a band-placed box
is a top-level lane frame; those are adapter facts about the executed scene,
so they are stated here and discharged by probe on executed runs
(`wip/Probe/PinBandsC2C3Probe.lean`). -/
def PinSetup (s : Scene) (bands : List Band) : Prop :=
  (∀ b ∈ s.boxes, b.parent ≠ "" → ∀ q ∈ s.boxes, q.id = b.parent →
    bandShift bands b.id = bandShift bands q.id)
  ∧ (∀ b ∈ s.boxes, ∀ c ∈ s.boxes, b.parent = c.parent → b.exclusive = true →
    c.exclusive = true → bandShift bands b.id = bandShift bands c.id)
  ∧ (∀ b ∈ s.boxes, (∃ band ∈ bands, band.id = b.id ∧ band.id ≠ "") →
    b.parent = "" ∧ b.exclusive = false)
  ∧ (∀ b ∈ s.boxes, b.id ≠ "")
  ∧ (∀ b ∈ s.boxes, ∀ q ∈ s.boxes, ∀ Q ∈ bands, b.parent = q.id → Q.id = q.id →
    Q.id ≠ "" → b.id ∈ Q.members ∧ bandShift bands b.id = Q.shift)

private theorem boxClauses_lanesOf_mem {boxes : List ModelBox} {lane : String}
    (h : lane ∈ lanesOf boxes) :
    ∃ mb ∈ boxes, mb.role = .group ∧ mb.parent = "" ∧ mb.id = lane := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, hpred⟩ := List.mem_filter.mp hx
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hrole, hpar⟩ := hpred
  exact ⟨x, hxb, beq_iff_eq.mp hrole, beq_iff_eq.mp hpar, rfl⟩

private theorem boxClauses_lanes_nodup {boxes : List ModelBox} :
    (boxes.map (·.id)).Nodup → (lanesOf boxes).Nodup := by
  induction boxes with
  | nil => intro _; simp [lanesOf]
  | cons b rest ih =>
    intro h
    have htail : (rest.map (·.id)).Nodup := (List.nodup_cons.mp h).2
    have hrest := ih htail
    have hnot : b.id ∉ rest.map (·.id) := (List.nodup_cons.mp h).1
    by_cases hp : (b.role == .group && b.parent == "") = true
    · have hne : b.id ∉ ((rest.filter fun b => b.role == .group && b.parent == "").map
          (·.id)) := by
        intro hmem
        obtain ⟨x, hxm, hidx⟩ := List.mem_map.mp hmem
        obtain ⟨hx, _⟩ := List.mem_filter.mp hxm
        have hmem' : x.id ∈ rest.map (·.id) := List.mem_map.mpr ⟨x, hx, rfl⟩
        rw [hidx] at hmem'
        exact hnot hmem'
      have heq : lanesOf (b :: rest) = b.id ::
          ((rest.filter fun b => b.role == .group && b.parent == "").map (·.id)) := by
        simp [lanesOf, hp]
      rw [heq]
      exact List.nodup_cons.mpr ⟨hne, hrest⟩
    · have hpF : (b.role == .group && b.parent == "") = false := by
        cases hb : (b.role == .group && b.parent == "") with
        | true => exact absurd hb hp
        | false => rfl
      have heq : lanesOf (b :: rest) =
          ((rest.filter fun b => b.role == .group && b.parent == "").map (·.id)) := by
        simp [lanesOf, hpF]
      rw [heq]
      exact hrest

private theorem boxClauses_layLanes_ids (boxes : List ModelBox) (s : Scene) (axis : Axis)
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

private theorem boxClauses_looseBand_id (boxes : List ModelBox) (s : Scene) (axis : Axis)
    (sp : Spacing) (loose : List String) (start : Int) :
    (looseBand boxes s axis sp loose start).id = "" := by
  unfold looseBand
  split <;> rfl

private theorem boxClauses_layBands_ids_nodup (boxes : List ModelBox) (s : Scene)
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
    rw [boxClauses_layLanes_ids]
    exact hLanes
  · have hemptyF : (looseNodes boxes).isEmpty = false := by
      cases hb : (looseNodes boxes).isEmpty with
      | true => exact absurd hb hempty
      | false => rfl
    simp only [hemptyF]
    rw [ite_eq_right Bool.false_ne_true, List.map_append, boxClauses_layLanes_ids]
    have hlo : ∀ (t : Int),
        (([looseBand boxes s axis sp (looseNodes boxes) t].map (·.id))) = [""] := by
      intro t
      simp [boxClauses_looseBand_id]
    rw [hlo, List.nodup_append]
    refine ⟨hLanes, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    intro heq
    exact hNe (heq ▸ ha)

private theorem boxClauses_band_unique {bands : List Band} :
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
private theorem boxClauses_chunk_mem_snd (bid : String) (bshift : Int) (members : List String)
    (e : String × Int)
    (h : e ∈ ((bid, bshift) :: members.map fun m => (m, bshift))) : e.2 = bshift := by
  simp only [List.mem_cons, List.mem_map] at h
  rcases h with rfl | ⟨m, _, rfl⟩
  · rfl
  · rfl

private theorem boxClauses_chunk_find_map (bid : String) (bshift : Int) (members : List String)
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
      have hsnd := boxClauses_chunk_mem_snd bid bshift members e hmemE
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

private theorem boxClauses_pinBoxDelta_eq (axis : Axis) (bands : List Band) (s : Scene)
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
        have hmap := boxClauses_chunk_find_map b.id b.shift b.members id
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
        have hmap := boxClauses_chunk_find_map b.id b.shift b.members id
        simp only [hcondF] at hmap
        exact hmap
      rw [hchunk, Option.none_or]
      have hfind : (b :: rest).find? (fun b => b.id == id || b.members.contains id) =
          rest.find? (fun b => b.id == id || b.members.contains id) := by
        simp only [List.find?_cons, hcondF]
      rw [hfind]
      exact ih

private theorem boxClauses_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem boxClauses_pinShiftBox_ok {b b' : Box} {pin : Pin} {axis : Axis}
    (h : (do pure { b with rect := ← (Move.constant (pin.boxDelta b.id)).rect axis b.rect } : Except LayoutError Box) = .ok b') :
    b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive ∧
    ∃ w, Measure.checkedI32 (axis.start b.rect + pin.boxDelta b.id) = .ok w ∧
      b'.rect = axis.withStart b.rect w ∧ w = axis.start b.rect + pin.boxDelta b.id := by
  obtain ⟨rect, hrect, hrfl⟩ := boxClauses_bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  obtain ⟨w, hw, hrectEq, hval⟩ := moveConstant_rect_value hrect
  exact ⟨rfl, rfl, rfl, rfl, w, hw, hrectEq, hval⟩

private theorem boxClauses_pinShift_mem (l : List Box) (pin : Pin) (axis : Axis) :
    ∀ (l' : List Box),
    l.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant (pin.boxDelta b.id)).rect axis b.rect } : Except LayoutError Box)) = .ok l' →
    ∀ b' ∈ l', ∃ b ∈ l, b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧
      b'.exclusive = b.exclusive ∧
      ∃ w, Measure.checkedI32 (axis.start b.rect + pin.boxDelta b.id) = .ok w ∧
        b'.rect = axis.withStart b.rect w ∧ w = axis.start b.rect + pin.boxDelta b.id := by
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
    obtain ⟨first, hfirst, h⟩ := boxClauses_bind_ok h
    obtain ⟨rest, hrest, h⟩ := boxClauses_bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    simp only [List.mem_cons] at hb'
    rcases hb' with rfl | hmem
    · obtain ⟨hid1, hpar1, _hrole1, _hexcl1, w, hw, heq, hval⟩ :=
        boxClauses_pinShiftBox_ok hfirst
      exact ⟨head, List.mem_cons.mpr (Or.inl rfl), hid1, hpar1, _hrole1, _hexcl1, w, hw,
        heq, hval⟩
    · obtain ⟨b, hbin, hid, hpar, hrole, hexcl, w, hw, heq, hval⟩ := ih _ hrest _ hmem
      exact ⟨b, List.mem_cons.mpr (Or.inr hbin), hid, hpar, hrole, hexcl, w, hw, heq, hval⟩

private theorem boxClauses_placeRect_other_x {start thickness : Int} {r : Rect} :
    (placeRect Axis.x start thickness r).y = r.y ∧
    (placeRect Axis.x start thickness r).h = r.h :=
  ⟨rfl, rfl⟩

private theorem boxClauses_placeRect_other_y {start thickness : Int} {r : Rect} :
    (placeRect Axis.y start thickness r).x = r.x ∧
    (placeRect Axis.y start thickness r).w = r.w :=
  ⟨rfl, rfl⟩

private theorem boxClauses_find_unique {α : Type} (f : α → String) :
    ∀ (l : List α), (l.map f).Nodup → ∀ (x : α), x ∈ l → ∀ v, f x = v →
      l.find? (fun a => f a == v) = some x := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons c cs ih =>
    intro hnd x hx v hv
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    cases hx with
    | head =>
      simp [hv]
    | tail _ hx' =>
      have hfx : f x ∈ cs.map f := List.mem_map.mpr ⟨x, hx', rfl⟩
      by_cases hcv : (f c == v) = true
      · exact absurd (by
          have hce : f c = v := beq_iff_eq.mp hcv
          rw [show f c = f x from hce.trans hv.symm]
          exact hfx) hnot
      · simp only [List.find?_cons, hcv]
        exact ih hnd' x hx' v hv

private theorem boxClauses_mapIdx_place_mem_aux (l : List Box) (n idx : Nat)
    (axis : Axis) (place : Rect → Rect)
    (hplace_x : axis = Axis.x → ∀ r : Rect, (place r).y = r.y ∧ (place r).h = r.h)
    (hplace_y : axis = Axis.y → ∀ r : Rect, (place r).x = r.x ∧ (place r).w = r.w) :
    ∀ b' ∈ l.mapIdx (fun j b => if j + n = idx then { b with rect := place b.rect } else b),
    ∃ b ∈ l, b'.id = b.id ∧
      (axis = Axis.x → b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h) ∧
      (axis = Axis.y → b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w) := by
  induction l generalizing n with
  | nil =>
    intro b' hb'
    simp only [List.mapIdx_nil] at hb'
    simp at hb'
  | cons head tail ih =>
    intro b' hb'
    rw [List.mapIdx_cons] at hb'
    simp only [List.mem_cons] at hb'
    rcases hb' with rfl | hmem
    · refine ⟨head, List.mem_cons.mpr (Or.inl rfl), ?hid, ?hx, ?hy⟩
      · by_cases hcond : n = idx <;> simp [hcond]
      · intro hAx
        by_cases hcond : n = idx
        · simp [hcond]
          exact (hplace_x hAx) head.rect
        · simp [hcond]
      · intro hAx
        by_cases hcond : n = idx
        · simp [hcond]
          exact (hplace_y hAx) head.rect
        · simp [hcond]
    · have hmem' : b' ∈ tail.mapIdx (fun j b => if j + (n + 1) = idx then { b with rect := place b.rect } else b) := by
        have heq : (fun j b => if j + 1 + n = idx then ({ b with rect := place b.rect } : Box) else b) =
            (fun j b => if j + (n + 1) = idx then ({ b with rect := place b.rect } : Box) else b) := by
          funext j b
          have h : j + 1 + n = j + (n + 1) := by omega
          rw [h]
        simpa only [heq] using hmem
      obtain ⟨b, hbin, hid, hx, hy⟩ := ih (n + 1) _ hmem'
      exact ⟨b, List.mem_cons.mpr (Or.inr hbin), hid, hx, hy⟩

private theorem boxClauses_replaceFrame_full {axis : Axis} {band : Band} {s s' : Scene}
    (h : replaceFrame axis band s = .ok s') :
    ∀ b' ∈ s'.boxes, ∃ b ∈ s.boxes,
      b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive ∧
      (axis = Axis.x → b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h) ∧
      (axis = Axis.y → b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w) ∧
      ((b.id = band.id ∧ b'.rect = placeRect axis band.start band.thickness b.rect) ∨
        b'.rect = b.rect) := by
  unfold replaceFrame at h
  cases hfind : s.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    simp only [hfind, Pure.pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h
    intro b' hb'
    exact ⟨b', hb', rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, Or.inr rfl⟩
  | some idx =>
    obtain ⟨hi, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
    simp only [hfind] at h
    cases hstart : Measure.checkedI32 band.start with
    | error _e => simp [hstart, Bind.bind, Except.bind] at h
    | ok _s =>
      simp only [hstart, Bind.bind, Except.bind] at h
      cases hthick : Measure.checkedI32 band.thickness with
      | error _e => simp [hthick] at h
      | ok _t =>
        simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at h
        intro b' hb'
        have hboxes : s'.boxes = s.boxes.mapIdx (fun j b =>
            if j = idx then ({ b with rect := placeRect axis _s _t b.rect } : Box) else b) := by
          rw [← h]
        rw [hboxes] at hb'
        obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hb'
        rw [List.getElem_mapIdx] at heq
        have hj' : j < s.boxes.length := by
          have hlen : (s.boxes.mapIdx (fun j b =>
              if j = idx then ({ b with rect := placeRect axis _s _t b.rect } : Box)
              else b)).length = s.boxes.length :=
            List.length_mapIdx
          rw [hlen] at hj
          exact hj
        have hmem : (s.boxes[j]'hj') ∈ s.boxes := List.getElem_mem hj'
        have hs' : _s = band.start := checkedI32_ok hstart
        have ht' : _t = band.thickness := checkedI32_ok hthick
        have hpbeta : (((s.boxes[idx]'hi).id == band.id)) = true := hp
        by_cases hcond : j = idx
        · subst j
          have heqb : (if idx = idx then Box.mk (s.boxes[idx]'hj').id
              (s.boxes[idx]'hj').role
              (placeRect axis _s _t (s.boxes[idx]'hj').rect)
              (s.boxes[idx]'hj').parent (s.boxes[idx]'hj').exclusive
              else (s.boxes[idx]'hj')) = b' := heq
          rw [ite_eq_left rfl] at heqb
          subst heqb
          have hbid : (s.boxes[idx]'hj').id = band.id := beq_iff_eq.mp hpbeta
          refine ⟨(s.boxes[idx]'hj'), hmem, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
          · intro hAx
            rw [hAx]
            exact boxClauses_placeRect_other_x
          · intro hAx
            rw [hAx]
            exact boxClauses_placeRect_other_y
          · left
            refine ⟨hbid, ?_⟩
            rw [hs', ht']
        · have heqb : (if j = idx then Box.mk (s.boxes[j]'hj').id
              (s.boxes[j]'hj').role
              (placeRect axis _s _t (s.boxes[j]'hj').rect)
              (s.boxes[j]'hj').parent (s.boxes[j]'hj').exclusive
              else (s.boxes[j]'hj')) = b' := heq
          rw [ite_eq_right hcond] at heqb
          subst heqb
          exact ⟨(s.boxes[j]'hj'), hmem, rfl, rfl, rfl, rfl,
            fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, Or.inr rfl⟩

private theorem boxClauses_placeRect_idem (axis : Axis) (s1 t1 s2 t2 : Int) (r : Rect) :
    placeRect axis s2 t2 (placeRect axis s1 t1 r) = placeRect axis s2 t2 r := by
  cases axis <;> rfl

private theorem boxClauses_start_withStart (axis : Axis) (r : Rect) (w : Int) :
    Axis.start axis (Axis.withStart axis r w) = w := by
  cases axis <;> rfl

private theorem boxClauses_length_withStart (axis : Axis) (r : Rect) (w : Int) :
    Axis.length axis (Axis.withStart axis r w) = Axis.length axis r := by
  cases axis <;> rfl

private theorem boxClauses_placeRect_start (axis : Axis) (s t : Int) (r : Rect) :
    Axis.start axis (placeRect axis s t r) = s := by
  unfold placeRect
  cases axis <;> rfl

private theorem boxClauses_placeRect_length (axis : Axis) (s t : Int) (r : Rect) :
    Axis.length axis (placeRect axis s t r) = t := by
  unfold placeRect
  cases axis <;> rfl
private theorem boxClauses_foldPlace_full (bands : List Band) (axis : Axis) (s : Scene) :
    (bands.map (·.id)).Nodup → ∀ (s' : Scene),
    bands.foldlM (fun scene band => replaceFrame axis band scene) s = .ok s' →
    ∀ b' ∈ s'.boxes, ∃ b ∈ s.boxes,
      b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive ∧
      (axis = Axis.x → b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h) ∧
      (axis = Axis.y → b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w) ∧
      ((∃ band ∈ bands, b.id = band.id ∧
        b'.rect = placeRect axis band.start band.thickness b.rect) ∨ b'.rect = b.rect) := by
  induction bands generalizing s with
  | nil =>
    intro _ s' h b' hb'
    have he : s' = s := by
      simpa only [List.foldlM_nil, Pure.pure, Except.pure,
        Except.ok.injEq] using h.symm
    subst he
    exact ⟨b', hb', rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, Or.inr rfl⟩
  | cons band rest ih =>
    intro hnd s' h b' hb'
    have hndRest : (rest.map (·.id)).Nodup := (List.nodup_cons.mp hnd).2
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, h⟩ := boxClauses_bind_ok h
    obtain ⟨m, hmin, hid1, hpar1, hrole1, hexcl1, hx1, hy1, hrect1⟩ :=
      ih mid hndRest s' h _ hb'
    obtain ⟨m0, hmin0, hid0, hpar0, hrole0, hexcl0, hx0, hy0, hrect0⟩ :=
      boxClauses_replaceFrame_full (axis := axis) (band := band) hmid _ hmin
    refine ⟨m0, hmin0, hid1.trans hid0, hpar1.trans hpar0, hrole1.trans hrole0,
      hexcl1.trans hexcl0, ?_, ?_, ?_⟩
    · intro hAx
      obtain ⟨hyM, hhM⟩ := hx1 hAx
      obtain ⟨hyB, hhB⟩ := hx0 hAx
      exact ⟨hyM.trans hyB, hhM.trans hhB⟩
    · intro hAx
      obtain ⟨hxM, hwM⟩ := hy1 hAx
      obtain ⟨hxB, hwB⟩ := hy0 hAx
      exact ⟨hxM.trans hxB, hwM.trans hwB⟩
    · rcases hrect1 with ⟨B, hBmem, hBid, hBrect⟩ | hsame
      · rcases hrect0 with ⟨hm0id, hm0rect⟩ | hsame0
        · have hBeq : B = band := boxClauses_band_unique hnd
            (List.mem_cons.mpr (Or.inr hBmem)) (List.mem_cons.mpr (Or.inl rfl))
            (hBid.symm.trans (hid0.trans hm0id))
          subst B
          rw [hm0rect] at hBrect
          rw [boxClauses_placeRect_idem] at hBrect
          exact Or.inl ⟨band, List.mem_cons.mpr (Or.inl rfl), hm0id, hBrect⟩
        · rw [hsame0] at hBrect
          exact Or.inl ⟨B, List.mem_cons.mpr (Or.inr hBmem),
            hid0.symm.trans hBid, hBrect⟩
      · rcases hrect0 with ⟨hm0id, hm0rect⟩ | hsame0
        · rw [hsame]
          exact Or.inl ⟨band, List.mem_cons.mpr (Or.inl rfl), hm0id, hm0rect⟩
        · exact Or.inr (hsame.trans hsame0)


private theorem boxClauses_pinned_full {pin : Pin} {bands : List Band} {s pinned : Scene}
    (hndB : (bands.map (·.id)).Nodup)
    (h : applyPin pin bands s = .ok pinned) :
    ∀ b' ∈ pinned.boxes, ∃ b ∈ s.boxes,
      b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive ∧
      (pin.axis = Axis.x → b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h) ∧
      (pin.axis = Axis.y → b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w) ∧
      ((∃ band ∈ bands, b.id = band.id ∧
        Axis.start pin.axis b'.rect = band.start ∧
        Axis.length pin.axis b'.rect = band.thickness) ∨
        (∃ D, Axis.start pin.axis b'.rect = Axis.start pin.axis b.rect + D ∧
          Axis.length pin.axis b'.rect = Axis.length pin.axis b.rect ∧
          D = pin.boxDelta b.id)) := by
  obtain ⟨shiftedBoxes, _shiftedLabels, _shiftedRoutes, _shiftedItems,
    hboxes, _hlabels, _hroutes, _hitems, hfold⟩ := applyPin_shifted h
  intro b' hb'
  obtain ⟨m, hmin, hid1, hpar1, hrole1, hexcl1, hx1, hy1, hrect1⟩ :=
    boxClauses_foldPlace_full bands pin.axis _ hndB _ hfold _ hb'
  have hmin' : m ∈ shiftedBoxes := hmin
  obtain ⟨b, hbin, hid0, hpar0, hrole0, hexcl0, w, _hw, heq0, hval⟩ :=
    boxClauses_pinShift_mem s.boxes pin pin.axis _ hboxes _ hmin'
  have hOtherM : (pin.axis = Axis.x → m.rect.y = b.rect.y ∧ m.rect.h = b.rect.h) ∧
      (pin.axis = Axis.y → m.rect.x = b.rect.x ∧ m.rect.w = b.rect.w) := by
    constructor
    · intro hAx
      have e := heq0
      rw [hAx] at e
      rw [e]
      exact ⟨rfl, rfl⟩
    · intro hAx
      have e := heq0
      rw [hAx] at e
      rw [e]
      exact ⟨rfl, rfl⟩
  refine ⟨b, hbin, hid1.trans hid0, hpar1.trans hpar0, hrole1.trans hrole0,
    hexcl1.trans hexcl0, ?_, ?_, ?_⟩
  · intro hAx
    obtain ⟨hyM, hhM⟩ := hx1 hAx
    obtain ⟨hyB, hhB⟩ := hOtherM.1 hAx
    exact ⟨hyM.trans hyB, hhM.trans hhB⟩
  · intro hAx
    obtain ⟨hxM, hwM⟩ := hy1 hAx
    obtain ⟨hxB, hwB⟩ := hOtherM.2 hAx
    exact ⟨hxM.trans hxB, hwM.trans hwB⟩
  · rcases hrect1 with ⟨B, hBmem, hBid, hBrect⟩ | hsame
    · left
      refine ⟨B, hBmem, hid0.symm.trans hBid, ?_, ?_⟩
      · have hs := boxClauses_placeRect_start pin.axis B.start B.thickness m.rect
        rw [hBrect]
        exact hs
      · have hl := boxClauses_placeRect_length pin.axis B.start B.thickness m.rect
        rw [hBrect]
        exact hl
    · right
      have hstartM : Axis.start pin.axis m.rect =
          Axis.start pin.axis b.rect + pin.boxDelta b.id := by
        rw [heq0, boxClauses_start_withStart]
        exact hval
      have hlenM : Axis.length pin.axis m.rect = Axis.length pin.axis b.rect := by
        rw [heq0, boxClauses_length_withStart]
      refine ⟨pin.boxDelta b.id, ?_, ?_, rfl⟩
      · rw [hsame]
        exact hstartM
      · rw [hsame]
        exact hlenM
private theorem boxClauses_shiftAll_mem (l : List Box) (axis : Axis) (delta : Int) :
    ∀ (l' : List Box),
    l.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant delta).rect axis b.rect } : Except LayoutError Box)) = .ok l' →
    ∀ b' ∈ l', ∃ b ∈ l, b'.id = b.id ∧
      ∃ w, Measure.checkedI32 (axis.start b.rect + delta) = .ok w ∧
        b'.rect = axis.withStart b.rect w ∧ w = axis.start b.rect + delta := by
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
    obtain ⟨first, hfirst, h⟩ := boxClauses_bind_ok h
    obtain ⟨rest, hrest, h⟩ := boxClauses_bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    simp only [List.mem_cons] at hb'
    rcases hb' with rfl | hmem
    · obtain ⟨rect, hrect, hrfl⟩ := boxClauses_bind_ok hfirst
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
      subst hrfl
      obtain ⟨w, hw, hrectEq, hval⟩ := moveConstant_rect_value hrect
      exact ⟨head, List.mem_cons.mpr (Or.inl rfl), rfl, w, hw, hrectEq, hval⟩
    · obtain ⟨b, hbin, hid, w, hw, heq, hval⟩ := ih _ hrest _ hmem
      exact ⟨b, List.mem_cons.mpr (Or.inr hbin), hid, w, hw, heq, hval⟩

private theorem boxClauses_shiftAll_full (l : List Box) (axis : Axis) (delta : Int) :
    ∀ (l' : List Box),
    l.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant delta).rect axis b.rect } : Except LayoutError Box)) = .ok l' →
    ∀ b' ∈ l', ∃ b ∈ l, b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧
      b'.exclusive = b.exclusive ∧
      ∃ w, Measure.checkedI32 (axis.start b.rect + delta) = .ok w ∧
        b'.rect = axis.withStart b.rect w ∧ w = axis.start b.rect + delta := by
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
    obtain ⟨first, hfirst, h⟩ := boxClauses_bind_ok h
    obtain ⟨rest, hrest, h⟩ := boxClauses_bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    simp only [List.mem_cons] at hb'
    rcases hb' with rfl | hmem
    · obtain ⟨rect, hrect, hrfl⟩ := boxClauses_bind_ok hfirst
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
      subst hrfl
      obtain ⟨w, hw, hrectEq, hval⟩ := moveConstant_rect_value hrect
      exact ⟨head, List.mem_cons.mpr (Or.inl rfl), rfl, rfl, rfl, rfl, w, hw, hrectEq, hval⟩
    · obtain ⟨b, hbin, hid, hpar, hrole, hexcl, w, hw, heq, hval⟩ := ih _ hrest _ hmem
      exact ⟨b, List.mem_cons.mpr (Or.inr hbin), hid, hpar, hrole, hexcl, w, hw, heq, hval⟩

private theorem boxClauses_shiftAll_scene_full {axis : Axis} {delta : Int} {s s' : Scene}
    (h : shiftAll axis delta s = .ok s') :
    ∀ b' ∈ s'.boxes, ∃ b ∈ s.boxes,
      b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive ∧
      ∃ w, Measure.checkedI32 (axis.start b.rect + delta) = .ok w ∧
        b'.rect = axis.withStart b.rect w ∧ w = axis.start b.rect + delta := by
  unfold shiftAll at h
  obtain ⟨boxes, hboxes, h⟩ := boxClauses_bind_ok h
  obtain ⟨labels, hlabels, h⟩ := boxClauses_bind_ok h
  obtain ⟨routes, hroutes, h⟩ := boxClauses_bind_ok h
  obtain ⟨items, _hitems, h⟩ := boxClauses_bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  intro b' hb'
  exact boxClauses_shiftAll_full s.boxes axis delta _ hboxes _ hb'

private theorem boxClauses_shiftAll_scene_mem {axis : Axis} {delta : Int} {s s' : Scene}
    (h : shiftAll axis delta s = .ok s') :
    ∀ b' ∈ s'.boxes, ∃ b ∈ s.boxes, b'.id = b.id ∧
      ∃ w, Measure.checkedI32 (axis.start b.rect + delta) = .ok w ∧
        b'.rect = axis.withStart b.rect w ∧ w = axis.start b.rect + delta := by
  unfold shiftAll at h
  obtain ⟨boxes, hboxes, h⟩ := boxClauses_bind_ok h
  obtain ⟨labels, hlabels, h⟩ := boxClauses_bind_ok h
  obtain ⟨routes, hroutes, h⟩ := boxClauses_bind_ok h
  obtain ⟨items, _hitems, h⟩ := boxClauses_bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  intro b' hb'
  exact boxClauses_shiftAll_mem s.boxes axis delta _ hboxes _ hb'

private theorem boxClauses_r_from_pinned {axis : Axis}
    {pinned routed origin stripScene r : Scene} {strip gap : Int}
    (hRouteEq : routed.boxes = pinned.boxes)
    (horig : restoreOrigin axis routed = .ok origin)
    (hStripEq : relocateLabels axis strip gap origin = .ok stripScene)
    (hGrowEq : r.boxes = stripScene.boxes) :
    ∃ oDelta, ∀ b' ∈ r.boxes, ∃ m ∈ pinned.boxes,
      b'.id = m.id ∧ b'.parent = m.parent ∧ b'.role = m.role ∧ b'.exclusive = m.exclusive ∧
      (axis = Axis.x → b'.rect.y = m.rect.y ∧ b'.rect.h = m.rect.h) ∧
      (axis = Axis.y → b'.rect.x = m.rect.x ∧ b'.rect.w = m.rect.w) ∧
      Axis.start axis b'.rect = Axis.start axis m.rect + oDelta ∧
      Axis.length axis b'.rect = Axis.length axis m.rect := by
  have hRelEq : stripScene.boxes = origin.boxes := relocateLabels_boxes hStripEq
  rcases restoreOrigin_cases horig with hEq | ⟨delta, _hpos, hshift⟩
  · refine ⟨0, fun b' hb' => ?_⟩
    rw [hGrowEq, hRelEq, hEq, hRouteEq] at hb'
    exact ⟨b', hb', rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩,
      by omega, rfl⟩
  · refine ⟨delta, fun b' hb' => ?_⟩
    rw [hGrowEq, hRelEq] at hb'
    obtain ⟨m0, hmin0, hid0, hpar0, hrole0, hexcl0, w, _hw, heqW, hval⟩ :=
      boxClauses_shiftAll_scene_full hshift _ hb'
    have hmin : m0 ∈ pinned.boxes := by
      rw [hRouteEq] at hmin0
      exact hmin0
    refine ⟨m0, hmin, hid0, hpar0, hrole0, hexcl0, ?_, ?_, ?_, ?_⟩
    · intro hAx
      have e := heqW
      rw [hAx] at e
      rw [e]
      exact ⟨rfl, rfl⟩
    · intro hAx
      have e := heqW
      rw [hAx] at e
      rw [e]
      exact ⟨rfl, rfl⟩
    · rw [heqW, boxClauses_start_withStart]
      exact hval
    · rw [heqW, boxClauses_length_withStart]

private theorem boxClauses_master {boxes : List ModelBox} {o : Options} {s r : Scene}
    {axis : Axis} {sp : Spacing} {bands : List Band}
    {pinned routed origin stripScene : Scene} {strip gap : Int}
    (hBoxes : (boxes.map (·.id)).Nodup) (hNe : ∀ b ∈ boxes, b.id ≠ "")
    (hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    (happ : applyPin (buildPin axis bands s) bands s = .ok pinned)
    (hroute : rerouteBands axis sp (LayoutConst.rank_gap.get o.profile) bands
      (buildPin axis bands s) s.routes pinned = .ok routed)
    (horig : restoreOrigin axis routed = .ok origin)
    (hStripEq : relocateLabels axis strip gap origin = .ok stripScene)
    (hgrow : growCanvas axis s.canvas stripScene = .ok r) :
    ∃ oDelta, ∀ b' ∈ r.boxes, ∃ b ∈ s.boxes,
      b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive ∧
      (axis = Axis.x → b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h) ∧
      (axis = Axis.y → b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w) ∧
      ((∃ D, Axis.start axis b'.rect = Axis.start axis b.rect + D ∧
        Axis.length axis b'.rect = Axis.length axis b.rect ∧
        D = (buildPin axis bands s).boxDelta b.id + oDelta) ∨
        (∃ band ∈ bands, b.id = band.id ∧
          Axis.start axis b'.rect = band.start + oDelta ∧
          Axis.length axis b'.rect = band.thickness)) := by
  have hLanes : (lanesOf boxes).Nodup := boxClauses_lanes_nodup hBoxes
  have hNeLanes : "" ∉ lanesOf boxes := by
    intro hmem
    obtain ⟨mb, hmb, _, _, hid⟩ := boxClauses_lanesOf_mem hmem
    exact hNe mb hmb hid
  have hndB : (bands.map (·.id)).Nodup := by
    rw [hbands]
    exact boxClauses_layBands_ids_nodup _ _ _ _ _ hLanes hNeLanes
  have hRouteEq : routed.boxes = pinned.boxes := (rerouteBands_frame hroute).1
  have hGrowEq : r.boxes = stripScene.boxes := (growCanvas_frame hgrow).1
  obtain ⟨oDelta, hL2⟩ := boxClauses_r_from_pinned hRouteEq horig hStripEq hGrowEq
  exact ⟨oDelta, fun b' hb' => by
    obtain ⟨m, hmin, hidM, hparM, hroleM, hexclM, hxM, hyM, hsM, hlM⟩ := hL2 _ hb'
    obtain ⟨b, hbin, hidL, hparL, hroleL, hexclL, hxL, hyL, hrectL⟩ :=
      boxClauses_pinned_full hndB happ _ hmin
    have hax : (buildPin axis bands s).axis = axis := rfl
    rw [hax] at hxL hyL hrectL
    refine ⟨b, hbin, hidM.trans hidL, hparM.trans hparL, hroleM.trans hroleL,
      hexclM.trans hexclL, ?_, ?_, ?_⟩
    · intro hAx
      obtain ⟨hyM', hhM⟩ := hxM hAx
      obtain ⟨hyB, hhB⟩ := hxL hAx
      exact ⟨hyM'.trans hyB, hhM.trans hhB⟩
    · intro hAx
      obtain ⟨hxM', hwM⟩ := hyM hAx
      obtain ⟨hxB, hwB⟩ := hyL hAx
      exact ⟨hxM'.trans hxB, hwM.trans hwB⟩
    · rcases hrectL with ⟨B, hBmem, hBid, hBs, hBl⟩ | ⟨D₂, hsM2, hlM2, hD₂⟩
      · right
        exact ⟨B, hBmem, hBid, by omega, hlM.trans hBl⟩
      · left
        refine ⟨D₂ + oDelta, by omega, hlM.trans hlM2, ?_⟩
        rw [hD₂]
    ⟩
private theorem foldl_min_le_mem {l : List Int} {init x : Int}
    (hmem : x ∈ l) : l.foldl min init ≤ x := by
  induction l generalizing init with
  | nil => simp at hmem
  | cons a rest ih =>
    rw [List.mem_cons] at hmem
    simp only [List.foldl_cons]
    rcases hmem with hEq | hmem
    · rw [hEq]
      have hle : rest.foldl min (min init a) ≤ min init a :=
        foldl_min_le rest (min init a)
      omega
    · exact ih (init := min init a) hmem

private theorem foldl_max_ge_mem {l : List Int} {init x : Int}
    (hmem : x ∈ l) : x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp at hmem
  | cons a rest ih =>
    rw [List.mem_cons] at hmem
    simp only [List.foldl_cons]
    rcases hmem with hEq | hmem
    · rw [hEq]
      have hle : max init a ≤ rest.foldl max (max init a) :=
        le_foldl_max rest (max init a)
      omega
    · exact ih (init := max init a) hmem

private theorem pinBounds_mem {vs : List Int} {lo hi x : Int}
    (h : bounds vs = some (lo, hi)) (hmem : x ∈ vs) : lo ≤ x ∧ x ≤ hi := by
  cases vs with
  | nil => simp [bounds] at h
  | cons v rest =>
    simp only [bounds, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact ⟨foldl_min_le _ _, le_foldl_max _ _⟩
    · exact ⟨foldl_min_le_mem hmem, foldl_max_ge_mem hmem⟩

private theorem contentValues_mem_start {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {lane : String} {members : List String} {b : Box}
    (hmem : b.id ∈ members)
    (hfind : s.boxes.find? (fun b' => b'.id == b.id) = some b) :
    axis.start b.rect ∈ contentValues boxes s axis lane members ∧
      axis.start b.rect + axis.length b.rect ∈ contentValues boxes s axis lane members := by
  unfold contentValues
  have hmemMap : axis.start b.rect ∈ members.flatMap (fun id =>
      match s.boxes.find? (fun b' => b'.id == id) with
      | none => ([] : List Int)
      | some bb => [axis.start bb.rect, axis.start bb.rect + axis.length bb.rect]) := by
    rw [List.mem_flatMap]
    exact ⟨b.id, hmem, by simp [hfind]⟩
  have hmemMap2 : axis.start b.rect + axis.length b.rect ∈ members.flatMap (fun id =>
      match s.boxes.find? (fun b' => b'.id == id) with
      | none => ([] : List Int)
      | some bb => [axis.start bb.rect, axis.start bb.rect + axis.length bb.rect]) := by
    rw [List.mem_flatMap]
    exact ⟨b.id, hmem, by simp [hfind]⟩
  constructor
  · exact List.mem_append.mpr (Or.inl hmemMap)
  · exact List.mem_append.mpr (Or.inl hmemMap2)

private theorem laneMember_bounds {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lane : String} {start : Int} {b : Box}
    (hmem : b.id ∈ (laneBand boxes s axis sp lane start).members)
    (hfind : s.boxes.find? (fun b' => b'.id == b.id) = some b) :
    ∃ lo hi : Int,
      bounds (contentValues boxes s axis lane
        ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id)) =
        some (lo, hi) ∧
      lo ≤ axis.start b.rect ∧ axis.start b.rect + axis.length b.rect ≤ hi := by
  have hmem' : b.id ∈ (boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id := by
    unfold laneBand at hmem
    simpa using hmem
  obtain ⟨hstart, hend⟩ := contentValues_mem_start hmem' hfind
  cases hc : contentValues boxes s axis lane
      ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id) with
  | nil =>
    rw [hc] at hstart
    simp at hstart
  | cons v rest =>
    have hEq : bounds (v :: rest) = some (rest.foldl min v, rest.foldl max v) := rfl
    have hstart' : axis.start b.rect ∈ v :: rest := by rw [← hc]; exact hstart
    have hend' : axis.start b.rect + axis.length b.rect ∈ v :: rest := by
      rw [← hc]; exact hend
    obtain ⟨hlo1, _⟩ := pinBounds_mem (h := hEq) hstart'
    obtain ⟨_, hhi2⟩ := pinBounds_mem (h := hEq) hend'
    exact ⟨_, _, hEq, hlo1, hhi2⟩

private theorem laneMember_within {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lane : String} {start : Int} {b : Box}
    (ht : 0 ≤ sp.title) (hc : 0 ≤ sp.clear)
    (hmem : b.id ∈ (laneBand boxes s axis sp lane start).members)
    (hfind : s.boxes.find? (fun b' => b'.id == b.id) = some b) :
    let band := laneBand boxes s axis sp lane start
    let d := band.shift
    band.start ≤ axis.start b.rect + d ∧
      axis.start b.rect + axis.length b.rect + d ≤ band.start + band.thickness := by
  obtain ⟨lo, hi, hEq, hlo1, hhi2⟩ := laneMember_bounds (hmem := hmem) (hfind := hfind)
  unfold laneBand
  simp only
  have hExt : (bounds (contentValues boxes s axis lane
      ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id))).getD
      (start, start) = (lo, hi) := by
    simp [hEq]
  rw [hExt]
  simp only
  omega

private theorem layBands_mem_cases {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lanes : List String} {band : Band}
    (hmem : band ∈ layBands boxes s axis sp lanes) :
    band ∈ layLanes boxes s axis sp lanes (firstLaneStart s lanes axis) ∨
      band = looseBand boxes s axis sp (looseNodes boxes)
        (firstLaneStart s lanes axis + ((layLanes boxes s axis sp lanes
          (firstLaneStart s lanes axis)).map (fun b => b.thickness)).sum) := by
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

private theorem layLanes_member_band {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lanes : List String} {start : Int} {Q : Band}
    (h : Q ∈ layLanes boxes s axis sp lanes start) :
    ∃ lane : String, ∃ st : Int, Q = laneBand boxes s axis sp lane st := by
  induction lanes generalizing start with
  | nil => simp [layLanes] at h
  | cons hd tl ih =>
    have heq : layLanes boxes s axis sp (hd :: tl) start =
        laneBand boxes s axis sp hd start ::
          layLanes boxes s axis sp tl (start + (laneBand boxes s axis sp hd start).thickness) := by
      simp only [layLanes]
    rw [heq, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨hd, start, rfl⟩
    · obtain ⟨lane, st, heqQ⟩ := ih h
      exact ⟨lane, st, heqQ⟩

private theorem bandWithin {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {bands : List Band} {Q : Band} {b : Box}
    (ht : 0 ≤ sp.title) (hc : 0 ≤ sp.clear)
    (hQ : Q ∈ bands) (hne : Q.id ≠ "")
    (hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    (hmem : b.id ∈ Q.members)
    (hfind : s.boxes.find? (fun b' => b'.id == b.id) = some b) :
    Q.start ≤ Axis.start axis b.rect + Q.shift ∧
      Axis.start axis b.rect + Axis.length axis b.rect + Q.shift ≤
        Q.start + Q.thickness := by
  rw [hbands] at hQ
  obtain hcases := layBands_mem_cases hQ
  rcases hcases with hlay | hloose
  · obtain ⟨lane, st, rfl⟩ := layLanes_member_band hlay
    exact laneMember_within ht hc hmem hfind
  · subst hloose
    have hid := boxClauses_looseBand_id boxes s axis sp (looseNodes boxes)
    simp only [hid] at hne
    exact absurd rfl hne

private theorem spacing_of_nonneg {profile : Profile} {sp : Spacing}
    (h : spacingOf profile = .ok sp) : 0 ≤ sp.title ∧ 0 ≤ sp.clear := by
  cases profile with
  | vector =>
    unfold spacingOf LayoutConst.slot LayoutConst.line_h
      LayoutConst.cluster_pad LayoutConst.Pair.get at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨by decide, by decide⟩
  | cell =>
    unfold spacingOf LayoutConst.slot LayoutConst.line_h
      LayoutConst.cluster_pad LayoutConst.Pair.get at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨by decide, by decide⟩

private theorem sceneFind_eq_self {boxes : List Box} (hn : (boxes.map (fun b => b.id)).Nodup)
    {x : Box} (hx : x ∈ boxes) : boxes.find? (fun b => b.id == x.id) = some x := by
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

private theorem find_some_id {l : List Box} {id : String} {x : Box}
    (h : l.find? (fun b => b.id == id) = some x) : x.id = id := by
  induction l with
  | nil => simp [List.find?] at h
  | cons hd tl ih =>
    by_cases hc : (hd.id == id) = true
    · simp only [List.find?_cons, hc] at h
      cases h
      exact beq_iff_eq.mp hc
    · simp only [List.find?_cons, hc] at h
      exact ih h
theorem pinC2Sep_of_pin {boxes : List ModelBox} {o : Options} {s r : Scene}
    {axis : Axis} {sp : Spacing}
    (hcover : PinBoxCoverage boxes s axis sp)
    (hBoxesNodup : (boxes.map (·.id)).Nodup)
    (hNe : ∀ b ∈ boxes, b.id ≠ "")
    (hsetup : PinSetup s (layBands boxes s axis sp (lanesOf boxes)))
    (haxis : axis = Axis.ofDirection o.direction)
    (hsp : spacingOf o.profile = .ok sp)
    (h : pinBands boxes o s = .ok r) :
    PinC2Sep o s r := by
  cases hLanes : lanesOf boxes with
  | nil =>
    have hNo : pinBands boxes o s = .ok s := pinBands_no_lanes hLanes
    have hrS : r = s := by rw [hNo] at h; simpa only [Except.ok.injEq] using h.symm
    subst hrS
    intro b' hb' c' hc' hne hexB hexC hpar
    exact ⟨b', hb', c', hc', rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
      fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨fun _ => Or.inl (by omega), fun _ => Or.inl (by omega)⟩⟩
  | cons lane rest =>
    have hNeLanes : lanesOf boxes ≠ [] := by
      rw [hLanes]; intro hnil; cases hnil
    obtain ⟨sp', axis', bands, pinned, routed, origin, strip, stripScene,
      hsp', haxis', hbands, happ, hroute, horig, _hstrip, hStripEq, hgrow⟩ :=
      pinBands_spec (boxes := boxes) (o := o) (s := s) (r := r) hNeLanes h
    have hspEq : sp' = sp := by
      have h := hsp'.symm.trans hsp
      simpa only [Except.ok.injEq] using h
    have haxisEq : axis' = axis := haxis'.trans haxis.symm
    rw [haxisEq] at hbands
    rw [haxisEq] at happ
    rw [haxisEq] at hroute
    rw [haxisEq] at horig
    rw [haxisEq] at hStripEq
    rw [haxisEq] at hgrow
    rw [haxisEq] at haxis'
    rw [hspEq] at hbands
    rw [hspEq] at hroute
    rw [hspEq] at hsp'
    have hLanesNodup : (lanesOf boxes).Nodup := boxClauses_lanes_nodup hBoxesNodup
    have hNeLanes' : "" ∉ lanesOf boxes := by
      intro hmem
      obtain ⟨mb, hmb, _, _, hid⟩ := boxClauses_lanesOf_mem hmem
      exact hNe mb hmb hid
    have hndB : (bands.map (·.id)).Nodup := by
      rw [hbands]
      exact boxClauses_layBands_ids_nodup boxes s axis sp (lanesOf boxes) hLanesNodup hNeLanes'
    obtain ⟨oDelta, hcorr⟩ :=
      boxClauses_master hBoxesNodup hNe hbands happ hroute horig hStripEq hgrow
    rw [← hbands] at hsetup
    obtain ⟨hparShift, hsibShift, hframeTop, hidsNe, hparMember⟩ := hsetup
    intro b' hb' c' hc' hne hexB hexC hpar
    obtain ⟨b, hbin, hidB, hparB, _hroleB, hexB', hxB, hyB, hrectB⟩ := hcorr b' hb'
    obtain ⟨c, hcin, hidC, hparC, _hroleC, hexC', hxC, hyC, hrectC⟩ := hcorr c' hc'
    have hexB0 : b.exclusive = true := by rw [← hexB']; exact hexB
    have hexC0 : c.exclusive = true := by rw [← hexC']; exact hexC
    have hparBC : b.parent = c.parent := by rw [← hparB, ← hparC]; exact hpar
    have hnbB : ∀ B ∈ bands, b.id = B.id → False := by
      intro B hBmem hBid
      have hBne : B.id ≠ "" := by rw [← hBid]; exact hidsNe b hbin
      have htop := hframeTop b hbin ⟨B, hBmem, hBid.symm, hBne⟩
      exact Bool.false_ne_true (htop.2.symm.trans hexB0)
    have hnbC : ∀ C ∈ bands, c.id = C.id → False := by
      intro C hCmem hCid
      have hCne : C.id ≠ "" := by rw [← hCid]; exact hidsNe c hcin
      have htop := hframeTop c hcin ⟨C, hCmem, hCid.symm, hCne⟩
      exact Bool.false_ne_true (htop.2.symm.trans hexC0)
    have hpin : (buildPin axis bands s).axis = axis := rfl
    rcases hrectB with ⟨DB, hDBstart, hDBlen, hDBdelta⟩ | ⟨B, hBmem, hBid, _, _⟩
    · rcases hrectC with ⟨DC, hDCstart, hDClen, hDCdelta⟩ | ⟨C, hCmem, hCid, _, _⟩
      · have hboxB : (buildPin axis bands s).boxDelta b.id = bandShift bands b.id :=
          boxClauses_pinBoxDelta_eq axis bands s b.id
        have hboxC : (buildPin axis bands s).boxDelta c.id = bandShift bands c.id :=
          boxClauses_pinBoxDelta_eq axis bands s c.id
        have hshiftEq : bandShift bands b.id = bandShift bands c.id :=
          hsibShift b hbin c hcin hparBC hexB0 hexC0
        have hDD : DB = DC := by
          rw [hDBdelta, hDCdelta, hboxB, hboxC, hshiftEq]
        cases hAx : Axis.ofDirection o.direction with
        | x =>
          have hpinX : (buildPin axis bands s).axis = Axis.x :=
            hpin.trans (haxis.trans hAx)
          obtain ⟨hyB, hhB⟩ := hxB hpinX
          obtain ⟨hyC, hhC⟩ := hxC hpinX
          have haxisX : axis = Axis.x := haxis.trans hAx
          rw [haxisX] at hDBstart hDBlen hDCstart hDClen
          have eB : b'.rect.x = b.rect.x + DB := hDBstart
          have eC : c'.rect.x = c.rect.x + DC := hDCstart
          have eBw : b'.rect.w = b.rect.w := hDBlen
          have eCw : c'.rect.w = c.rect.w := hDClen
          refine ⟨b, hbin, c, hcin, hidB, hidC, hexB', hexC', hparB, hparC, ?_, ?_, ?_⟩
          · intro _
            exact ⟨hyB, hhB, eBw, hyC, hhC, eCw⟩
          · intro hY
            exact absurd hY (by decide)
          · constructor
            · intro _
              exact Or.inl (by omega)
            · intro hY
              exact absurd hY (by decide)
        | y =>
          have hpinY : (buildPin axis bands s).axis = Axis.y :=
            hpin.trans (haxis.trans hAx)
          obtain ⟨hxB', hwB⟩ := hyB hpinY
          obtain ⟨hxC', hwC⟩ := hyC hpinY
          have haxisY : axis = Axis.y := haxis.trans hAx
          rw [haxisY] at hDBstart hDBlen hDCstart hDClen
          have eB : b'.rect.y = b.rect.y + DB := hDBstart
          have eC : c'.rect.y = c.rect.y + DC := hDCstart
          have eBh : b'.rect.h = b.rect.h := hDBlen
          have eCh : c'.rect.h = c.rect.h := hDClen
          refine ⟨b, hbin, c, hcin, hidB, hidC, hexB', hexC', hparB, hparC, ?_, ?_, ?_⟩
          · intro hX
            exact absurd hX (by decide)
          · intro _
            exact ⟨hxB', hwB, eBh, hxC', hwC, eCh⟩
          · constructor
            · intro hX
              exact absurd hX (by decide)
            · intro _
              exact Or.inl (by omega)
      · exact (hnbC C hCmem hCid).elim
    · exact (hnbB B hBmem hBid).elim

theorem pinC3Cross_of_pin {boxes : List ModelBox} {o : Options} {s r : Scene}
    {axis : Axis} {sp : Spacing}
    (hcover : PinBoxCoverage boxes s axis sp)
    (hsNodup : (s.boxes.map (·.id)).Nodup)
    (hBoxesNodup : (boxes.map (·.id)).Nodup)
    (hNe : ∀ b ∈ boxes, b.id ≠ "")
    (hC3 : Validator.C3 s.layoutDump)
    (hsetup : PinSetup s (layBands boxes s axis sp (lanesOf boxes)))
    (haxis : axis = Axis.ofDirection o.direction)
    (hsp : spacingOf o.profile = .ok sp)
    (h : pinBands boxes o s = .ok r) :
    PinC3Cross o s r := by
  cases hLanes : lanesOf boxes with
  | nil =>
    have hNo : pinBands boxes o s = .ok s := pinBands_no_lanes hLanes
    have hrS : r = s := by rw [hNo] at h; simpa only [Except.ok.injEq] using h.symm
    subst hrS
    unfold PinC3Cross
    constructor
    · intro b' hb' hne p hp
      have hpmem : p ∈ r.boxes := by
        have h' : r.boxes.find? (fun b => b.id == b'.parent) = some p := hp
        exact List.mem_of_find?_eq_some h'
      exact ⟨b', hb', p, hpmem, rfl, rfl, rfl, hp, fun _ => ⟨rfl, rfl, rfl, rfl⟩,
        fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
    · intro b' hb' hne p hp
      have hCont := hC3 b' hb' hne p hp
      constructor
      · intro _
        unfold Rect.Contained at hCont
        exact ⟨hCont.1, hCont.2.1⟩
      · intro _
        unfold Rect.Contained at hCont
        exact ⟨hCont.2.2.1, hCont.2.2.2⟩
  | cons lane rest =>
    have hNeLanes : lanesOf boxes ≠ [] := by
      rw [hLanes]; intro hnil; cases hnil
    obtain ⟨sp', axis', bands, pinned, routed, origin, strip, stripScene,
      hsp', haxis', hbands, happ, hroute, horig, _hstrip, hStripEq, hgrow⟩ :=
      pinBands_spec (boxes := boxes) (o := o) (s := s) (r := r) hNeLanes h
    have hspEq : sp' = sp := by
      have h := hsp'.symm.trans hsp
      simpa only [Except.ok.injEq] using h
    have haxisEq : axis' = axis := haxis'.trans haxis.symm
    rw [haxisEq] at hbands happ hroute horig hStripEq hgrow haxis'
    rw [hspEq] at hbands hroute hsp'
    have hLanesNodup : (lanesOf boxes).Nodup := boxClauses_lanes_nodup hBoxesNodup
    have hNeLanes' : "" ∉ lanesOf boxes := by
      intro hmem
      obtain ⟨mb, hmb, _, _, hid⟩ := boxClauses_lanesOf_mem hmem
      exact hNe mb hmb hid
    have hndB : (bands.map (·.id)).Nodup := by
      rw [hbands]
      exact boxClauses_layBands_ids_nodup boxes s axis sp (lanesOf boxes) hLanesNodup hNeLanes'
    obtain ⟨oDelta, hcorr⟩ :=
      boxClauses_master hBoxesNodup hNe hbands happ hroute horig hStripEq hgrow
    rw [← hbands] at hsetup
    obtain ⟨hparShift, hsibShift, hframeTop, hidsNe, hparMember⟩ := hsetup
    obtain ⟨ht, hc⟩ := spacing_of_nonneg hsp
    have hpin : (buildPin axis bands s).axis = axis := rfl
    have hsetup2 : ∀ (b' : Box), b' ∈ r.boxes → ∀ (p : Box),
        b'.parent ≠ "" → r.layoutDump.box? b'.parent = some p →
        ∃ b ∈ s.boxes, ∃ q ∈ s.boxes,
          b.id = b'.id ∧ q.id = p.id ∧ b.parent = b'.parent ∧
          s.layoutDump.box? b.parent = some q ∧
          q.rect.Contained b.rect ∧
          (Axis.ofDirection o.direction = Axis.x → b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h ∧
            p.rect.y = q.rect.y ∧ p.rect.h = q.rect.h) ∧
          (Axis.ofDirection o.direction = Axis.y → b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w ∧
            p.rect.x = q.rect.x ∧ p.rect.w = q.rect.w) ∧
          ((∃ D, Axis.start axis b'.rect = Axis.start axis b.rect + D ∧
            Axis.length axis b'.rect = Axis.length axis b.rect ∧
            D = (buildPin axis bands s).boxDelta b.id + oDelta) ∨
            (∃ band ∈ bands, b.id = band.id ∧
              Axis.start axis b'.rect = band.start + oDelta ∧
              Axis.length axis b'.rect = band.thickness)) ∧
          ((∃ D, Axis.start axis p.rect = Axis.start axis q.rect + D ∧
            Axis.length axis p.rect = Axis.length axis q.rect ∧
            D = (buildPin axis bands s).boxDelta q.id + oDelta) ∨
            (∃ band ∈ bands, q.id = band.id ∧
              Axis.start axis p.rect = band.start + oDelta ∧
              Axis.length axis p.rect = band.thickness)) := by
      intro b' hb' p hne hp
      have hpmem : p ∈ r.boxes := by
        have h' : r.boxes.find? (fun b => b.id == b'.parent) = some p := hp
        exact List.mem_of_find?_eq_some h'
      obtain ⟨b, hbin, hidB, hparB, _hroleB, _hexB, hxB, hyB, hrectB⟩ := hcorr b' hb'
      obtain ⟨q, hqin, hidQ, hparQ, _hroleQ, _hexQ, hxQ, hyQ, hrectQ⟩ := hcorr p hpmem
      have hpid : p.id = b'.parent := find_some_id hp
      have hqparent : q.id = b.parent := hidQ.symm.trans (hpid.trans hparB)
      have hneB : b.parent ≠ "" := by rw [← hparB]; exact hne
      have hlookS : s.layoutDump.box? b.parent = some q := by
        have h1 : s.boxes.find? (fun a => a.id == q.id) = some q :=
          sceneFind_eq_self hsNodup hqin
        have h2 : s.boxes.find? (fun a => a.id == b.parent) = some q := by
          rw [← hqparent]; exact h1
        exact h2
      have hCont := hC3 b hbin hneB q hlookS
      refine ⟨b, hbin, q, hqin, hidB.symm, hidQ.symm, hparB.symm, hlookS, hCont, ?_, ?_,
        hrectB, hrectQ⟩
      · intro hAxX
        have hpinX : (buildPin axis bands s).axis = Axis.x :=
          hpin.trans (haxis.trans hAxX)
        obtain ⟨hyB, hhB⟩ := hxB hpinX
        obtain ⟨hyQ, hhQ⟩ := hxQ hpinX
        exact ⟨hyB, hhB, hyQ, hhQ⟩
      · intro hAxY
        have hpinY : (buildPin axis bands s).axis = Axis.y :=
          hpin.trans (haxis.trans hAxY)
        obtain ⟨hxB', hwB⟩ := hyB hpinY
        obtain ⟨hxQ', hwQ⟩ := hyQ hpinY
        exact ⟨hxB', hwB, hxQ', hwQ⟩
    unfold PinC3Cross
    constructor
    · intro b' hb' hne p hp
      obtain ⟨b, hbin, q, hqin, hid, hqid, hpar, hlook, hC, hx, hy, _, _⟩ :=
        hsetup2 b' hb' p hne hp
      exact ⟨b, hbin, q, hqin, hid, hqid, hpar, hlook, hx, hy⟩
    · intro b' hb' hne p hp
      obtain ⟨b, hbin, q, hqin, hid, hqid, hpar, hlook, hC, hx, hy, hrectB, hrectQ⟩ :=
        hsetup2 b' hb' p hne hp
      have hpid : p.id = b'.parent := find_some_id hp
      have hqparent : q.id = b.parent := hqid.trans (hpid.trans hpar.symm)
      have hneB : b.parent ≠ "" := by rw [hpar]; exact hne
      have hxC : q.rect.x ≤ b.rect.x ∧ b.rect.x + b.rect.w ≤ q.rect.x + q.rect.w := by
        unfold Rect.Contained at hC
        exact ⟨hC.1, hC.2.1⟩
      have hyC : q.rect.y ≤ b.rect.y ∧ b.rect.y + b.rect.h ≤ q.rect.y + q.rect.h := by
        unfold Rect.Contained at hC
        exact ⟨hC.2.2.1, hC.2.2.2⟩
      constructor
      · intro hAxX
        rcases hrectB with ⟨DB, hDBstart, hDBlen, hDBdelta⟩ | ⟨B, hBmem, hBid, _, _⟩
        · rcases hrectQ with ⟨DQ, hDQstart, hDQlen, hDQdelta⟩ | ⟨Q, hQmem, hQid, hQstart, hQlen⟩
          · have hshiftEq : bandShift bands b.id = bandShift bands q.id :=
              hparShift b hbin hneB q hqin hqparent
            have hboxB : (buildPin axis bands s).boxDelta b.id = bandShift bands b.id :=
              boxClauses_pinBoxDelta_eq axis bands s b.id
            have hboxC : (buildPin axis bands s).boxDelta q.id = bandShift bands q.id :=
              boxClauses_pinBoxDelta_eq axis bands s q.id
            have hDD : DB = DQ := by
              rw [hDBdelta, hDQdelta, hboxB, hboxC, hshiftEq]
            have haxisX : axis = Axis.x := haxis.trans hAxX
            rw [haxisX] at hDBstart hDBlen hDQstart hDQlen
            have eB : b'.rect.x = b.rect.x + DB := hDBstart
            have eQ : p.rect.x = q.rect.x + DQ := hDQstart
            have eBw : b'.rect.w = b.rect.w := hDBlen
            have eQw : p.rect.w = q.rect.w := hDQlen
            omega
          · have hqne : q.id ≠ "" := by rw [hqparent]; exact hneB
            have hQne : Q.id ≠ "" := by rw [← hQid]; exact hqne
            obtain ⟨hmem, hshift⟩ :=
              hparMember b hbin q hqin Q hQmem hqparent.symm hQid.symm hQne
            have hfind : s.boxes.find? (fun b' => b'.id == b.id) = some b :=
              sceneFind_eq_self hsNodup hbin
            have hwithin := bandWithin ht hc hQmem hQne hbands hmem hfind
            have hboxB : (buildPin axis bands s).boxDelta b.id = bandShift bands b.id :=
              boxClauses_pinBoxDelta_eq axis bands s b.id
            have hDBQ : DB = Q.shift + oDelta := by
              rw [hDBdelta, hboxB, hshift]
            have haxisX : axis = Axis.x := haxis.trans hAxX
            rw [haxisX] at hDBstart hDBlen hQstart hQlen hwithin
            have eB : b'.rect.x = b.rect.x + DB := hDBstart
            have eBw : b'.rect.w = b.rect.w := hDBlen
            have eQ : p.rect.x = Q.start + oDelta := hQstart
            have eQw : p.rect.w = Q.thickness := hQlen
            have hw1 : Q.start ≤ b.rect.x + Q.shift ∧
                b.rect.x + b.rect.w + Q.shift ≤ Q.start + Q.thickness := hwithin
            omega
        · have hBne : B.id ≠ "" := by rw [← hBid]; exact hidsNe b hbin
          have htop := hframeTop b hbin ⟨B, hBmem, hBid.symm, hBne⟩
          exact (hneB htop.1).elim
      · intro hAxY
        rcases hrectB with ⟨DB, hDBstart, hDBlen, hDBdelta⟩ | ⟨B, hBmem, hBid, _, _⟩
        · rcases hrectQ with ⟨DQ, hDQstart, hDQlen, hDQdelta⟩ | ⟨Q, hQmem, hQid, hQstart, hQlen⟩
          · have hshiftEq : bandShift bands b.id = bandShift bands q.id :=
              hparShift b hbin hneB q hqin hqparent
            have hboxB : (buildPin axis bands s).boxDelta b.id = bandShift bands b.id :=
              boxClauses_pinBoxDelta_eq axis bands s b.id
            have hboxC : (buildPin axis bands s).boxDelta q.id = bandShift bands q.id :=
              boxClauses_pinBoxDelta_eq axis bands s q.id
            have hDD : DB = DQ := by
              rw [hDBdelta, hDQdelta, hboxB, hboxC, hshiftEq]
            have haxisY : axis = Axis.y := haxis.trans hAxY
            rw [haxisY] at hDBstart hDBlen hDQstart hDQlen
            have eB : b'.rect.y = b.rect.y + DB := hDBstart
            have eQ : p.rect.y = q.rect.y + DQ := hDQstart
            have eBh : b'.rect.h = b.rect.h := hDBlen
            have eQh : p.rect.h = q.rect.h := hDQlen
            omega
          · have hqne : q.id ≠ "" := by rw [hqparent]; exact hneB
            have hQne : Q.id ≠ "" := by rw [← hQid]; exact hqne
            obtain ⟨hmem, hshift⟩ :=
              hparMember b hbin q hqin Q hQmem hqparent.symm hQid.symm hQne
            have hfind : s.boxes.find? (fun b' => b'.id == b.id) = some b :=
              sceneFind_eq_self hsNodup hbin
            have hwithin := bandWithin ht hc hQmem hQne hbands hmem hfind
            have hboxB : (buildPin axis bands s).boxDelta b.id = bandShift bands b.id :=
              boxClauses_pinBoxDelta_eq axis bands s b.id
            have hDBQ : DB = Q.shift + oDelta := by
              rw [hDBdelta, hboxB, hshift]
            have haxisY : axis = Axis.y := haxis.trans hAxY
            rw [haxisY] at hDBstart hDBlen hQstart hQlen hwithin
            have eB : b'.rect.y = b.rect.y + DB := hDBstart
            have eBh : b'.rect.h = b.rect.h := hDBlen
            have eQ : p.rect.y = Q.start + oDelta := hQstart
            have eQh : p.rect.h = Q.thickness := hQlen
            have hw1 : Q.start ≤ b.rect.y + Q.shift ∧
                b.rect.y + b.rect.h + Q.shift ≤ Q.start + Q.thickness := hwithin
            omega
        · have hBne : B.id ≠ "" := by rw [← hBid]; exact hidsNe b hbin
          have htop := hframeTop b hbin ⟨B, hBmem, hBid.symm, hBne⟩
          exact (hneB htop.1).elim

theorem pinBands_c3' {boxes : List ModelBox} {o : Options} {s r : Scene}
    {axis : Axis} {sp : Spacing}
    (hcover : PinBoxCoverage boxes s axis sp)
    (hsNodup : (s.boxes.map (·.id)).Nodup)
    (hBoxesNodup : (boxes.map (·.id)).Nodup)
    (hNe : ∀ b ∈ boxes, b.id ≠ "")
    (hC3 : Validator.C3 s.layoutDump)
    (hsetup : PinSetup s (layBands boxes s axis sp (lanesOf boxes)))
    (haxis : axis = Axis.ofDirection o.direction)
    (hsp : spacingOf o.profile = .ok sp)
    (h : pinBands boxes o s = .ok r) :
    Validator.C3 r.layoutDump :=
  pinBands_c3 hC3
    (pinC3Cross_of_pin hcover hsNodup hBoxesNodup hNe hC3 hsetup haxis hsp h) h

theorem pinBands_c2' {boxes : List ModelBox} {o : Options} {s r : Scene}
    {axis : Axis} {sp : Spacing}
    (hcover : PinBoxCoverage boxes s axis sp)
    (hBoxesNodup : (boxes.map (·.id)).Nodup)
    (hNe : ∀ b ∈ boxes, b.id ≠ "")
    (hsetup : PinSetup s (layBands boxes s axis sp (lanesOf boxes)))
    (haxis : axis = Axis.ofDirection o.direction)
    (hsp : spacingOf o.profile = .ok sp)
    (hC2 : Validator.C2 s.layoutDump)
    (h : pinBands boxes o s = .ok r) :
    Validator.C2 r.layoutDump :=
  pinBands_c2 hC2
    (pinC2Sep_of_pin hcover hBoxesNodup hNe hsetup haxis hsp h) h

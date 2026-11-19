import Elegant.Layered.LaneBandsPhaseFacts
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

/-- Cross-axis cover for the pinned scene: every output box keeps its
other-axis coordinates and sizes from an input box, the canvas keeps its
other-axis extent, and the output box lies inside the output canvas along
the pinning axis. The cross part is what `growCanvas_exact` supplies after
the origin restore; the other part follows from the input clause because
every pinning move is rigid along the other axis. -/
def PinC1Cover (o : Options) (s r : Scene) : Prop :=
  (∀ b' ∈ r.boxes, ∃ b ∈ s.boxes, b'.id = b.id ∧
    (Axis.ofDirection o.direction = Axis.x → b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h) ∧
    (Axis.ofDirection o.direction = Axis.y → b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w))
  ∧ (Axis.ofDirection o.direction = Axis.x → r.canvas.h = s.canvas.h)
  ∧ (Axis.ofDirection o.direction = Axis.y → r.canvas.w = s.canvas.w)
  ∧ (∀ b' ∈ r.boxes,
      (Axis.ofDirection o.direction = Axis.x →
        0 ≤ b'.rect.x ∧ b'.rect.x + b'.rect.w ≤ r.canvas.w) ∧
      (Axis.ofDirection o.direction = Axis.y →
        0 ≤ b'.rect.y ∧ b'.rect.y + b'.rect.h ≤ r.canvas.h))

/-- Parent-cover residual for clause C3: every output parent edge comes from
an input parent edge with the same other-axis geometry, and the output
child lies inside its output parent along the pinning axis. The cross part
is the band fact (`laneBand` is laid out from `contentValues` bounds plus
title and clearances, so the shifted member interval sits inside the lane
band rect that replaces the lane frame); nested groups move rigidly with
their members, so their other-axis containment transfers from the input. -/
def PinC3Cross (o : Options) (s r : Scene) : Prop :=
  (∀ b' ∈ r.boxes, b'.parent ≠ "" → ∀ p, r.layoutDump.box? b'.parent = some p →
    ∃ b ∈ s.boxes, ∃ q ∈ s.boxes, b.id = b'.id ∧ q.id = p.id ∧ b.parent = b'.parent ∧
      s.layoutDump.box? b.parent = some q ∧
      (Axis.ofDirection o.direction = Axis.x →
        b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h ∧
        p.rect.y = q.rect.y ∧ p.rect.h = q.rect.h) ∧
      (Axis.ofDirection o.direction = Axis.y →
        b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w ∧
        p.rect.x = q.rect.x ∧ p.rect.w = q.rect.w))
  ∧ (∀ b' ∈ r.boxes, b'.parent ≠ "" → ∀ p, r.layoutDump.box? b'.parent = some p →
      (Axis.ofDirection o.direction = Axis.x →
        p.rect.x ≤ b'.rect.x ∧ b'.rect.x + b'.rect.w ≤ p.rect.x + p.rect.w) ∧
      (Axis.ofDirection o.direction = Axis.y →
        p.rect.y ≤ b'.rect.y ∧ b'.rect.y + b'.rect.h ≤ p.rect.y + p.rect.h))

/-- Separation residual for clause C2: every output exclusive same-parent
pair comes from an input pair with the same identity, exclusivity, parents
and other-axis geometry, and either both boxes moved by one common
cross-axis shift (so disjointness transfers by rigid translation) or their
cross intervals are already disjoint (so they are disjoint outright).
Lane frames are groups and hence non-exclusive on executed runs, so pairs
involving them are vacuous; when they are exclusive they sit in disjoint
bands and fall in the cross-separated case. -/
def PinC2Sep (o : Options) (s r : Scene) : Prop :=
  ∀ b' ∈ r.boxes, ∀ c' ∈ r.boxes, b'.id ≠ c'.id → b'.exclusive = true →
    c'.exclusive = true → b'.parent = c'.parent →
    ∃ b ∈ s.boxes, ∃ c ∈ s.boxes, b'.id = b.id ∧ c'.id = c.id ∧
      b'.exclusive = b.exclusive ∧ c'.exclusive = c.exclusive ∧
      b'.parent = b.parent ∧ c'.parent = c.parent ∧
      (Axis.ofDirection o.direction = Axis.x →
        b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h ∧ b'.rect.w = b.rect.w ∧
        c'.rect.y = c.rect.y ∧ c'.rect.h = c.rect.h ∧ c'.rect.w = c.rect.w) ∧
      (Axis.ofDirection o.direction = Axis.y →
        b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w ∧ b'.rect.h = b.rect.h ∧
        c'.rect.x = c.rect.x ∧ c'.rect.w = c.rect.w ∧ c'.rect.h = c.rect.h) ∧
      ((Axis.ofDirection o.direction = Axis.x →
        b'.rect.x - b.rect.x = c'.rect.x - c.rect.x ∨
        b'.rect.x + b'.rect.w ≤ c'.rect.x ∨ c'.rect.x + c'.rect.w ≤ b'.rect.x) ∧
       (Axis.ofDirection o.direction = Axis.y →
        b'.rect.y - b.rect.y = c'.rect.y - c.rect.y ∨
        b'.rect.y + b'.rect.h ≤ c'.rect.y ∨ c'.rect.y + c'.rect.h ≤ b'.rect.y))

private theorem boxClauses_foldl_min_mem (l : List Int) (v0 v : Int)
    (h : v ∈ v0 :: l) : l.foldl min v0 ≤ v := by
  induction l generalizing v0 with
  | nil =>
    simp at h
    simp only [List.foldl_nil]
    omega
  | cons a rest ih =>
    simp only [List.mem_cons] at h
    rcases h with hEq | hOr
    · rw [hEq]
      simp only [List.foldl_cons]
      have h1 := foldl_min_le rest (min v0 a)
      omega
    · rcases hOr with hEq2 | hmemRest
      · rw [hEq2]
        simp only [List.foldl_cons]
        have h1 := foldl_min_le rest (min v0 a)
        omega
      · have hIH : rest.foldl min (min v0 a) ≤ v :=
          ih (min v0 a) (List.mem_cons.mpr (Or.inr hmemRest))
        simp only [List.foldl_cons] at hIH ⊢
        exact hIH

private theorem boxClauses_foldl_max_mem (l : List Int) (v0 v : Int)
    (h : v ∈ v0 :: l) : v ≤ l.foldl max v0 := by
  induction l generalizing v0 with
  | nil =>
    simp at h
    simp only [List.foldl_nil]
    omega
  | cons a rest ih =>
    simp only [List.mem_cons] at h
    rcases h with hEq | hOr
    · rw [hEq]
      simp only [List.foldl_cons]
      have h1 := le_foldl_max rest (max v0 a)
      omega
    · rcases hOr with hEq2 | hmemRest
      · rw [hEq2]
        simp only [List.foldl_cons]
        have h1 := le_foldl_max rest (max v0 a)
        omega
      · have hIH : v ≤ rest.foldl max (max v0 a) :=
          ih (max v0 a) (List.mem_cons.mpr (Or.inr hmemRest))
        simp only [List.foldl_cons] at hIH ⊢
        exact hIH

private theorem boxClauses_bounds_mem {vs : List Int} {lo hi v : Int}
    (h : bounds vs = some (lo, hi)) (hmem : v ∈ vs) : lo ≤ v ∧ v ≤ hi := by
  cases vs with
  | nil => simp only [bounds] at h; cases h
  | cons v0 rest =>
    simp only [bounds, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨boxClauses_foldl_min_mem rest v0 v hmem,
      boxClauses_foldl_max_mem rest v0 v hmem⟩

private theorem boxClauses_geom_start_mem_false {axis : Axis} {s : Scene} {b : Box}
    (hb : b ∈ s.boxes) : axis.start b.rect ∈ geometryValues axis false s := by
  simp [geometryValues]
  exact Or.inl ⟨b, hb, rfl⟩

private theorem boxClauses_geom_start_mem_true {axis : Axis} {s : Scene} {b : Box}
    (hb : b ∈ s.boxes) : axis.start b.rect ∈ geometryValues axis true s := by
  simp [geometryValues, rectValues]
  exact Or.inl ⟨b, hb, Or.inl rfl⟩

private theorem boxClauses_geom_far_mem_true {axis : Axis} {s : Scene} {b : Box}
    (hb : b ∈ s.boxes) :
    axis.start b.rect + axis.length b.rect ∈ geometryValues axis true s := by
  simp [geometryValues, rectValues]
  exact Or.inl ⟨b, hb, Or.inr rfl⟩
private theorem boxClauses_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem boxClauses_pinShiftBox_ok {b b' : Box} {pin : Pin} {axis : Axis}
    (h : (do pure { b with rect := ← (Move.constant (pin.boxDelta b.id)).rect axis b.rect } : Except LayoutError Box) = .ok b') :
    b'.id = b.id ∧ b'.parent = b.parent ∧
    ∃ w, Measure.checkedI32 (axis.start b.rect + pin.boxDelta b.id) = .ok w ∧
      b'.rect = axis.withStart b.rect w ∧ w = axis.start b.rect + pin.boxDelta b.id := by
  obtain ⟨rect, hrect, hrfl⟩ := boxClauses_bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  obtain ⟨w, hw, hrectEq, hval⟩ := moveConstant_rect_value hrect
  exact ⟨rfl, rfl, w, hw, hrectEq, hval⟩

private theorem boxClauses_pinShift_mem (l : List Box) (pin : Pin) (axis : Axis) :
    ∀ (l' : List Box),
    l.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant (pin.boxDelta b.id)).rect axis b.rect } : Except LayoutError Box)) = .ok l' →
    ∀ b' ∈ l', ∃ b ∈ l, b'.id = b.id ∧ b'.parent = b.parent ∧
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
    · obtain ⟨hid1, hpar1, w, hw, heq, hval⟩ := boxClauses_pinShiftBox_ok hfirst
      exact ⟨head, List.mem_cons.mpr (Or.inl rfl), hid1, hpar1, w, hw, heq, hval⟩
    · obtain ⟨b, hbin, hid, hpar, w, hw, heq, hval⟩ := ih _ hrest _ hmem
      exact ⟨b, List.mem_cons.mpr (Or.inr hbin), hid, hpar, w, hw, heq, hval⟩

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

private theorem boxClauses_placeRect_other_x {start thickness : Int} {r : Rect} :
    (placeRect Axis.x start thickness r).y = r.y ∧
    (placeRect Axis.x start thickness r).h = r.h :=
  ⟨rfl, rfl⟩

private theorem boxClauses_placeRect_other_y {start thickness : Int} {r : Rect} :
    (placeRect Axis.y start thickness r).x = r.x ∧
    (placeRect Axis.y start thickness r).w = r.w :=
  ⟨rfl, rfl⟩
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

private theorem boxClauses_replaceFrame_mem {axis : Axis} {band : Band} {s s' : Scene}
    (h : replaceFrame axis band s = .ok s') :
    ∀ b' ∈ s'.boxes, ∃ b ∈ s.boxes, b'.id = b.id ∧
      (axis = Axis.x → b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h) ∧
      (axis = Axis.y → b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w) := by
  unfold replaceFrame at h
  cases hfind : s.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    simp only [hfind, Pure.pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h
    intro b' hb'
    exact ⟨b', hb', rfl, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩
  | some idx =>
    simp only [hfind] at h
    cases hstart : Measure.checkedI32 band.start with
    | error _e => simp [hstart, Bind.bind, Except.bind] at h
    | ok _s =>
      simp only [hstart, Bind.bind, Except.bind] at h
      cases hthick : Measure.checkedI32 band.thickness with
      | error _e => simp [hthick] at h
      | ok _t =>
        simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at h
        subst h
        intro b' hb'
        have hmem := boxClauses_mapIdx_place_mem_aux s.boxes 0 idx axis
          (placeRect axis _s _t)
          (by intro hAx; rw [hAx]; intro r; exact boxClauses_placeRect_other_x)
          (by intro hAx; rw [hAx]; intro r; exact boxClauses_placeRect_other_y) _ hb'
        obtain ⟨b, hbin, hid, hx, hy⟩ := hmem
        exact ⟨b, hbin, hid, hx, hy⟩
private theorem boxClauses_foldReplace_mem (bands : List Band) (axis : Axis) (s : Scene) :
    ∀ (s' : Scene),
    bands.foldlM (fun scene band => replaceFrame axis band scene) s = .ok s' →
    ∀ b' ∈ s'.boxes, ∃ b ∈ s.boxes, b'.id = b.id ∧
      (axis = Axis.x → b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h) ∧
      (axis = Axis.y → b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w) := by
  induction bands generalizing s with
  | nil =>
    intro s' h b' hb'
    have he : s' = s := by
      simpa only [List.foldlM_nil, Pure.pure, Except.pure,
        Except.ok.injEq] using h.symm
    subst he
    exact ⟨b', hb', rfl, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩
  | cons band rest ih =>
    intro s' h b' hb'
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, h⟩ := boxClauses_bind_ok h
    obtain ⟨m, hmin, hid1, hx1, hy1⟩ := ih mid s' h _ hb'
    obtain ⟨b, hbin, hid2, hx2, hy2⟩ := boxClauses_replaceFrame_mem hmid _ hmin
    refine ⟨b, hbin, hid1.trans hid2, ?_, ?_⟩
    · intro hAx
      obtain ⟨hyM, hhM⟩ := hx1 hAx
      obtain ⟨hyB, hhB⟩ := hx2 hAx
      omega
    · intro hAx
      obtain ⟨hxM, hwM⟩ := hy1 hAx
      obtain ⟨hxB, hwB⟩ := hy2 hAx
      omega

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
private theorem boxClauses_restoreOrigin_nonneg {axis : Axis} {s origin : Scene}
    (h : restoreOrigin axis s = .ok origin) :
    ∀ b' ∈ origin.boxes, 0 ≤ axis.start b'.rect := by
  unfold restoreOrigin at h
  cases hbounds : bounds (geometryValues axis false s) with
  | none =>
    simp only [hbounds] at h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro b' hb'
    have hmem := boxClauses_geom_start_mem_false (axis := axis) hb'
    have hempty : geometryValues axis false s = [] := by
      cases hlist : geometryValues axis false s with
      | nil => rfl
      | cons hd tl =>
        simp only [hlist, bounds] at hbounds
        cases hbounds
    rw [hempty] at hmem
    simp at hmem
  | some p =>
    simp only [hbounds] at h
    cases p with
    | mk lo hi =>
      simp only at h
      by_cases hlo : lo < 0
      · simp only [hlo, ↓reduceIte] at h
        intro b' hb'
        obtain ⟨b, hbin, hid, w, hw, heq, hval⟩ :=
          boxClauses_shiftAll_scene_mem h _ hb'
        have hmem := boxClauses_geom_start_mem_false (axis := axis) hbin
        have hle := (boxClauses_bounds_mem hbounds hmem).1
        have hstart : axis.start b'.rect = w := by
          cases axis with
          | x => simp [heq, Axis.start, Axis.withStart]
          | y => simp [heq, Axis.start, Axis.withStart]
        omega
      · simp only [hlo, ↓reduceIte] at h
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at h

        subst h
        intro b' hb'
        have hmem := boxClauses_geom_start_mem_false (axis := axis) hb'
        have hle := (boxClauses_bounds_mem hbounds hmem).1
        omega

private theorem boxClauses_highest_covers {axis : Axis} {s : Scene} {b : Box}
    (hb : b ∈ s.boxes) :
    axis.start b.rect + axis.length b.rect ≤ highest axis s := by
  have hmem := boxClauses_geom_far_mem_true (axis := axis) hb
  cases hbounds : bounds (geometryValues axis true s) with
  | none =>
    have hempty : geometryValues axis true s = [] := by
      cases hlist : geometryValues axis true s with
      | nil => rfl
      | cons hd tl =>
        simp only [hlist, bounds] at hbounds
        cases hbounds
    rw [hempty] at hmem
    simp at hmem
  | some p =>
    obtain ⟨lo, hi⟩ := p
    have hle := (boxClauses_bounds_mem hbounds hmem).2
    have hhigh : highest axis s = max 0 hi := by
      unfold highest
      rw [hbounds]
      simp

    rw [hhigh]
    omega
private theorem boxClauses_growCanvas_other {axis : Axis} {canvas : Size} {s r : Scene}
    (h : growCanvas axis canvas s = .ok r) :
    (axis = Axis.x → r.canvas.h = canvas.h) ∧
    (axis = Axis.y → r.canvas.w = canvas.w) := by
  unfold growCanvas at h
  cases hgrown : Measure.checkedI32 (highest axis s) with
  | error e => simp [hgrown, Bind.bind, Except.bind] at h
  | ok grown =>
    simp only [hgrown, Bind.bind, Except.bind, Pure.pure, Except.pure,
      Except.ok.injEq] at h
    subst h
    constructor
    · intro hAx
      rw [hAx]
      rfl
    · intro hAx
      rw [hAx]
      rfl

private theorem boxClauses_applyPin_mem {pin : Pin} {bands : List Band} {s pinned : Scene}
    (h : applyPin pin bands s = .ok pinned) :
    ∀ b' ∈ pinned.boxes, ∃ b ∈ s.boxes, b'.id = b.id ∧
      (pin.axis = Axis.x → b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h) ∧
      (pin.axis = Axis.y → b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w) := by
  obtain ⟨shiftedBoxes, shiftedLabels, shiftedRoutes, shiftedItems,
    hboxes, _hlabels, _hroutes, _hitems, hfold⟩ := applyPin_shifted h
  intro b' hb'
  obtain ⟨m, hmin, hid1, hxFold, hyFold⟩ :=
    boxClauses_foldReplace_mem bands pin.axis ({ s with boxes := shiftedBoxes, labels := shiftedLabels, routes := shiftedRoutes, items := shiftedItems } : Scene) _ hfold _ hb'
  obtain ⟨b, hbin, hid2, _hpar2, w2, _hw2, heq2, _hval2⟩ :=
    boxClauses_pinShift_mem s.boxes pin pin.axis _ hboxes _ hmin
  refine ⟨b, hbin, hid1.trans hid2, ?_, ?_⟩
  · intro hAx
    obtain ⟨hyM, hhM⟩ := hxFold hAx
    have h1 : m.rect = pin.axis.withStart b.rect w2 := heq2
    rw [hAx] at h1
    have hyB : m.rect.y = b.rect.y := calc m.rect.y
        = (Axis.x.withStart b.rect w2).y := by rw [h1]
      _ = b.rect.y := rfl
    have hhB : m.rect.h = b.rect.h := calc m.rect.h
        = (Axis.x.withStart b.rect w2).h := by rw [h1]
      _ = b.rect.h := rfl
    exact ⟨hyM.trans hyB, hhM.trans hhB⟩
  · intro hAx
    obtain ⟨hxM, hwM⟩ := hyFold hAx
    have h1 : m.rect = pin.axis.withStart b.rect w2 := heq2
    rw [hAx] at h1
    have hxB : m.rect.x = b.rect.x := calc m.rect.x
        = (Axis.y.withStart b.rect w2).x := by rw [h1]
      _ = b.rect.x := rfl
    have hwB : m.rect.w = b.rect.w := calc m.rect.w
        = (Axis.y.withStart b.rect w2).w := by rw [h1]
      _ = b.rect.w := rfl
    exact ⟨hxM.trans hxB, hwM.trans hwB⟩





private theorem boxClauses_disjoint_of_shift_x {a a' b b' : Rect} {d : Int}
    (haX : a'.x = a.x + d) (hbX : b'.x = b.x + d)
    (haW : a'.w = a.w) (hbW : b'.w = b.w)
    (haY : a'.y = a.y) (haH : a'.h = a.h)
    (hbY : b'.y = b.y) (hbH : b'.h = b.h)
    (hDisj : Disjoint a b) : Disjoint a' b' := by
  unfold Disjoint Rect.meetsInterior at hDisj ⊢
  omega

private theorem boxClauses_disjoint_of_shift_y {a a' b b' : Rect} {d : Int}
    (haY : a'.y = a.y + d) (hbY : b'.y = b.y + d)
    (haH : a'.h = a.h) (hbH : b'.h = b.h)
    (haX : a'.x = a.x) (haW : a'.w = a.w)
    (hbX : b'.x = b.x) (hbW : b'.w = b.w)
    (hDisj : Disjoint a b) : Disjoint a' b' := by
  unfold Disjoint Rect.meetsInterior at hDisj ⊢
  omega

private theorem boxClauses_disjoint_of_cross_x {a b : Rect}
    (h : a.x + a.w ≤ b.x ∨ b.x + b.w ≤ a.x) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  omega

private theorem boxClauses_disjoint_of_cross_y {a b : Rect}
    (h : a.y + a.h ≤ b.y ∨ b.y + b.h ≤ a.y) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  omega

theorem pinC1Cover_of_pin {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hC1 : Validator.C1 s.layoutDump) (h : pinBands boxes o s = .ok r) :
    PinC1Cover o s r := by
  cases hLanes : lanesOf boxes with
  | nil =>
    have hNo : pinBands boxes o s = .ok s := pinBands_no_lanes hLanes
    rw [hNo] at h
    cases h
    unfold PinC1Cover
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b' hb'
      exact ⟨b', hb', rfl, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩
    · intro _; rfl
    · intro _; rfl
    · intro b' hb'
      constructor
      · intro _
        have hCont := hC1 b' hb'
        simp only [Validator.canvasRect, Rect.Contained, Scene.layoutDump] at hCont ⊢
        omega
      · intro _
        have hCont := hC1 b' hb'
        simp only [Validator.canvasRect, Rect.Contained, Scene.layoutDump] at hCont ⊢
        omega
  | cons lane rest =>
    have hNe : lanesOf boxes ≠ [] := by rw [hLanes]; simp
    obtain ⟨_sp, axis, bands, pinned, routed, origin, _strip, stripScene,
      _hsp, haxis, _hbands, happ, hroute, horig, _hstrip, hstripEq, hgrow⟩ :=
      pinBands_spec (boxes := boxes) (o := o) (s := s) (r := r) hNe h
    have hGrowEq : r.boxes = stripScene.boxes := (growCanvas_frame hgrow).1
    have hRouteEq : routed.boxes = pinned.boxes := (rerouteBands_frame hroute).1
    have hCan := boxClauses_growCanvas_other hgrow
    have hNonneg := boxClauses_restoreOrigin_nonneg horig
    unfold PinC1Cover
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b' hb'
      have hbStrip : b' ∈ stripScene.boxes := hGrowEq ▸ hb'
      have hbOrig : b' ∈ origin.boxes := by
        have hEq : stripScene.boxes = origin.boxes := by rw [hstripEq]; rfl
        rw [hEq] at hbStrip
        exact hbStrip
      have hOrigCases := restoreOrigin_cases horig
      rcases hOrigCases with hEqOr | ⟨delta, _hpos, hshift⟩
      · have hbRout : b' ∈ routed.boxes := hEqOr ▸ hbOrig
        have hbPin : b' ∈ pinned.boxes := by rw [hRouteEq] at hbRout; exact hbRout
        obtain ⟨b, hbin, hid, hx, hy⟩ := boxClauses_applyPin_mem happ _ hbPin
        have hPinAx : (buildPin axis bands s).axis = axis := rfl
        refine ⟨b, hbin, hid, ?_, ?_⟩
        · intro hAx
          have hPinX : (buildPin axis bands s).axis = Axis.x :=
            hPinAx.trans (haxis.trans hAx)
          exact hx hPinX
        · intro hAx
          have hPinY : (buildPin axis bands s).axis = Axis.y :=
            hPinAx.trans (haxis.trans hAx)
          exact hy hPinY
      · obtain ⟨bR, hbinR, hidR, wR, _hwR, heqR, _hvalR⟩ :=
          boxClauses_shiftAll_scene_mem hshift _ hbOrig
        have hbRPin : bR ∈ pinned.boxes := by
          have hEq : routed.boxes = pinned.boxes := hRouteEq
          have hbRRout : bR ∈ routed.boxes := hbinR
          rw [hEq] at hbRRout
          exact hbRRout
        obtain ⟨b, hbin, hid, hx, hy⟩ := boxClauses_applyPin_mem happ _ hbRPin
        have hPinAx : (buildPin axis bands s).axis = axis := rfl
        refine ⟨b, hbin, hidR.trans hid, ?_, ?_⟩
        · intro hAx
          have hPinX : (buildPin axis bands s).axis = Axis.x :=
            hPinAx.trans (haxis.trans hAx)
          obtain ⟨hyM, hhM⟩ := hx hPinX
          have h1 : b'.rect = axis.withStart bR.rect wR := heqR
          have h2 : axis = Axis.x := haxis.trans hAx
          rw [h2] at h1
          have hyR : b'.rect.y = bR.rect.y := calc b'.rect.y
              = ((Axis.x.withStart bR.rect wR).y) := by rw [h1]
            _ = bR.rect.y := rfl
          have hhR : b'.rect.h = bR.rect.h := calc b'.rect.h
              = ((Axis.x.withStart bR.rect wR).h) := by rw [h1]
            _ = bR.rect.h := rfl
          exact ⟨hyR.trans hyM, hhR.trans hhM⟩
        · intro hAx
          have hPinY : (buildPin axis bands s).axis = Axis.y :=
            hPinAx.trans (haxis.trans hAx)
          obtain ⟨hxM, hwM⟩ := hy hPinY
          have h1 : b'.rect = axis.withStart bR.rect wR := heqR
          have h2 : axis = Axis.y := haxis.trans hAx
          rw [h2] at h1
          have hxR : b'.rect.x = bR.rect.x := calc b'.rect.x
              = ((Axis.y.withStart bR.rect wR).x) := by rw [h1]
            _ = bR.rect.x := rfl
          have hwR : b'.rect.w = bR.rect.w := calc b'.rect.w
              = ((Axis.y.withStart bR.rect wR).w) := by rw [h1]
            _ = bR.rect.w := rfl
          exact ⟨hxR.trans hxM, hwR.trans hwM⟩
    · intro hAx
      have hAx' : axis = Axis.x := haxis.trans hAx
      obtain ⟨hCanX, _⟩ := hCan
      exact hCanX hAx'
    · intro hAx
      have hAx' : axis = Axis.y := haxis.trans hAx
      obtain ⟨_, hCanY⟩ := hCan
      exact hCanY hAx'
    · intro b' hb'
      constructor
      · intro hAx
        have hAx' : axis = Axis.x := haxis.trans hAx
        have hbStrip : b' ∈ stripScene.boxes := hGrowEq ▸ hb'
        have hbOrig : b' ∈ origin.boxes := by
          have hEq : stripScene.boxes = origin.boxes := by rw [hstripEq]; rfl
          rw [hEq] at hbStrip
          exact hbStrip
        have h0 := hNonneg _ hbOrig
        have hfar := boxClauses_highest_covers (axis := axis) hbStrip
        have hGrowCovers := growCanvas_covers hgrow
        have hGrowEx := growCanvas_exact hgrow
        obtain ⟨grown, _hg, hgEq, hCanEq⟩ := hGrowEx
        rw [hAx'] at h0 hfar hGrowCovers hCanEq
        simp only [Axis.start, Axis.length, Axis.extent, Axis.withExtent] at h0 hfar hGrowCovers hCanEq ⊢
        omega
      · intro hAx
        have hAx' : axis = Axis.y := haxis.trans hAx
        have hbStrip : b' ∈ stripScene.boxes := hGrowEq ▸ hb'
        have hbOrig : b' ∈ origin.boxes := by
          have hEq : stripScene.boxes = origin.boxes := by rw [hstripEq]; rfl
          rw [hEq] at hbStrip
          exact hbStrip
        have h0 := hNonneg _ hbOrig
        have hfar := boxClauses_highest_covers (axis := axis) hbStrip
        have hGrowCovers := growCanvas_covers hgrow
        have hGrowEx := growCanvas_exact hgrow
        obtain ⟨grown, _hg, hgEq, hCanEq⟩ := hGrowEx
        rw [hAx'] at h0 hfar hGrowCovers hCanEq
        simp only [Axis.start, Axis.length, Axis.extent, Axis.withExtent] at h0 hfar hGrowCovers hCanEq ⊢
        omega

/-- Pinning keeps clause C1 (every box in the canvas). -/
theorem pinBands_c1 {boxes : List ModelBox} {o : Options} {s r : Scene}
  (hC1 : Validator.C1 s.layoutDump)
  (h : pinBands boxes o s = .ok r) : Validator.C1 r.layoutDump := by
  have hRes := pinC1Cover_of_pin hC1 h
  cases hLanes : lanesOf boxes with
  | nil =>
    have hNo : pinBands boxes o s = .ok s := pinBands_no_lanes hLanes
    rw [hNo] at h
    cases h
    exact hC1
  | cons lane rest =>
    unfold PinC1Cover at hRes
    obtain ⟨hCorr, hCanX, hCanY, hCross⟩ := hRes
    intro b' hb'
    obtain ⟨b, hb, _hid, hx, hy⟩ := hCorr b' hb'
    have hCont := hC1 b hb
    have hCrossB := hCross b' hb'
    cases hAx : Axis.ofDirection o.direction with
    | x =>
      obtain ⟨hyEq, hhEq⟩ := hx hAx
      have hCan := hCanX hAx
      obtain ⟨hx0, hx1⟩ := (hCrossB.1 hAx)
      have hRw : r.layoutDump.canvas.w = r.canvas.w := rfl
      have hRh : r.layoutDump.canvas.h = r.canvas.h := rfl
      have hSh : s.layoutDump.canvas.h = s.canvas.h := rfl
      simp only [Validator.canvasRect, Rect.Contained, Scene.layoutDump] at hCont ⊢
      omega
    | y =>
      obtain ⟨hxEq, hwEq⟩ := hy hAx
      have hCan := hCanY hAx
      obtain ⟨hy0, hy1⟩ := (hCrossB.2 hAx)
      have hRw : r.layoutDump.canvas.w = r.canvas.w := rfl
      have hRh : r.layoutDump.canvas.h = r.canvas.h := rfl
      have hSw : s.layoutDump.canvas.w = s.canvas.w := rfl
      simp only [Validator.canvasRect, Rect.Contained, Scene.layoutDump] at hCont ⊢
      omega

/-- Pinning keeps clause C3 (a box lies inside its parent). -/
theorem pinBands_c3 {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hC3 : Validator.C3 s.layoutDump) (hRes : PinC3Cross o s r)
    (h : pinBands boxes o s = .ok r) : Validator.C3 r.layoutDump := by
  cases hLanes : lanesOf boxes with
  | nil =>
    have hNo : pinBands boxes o s = .ok s := pinBands_no_lanes hLanes
    rw [hNo] at h
    cases h
    exact hC3
  | cons lane rest =>
    unfold PinC3Cross at hRes
    obtain ⟨hLook, hCross⟩ := hRes
    intro b' hb' hne p hp
    obtain ⟨b, hb, q, hq, _hidB, _hidQ, hparEq, hlookS, hOtherX, hOtherY⟩ :=
      hLook b' hb' hne p hp
    have hneB : b.parent ≠ "" := by rw [hparEq]; exact hne
    have hCont := hC3 b hb hneB q hlookS
    have hCrossB := hCross b' hb' hne p hp
    cases hAx : Axis.ofDirection o.direction with
    | x =>
      obtain ⟨hyB, hhB, hyP, hhP⟩ := hOtherX hAx
      obtain ⟨hx0, hx1⟩ := (hCrossB.1 hAx)
      unfold Rect.Contained at hCont ⊢
      omega
    | y =>
      obtain ⟨hxB, hwB, hxP, hwP⟩ := hOtherY hAx
      obtain ⟨hy0, hy1⟩ := (hCrossB.2 hAx)
      unfold Rect.Contained at hCont ⊢
      omega

/-- Pinning keeps clause C2 (exclusive siblings are disjoint). -/
theorem pinBands_c2 {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hC2 : Validator.C2 s.layoutDump) (hRes : PinC2Sep o s r)
    (h : pinBands boxes o s = .ok r) : Validator.C2 r.layoutDump := by
  cases hLanes : lanesOf boxes with
  | nil =>
    have hNo : pinBands boxes o s = .ok s := pinBands_no_lanes hLanes
    rw [hNo] at h
    cases h
    exact hC2
  | cons lane rest =>
    unfold PinC2Sep at hRes
    intro b' hb' c' hc' hne hexB hexC hpar
    obtain ⟨b, hb, c, hc, hidB, hidC, hexEqB, hexEqC, hparEqB, hparEqC,
      hOtherX, hOtherY, hSep⟩ := hRes b' hb' c' hc' hne hexB hexC hpar
    have hneBC : b.id ≠ c.id := by
      intro hEq
      exact hne (hidB.trans (hEq.trans hidC.symm))
    have hexB0 : b.exclusive = true := by rw [← hexEqB]; exact hexB
    have hexC0 : c.exclusive = true := by rw [← hexEqC]; exact hexC
    have hparBC : b.parent = c.parent := by
      rw [← hparEqB, ← hparEqC]; exact hpar
    have hDisj := hC2 b hb c hc hneBC hexB0 hexC0 hparBC
    cases hAx : Axis.ofDirection o.direction with
    | x =>
      obtain ⟨hyB, hhB, hwB, hyC, hhC, hwC⟩ := hOtherX hAx
      obtain ⟨hShiftPart, _hYPart⟩ := hSep
      have hDisjX := hShiftPart hAx
      rcases hDisjX with hShift | hCross1 | hCross2
      · have haX : b'.rect.x = b.rect.x + (b'.rect.x - b.rect.x) := by omega
        have hcX : c'.rect.x = c.rect.x + (b'.rect.x - b.rect.x) := by omega
        exact boxClauses_disjoint_of_shift_x haX hcX hwB hwC hyB hhB hyC hhC hDisj
      · exact boxClauses_disjoint_of_cross_x (Or.inl hCross1)
      · exact boxClauses_disjoint_of_cross_x (Or.inr hCross2)
    | y =>
      obtain ⟨hxB, hwB, hhB, hxC, hwC, hhC⟩ := hOtherY hAx
      obtain ⟨_hXPart, hShiftPart⟩ := hSep
      have hDisjY := hShiftPart hAx
      rcases hDisjY with hShift | hCross1 | hCross2
      · have haY : b'.rect.y = b.rect.y + (b'.rect.y - b.rect.y) := by omega
        have hcY : c'.rect.y = c.rect.y + (b'.rect.y - b.rect.y) := by omega
        exact boxClauses_disjoint_of_shift_y haY hcY hhB hhC hxB hwB hxC hwC hDisj
      · exact boxClauses_disjoint_of_cross_y (Or.inl hCross1)
      · exact boxClauses_disjoint_of_cross_y (Or.inr hCross2)

end LaneBands
end Layered
end Elegant

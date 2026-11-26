import Elegant.Layered.LaneBands

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- Phase decomposition of a successful `pinBands` run. -/
theorem pinBands_spec {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hlanes : lanesOf boxes ≠ [])
    (h : pinBands boxes o s = .ok r) :
    ∃ (sp : Spacing) (axis : Axis) (bands : List Band)
      (pinned routed origin : Scene) (strip : Int) (stripScene : Scene),
      spacingOf o.profile = .ok sp ∧
      axis = Axis.ofDirection o.direction ∧
      bands = layBands boxes s axis sp (lanesOf boxes) ∧
      applyPin (buildPin axis bands s) bands s = .ok pinned ∧
      rerouteBands axis sp (LayoutConst.rank_gap.get o.profile) bands
        (buildPin axis bands s) s.routes pinned = .ok routed ∧
      restoreOrigin axis routed = .ok origin ∧
      Measure.checkedI32 (highest axis origin + sp.slot) = .ok strip ∧
      relocateLabels axis strip sp.slot origin = .ok stripScene ∧
      growCanvas axis s.canvas stripScene = .ok r := by
  have hempty : (lanesOf boxes).isEmpty = false := by
    cases heq : lanesOf boxes with
    | nil => exact absurd heq hlanes
    | cons _ _ => rfl
  unfold pinBands at h
  simp only [hempty, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨sp, hsp, h⟩ := bind_ok h
  obtain ⟨pinned, happ, h⟩ := bind_ok h
  obtain ⟨routed, hroute, h⟩ := bind_ok h
  obtain ⟨origin, horig, h⟩ := bind_ok h
  obtain ⟨strip, hstrip, h⟩ := bind_ok h
  obtain ⟨stripScene, hreloc, h⟩ := bind_ok h
  exact ⟨sp, Axis.ofDirection o.direction,
    layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes),
    pinned, routed, origin, strip, stripScene,
    hsp, rfl, rfl, happ, hroute, horig, hstrip, hreloc, h⟩

/-- A checked value that succeeds equals the exact integer. -/
theorem checked_value {v w : Int}
    (h : Measure.checkedI32 v = .ok w) : w = v :=
  checkedI32_ok h

/-- A constant move that succeeds adds exactly its delta. -/
theorem moveConstant_value {delta v w : Int}
    (h : (Move.constant delta).apply v = .ok w) : w = v + delta := by
  unfold Move.apply Move.offset at h
  exact checkedI32_ok h

/-- A constant move on a rectangle shifts the cross-axis start by the exact sum. -/
theorem moveConstant_rect_value {axis : Axis} {r r' : Rect} {delta : Int}
    (h : (Move.constant delta).rect axis r = .ok r') :
    ∃ w, Measure.checkedI32 (axis.start r + delta) = .ok w ∧
      r' = axis.withStart r w ∧ w = axis.start r + delta := by
  unfold Move.rect at h
  obtain ⟨w, hw, hrfl⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  have hoff : (Move.constant delta).apply (axis.start r) =
      Measure.checkedI32 (axis.start r + delta) := by
    simp [Move.apply, Move.offset]
  rw [hoff] at hw
  exact ⟨w, hw, rfl, checkedI32_ok hw⟩

/-- A cross-axis rectangle shift leaves the other axis and the size unchanged. -/
theorem moveConstant_rect_frame {axis : Axis} {r r' : Rect} {delta : Int}
    (h : (Move.constant delta).rect axis r = .ok r') :
    (axis = .x → r'.y = r.y ∧ r'.w = r.w ∧ r'.h = r.h) ∧
    (axis = .y → r'.x = r.x ∧ r'.w = r.w ∧ r'.h = r.h) := by
  obtain ⟨w, _, hrfl, _⟩ := moveConstant_rect_value (axis := axis) (r := r) (delta := delta) h
  subst hrfl
  constructor
  · intro haxis
    subst haxis
    simp [Axis.withStart]
  · intro haxis
    subst haxis
    simp [Axis.withStart]

/-- The router leaves boxes, labels, and the canvas untouched. -/
theorem rerouteBands_frame {axis : Axis} {sp : Spacing} {bend : Int}
    {bands : List Band} {pin : Pin} {original : List Route}
    {s s' : Scene} (h : rerouteBands axis sp bend bands pin original s = .ok s') :
    s'.boxes = s.boxes ∧ s'.labels = s.labels ∧ s'.canvas = s.canvas := by
  unfold rerouteBands at h
  obtain ⟨_routes, _, h⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

/-- Growing the canvas leaves boxes, routes, and labels untouched. -/
theorem growCanvas_frame {axis : Axis} {canvas : Size} {s s' : Scene}
    (h : growCanvas axis canvas s = .ok s') :
    s'.boxes = s.boxes ∧ s'.routes = s.routes ∧ s'.labels = s.labels := by
  unfold growCanvas at h
  cases hgrown : Measure.checkedI32 (highest axis s) with
  | error e => simp [hgrown, Bind.bind, Except.bind] at h
  | ok _grown =>
    simp only [hgrown, Bind.bind, Except.bind, Pure.pure, Except.pure,
      Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩

/-- One shifted label keeps its identity and moves by the exact checked sum. -/
private theorem shiftLabel_ok {l l' : SceneLabel} {axis : Axis} {delta : Int}
    (h : (do pure { l with rect := ← (Move.constant delta).rect axis l.rect } : Except LayoutError SceneLabel) = .ok l') :
    l'.id = l.id ∧ l'.owner = l.owner ∧
    ∃ w, Measure.checkedI32 (axis.start l.rect + delta) = .ok w ∧
      l'.rect = axis.withStart l.rect w ∧ w = axis.start l.rect + delta := by
  obtain ⟨rect, hrect, hrfl⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  obtain ⟨w, hw, hrectEq, hval⟩ := moveConstant_rect_value hrect
  exact ⟨rfl, rfl, w, hw, hrectEq, hval⟩

private theorem shiftLabels_maps (l : List SceneLabel) (axis : Axis) (delta : Int) :
    ∀ (l' : List SceneLabel),
    l.mapM (fun b : SceneLabel => (do pure { b with rect := ← (Move.constant delta).rect axis b.rect } : Except LayoutError SceneLabel)) = .ok l' →
    l'.length = l.length ∧ l'.map (·.id) = l.map (·.id) ∧
      l'.map (·.owner) = l.map (·.owner) := by
  induction l with
  | nil =>
    intro l' h
    have he : l' = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    exact ⟨rfl, rfl, rfl⟩
  | cons head tail ih =>
    intro l' h
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    obtain ⟨hlen, hid, howner⟩ := ih _ hrest
    obtain ⟨hid1, howner1, _mem⟩ := shiftLabel_ok hfirst
    simp only [List.length_cons, List.map_cons, hlen, hid1, hid,
      howner1, howner]
    trivial

/-- One shifted point moves by the exact checked sum. -/
private theorem shiftPoint_ok {p p' : Point} {axis : Axis} {delta : Int}
    (h : ((Move.constant delta).point axis p : Except LayoutError Point) = .ok p') :
    ∃ w, Measure.checkedI32 (axis.point p + delta) = .ok w ∧
      p' = axis.withPoint p w ∧ w = axis.point p + delta ∧
      axis.other.point p' = axis.other.point p := by
  unfold Move.point at h
  obtain ⟨w, hw, hrfl⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  have hoff : (Move.constant delta).apply (axis.point p) =
      Measure.checkedI32 (axis.point p + delta) := by
    simp [Move.apply, Move.offset]
  rw [hoff] at hw
  refine ⟨w, hw, rfl, checkedI32_ok hw, ?_⟩
  cases axis <;> simp [Axis.withPoint, Axis.other, Axis.point]

private theorem shiftPoints_other (l : List Point) (axis : Axis) (delta : Int) :
    ∀ (l' : List Point),
    l.mapM ((Move.constant delta).point axis) = .ok l' →
    l'.length = l.length ∧
      l'.map (axis.other.point) = l.map (axis.other.point) := by
  induction l with
  | nil =>
    intro l' h
    have he : l' = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    intro l' h
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    obtain ⟨hlen, hother⟩ := ih _ hrest
    obtain ⟨w, _hw, _heq, _hval, hother1⟩ := shiftPoint_ok hfirst
    simp only [List.length_cons, List.map_cons, hlen, hother1, hother]
    trivial
private theorem shiftRoute_ok {r r' : Route} {axis : Axis} {delta : Int}
    (h : (do pure { r with points := ← r.points.mapM ((Move.constant delta).point axis) } : Except LayoutError Route) = .ok r') :
    r'.id = r.id ∧ r'.fromId = r.fromId ∧ r'.toId = r.toId ∧
    r'.points.length = r.points.length ∧
      r'.points.map (axis.other.point) = r.points.map (axis.other.point) := by
  obtain ⟨pts, hpts, hrfl⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  obtain ⟨hlen, hother⟩ := shiftPoints_other r.points axis delta _ hpts
  exact ⟨rfl, rfl, rfl, hlen, hother⟩

private theorem shiftRoutes_maps (l : List Route) (axis : Axis) (delta : Int) :
    ∀ (l' : List Route),
    l.mapM (fun r : Route => (do pure { r with points := ← r.points.mapM ((Move.constant delta).point axis) } : Except LayoutError Route)) = .ok l' →
    l'.length = l.length ∧ l'.map (·.id) = l.map (·.id) ∧
      l'.map (·.fromId) = l.map (·.fromId) ∧
      l'.map (·.toId) = l.map (·.toId) := by
  induction l with
  | nil =>
    intro l' h
    have he : l' = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    exact ⟨rfl, rfl, rfl, rfl⟩
  | cons head tail ih =>
    intro l' h
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    obtain ⟨hlen, hid, hfrom, hto⟩ := ih _ hrest
    obtain ⟨hid1, hfrom1, hto1, _plen, _pother⟩ := shiftRoute_ok hfirst
    simp only [List.length_cons, List.map_cons, hlen, hid1, hid,
      hfrom1, hfrom, hto1, hto]
    trivial


theorem shiftBox_ok {b b' : Box} {axis : Axis} {delta : Int}
    (h : (do pure { b with rect := ← (Move.constant delta).rect axis b.rect } : Except LayoutError Box) = .ok b') :
    b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive ∧
    ∃ w, Measure.checkedI32 (axis.start b.rect + delta) = .ok w ∧
      b'.rect = axis.withStart b.rect w ∧ w = axis.start b.rect + delta := by
  obtain ⟨rect, hrect, hrfl⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  obtain ⟨w, hw, hrectEq, hval⟩ := moveConstant_rect_value hrect
  exact ⟨rfl, rfl, rfl, rfl, w, hw, hrectEq, hval⟩

theorem shiftBoxes_maps (l : List Box) (axis : Axis) (delta : Int) :
    ∀ (l' : List Box),
    l.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant delta).rect axis b.rect } : Except LayoutError Box)) = .ok l' →
    l'.length = l.length ∧ l'.map (·.id) = l.map (·.id) ∧
      l'.map (·.parent) = l.map (·.parent) ∧
      l'.map (·.role) = l.map (·.role) ∧
      l'.map (·.exclusive) = l.map (·.exclusive) := by
  induction l with
  | nil =>
    intro l' h
    have he : l' = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons head tail ih =>
    intro l' h
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    obtain ⟨hlen, hid, hparent, hrole, hexcl⟩ := ih _ hrest
    obtain ⟨hid1, hparent1, hrole1, hexcl1, _mem⟩ := shiftBox_ok hfirst
    simp only [List.length_cons, List.map_cons, hlen, hid1, hid,
      hparent1, hparent, hrole1, hrole, hexcl1, hexcl]
    trivial


/-- A uniform shift preserves route identity and the canvas. -/
theorem shiftAll_routes_canvas {axis : Axis} {delta : Int} {s s' : Scene}
    (h : shiftAll axis delta s = .ok s') :
    s'.routes.length = s.routes.length ∧
      s'.routes.map (·.id) = s.routes.map (·.id) ∧
      s'.canvas = s.canvas := by
  unfold shiftAll at h
  obtain ⟨_boxes, hboxes, h⟩ := bind_ok h
  obtain ⟨_labels, hlabels, h⟩ := bind_ok h
  obtain ⟨_routes, hroutes, h⟩ := bind_ok h
  obtain ⟨_items, _hitems, h⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hlenR, hidR, _, _⟩ := shiftRoutes_maps s.routes axis delta _ hroutes
  exact ⟨hlenR, hidR, rfl⟩

/-- Restoring the origin either leaves the scene or shifts it by one delta. -/
theorem restoreOrigin_cases {axis : Axis} {s s' : Scene}
    (h : restoreOrigin axis s = .ok s') :
    s' = s ∨ ∃ delta : Int, 0 < delta ∧ shiftAll axis delta s = .ok s' := by
  unfold restoreOrigin at h
  cases hbounds : bounds (geometryValues axis false s) with
  | none =>
    simp only [hbounds] at h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Or.inl rfl
  | some p =>
    simp only [hbounds] at h
    cases p with
    | mk lo hi =>
      simp only at h
      by_cases hlo : lo < 0
      · simp only [hlo, ↓reduceIte] at h
        exact Or.inr ⟨-lo, by omega, h⟩
      · simp only [hlo, ↓reduceIte] at h
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact Or.inl rfl

/-- Every label produced by `moveOffendingLabels` comes from the input list with
its identity kept: an untouched label keeps its rectangle, and a relocated
label starts at or past the strip with its other axis and size kept. -/
private theorem moveOffendingLabels_mem {axis : Axis} {strip gap : Int} {s : Scene} :
    ∀ (ls : List SceneLabel) (moved : List LabelRelocation)
      (labels : List SceneLabel) (moved' : List LabelRelocation),
      moveOffendingLabels axis strip gap s ls moved = .ok (labels, moved') →
      ∀ l ∈ labels, ∃ m ∈ ls, m.id = l.id ∧ m.owner = l.owner ∧
        (¬ needsRelocation s m → l.rect = m.rect) ∧
        (needsRelocation s m → strip ≤ axis.start l.rect ∧
          axis.other.start l.rect = axis.other.start m.rect ∧
          l.rect.w = m.rect.w ∧ l.rect.h = m.rect.h) := by
  intro ls
  induction ls with
  | nil =>
    intro moved labels moved' h l hl
    simp only [moveOffendingLabels, Pure.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp at hl
  | cons head tail ih =>
    intro moved labels moved' h l hl
    simp only [moveOffendingLabels] at h
    split at h
    · rename_i hneeds
      obtain ⟨rect, hrect, h⟩ := bind_ok h
      obtain ⟨p, hp, h⟩ := bind_ok h
      cases p with
      | mk rest moved2 =>
        dsimp only at h
        simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hspec := vacantLabelStrip_preserves_and_clears hrect
        simp only [List.mem_cons] at hl
        rcases hl with rfl | htail
        · refine ⟨head, List.mem_cons.mpr (Or.inl rfl), rfl, rfl, ?_, ?_⟩
          · intro hneg
            exact absurd hneeds hneg
          · intro _
            obtain ⟨hle, hother, hw, hh, -⟩ := hspec
            exact ⟨hle, hother, hw, hh⟩
        · obtain ⟨m, hm, hid, hown, hstay, hmove⟩ := ih _ _ _ hp _ htail
          exact ⟨m, List.mem_cons.mpr (Or.inr hm), hid, hown, hstay, hmove⟩
    · rename_i hneeds
      obtain ⟨p, hp, h⟩ := bind_ok h
      cases p with
      | mk rest moved2 =>
        dsimp only at h
        simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [List.mem_cons] at hl
        rcases hl with rfl | htail
        · refine ⟨l, List.mem_cons.mpr (Or.inl rfl), rfl, rfl, ?_, ?_⟩
          · intro _
            rfl
          · intro hpos
            exact absurd hpos hneeds
        · obtain ⟨m, hm, hid, hown, hstay, hmove⟩ := ih _ _ _ hp _ htail
          exact ⟨m, List.mem_cons.mpr (Or.inr hm), hid, hown, hstay, hmove⟩

/-- Relocated labels either stay or move at or past the strip; identity and the
other axis and size are preserved. The old exact-strip equality is unprovable
because relocation bumps past earlier moves; the bound is what the strip
disjointness argument actually needs. -/
theorem relocateLabels_labels {axis : Axis} {strip gap : Int} {s result : Scene}
    {l : SceneLabel}
    (h : relocateLabels axis strip gap s = .ok result)
    (hmem : l ∈ result.labels) :
    ∃ m ∈ s.labels, m.id = l.id ∧ m.owner = l.owner ∧
      (¬ needsRelocation s m → l.rect = m.rect) ∧
      (needsRelocation s m → strip ≤ axis.start l.rect ∧
        axis.other.start l.rect = axis.other.start m.rect ∧
        l.rect.w = m.rect.w ∧ l.rect.h = m.rect.h) := by
  unfold relocateLabels at h
  obtain ⟨p, hp, h⟩ := bind_ok h
  cases p with
  | mk labels moved =>
    dsimp only at h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hmem' : l ∈ labels := hmem
    obtain ⟨m, hm, hid, hown, hstay, hmove⟩ :=
      moveOffendingLabels_mem _ _ _ _ hp _ hmem'
    exact ⟨m, hm, hid, hown, hstay, hmove⟩

/-- The grown canvas is the max of the old extent and the checked geometry height. -/
theorem growCanvas_exact {axis : Axis} {canvas : Size} {s s' : Scene}
    (h : growCanvas axis canvas s = .ok s') :
    ∃ grown : Int, Measure.checkedI32 (highest axis s) = .ok grown ∧
      grown = highest axis s ∧
      s'.canvas = axis.withExtent canvas (max (axis.extent canvas) grown) := by
  unfold growCanvas at h
  cases hgrown : Measure.checkedI32 (highest axis s) with
  | error e => simp [hgrown, Bind.bind, Except.bind] at h
  | ok grown =>
    simp only [hgrown, Bind.bind, Except.bind, Pure.pure, Except.pure,
      Except.ok.injEq] at h
    subst h
    exact ⟨grown, rfl, checkedI32_ok hgrown, rfl⟩
/-- A uniform shift preserves box and label identity. -/
theorem shiftAll_boxes_labels {axis : Axis} {delta : Int} {s s' : Scene}
    (h : shiftAll axis delta s = .ok s') :
    s'.boxes.length = s.boxes.length ∧
      s'.boxes.map (·.id) = s.boxes.map (·.id) ∧
      s'.labels.length = s.labels.length ∧
      s'.labels.map (·.id) = s.labels.map (·.id) := by
  unfold shiftAll at h
  obtain ⟨_boxes, hboxes, h⟩ := bind_ok h
  obtain ⟨_labels, hlabels, h⟩ := bind_ok h
  obtain ⟨_routes, _hroutes, h⟩ := bind_ok h
  obtain ⟨_items, _hitems, h⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hlenB, hidB, _, _, _⟩ := shiftBoxes_maps s.boxes axis delta _ hboxes
  obtain ⟨hlenL, hidL, _hownerL⟩ := shiftLabels_maps s.labels axis delta _ hlabels
  exact ⟨hlenB, hidB, hlenL, hidL⟩

/-- Frame replacement preserves length and leaves labels, routes, and canvas. -/
theorem replaceFrame_frame {axis : Axis} {band : Band} {s s' : Scene}
    (h : replaceFrame axis band s = .ok s') :
    s'.boxes.length = s.boxes.length ∧
      s'.labels = s.labels ∧ s'.routes = s.routes ∧ s'.canvas = s.canvas := by
  unfold replaceFrame at h
  cases hfind : s.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    simp only [hfind, Pure.pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩
  | some _idx =>
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
        refine ⟨?_, rfl, rfl, rfl⟩
        simp only [List.length_mapIdx]

private theorem mapIdx_boxes_id_aux (l : List Box) (n idx : Nat)
    (place : Rect → Rect) :
    ((l.mapIdx fun j b => if j + n = idx then { b with rect := place b.rect } else b).map (·.id)) =
      l.map (·.id) := by
  induction l generalizing n with
  | nil => rfl
  | cons head tail ih =>
    rw [List.mapIdx_cons]
    simp only [List.map_cons]
    have hhead : (if n = idx then { head with rect := place head.rect } else head).id =
        head.id := by
      by_cases h : n = idx <;> simp [h]
    have htail : ((tail.mapIdx fun i b => if i + 1 + n = idx then { b with rect := place b.rect } else b).map (·.id)) =
        tail.map (·.id) := by
      have heq : (fun i b => if i + 1 + n = idx then ({ b with rect := place b.rect } : Box) else b) =
          (fun j b => if j + (n + 1) = idx then ({ b with rect := place b.rect } : Box) else b) := by
        funext j b
        have h : j + 1 + n = j + (n + 1) := by omega
        rw [h]
      rw [heq]
      exact ih (n + 1)
    simp only [Nat.zero_add] at hhead ⊢
    rw [hhead, htail]
private theorem mapIdx_boxes_parent_aux (l : List Box) (n idx : Nat)
    (place : Rect → Rect) :
    ((l.mapIdx fun j b => if j + n = idx then { b with rect := place b.rect } else b).map (·.parent)) =
      l.map (·.parent) := by
  induction l generalizing n with
  | nil => rfl
  | cons head tail ih =>
    rw [List.mapIdx_cons]
    simp only [List.map_cons]
    have hhead : (if n = idx then { head with rect := place head.rect } else head).parent =
        head.parent := by
      by_cases h : n = idx <;> simp [h]
    have htail : ((tail.mapIdx fun i b => if i + 1 + n = idx then { b with rect := place b.rect } else b).map (·.parent)) =
        tail.map (·.parent) := by
      have heq : (fun i b => if i + 1 + n = idx then ({ b with rect := place b.rect } : Box) else b) =
          (fun j b => if j + (n + 1) = idx then ({ b with rect := place b.rect } : Box) else b) := by
        funext j b
        have h : j + 1 + n = j + (n + 1) := by omega
        rw [h]
      rw [heq]
      exact ih (n + 1)
    simp only [Nat.zero_add] at hhead ⊢
    rw [hhead, htail]
private theorem mapIdx_boxes_role_aux (l : List Box) (n idx : Nat)
    (place : Rect → Rect) :
    ((l.mapIdx fun j b => if j + n = idx then { b with rect := place b.rect } else b).map (·.role)) =
      l.map (·.role) := by
  induction l generalizing n with
  | nil => rfl
  | cons head tail ih =>
    rw [List.mapIdx_cons]
    simp only [List.map_cons]
    have hhead : (if n = idx then { head with rect := place head.rect } else head).role =
        head.role := by
      by_cases h : n = idx <;> simp [h]
    have htail : ((tail.mapIdx fun i b => if i + 1 + n = idx then { b with rect := place b.rect } else b).map (·.role)) =
        tail.map (·.role) := by
      have heq : (fun i b => if i + 1 + n = idx then ({ b with rect := place b.rect } : Box) else b) =
          (fun j b => if j + (n + 1) = idx then ({ b with rect := place b.rect } : Box) else b) := by
        funext j b
        have h : j + 1 + n = j + (n + 1) := by omega
        rw [h]
      rw [heq]
      exact ih (n + 1)
    simp only [Nat.zero_add] at hhead ⊢
    rw [hhead, htail]

private theorem mapIdx_boxes_excl_aux (l : List Box) (n idx : Nat)
    (place : Rect → Rect) :
    ((l.mapIdx fun j b => if j + n = idx then { b with rect := place b.rect } else b).map (·.exclusive)) =
      l.map (·.exclusive) := by
  induction l generalizing n with
  | nil => rfl
  | cons head tail ih =>
    rw [List.mapIdx_cons]
    simp only [List.map_cons]
    have hhead : (if n = idx then { head with rect := place head.rect } else head).exclusive =
        head.exclusive := by
      by_cases h : n = idx <;> simp [h]
    have htail : ((tail.mapIdx fun i b => if i + 1 + n = idx then { b with rect := place b.rect } else b).map (·.exclusive)) =
        tail.map (·.exclusive) := by
      have heq : (fun i b => if i + 1 + n = idx then ({ b with rect := place b.rect } : Box) else b) =
          (fun j b => if j + (n + 1) = idx then ({ b with rect := place b.rect } : Box) else b) := by
        funext j b
        have h : j + 1 + n = j + (n + 1) := by omega
        rw [h]
      rw [heq]
      exact ih (n + 1)
    simp only [Nat.zero_add] at hhead ⊢
    rw [hhead, htail]

/-- Frame replacement preserves box identity. -/
theorem replaceFrame_boxes_maps {axis : Axis} {band : Band} {s s' : Scene}
    (h : replaceFrame axis band s = .ok s') :
    s'.boxes.map (·.id) = s.boxes.map (·.id) ∧
      s'.boxes.map (·.parent) = s.boxes.map (·.parent) ∧
      s'.boxes.map (·.role) = s.boxes.map (·.role) ∧
      s'.boxes.map (·.exclusive) = s.boxes.map (·.exclusive) := by
  unfold replaceFrame at h
  cases hfind : s.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    simp only [hfind, Pure.pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩
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
        have hs : _s = band.start := checkedI32_ok hstart
        have ht : _t = band.thickness := checkedI32_ok hthick
        subst hs
        subst ht
        simp only
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact mapIdx_boxes_id_aux s.boxes 0 idx
            (placeRect axis band.start band.thickness)
        · exact mapIdx_boxes_parent_aux s.boxes 0 idx
            (placeRect axis band.start band.thickness)
        · exact mapIdx_boxes_role_aux s.boxes 0 idx
            (placeRect axis band.start band.thickness)
        · exact mapIdx_boxes_excl_aux s.boxes 0 idx
            (placeRect axis band.start band.thickness)
theorem foldReplaceFrame_all (bands : List Band) (axis : Axis) (s : Scene) :
    ∀ (s' : Scene),
    bands.foldlM (fun scene band => replaceFrame axis band scene) s = .ok s' →
    s'.boxes.length = s.boxes.length ∧
      s'.boxes.map (·.id) = s.boxes.map (·.id) ∧
      s'.boxes.map (·.parent) = s.boxes.map (·.parent) ∧
      s'.boxes.map (·.role) = s.boxes.map (·.role) ∧
      s'.boxes.map (·.exclusive) = s.boxes.map (·.exclusive) ∧
      s'.labels = s.labels ∧ s'.routes = s.routes ∧ s'.canvas = s.canvas := by
  induction bands generalizing s with
  | nil =>
    intro s' h
    have he : s' = s := by
      simpa only [List.foldlM_nil, Pure.pure, Except.pure,
        Except.ok.injEq] using h.symm
    subst he
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons band rest ih =>
    intro s' h
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, h⟩ := bind_ok h
    obtain ⟨hlenM, hlabM, hrouteM, hcanvasM⟩ := replaceFrame_frame (axis := axis) (band := band) hmid
    obtain ⟨hidM, hparM, hroleM, hexclM⟩ := replaceFrame_boxes_maps (axis := axis) (band := band) hmid
    obtain ⟨hlenR, hidR, hparR, hroleR, hexclR, hlabR, hrouteR, hcanvasR⟩ := ih mid s' h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · rw [hidR, hidM]
    · rw [hparR, hparM]
    · rw [hroleR, hroleM]
    · rw [hexclR, hexclM]
    · rw [hlabR, hlabM]
    · rw [hrouteR, hrouteM]
    · rw [hcanvasR, hcanvasM]
theorem pinShiftBox_ok {b b' : Box} {pin : Pin} {axis : Axis}
    (h : (do pure { b with rect := ← (Move.constant (pin.boxDelta b.id)).rect axis b.rect } : Except LayoutError Box) = .ok b') :
    b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive ∧
    ∃ w, Measure.checkedI32 (axis.start b.rect + pin.boxDelta b.id) = .ok w ∧
      b'.rect = axis.withStart b.rect w ∧ w = axis.start b.rect + pin.boxDelta b.id := by
  obtain ⟨rect, hrect, hrfl⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  obtain ⟨w, hw, hrectEq, hval⟩ := moveConstant_rect_value hrect
  exact ⟨rfl, rfl, rfl, rfl, w, hw, hrectEq, hval⟩
theorem pinShiftBoxes_mem (l : List Box) (pin : Pin) (axis : Axis) :
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
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    simp only [List.mem_cons] at hb'
    rcases hb' with rfl | hmem
    · obtain ⟨hid1, hpar1, _, _, w, hw, heq, hval⟩ := pinShiftBox_ok hfirst
      exact ⟨head, List.mem_cons.mpr (Or.inl rfl), hid1, hpar1, w, hw, heq, hval⟩
    · obtain ⟨b, hbin, hid, hpar, w, hw, heq, hval⟩ := ih _ hrest _ hmem
      exact ⟨b, List.mem_cons.mpr (Or.inr hbin), hid, hpar, w, hw, heq, hval⟩




theorem pinShiftBoxes_maps (l : List Box) (pin : Pin) (axis : Axis) :
    ∀ (l' : List Box),
    l.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant (pin.boxDelta b.id)).rect axis b.rect } : Except LayoutError Box)) = .ok l' →
    l'.length = l.length ∧ l'.map (·.id) = l.map (·.id) ∧
      l'.map (·.parent) = l.map (·.parent) ∧
      l'.map (·.role) = l.map (·.role) ∧
      l'.map (·.exclusive) = l.map (·.exclusive) := by
  induction l with
  | nil =>
    intro l' h
    have he : l' = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons head tail ih =>
    intro l' h
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    obtain ⟨hlen, hid, hparent, hrole, hexcl⟩ := ih _ hrest
    obtain ⟨hid1, hparent1, hrole1, hexcl1, _mem⟩ := pinShiftBox_ok hfirst
    simp only [List.length_cons, List.map_cons, hlen, hid1, hid,
      hparent1, hparent, hrole1, hrole, hexcl1, hexcl]
    trivial

private theorem pinShiftLabel_ok {l l' : SceneLabel} {pin : Pin} {axis : Axis}
    (h : (do pure { l with rect := ← (Move.constant (pin.labelDelta l.owner)).rect axis l.rect } : Except LayoutError SceneLabel) = .ok l') :
    l'.id = l.id ∧ l'.owner = l.owner ∧
    ∃ w, Measure.checkedI32 (axis.start l.rect + pin.labelDelta l.owner) = .ok w ∧
      l'.rect = axis.withStart l.rect w ∧ w = axis.start l.rect + pin.labelDelta l.owner := by
  obtain ⟨rect, hrect, hrfl⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  obtain ⟨w, hw, hrectEq, hval⟩ := moveConstant_rect_value hrect
  exact ⟨rfl, rfl, w, hw, hrectEq, hval⟩

private theorem pinShiftLabels_maps (l : List SceneLabel) (pin : Pin) (axis : Axis) :
    ∀ (l' : List SceneLabel),
    l.mapM (fun b : SceneLabel => (do pure { b with rect := ← (Move.constant (pin.labelDelta b.owner)).rect axis b.rect } : Except LayoutError SceneLabel)) = .ok l' →
    l'.length = l.length ∧ l'.map (·.id) = l.map (·.id) ∧
      l'.map (·.owner) = l.map (·.owner) := by
  induction l with
  | nil =>
    intro l' h
    have he : l' = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    exact ⟨rfl, rfl, rfl⟩
  | cons head tail ih =>
    intro l' h
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    obtain ⟨hlen, hid, howner⟩ := ih _ hrest
    obtain ⟨hid1, howner1, _mem⟩ := pinShiftLabel_ok hfirst
    simp only [List.length_cons, List.map_cons, hlen, hid1, hid,
      howner1, howner]
    trivial



private theorem pinRoute_ok {r r' : Route} {pin : Pin} {axis : Axis}
    (h : (match pin.route r.id with
      | none => (pure r : Except LayoutError Route)
      | some d => (do pure { r with points := ← r.points.mapM ((routeMove d).point axis) } : Except LayoutError Route)) = .ok r') :
    r'.id = r.id ∧ r'.fromId = r.fromId ∧ r'.toId = r.toId ∧
      (pin.route r.id = none → r'.points = r.points) := by
  cases hroute : pin.route r.id with
  | none =>
    simp only [hroute] at h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  | some d =>
    simp only [hroute] at h
    obtain ⟨_pts, _hpts, hrfl⟩ := bind_ok h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
    subst hrfl
    exact ⟨rfl, rfl, rfl, fun hnone => by cases hnone⟩

private theorem pinRoutes_maps (l : List Route) (pin : Pin) (axis : Axis) :
    ∀ (l' : List Route),
    l.mapM (fun r : Route => match pin.route r.id with
      | none => (pure r : Except LayoutError Route)
      | some d => (do pure { r with points := ← r.points.mapM ((routeMove d).point axis) } : Except LayoutError Route)) = .ok l' →
    l'.length = l.length ∧ l'.map (·.id) = l.map (·.id) ∧
      l'.map (·.fromId) = l.map (·.fromId) ∧
      l'.map (·.toId) = l.map (·.toId) := by
  induction l with
  | nil =>
    intro l' h
    have he : l' = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    exact ⟨rfl, rfl, rfl, rfl⟩
  | cons head tail ih =>
    intro l' h
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    obtain ⟨hlen, hid, hfrom, hto⟩ := ih _ hrest
    obtain ⟨hid1, hfrom1, hto1, _hpts⟩ := pinRoute_ok hfirst
    simp only [List.length_cons, List.map_cons, hlen, hid1, hid,
      hfrom1, hfrom, hto1, hto]
    trivial

/-- The first stage of `applyPin` shifts every list by its pin delta. -/
theorem applyPin_shifted {pin : Pin} {bands : List Band} {s pinned : Scene}
    (h : applyPin pin bands s = .ok pinned) :
    ∃ (shiftedBoxes : List Box) (shiftedLabels : List SceneLabel)
      (shiftedRoutes : List Route) (shiftedItems : List Group),
      s.boxes.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant (pin.boxDelta b.id)).rect pin.axis b.rect } : Except LayoutError Box)) = .ok shiftedBoxes ∧
      s.labels.mapM (fun b : SceneLabel => (do pure { b with rect := ← (Move.constant (pin.labelDelta b.owner)).rect pin.axis b.rect } : Except LayoutError SceneLabel)) = .ok shiftedLabels ∧
      s.routes.mapM (fun r : Route => (match pin.route r.id with | none => (pure r : Except LayoutError Route) | some d => (do pure { r with points := ← r.points.mapM ((routeMove d).point pin.axis) } : Except LayoutError Route))) = .ok shiftedRoutes ∧
      s.items.mapM (moveGroup pin) = .ok shiftedItems ∧
      bands.foldlM (fun scene band => replaceFrame pin.axis band scene) { s with boxes := shiftedBoxes, labels := shiftedLabels, routes := shiftedRoutes, items := shiftedItems } = .ok pinned := by
  unfold applyPin at h
  obtain ⟨shiftedBoxes, hboxes, h⟩ := bind_ok h
  obtain ⟨shiftedLabels, hlabels, h⟩ := bind_ok h
  obtain ⟨shiftedRoutes, hroutes, h⟩ := bind_ok h
  obtain ⟨shiftedItems, hitems, h⟩ := bind_ok h
  exact ⟨shiftedBoxes, shiftedLabels, shiftedRoutes, shiftedItems,
    hboxes, hlabels, hroutes, hitems, h⟩

/-- The result dump reads its components off the result scene. -/
theorem pinBands_layoutDump {r : Scene} :
    r.layoutDump.boxes = r.boxes ∧ r.layoutDump.routes = r.routes ∧
      r.layoutDump.canvas = r.canvas ∧
      r.layoutDump.labels = r.labels.map (·.toLabel) := by
  exact ⟨rfl, rfl, rfl, rfl⟩



end LaneBands
end Layered
end Elegant

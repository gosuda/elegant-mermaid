import Elegant.Layered.LaneEnds
import Elegant.Layered.LaneBandsRouteClauses
import Elegant.Layered.LaneBandsClearance

set_option autoImplicit false

/-! Clause transport for the final lane-end attachment. `attachLaneEnds` leaves boxes,
labels, and the canvas untouched, so every clause the pinned scene already has transfers;
the moved end keeps its rank coordinate, so orthogonality transfers through
`simplifyPoints`; ends on old frame sides land on the new frame boundary; and the new
gap segment misses every out-of-scope exclusive box. -/

namespace Elegant
namespace Layered
namespace LaneBands

/-- Binding step of an `Except` computation. -/
private theorem bindOk {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- The old frame of a lane: the stretched box moved back to its unpinned cross range. -/
def oldFrame (axis : Axis) (f : LaneFrame) (r : Rect) : Rect :=
  placeRect axis (axis.start r + f.near) f.length r

/-- The boundary an end sat on before pinning: the old frame for lanes, the box itself. -/
def endRect (axis : Axis) (frames : List LaneFrame) (b : Box) : Rect :=
  match frames.find? (·.id == b.id) with
  | some f => oldFrame axis f b.rect
  | none => b.rect

/-- C5 against the old frames: what `pinBands` establishes including for lane ends. -/
abbrev EndsOnOld (axis : Axis) (frames : List LaneFrame) (d : LayoutDump) : Prop :=
  ∀ r ∈ d.routes, ∃ p q : Point, ∃ fb tb : Box,
    r.points.head? = some p ∧ r.points.getLast? = some q ∧
      d.box? r.fromId = some fb ∧ d.box? r.toId = some tb ∧
      Validator.onBoundary p (endRect axis frames fb) ∧
      Validator.onBoundary q (endRect axis frames tb)

/-- Every frame sits inside its box along the cross axis. -/
abbrev FramesFit (axis : Axis) (frames : List LaneFrame) (d : LayoutDump) : Prop :=
  ∀ f ∈ frames, ∀ b, d.box? f.id = some b →
    0 ≤ f.near ∧ f.near + f.length ≤ axis.length b.rect

/-- Every out-of-scope exclusive box is inside the old frame range or off the band. -/
abbrev GapClear (axis : Axis) (frames : List LaneFrame) (d : LayoutDump) : Prop :=
  ∀ f ∈ frames, ∀ fb, d.box? f.id = some fb →
    ∀ b ∈ d.boxes, b.exclusive = true → b.id ≠ f.id →
      (axis.start fb.rect + f.near ≤ axis.start b.rect ∧
        axis.start b.rect + axis.length b.rect ≤
          axis.start fb.rect + f.near + f.length) ∨
      axis.start b.rect + axis.length b.rect ≤ axis.start fb.rect ∨
      axis.start fb.rect + axis.length fb.rect ≤ axis.start b.rect

/-- Every exclusive box has positive width and height. -/
abbrev ExclusivePositive (d : LayoutDump) : Prop :=
  ∀ b ∈ d.boxes, b.exclusive = true → 0 < b.rect.w ∧ 0 < b.rect.h

theorem pinLanes_spec {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hlanes : lanesOf boxes ≠ [])
    (h : pinLanes boxes o s = .ok r) :
    ∃ (sp : Spacing) (pinned : Scene),
      spacingOf o.profile = .ok sp ∧
      pinBands boxes o s = .ok pinned ∧
      attachLaneEnds (Axis.ofDirection o.direction)
        (laneFrames (Axis.ofDirection o.direction)
          (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
        pinned = .ok r := by
  have hempty : (lanesOf boxes).isEmpty = false := by
    cases heq : lanesOf boxes with
    | nil => exact absurd heq hlanes
    | cons _ _ => rfl
  unfold pinLanes at h
  simp only [hempty, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨pinned, hpin, h⟩ := bindOk h
  obtain ⟨sp, hsp, h⟩ := bindOk h
  exact ⟨sp, pinned, hsp, hpin, h⟩
theorem attachRoute_ids {axis : Axis} {frames : List LaneFrame} {boxes : List Box}
    {r r' : Route} (h : attachRoute axis frames boxes r = .ok r') :
    r'.id = r.id ∧ r'.fromId = r.fromId ∧ r'.toId = r.toId ∧
      r'.orthogonal = r.orthogonal := by
  unfold attachRoute at h
  cases h1 : r.points.head? with
  | none =>
    cases h2 : r.points.getLast? with
    | none =>
      simp only [h1, h2] at h
      have hok : Except.ok r = Except.ok r' := h
      cases hok
      exact ⟨rfl, rfl, rfl, rfl⟩
    | some last =>
      simp only [h1, h2] at h
      have hok : Except.ok r = Except.ok r' := h
      cases hok
      exact ⟨rfl, rfl, rfl, rfl⟩
  | some first =>
    cases h2 : r.points.getLast? with
    | none =>
      simp only [h1, h2] at h
      have hok : Except.ok r = Except.ok r' := h
      cases hok
      exact ⟨rfl, rfl, rfl, rfl⟩
    | some last =>
      simp only [h1, h2] at h
      obtain ⟨head, e1, h⟩ := bindOk h
      obtain ⟨tail, e2, h⟩ := bindOk h
      split at h
      · have hok : Except.ok r = Except.ok r' := h
        cases hok
        exact ⟨rfl, rfl, rfl, rfl⟩
      · have hok : Except.ok
            { r with points := simplifyPoints (head.toList ++ r.points ++ tail.toList) } =
            Except.ok r' := h
        cases hok
        exact ⟨rfl, rfl, rfl, rfl⟩
theorem attachLaneEnds_frame {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (h : attachLaneEnds axis frames s = .ok d') :
    d'.boxes = s.boxes ∧ d'.labels = s.labels ∧ d'.canvas = s.canvas ∧
    d'.routes.map (fun r => (r.id, r.fromId, r.toId, r.orthogonal)) =
      s.routes.map (fun r => (r.id, r.fromId, r.toId, r.orthogonal)) := by
  unfold attachLaneEnds at h
  obtain ⟨routes, hm, h⟩ := bindOk h
  dsimp only at h
  cases h
  refine ⟨rfl, rfl, rfl, ?_⟩
  have hspec := mapM_except_spec (attachRoute axis frames s.boxes) s.routes routes hm
  have hlen : routes.length = s.routes.length := hspec.1
  apply List.ext_getElem?
  intro i
  cases ha : s.routes[i]? with
  | none =>
    have hnone : routes[i]? = none :=
      List.getElem?_eq_none_iff.mpr (by
        rw [hlen]
        exact List.getElem?_eq_none_iff.mp ha)
    simp only [List.getElem?_map, ha, hnone]
  | some a =>
    have hi : i < s.routes.length := by
      by_cases hc : i < s.routes.length
      · exact hc
      · have hc' : s.routes.length ≤ i := by omega
        have hnone := List.getElem?_eq_none_iff.mpr hc'
        rw [ha] at hnone
        cases hnone
    have hj : i < routes.length := by rw [hlen]; exact hi
    obtain ⟨a', b, ha', hb', hab'⟩ := hspec.2 i hi hj
    rw [ha] at ha'
    have haeq : a = a' := Option.some.inj ha'
    subst haeq
    obtain ⟨hid, hfrom, hto, horth⟩ := attachRoute_ids hab'
    simp only [List.getElem?_map, ha, hb']
    show (some (b.id, b.fromId, b.toId, b.orthogonal)) =
      (some (a.id, a.fromId, a.toId, a.orthogonal))
    have hbeq : (b.id, b.fromId, b.toId, b.orthogonal) =
        (a.id, a.fromId, a.toId, a.orthogonal) := by
      rw [hid, hfrom, hto, horth]
    exact congrArg some hbeq

theorem attachRoute_shape {axis : Axis} {frames : List LaneFrame} {boxes : List Box}
    {r r' : Route} (h : attachRoute axis frames boxes r = .ok r') :
    (r'.id = r.id ∧ r'.fromId = r.fromId ∧ r'.toId = r.toId ∧
      r'.orthogonal = r.orthogonal) ∧
    (r'.points = r.points ∨
      ∃ first last : Point, ∃ ho to_ : Option Point,
        r.points.head? = some first ∧ r.points.getLast? = some last ∧
        attachEnd axis frames boxes r.fromId first = .ok ho ∧
        attachEnd axis frames boxes r.toId last = .ok to_ ∧
        r'.points = simplifyPoints (ho.toList ++ r.points ++ to_.toList)) := by
  have hids := attachRoute_ids h
  refine ⟨hids, ?_⟩
  unfold attachRoute at h
  cases h1 : r.points.head? with
  | none =>
    cases h2 : r.points.getLast? with
    | none =>
      simp only [h1, h2] at h
      have hok : Except.ok r = Except.ok r' := h
      cases hok
      exact Or.inl rfl
    | some last =>
      simp only [h1, h2] at h
      have hok : Except.ok r = Except.ok r' := h
      cases hok
      exact Or.inl rfl
  | some first =>
    cases h2 : r.points.getLast? with
    | none =>
      simp only [h1, h2] at h
      have hok : Except.ok r = Except.ok r' := h
      cases hok
      exact Or.inl rfl
    | some last =>
      simp only [h1, h2] at h
      obtain ⟨head, e1, h⟩ := bindOk h
      obtain ⟨tail, e2, h⟩ := bindOk h
      split at h
      · have hok : Except.ok r = Except.ok r' := h
        cases hok
        exact Or.inl rfl
      · have hok : Except.ok
            { r with points := simplifyPoints (head.toList ++ r.points ++ tail.toList) } =
            Except.ok r' := h
        cases hok
        exact Or.inr ⟨first, last, head, tail, rfl, rfl, e1, e2, rfl⟩

theorem attachLaneEnds_mem {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    {r' : Route} (h : attachLaneEnds axis frames s = .ok d') (hr' : r' ∈ d'.routes) :
    ∃ r, r ∈ s.routes ∧ r'.id = r.id ∧ r'.fromId = r.fromId ∧ r'.toId = r.toId ∧
      r'.orthogonal = r.orthogonal ∧
      (r'.points = r.points ∨
        ∃ first last : Point, ∃ ho to_ : Option Point,
          r.points.head? = some first ∧ r.points.getLast? = some last ∧
          attachEnd axis frames s.boxes r.fromId first = .ok ho ∧
          attachEnd axis frames s.boxes r.toId last = .ok to_ ∧
          r'.points = simplifyPoints (ho.toList ++ r.points ++ to_.toList)) := by
  unfold attachLaneEnds at h
  obtain ⟨routes, hm, h⟩ := bindOk h
  dsimp only at h
  cases h
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr'
  have hkr : k < routes.length := by
    by_cases hc : k < routes.length
    · exact hc
    · have hnone := List.getElem?_eq_none_iff.mpr (by omega : routes.length ≤ k)
      rw [hk] at hnone
      cases hnone
  have hspec := mapM_except_spec (attachRoute axis frames s.boxes) s.routes routes hm
  have hlen : routes.length = s.routes.length := hspec.1
  have hi : k < s.routes.length := by rw [← hlen]; exact hkr
  obtain ⟨a, b, ha, hb, hab⟩ := hspec.2 k hi hkr
  have hbb : (some b) = (some r') := by rw [← hb]; exact hk
  have hbeq : b = r' := Option.some.inj hbb
  subst hbeq
  obtain ⟨hids, hshape⟩ := attachRoute_shape hab
  obtain ⟨hid, hfrom, hto, horth⟩ := hids
  have hmem : a ∈ s.routes := List.mem_of_getElem? ha
  cases hshape with
  | inl hpts => exact ⟨a, hmem, hid, hfrom, hto, horth, Or.inl hpts⟩
  | inr hex => exact ⟨a, hmem, hid, hfrom, hto, horth, Or.inr hex⟩
theorem find?_tuple_of_map_eq {l l' : List Route} (x : String)
    (h : l.map (fun r => (r.id, r.fromId, r.toId, r.orthogonal)) =
      l'.map (fun r => (r.id, r.fromId, r.toId, r.orthogonal))) :
    (l.find? (fun r => r.id == x)).map (fun r => (r.fromId, r.toId)) =
    (l'.find? (fun r => r.id == x)).map (fun r => (r.fromId, r.toId)) := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons b bs =>
      simp only [List.map_nil, List.map_cons] at h
      cases h
  | cons a as ih =>
    cases l' with
    | nil =>
      simp only [List.map_nil, List.map_cons] at h
      cases h
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hhead, htail⟩ := h
      have hid : a.id = b.id := congrArg Prod.fst hhead
      by_cases heq : (a.id == x) = true
      · have hbe : (b.id == x) = true := by rw [← hid]; exact heq
        have e1 : (a :: as).find? (fun r => r.id == x) = some a :=
          List.find?_cons_of_pos heq
        have e2 : (b :: bs).find? (fun r => r.id == x) = some b :=
          List.find?_cons_of_pos hbe
        rw [e1, e2, Option.map_some, Option.map_some]
        have hrest : (a.fromId, (a.toId, a.orthogonal)) =
            (b.fromId, (b.toId, b.orthogonal)) := congrArg Prod.snd hhead
        have efrom : a.fromId = b.fromId := congrArg Prod.fst hrest
        have eto : a.toId = b.toId := congrArg Prod.fst (congrArg Prod.snd hrest)
        have hft : (a.fromId, a.toId) = (b.fromId, b.toId) := by rw [efrom, eto]
        rw [hft]
      · have hbe : ¬(b.id == x) = true := by rw [← hid]; exact heq
        have e1 : (a :: as).find? (fun r => r.id == x) = as.find? (fun r => r.id == x) :=
          List.find?_cons_of_neg heq
        have e2 : (b :: bs).find? (fun r => r.id == x) = bs.find? (fun r => r.id == x) :=
          List.find?_cons_of_neg hbe
        rw [e1, e2]
        exact ih htail
theorem box_eq_of_frame {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (h : attachLaneEnds axis frames s = .ok d') (x : String) :
    d'.layoutDump.box? x = s.layoutDump.box? x := by
  have hfr := attachLaneEnds_frame h
  show (d'.boxes.find? (fun b => b.id == x) = s.boxes.find? (fun b => b.id == x))
  rw [hfr.1]

theorem ancestors_eq_of_frame {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (h : attachLaneEnds axis frames s = .ok d') (id : String) :
    d'.layoutDump.ancestors id = s.layoutDump.ancestors id :=
  ancestors_boxes_eq (attachLaneEnds_frame h).1 id


theorem labelOwnerAnc_eq_of_frame {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (h : attachLaneEnds axis frames s = .ok d') (l : Label) :
    d'.layoutDump.labelOwnerAnc l = s.layoutDump.labelOwnerAnc l := by
  have hfr := attachLaneEnds_frame h
  have hfind := find?_tuple_of_map_eq l.owner hfr.2.2.2
  have hanc := ancestors_eq_of_frame h
  unfold LayoutDump.labelOwnerAnc
  show (match d'.routes.find? (fun r => r.id == l.owner) with
    | some r => d'.layoutDump.ancestors r.fromId ++ d'.layoutDump.ancestors r.toId
    | none => l.owner :: d'.layoutDump.ancestors l.owner) =
    (match s.routes.find? (fun r => r.id == l.owner) with
    | some r => s.layoutDump.ancestors r.fromId ++ s.layoutDump.ancestors r.toId
    | none => l.owner :: s.layoutDump.ancestors l.owner)
  cases hd' : d'.routes.find? (fun r => r.id == l.owner) with
  | none =>
    cases hs' : s.routes.find? (fun r => r.id == l.owner) with
    | none =>
      rw [hanc]
    | some r =>
      simp only [hd', hs', Option.map_none, Option.map_some] at hfind
      cases hfind
  | some r' =>
    cases hs' : s.routes.find? (fun r => r.id == l.owner) with
    | none =>
      simp only [hd', hs', Option.map_none, Option.map_some] at hfind
      cases hfind
    | some r =>
      simp only [hd', hs', Option.map_some] at hfind
      have hft : (r'.fromId, r'.toId) = (r.fromId, r.toId) := Option.some.inj hfind
      have hff : r'.fromId = r.fromId := congrArg Prod.fst hft
      dsimp only
      have hft2 : r'.toId = r.toId := congrArg Prod.snd hft
      rw [hff, hft2, hanc, hanc]

theorem routeScope_eq_of_frame {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (h : attachLaneEnds axis frames s = .ok d') (r : Route) :
    d'.layoutDump.routeScope r = s.layoutDump.routeScope r :=
  routeScope_boxes_eq (attachLaneEnds_frame h).1 r

theorem attachLaneEnds_c1 {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (hC1 : Validator.C1 s.layoutDump) (h : attachLaneEnds axis frames s = .ok d') :
    Validator.C1 d'.layoutDump := by
  have hfr := attachLaneEnds_frame h
  have hcan : d'.layoutDump.canvas = s.layoutDump.canvas := hfr.2.2.1
  have hcr : Validator.canvasRect d'.layoutDump = Validator.canvasRect s.layoutDump := by
    unfold Validator.canvasRect
    rw [hcan]
  show ∀ b ∈ d'.boxes, (Validator.canvasRect d'.layoutDump).Contained b.rect
  rw [hcr, hfr.1]
  exact hC1

theorem attachLaneEnds_c2 {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (hC2 : Validator.C2 s.layoutDump) (h : attachLaneEnds axis frames s = .ok d') :
    Validator.C2 d'.layoutDump := by
  have hfr := attachLaneEnds_frame h
  show ∀ b ∈ d'.boxes, ∀ c ∈ d'.boxes, b.id ≠ c.id → b.exclusive = true →
    c.exclusive = true → b.parent = c.parent → Disjoint b.rect c.rect
  rw [hfr.1]
  exact hC2

theorem attachLaneEnds_c3 {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (hC3 : Validator.C3 s.layoutDump) (h : attachLaneEnds axis frames s = .ok d') :
    Validator.C3 d'.layoutDump := by
  have hfr := attachLaneEnds_frame h
  have hbox := box_eq_of_frame h
  show ∀ b ∈ d'.boxes, b.parent ≠ "" → ∀ p : Box,
    d'.layoutDump.box? b.parent = some p → p.rect.Contained b.rect
  rw [hfr.1]
  intro b hb hne p hp
  rw [hbox] at hp
  exact hC3 b hb hne p hp

theorem attachLaneEnds_c7 {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (hC7 : Validator.C7 s.layoutDump) (h : attachLaneEnds axis frames s = .ok d') :
    Validator.C7 d'.layoutDump := by
  have hfr := attachLaneEnds_frame h
  have hlab : d'.layoutDump.labels = s.layoutDump.labels := by
    show (d'.labels.map (·.toLabel) = s.labels.map (·.toLabel))
    rw [hfr.2.1]
  have hanc := labelOwnerAnc_eq_of_frame h
  show ∀ l ∈ d'.layoutDump.labels, ∀ b ∈ d'.boxes, b.exclusive = true →
    b.id ∉ d'.layoutDump.labelOwnerAnc l → ¬ l.rect.meetsInterior b.rect
  rw [hlab, hfr.1]
  intro l hl b hb hex hscope
  rw [hanc] at hscope
  exact hC7 l hl b hb hex hscope

theorem attachLaneEnds_c8a {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (hC8a : Validator.C8a s.layoutDump) (h : attachLaneEnds axis frames s = .ok d') :
    Validator.C8a d'.layoutDump := by
  have hfr := attachLaneEnds_frame h
  have hanc := ancestors_eq_of_frame h
  show ∀ g ∈ d'.boxes, g.role = "group" → ∀ b ∈ d'.boxes, b.id ≠ g.id →
    g.id ∉ d'.layoutDump.ancestors b.id → b.id ∉ d'.layoutDump.ancestors g.id →
    Disjoint g.rect b.rect
  rw [hfr.1]
  intro g hg hgr b hb hne h1 h2
  rw [hanc] at h1 h2
  exact hC8a g hg hgr b hb hne h1 h2

theorem attachLaneEnds_c8b {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (hC8b : Validator.C8b s.layoutDump) (h : attachLaneEnds axis frames s = .ok d') :
    Validator.C8b d'.layoutDump := by
  have hfr := attachLaneEnds_frame h
  have hlab : d'.layoutDump.labels = s.layoutDump.labels := by
    show (d'.labels.map (·.toLabel) = s.labels.map (·.toLabel))
    rw [hfr.2.1]
  show ∀ g ∈ d'.boxes, g.role = "group" → ∀ l ∈ d'.layoutDump.labels,
    Disjoint g.rect l.rect ∨ Rect.StrictInside g.rect l.rect
  rw [hfr.1, hlab]
  exact hC8b

theorem attachLaneEnds_c8 {axis : Axis} {frames : List LaneFrame} {s d' : Scene}
    (hC8 : Validator.C8 s.layoutDump) (h : attachLaneEnds axis frames s = .ok d') :
    Validator.C8 d'.layoutDump :=
  ⟨attachLaneEnds_c8a hC8.1 h, attachLaneEnds_c8b hC8.2 h⟩

theorem chain_aligned_of_orthogonal : ∀ (points : List Point),
    Polyline.isOrthogonal points = true → Elegant.Grid.Chain Elegant.Grid.Aligned points
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: rest, ho => by
    have ho' := ho
    rw [Polyline.isOrthogonal_cons, Bool.and_eq_true] at ho'
    exact ⟨by simpa only [Elegant.Grid.Aligned, Bool.or_eq_true, decide_eq_true_eq] using ho'.1,
      chain_aligned_of_orthogonal (b :: rest) ho'.2⟩

theorem attachEnd_rank {axis : Axis} {frames : List LaneFrame} {boxes : List Box}
    {id : String} {p q : Point} (h : attachEnd axis frames boxes id p = .ok (some q)) :
    axis.other.point q = axis.other.point p := by
  unfold attachEnd at h
  cases hf : frames.find? (fun b => b.id == id) with
  | none =>
    cases hb : boxes.find? (fun b => b.id == id) with
    | none =>
      simp only [hf, hb] at h
      have hok : Except.ok (none : Option Point) = Except.ok (some q) := h
      cases hok
    | some b =>
      simp only [hf, hb] at h
      have hok : Except.ok (none : Option Point) = Except.ok (some q) := h
      cases hok
  | some f =>
    cases hb : boxes.find? (fun b => b.id == id) with
    | none =>
      simp only [hf, hb] at h
      have hok : Except.ok (none : Option Point) = Except.ok (some q) := h
      cases hok
    | some b =>
      simp only [hf, hb] at h
      split at h
      · obtain ⟨v, _hv, h⟩ := bindOk h
        have hok : Except.ok (some (axis.withPoint p v)) = Except.ok (some q) := h
        cases hok
        cases axis <;> rfl
      · split at h
        · have hok : Except.ok (some (axis.withPoint p (axis.start b.rect))) =
            Except.ok (some q) := h
          cases hok
          cases axis <;> rfl
        · have hok : Except.ok (none : Option Point) = Except.ok (some q) := h
          cases hok

theorem placeRect_other {axis : Axis} (start thickness : Int) (r : Rect) :
    axis.other.start (placeRect axis start thickness r) = axis.other.start r ∧
    axis.other.length (placeRect axis start thickness r) = axis.other.length r := by
  cases axis <;>
    simp [placeRect, Axis.withStart, Axis.withLength, Axis.start, Axis.length, Axis.other]

theorem placeRect_cross {axis : Axis} (start thickness : Int) (r : Rect) :
    axis.start (placeRect axis start thickness r) = start ∧
    axis.length (placeRect axis start thickness r) = thickness := by
  cases axis <;>
    simp [placeRect, Axis.withStart, Axis.withLength, Axis.start, Axis.length]

end LaneBands
end Layered
end Elegant

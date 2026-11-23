import Elegant.Kinds.Common
import Elegant.Lanes
import Elegant.StyledMeasure
import Elegant.LanesFacts

set_option autoImplicit false

namespace Elegant.Kinds.Timeline

open Common

abbrev Family := Lanes.Timeline.Input
def shapeKind (b : ModelBox) : String :=
  let k := (b.shape.splitOn ":").headD ""
  if k == "" then "period" else k

def sectionOf (b : ModelBox) : Except LayoutError Int :=
  match (b.shape.splitOn ":").tail with
  | [] => pure (-1)
  | s :: _ => match s.toInt? with
    | some n => if 0 ≤ n then pure n else throw .domain
    | none => throw .domain

def measureCaption (profile : Profile) (role : TextRole) (target : Int) (text : String)
    (fontFamily : Bool := false) :
    Except LayoutError Lanes.Caption := do
  let mr := match role with
    | .title => Measure.Role.title
    | .body => Measure.Role.body
    | _ => Measure.Role.label
  let metric ← match profile with
    | .cell => pure Measure.Metric.cell
    | .vector => mr.metric fontFamily
  let lines ← match StyledMeasure.wrap metric target text.toList with
    | .ok ls => pure ls
    | .error _ => throw .overflow
  let lh : Int := if profile == .cell then 1 else if role == .title then 1536 else 1280
  return ⟨lines, lines.foldl (fun w l => max w l.width) 0,
    ((max 1 lines.length : Nat) : Int) * lh, role⟩

def target (c : Lanes.TimelineConsts) (slots : Nat) : Int :=
  (slots : Int) * c.cardWidth + ((slots : Int) - 1) * c.columnGap - 2 * c.cardPadding

def parentsRooted (m : Model) : Bool := m.boxes.all fun b => b.parent == ""

def decode (m : Model) : Except LayoutError Family := do
  if !parentsRooted m then throw .domain
  let c := Lanes.TimelineConsts.load m.profile
  let mut g : Family := { direction := m.options.direction, title := none, sections := [], periods := [] }
  for b in m.boxes do
    match shapeKind b with
    | "title" =>
      let caption ← measureCaption (fontFamily := m.options.fontFamily) m.profile .title I32_MAX (boxText m b)
      g := { g with title := some { id := b.id, caption } }
    | "section" =>
      let count := (m.boxes.filter fun p =>
        shapeKind p == "period" && (match sectionOf p with
          | .ok index => index == (g.sections.length : Int)
          | .error _ => false)).length
      let slots := if m.options.direction == .LR then max 1 count else 1
      let caption ← measureCaption (fontFamily := m.options.fontFamily) m.profile .label (target c slots) (boxText m b)
      g := { g with sections := g.sections ++ [{ id := b.id, caption }] }
    | "period" =>
      let sectionIndex ← sectionOf b
      if sectionIndex ≥ (g.sections.length : Int) then throw .domain
      let caption ← measureCaption (fontFamily := m.options.fontFamily) m.profile .label (target c 1) (boxText m b)
      g := { g with periods := g.periods ++ [{ id := b.id, caption, sectionIndex, events := [] }] }
    | "event" =>
      let some previous := g.periods.getLast? | throw .domain
      let some route := m.routes.find? (·.toId == b.id) | throw .domain
      let expectedSource := if m.options.direction == .LR then
        ((previous.events.getLast?).map (·.id)).getD previous.id
        else previous.id
      if route.fromId != expectedSource then throw .domain
      let caption ← measureCaption (fontFamily := m.options.fontFamily) m.profile .body (target c 1) (boxText m b)
      let event : Lanes.Timeline.Event := { id := b.id, caption, link := route.id }
      let updated := { previous with events := previous.events ++ [event] }
      g := { g with periods := g.periods.set (g.periods.length - 1) updated }
    | _ => throw .domain
  return g

def rectFor (g : Family) (p : Lanes.Timeline.Plan) (id : String) : Option Rect :=
  if (g.title.map (·.id)) == some id then some p.title
  else match g.sections.findIdx? (·.id == id) with
    | some i => p.sections[i]?
    | none => match g.periods.findIdx? (·.id == id) with
      | some i => p.periods[i]?
      | none => ((g.periods.zip p.events).flatMap fun (period, rects) =>
          (period.events.zip rects).map fun (e, r) => (e.id, r)).findSome? fun (name, r) =>
            if name == id then some r else none

def scene (m : Model) : Except LayoutError Scene := do
  let g ← decode m
  let r ← Lanes.Timeline.layout g m.profile
  let boxes ← m.boxes.mapM fun b => do
    let some rect := rectFor g r.geometry b.id | throw .domain
    pure (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box)
  let paths := r.geometry.routes.flatten
  if paths.length != m.routes.length then throw .domain
  let namedPaths := (g.periods.zip r.geometry.routes).flatMap fun (period, routes) =>
    (period.events.zip routes).map fun (event, points) => (event.link, points)
  let routes ← m.routes.mapM fun route => do
    let some points := namedPaths.findSome? (fun (id, points) =>
      if id == route.id then some points else none) | throw .domain
    pure (⟨route.id, route.fromId, route.toId, route.orthogonal, points⟩ : Route)
  return { kind := m.kind, profile := m.profile, options := m.options, canvas := r.canvas, boxes, routes, labels := [], items := r.groups }

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  match scene m with
  | .error e => .error (.geometry e)
  | .ok s => .ok { scene := s.projectCellAttachments (routeMarkers m), budgetExhausted := false }

theorem decode_parentsRooted {m : Model} {g : Family} (h : decode m = .ok g) :
    parentsRooted m = true := by
  cases hp : parentsRooted m with
  | true => rfl
  | false =>
    simp [decode, hp, Bind.bind, Except.bind] at h

theorem decode_box_parent {m : Model} {g : Family} (h : decode m = .ok g)
    {b : ModelBox} (hb : b ∈ m.boxes) : b.parent = "" := by
  have hp := decode_parentsRooted h
  unfold parentsRooted at hp
  have := (List.all_eq_true.mp hp) b hb
  exact beq_iff_eq.mp this

theorem layout_scene {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    ∃ s, scene m = .ok s ∧ result.scene.layoutDump = s.layoutDump := by
  cases hs : scene m with
  | error e => simp [layout, hs] at h
  | ok s =>
    have he : result =
        { scene := s.projectCellAttachments (routeMarkers m), budgetExhausted := false } := by
      simpa [layout, hs] using h.symm
    refine ⟨s, rfl, ?_⟩
    rw [he]
    exact Scene.projectCellAttachments_layoutDump s (routeMarkers m)

def RectSource (g : Family) (p : Lanes.Timeline.Plan) (id : String) (rect : Rect) : Prop :=
  (∃ card : Lanes.Timeline.Card, g.title = some card ∧ card.id = id ∧ rect = p.title) ∨
  (∃ (i : Nat) (card : Lanes.Timeline.Card), g.sections[i]? = some card ∧
    card.id = id ∧ p.sections[i]? = some rect) ∨
  (∃ (i : Nat) (period : Lanes.Timeline.Period), g.periods[i]? = some period ∧
    period.id = id ∧ p.periods[i]? = some rect) ∨
  (∃ (period : Lanes.Timeline.Period) (rects : List Rect) (event : Lanes.Timeline.Event),
    (period, rects) ∈ g.periods.zip p.events ∧
    (event, rect) ∈ period.events.zip rects ∧ event.id = id)

theorem rectFor_source {g : Family} {p : Lanes.Timeline.Plan} {id : String} {rect : Rect}
    (h : rectFor g p id = some rect) : RectSource g p id rect := by
  unfold rectFor at h
  split at h
  · rename_i htitle
    cases ht : g.title with
    | none => simp [ht] at htitle
    | some card =>
      have hid : card.id = id := by simpa only [ht, Option.map_some, beq_iff_eq,
        Option.some.injEq] using htitle
      exact Or.inl ⟨card, ht, hid, (Option.some.inj h).symm⟩
  · cases hs : g.sections.findIdx? (·.id == id) with
    | some i =>
      rw [hs] at h
      obtain ⟨hi, hid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hs
      refine Or.inr (Or.inl ⟨i, g.sections[i], ?_, ?_, h⟩)
      · exact List.getElem?_eq_getElem hi
      · exact beq_iff_eq.mp hid
    | none =>
      rw [hs] at h
      cases hp : g.periods.findIdx? (·.id == id) with
      | some i =>
        rw [hp] at h
        obtain ⟨hi, hid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hp
        refine Or.inr (Or.inr (Or.inl ⟨i, g.periods[i], ?_, ?_, h⟩))
        · exact List.getElem?_eq_getElem hi
        · exact beq_iff_eq.mp hid
      | none =>
        rw [hp] at h
        obtain ⟨before, pair, after, hlist, hfound, _⟩ :=
          List.findSome?_eq_some_iff.mp h
        have hpair : pair ∈ ((g.periods.zip p.events).flatMap fun (period, rects) =>
            (period.events.zip rects).map fun (event, r) => (event.id, r)) := by
          rw [hlist]
          simp
        have hid : pair.1 = id := by
          by_cases he : pair.1 == id
          · exact beq_iff_eq.mp he
          · simp [he] at hfound
        have hrect : pair.2 = rect := by
          simpa only [show (pair.1 == id) = true from beq_iff_eq.mpr hid,
            ↓reduceIte, Option.some.injEq] using hfound
        obtain ⟨⟨period, rects⟩, hperiod, hpair⟩ := List.mem_flatMap.mp hpair
        obtain ⟨⟨event, r⟩, hevent, heq⟩ := List.mem_map.mp hpair
        have heqId : event.id = id := (congrArg Prod.fst heq).trans hid
        have heqRect : r = rect := (congrArg Prod.snd heq).trans hrect
        subst r
        exact Or.inr (Or.inr (Or.inr ⟨period, rects, event, hperiod, hevent, heqId⟩))

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

inductive Correspond {α β : Type} (rel : α → β → Prop) : List α → List β → Prop
  | nil : Correspond rel [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      rel a b → Correspond rel as bs → Correspond rel (a :: as) (b :: bs)

theorem Correspond.imp {α β : Type} {rel next : α → β → Prop}
    {input : List α} {output : List β} (h : Correspond rel input output)
    (step : ∀ a b, rel a b → next a b) : Correspond next input output := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (step _ _ hab) ih

theorem mapM_correspond {α β : Type} (f : α → Except LayoutError β) :
    ∀ (input : List α) (output : List β), input.mapM f = .ok output →
      Correspond (fun a b => f a = .ok b) input output := by
  intro input
  induction input with
  | nil =>
    intro output h
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst output
    exact .nil
  | cons a rest ih =>
    intro output h
    rw [List.mapM_cons] at h
    obtain ⟨b, hab, h⟩ := bind_ok h
    obtain ⟨bs, hrest, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst output
    exact .cons hab (ih bs hrest)

theorem forall₂_left_lookup {α β : Type} {rel : α → β → Prop}
    {input : List α} {output : List β} (h : Correspond rel input output)
    {a : α} (ha : a ∈ input) : ∃ b ∈ output, rel a b := by
  induction h with
  | nil => cases ha
  | @cons x y xs ys hxy _ ih =>
    rcases List.mem_cons.mp ha with he | hm
    · subst a
      exact ⟨y, List.mem_cons_self .., hxy⟩
    · obtain ⟨b, hb, hab⟩ := ih hm
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem forall₂_right_lookup {α β : Type} {rel : α → β → Prop}
    {input : List α} {output : List β} (h : Correspond rel input output)
    {b : β} (hb : b ∈ output) : ∃ a ∈ input, rel a b := by
  induction h with
  | nil => cases hb
  | @cons x y xs ys hxy _ ih =>
    rcases List.mem_cons.mp hb with he | hm
    · subst b
      exact ⟨x, List.mem_cons_self .., hxy⟩
    · obtain ⟨a, ha, hab⟩ := ih hm
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

def BoxCorrespond (g : Family) (p : Lanes.Timeline.Plan) (b : ModelBox) (out : Box) :
    Prop :=
  out.id = b.id ∧ out.parent = b.parent ∧ out.role = b.role.id ∧
    out.exclusive = b.exclusive ∧ rectFor g p b.id = some out.rect

def NamedPath (g : Family) (p : Lanes.Timeline.Plan) (id : String) :
    Option (List Point) :=
  ((g.periods.zip p.routes).flatMap fun (period, routes) =>
    (period.events.zip routes).map fun (event, points) => (event.link, points)).findSome?
      (fun (name, points) => if name == id then some points else none)

def RouteCorrespond (g : Family) (p : Lanes.Timeline.Plan)
    (route : ModelRoute) (out : Route) : Prop :=
  out.id = route.id ∧ out.fromId = route.fromId ∧ out.toId = route.toId ∧
    out.orthogonal = route.orthogonal ∧ NamedPath g p route.id = some out.points

theorem scene_execution {m : Model} {s : Scene} (h : scene m = .ok s) :
    ∃ g r, decode m = .ok g ∧ Lanes.Timeline.layout g m.profile = .ok r ∧
      s.canvas = r.canvas ∧ s.labels = [] ∧
      Correspond (BoxCorrespond g r.geometry) m.boxes s.boxes ∧
      Correspond (RouteCorrespond g r.geometry) m.routes s.routes := by
  unfold scene at h
  obtain ⟨g, hg, h⟩ := bind_ok h
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨boxes, hboxes, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨routes, hroutes, h⟩ := bind_ok h
    have hs : ({ kind := m.kind, profile := m.profile, options := m.options, canvas := r.canvas, boxes := boxes, routes := routes, labels := [], items := r.groups } : Scene) = s := by
      simpa only [pure, Except.pure, Except.ok.injEq] using h
    subst s
    refine ⟨g, r, hg, hr, rfl, rfl, ?_, ?_⟩
    · refine (mapM_correspond _ _ _ hboxes).imp ?_
      intro b box hb
      cases hrect : rectFor g r.geometry b.id with
      | none => simp [hrect] at hb
      | some rect =>
        have he : (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box) = box := by
          simpa only [hrect, pure, Except.pure, Except.ok.injEq] using hb
        subst box
        exact ⟨rfl, rfl, rfl, rfl, hrect⟩
    · refine (mapM_correspond _ _ _ hroutes).imp ?_
      intro route out hroute
      cases hpoints : NamedPath g r.geometry route.id with
      | none =>
        simp only [NamedPath] at hpoints
        simp only [hpoints] at hroute
        change (Except.error LayoutError.domain : Except LayoutError Route) = Except.ok out at hroute
        cases hroute
      | some points =>
        have hlookup := hpoints
        simp only [NamedPath] at hlookup
        have he : (⟨route.id, route.fromId, route.toId, route.orthogonal, points⟩ : Route) =
            out := by
          simpa only [hlookup, pure, Except.pure, Except.ok.injEq] using hroute
        subst out
        exact ⟨rfl, rfl, rfl, rfl, hpoints⟩

theorem scene_box_rectFor {m : Model} {s : Scene} (h : scene m = .ok s)
    {b : ModelBox} (hb : b ∈ m.boxes) :
    ∃ g r out, decode m = .ok g ∧ Lanes.Timeline.layout g m.profile = .ok r ∧
      out ∈ s.boxes ∧ BoxCorrespond g r.geometry b out ∧
      RectSource g r.geometry b.id out.rect := by
  obtain ⟨g, r, hg, hr, _hc, _hl, hboxes, _hroutes⟩ := scene_execution h
  obtain ⟨out, hout, hcorr⟩ := forall₂_left_lookup hboxes hb
  exact ⟨g, r, out, hg, hr, hout, hcorr, rectFor_source hcorr.2.2.2.2⟩

theorem scene_box_source {m : Model} {s : Scene} (h : scene m = .ok s)
    {out : Box} (hout : out ∈ s.boxes) :
    ∃ g r b, decode m = .ok g ∧ Lanes.Timeline.layout g m.profile = .ok r ∧
      b ∈ m.boxes ∧ BoxCorrespond g r.geometry b out ∧
      RectSource g r.geometry out.id out.rect := by
  obtain ⟨g, r, hg, hr, _hc, _hl, hboxes, _hroutes⟩ := scene_execution h
  obtain ⟨b, hb, hcorr⟩ := forall₂_right_lookup hboxes hout
  refine ⟨g, r, b, hg, hr, hb, hcorr, ?_⟩
  rw [hcorr.1]
  exact rectFor_source hcorr.2.2.2.2

theorem scene_parent {m : Model} {s : Scene} (h : scene m = .ok s) :
    Validator.C3 s.layoutDump := by
  intro box hb hn _parent _hp
  obtain ⟨g, _r, b, hg, _hr, hbm, hcorr, _hsource⟩ := scene_box_source h hb
  exact False.elim (hn (hcorr.2.1.trans (decode_box_parent hg hbm)))

theorem scene_label_clearance {m : Model} {s : Scene} (h : scene m = .ok s) :
    Validator.C7 s.layoutDump := by
  obtain ⟨_g, _r, _hg, _hr, _hc, hl, _hb, _hroute⟩ := scene_execution h
  intro label hlabel
  change label ∈ s.labels.map (·.toLabel) at hlabel
  rw [hl] at hlabel
  cases hlabel

theorem scene_frame_labels {m : Model} {s : Scene} (h : scene m = .ok s) :
    Validator.C8b s.layoutDump := by
  obtain ⟨_g, _r, _hg, _hr, _hc, hl, _hb, _hroute⟩ := scene_execution h
  intro _frame _hf _hrole label hlabel
  change label ∈ s.labels.map (·.toLabel) at hlabel
  rw [hl] at hlabel
  cases hlabel

theorem layout_parent {m : Model} {r : Layered.FamilyResult}
    (h : layout m = .ok r) : Validator.C3 r.scene.layoutDump := by
  obtain ⟨s, hs, hd⟩ := layout_scene h
  rw [hd]
  exact scene_parent hs

theorem layout_label_clearance {m : Model} {r : Layered.FamilyResult}
    (h : layout m = .ok r) : Validator.C7 r.scene.layoutDump := by
  obtain ⟨s, hs, hd⟩ := layout_scene h
  rw [hd]
  exact scene_label_clearance hs

theorem layout_frame_labels {m : Model} {r : Layered.FamilyResult}
    (h : layout m = .ok r) : Validator.C8b r.scene.layoutDump := by
  obtain ⟨s, hs, hd⟩ := layout_scene h
  rw [hd]
  exact scene_frame_labels hs

def cardRects (g : Family) (p : Lanes.Timeline.Plan) : List Rect :=
  (if g.title.isSome then [p.title] else []) ++
    p.sections ++ p.periods ++ p.events.flatten

theorem rectSource_mem {g : Family} {p : Lanes.Timeline.Plan} {id : String} {rect : Rect}
    (h : RectSource g p id rect) : rect ∈ cardRects g p := by
  rcases h with ⟨card, ht, _hid, hr⟩ | ⟨i, card, _hc, _hid, hr⟩ |
    ⟨i, period, _hp, _hid, hr⟩ | ⟨period, rects, event, hp, he, _hid⟩
  · subst rect
    simp [cardRects, ht]
  · have hm := List.mem_of_getElem? hr
    simp [cardRects, hm]
  · have hm := List.mem_of_getElem? hr
    simp [cardRects, hm]
  · have hrect : rect ∈ rects := (List.of_mem_zip he).2
    have hrects : rects ∈ p.events := (List.of_mem_zip hp).2
    have hm : rect ∈ p.events.flatten := List.mem_flatten.mpr ⟨rects, hrects, hrect⟩
    simp [cardRects, hm]

theorem cardRects_shift (g : Family) (p : Lanes.Timeline.Plan) (dx dy : Int) :
    cardRects g (p.shift dx dy) = (cardRects g p).map (Lanes.shiftRect dx dy) := by
  unfold cardRects Lanes.Timeline.Plan.shift
  split <;> simp [List.map_append, List.map_flatten]

theorem cardRects_mem_parts {g : Family} {p : Lanes.Timeline.Plan} {rect : Rect}
    (profile : Profile) (h : rect ∈ cardRects g p) : rect ∈ p.parts g profile := by
  simp only [cardRects, List.mem_append] at h
  simp only [Lanes.Timeline.Plan.parts, List.mem_append]
  rcases h with ((ht | hs) | hp) | he
  all_goals simp_all
private theorem union_contains_left (a b : Rect) : (a.unionRaw b).Contained a := by
  unfold Rect.unionRaw Rect.Contained
  dsimp only
  omega

private theorem union_contains_right (a b : Rect) : (a.unionRaw b).Contained b := by
  unfold Rect.unionRaw Rect.Contained
  dsimp only
  omega

theorem fold_union_contains (rects : List Rect) (initial : Rect) :
    (rects.foldl Rect.unionRaw initial).Contained initial ∧
      ∀ rect ∈ rects, (rects.foldl Rect.unionRaw initial).Contained rect := by
  induction rects generalizing initial with
  | nil => exact ⟨Rect.Contained.refl _, fun _ hm => False.elim (List.not_mem_nil hm)⟩
  | cons first rest ih =>
    obtain ⟨hinit, hrest⟩ := ih (initial.unionRaw first)
    refine ⟨hinit.trans (union_contains_left _ _), ?_⟩
    intro rect hm
    rcases List.mem_cons.mp hm with he | hr
    · subst rect
      exact hinit.trans (union_contains_right _ _)
    · exact hrest rect hr

theorem extent_contains_part (g : Family) (p : Lanes.Timeline.Plan) (profile : Profile)
    {rect : Rect} (h : rect ∈ p.parts g profile) : (p.extent g profile).Contained rect := by
  unfold Lanes.Timeline.Plan.extent
  cases hp : p.parts g profile with
  | nil => simp [hp] at h
  | cons first rest =>
    rw [hp] at h
    rcases List.mem_cons.mp h with he | hm
    · subst rect
      exact (fold_union_contains rest first).1
    · exact (fold_union_contains rest first).2 rect hm

theorem native_layout_geometry {g : Family} {profile : Profile}
    {r : Lanes.Timeline.Result} (h : Lanes.Timeline.layout g profile = .ok r) :
    let c := Lanes.TimelineConsts.load profile
    let raw := Lanes.Timeline.plan g c
    let ext := raw.extent g profile
    r.geometry = raw.shift (c.canvasMargin - ext.x) (c.canvasMargin - ext.y) ∧
      r.canvas = ⟨ext.w + 2 * c.canvasMargin, ext.h + 2 * c.canvasMargin⟩ := by
  let c := Lanes.TimelineConsts.load profile
  let raw := Lanes.Timeline.plan g c
  let ext := raw.extent g profile
  let p := raw.shift (c.canvasMargin - ext.x) (c.canvasMargin - ext.y)
  let canvas : Size := ⟨ext.w + 2 * c.canvasMargin, ext.h + 2 * c.canvasMargin⟩
  let values := [canvas.w, canvas.h] ++
    ((if g.title.isSome then [p.title] else []) ++ p.sections ++ p.periods ++ p.events.flatten).flatMap
      (Lanes.rectValues 0 0) ++ p.routes.flatten.flatten.flatMap (Lanes.pointValues 0 0) ++
      Lanes.pointValues 0 0 p.axisStart ++ Lanes.pointValues 0 0 p.axisEnd
  by_cases hg : (g.periods.all fun period =>
      decide (-1 ≤ period.sectionIndex ∧ period.sectionIndex < (g.sections.length : Int))) = true
  · simp only [Lanes.Timeline.layout, hg, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at h
    change (if (!values.all Lanes.withinLimit) = true then Except.error LayoutError.overflow
      else Except.ok ({ canvas := canvas, geometry := p, groups := Lanes.Timeline.paint g profile c p } : Lanes.Timeline.Result)) = .ok r at h
    cases hv : values.all Lanes.withinLimit with
    | false => simp [hv] at h
    | true =>
      simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
      subst r
      exact ⟨rfl, rfl⟩
  · have hfalse : (g.periods.all fun period =>
        decide (-1 ≤ period.sectionIndex ∧ period.sectionIndex < (g.sections.length : Int))) =
        false := by
      cases he : (g.periods.all fun period =>
          decide (-1 ≤ period.sectionIndex ∧ period.sectionIndex < (g.sections.length : Int))) with
      | false => rfl
      | true => exact False.elim (hg he)
    unfold Lanes.Timeline.layout at h
    rw [hfalse] at h
    change (Except.error LayoutError.domain : Except LayoutError Lanes.Timeline.Result) =
      Except.ok r at h
    cases h

theorem native_rect_inside_canvas {g : Family} {profile : Profile}
    {r : Lanes.Timeline.Result} (h : Lanes.Timeline.layout g profile = .ok r)
    {id : String} {rect : Rect} (hs : RectSource g r.geometry id rect) :
    (⟨0, 0, r.canvas.w, r.canvas.h⟩ : Rect).Contained rect := by
  let c := Lanes.TimelineConsts.load profile
  let raw := Lanes.Timeline.plan g c
  let ext := raw.extent g profile
  obtain ⟨hgeometry, hcanvas⟩ := native_layout_geometry h
  have hmem := rectSource_mem hs
  rw [hgeometry, cardRects_shift] at hmem
  obtain ⟨original, horiginal, hshift⟩ := List.mem_map.mp hmem
  have hin := extent_contains_part g raw profile
    (cardRects_mem_parts profile horiginal)
  have hmargin : 0 ≤ c.canvasMargin :=
    (Lanes.timeline_constants_positive profile).2.2.2.2.2
  rw [hcanvas, ← hshift]
  change (⟨0, 0, ext.w + 2 * c.canvasMargin, ext.h + 2 * c.canvasMargin⟩ : Rect).Contained
    (Lanes.shiftRect (c.canvasMargin - ext.x) (c.canvasMargin - ext.y) original)
  change ext.Contained original at hin
  unfold Rect.Contained Lanes.shiftRect at *
  dsimp only at *
  omega

theorem scene_canvas {m : Model} {s : Scene} (h : scene m = .ok s) :
    Validator.C1 s.layoutDump := by
  obtain ⟨g, r, _hg, hr, hcanvas, _hl, hboxes, _hroutes⟩ := scene_execution h
  intro box hb
  obtain ⟨b, _hb, hcorr⟩ := forall₂_right_lookup hboxes hb
  change (⟨0, 0, s.canvas.w, s.canvas.h⟩ : Rect).Contained box.rect
  rw [hcanvas]
  exact native_rect_inside_canvas hr (rectFor_source hcorr.2.2.2.2)

theorem layout_canvas {m : Model} {r : Layered.FamilyResult}
    (h : layout m = .ok r) : Validator.C1 r.scene.layoutDump := by
  obtain ⟨s, hs, hd⟩ := layout_scene h
  rw [hd]
  exact scene_canvas hs

theorem namedPath_source {g : Family} {p : Lanes.Timeline.Plan}
    {id : String} {points : List Point} (h : NamedPath g p id = some points) :
    ∃ period routes event, (period, routes) ∈ g.periods.zip p.routes ∧
      (event, points) ∈ period.events.zip routes ∧ event.link = id := by
  unfold NamedPath at h
  obtain ⟨before, pair, after, hlist, hfound, _⟩ :=
    List.findSome?_eq_some_iff.mp h
  have hpair : pair ∈ ((g.periods.zip p.routes).flatMap fun (period, routes) =>
      (period.events.zip routes).map fun (event, path) => (event.link, path)) := by
    rw [hlist]
    simp
  have hid : pair.1 = id := by
    by_cases he : pair.1 == id
    · exact beq_iff_eq.mp he
    · simp [he] at hfound
  have hpoints : pair.2 = points := by
    simpa only [show (pair.1 == id) = true from beq_iff_eq.mpr hid,
      ↓reduceIte, Option.some.injEq] using hfound
  obtain ⟨⟨period, routes⟩, hperiod, hpair⟩ := List.mem_flatMap.mp hpair
  obtain ⟨⟨event, path⟩, hevent, heq⟩ := List.mem_map.mp hpair
  have heqId : event.link = id := (congrArg Prod.fst heq).trans hid
  have heqPoints : path = points := (congrArg Prod.snd heq).trans hpoints
  subst path
  exact ⟨period, routes, event, hperiod, hevent, heqId⟩

theorem scene_route_source {m : Model} {s : Scene} (h : scene m = .ok s)
    {out : Route} (hout : out ∈ s.routes) :
    ∃ g r route period routes event,
      decode m = .ok g ∧ Lanes.Timeline.layout g m.profile = .ok r ∧
      route ∈ m.routes ∧ RouteCorrespond g r.geometry route out ∧
      (period, routes) ∈ g.periods.zip r.geometry.routes ∧
      (event, out.points) ∈ period.events.zip routes ∧ event.link = route.id := by
  obtain ⟨g, r, hg, hr, _hc, _hl, _hboxes, hroutes⟩ := scene_execution h
  obtain ⟨route, hroute, hcorr⟩ := forall₂_right_lookup hroutes hout
  obtain ⟨period, routes, event, hp, he, hid⟩ := namedPath_source hcorr.2.2.2.2
  exact ⟨g, r, route, period, routes, event, hg, hr, hroute, hcorr, hp, he, hid⟩

def RoutesOrthogonal (routes : List (List (List Point))) : Prop :=
  ∀ paths ∈ routes, ∀ points ∈ paths, Polyline.isOrthogonal points = true

private theorem foldl_preserves {α β : Type} (step : β → α → β) (P : β → Prop)
    (hstep : ∀ state item, P state → P (step state item)) :
    ∀ (items : List α) (initial : β), P initial → P (items.foldl step initial) := by
  intro items
  induction items with
  | nil => intro initial hi; exact hi
  | cons item rest ih =>
    intro initial hi
    exact ih _ (hstep initial item hi)

theorem horizontal_routes_fold_orthogonal (x : Int) (rects : List Rect)
    (initial : Rect × List (List Point))
    (hi : ∀ points ∈ initial.2, Polyline.isOrthogonal points = true) :
    ∀ points ∈ (rects.foldl (fun (state : Rect × List (List Point)) box =>
      (box, state.2 ++ [[⟨x, state.1.y + state.1.h⟩, ⟨x, box.y⟩]])) initial).2,
      Polyline.isOrthogonal points = true := by
  apply foldl_preserves _
    (fun state : Rect × List (List Point) =>
      ∀ points ∈ state.2, Polyline.isOrthogonal points = true) ?_ rects initial hi
  intro state box hs points hp
  rcases List.mem_append.mp hp with hold | hnew
  · exact hs points hold
  · have he : points = [⟨x, state.1.y + state.1.h⟩, ⟨x, box.y⟩] := by
      simpa only [List.mem_singleton] using hnew
    subst points
    simp [Polyline.isOrthogonal]

theorem horizontalPlan_orthogonal (g : Family) (c : Lanes.TimelineConsts) :
    RoutesOrthogonal (Lanes.Timeline.horizontalPlan g c).routes := by
  intro paths hp points hpoints
  change paths ∈ (((Lanes.Timeline.horizontalPlan g c).periods.zip
    (Lanes.Timeline.horizontalPlan g c).events).map fun (r, es) =>
      (es.foldl (fun (state : Rect × List (List Point)) b =>
        let x := r.x + Lanes.half (Lanes.Timeline.cardWidth g c)
        (b, state.2 ++ [[⟨x, state.1.y + state.1.h⟩, ⟨x, b.y⟩]])) (r, [])).2) at hp
  obtain ⟨⟨r, es⟩, _hpair, he⟩ := List.mem_map.mp hp
  rw [← he] at hpoints
  exact horizontal_routes_fold_orthogonal
    (r.x + Lanes.half (Lanes.Timeline.cardWidth g c)) es (r, [])
    (fun _ hm => False.elim (List.not_mem_nil hm)) points hpoints

theorem elbow_orthogonal (a b : Point) (x : Int) :
    Polyline.isOrthogonal (Lanes.Timeline.elbow a b x) = true := by
  unfold Lanes.Timeline.elbow
  split
  · rename_i he
    have hy : a.y = b.y := beq_iff_eq.mp he
    simp [Polyline.isOrthogonal, hy]
  · simp [Polyline.isOrthogonal]

theorem verticalRow_orthogonal (g : Family) (c : Lanes.TimelineConsts) (i : Nat)
    (state : Lanes.Timeline.VerticalState) (hs : RoutesOrthogonal state.routes) :
    RoutesOrthogonal (Lanes.Timeline.verticalRow g c i state).routes := by
  intro paths hp points hpoints
  change paths ∈ state.routes.set i _ at hp
  rcases List.mem_or_eq_of_mem_set hp with hold | hnew
  · exact hs paths hold points hpoints
  · rw [hnew] at hpoints
    obtain ⟨box, _hbox, he⟩ := List.mem_map.mp hpoints
    rw [← he]
    exact elbow_orthogonal _ _ _

theorem verticalPlan_orthogonal (g : Family) (c : Lanes.TimelineConsts) :
    RoutesOrthogonal (Lanes.Timeline.verticalPlan g c).routes := by
  let initial : Lanes.Timeline.VerticalState :=
    { y := Lanes.Timeline.contentTop g c, sections := List.replicate g.sections.length Lanes.zeroRect, periods := List.replicate g.periods.length Lanes.zeroRect, events := List.replicate g.periods.length [], routes := List.replicate g.periods.length [] }
  let rowStep := fun (state : Lanes.Timeline.VerticalState) (i : Nat) =>
    Lanes.Timeline.verticalRow g c i state
  let sectionStep := fun (state : Lanes.Timeline.VerticalState) (s : Nat) =>
    let rect : Rect := ⟨c.leftMargin, state.y, Lanes.Timeline.cardWidth g c,
      Lanes.Timeline.sectionHeight g c⟩
    let state := { state with y := state.y + Lanes.Timeline.sectionHeight g c + c.sectionGap, sections := state.sections.set s rect }
    (Lanes.Timeline.members g (s : Int)).foldl rowStep state
  have hrow : ∀ (state : Lanes.Timeline.VerticalState) (i : Nat), RoutesOrthogonal state.routes →
      RoutesOrthogonal (rowStep state i).routes :=
    fun state i hs => verticalRow_orthogonal g c i state hs
  have hinitial : RoutesOrthogonal initial.routes := by
    intro paths hp points hpoints
    have he : paths = [] := (List.mem_replicate.mp hp).2
    subst paths
    cases hpoints
  have hsections : ∀ (state : Lanes.Timeline.VerticalState) (s : Nat), RoutesOrthogonal state.routes →
      RoutesOrthogonal (sectionStep state s).routes := by
    intro state s hs
    exact foldl_preserves rowStep (fun st => RoutesOrthogonal st.routes) hrow _ _ hs
  change RoutesOrthogonal
    ((List.range g.sections.length).foldl sectionStep
      ((Lanes.Timeline.members g (-1)).foldl rowStep initial)).routes
  exact foldl_preserves sectionStep (fun state => RoutesOrthogonal state.routes) hsections _ _
    (foldl_preserves rowStep (fun state => RoutesOrthogonal state.routes) hrow _ _ hinitial)

theorem plan_orthogonal (g : Family) (c : Lanes.TimelineConsts) :
    RoutesOrthogonal (Lanes.Timeline.plan g c).routes := by
  unfold Lanes.Timeline.plan
  split
  · exact horizontalPlan_orthogonal g c
  · exact verticalPlan_orthogonal g c

theorem shift_orthogonal (dx dy : Int) :
    ∀ (points : List Point), Polyline.isOrthogonal points = true →
      Polyline.isOrthogonal (points.map (Lanes.shiftPoint dx dy)) = true := by
  intro points
  induction points with
  | nil => intro _; rfl
  | cons p rest ih =>
    cases rest with
    | nil => intro _; rfl
    | cons q tail =>
      intro h
      have hparts := Bool.and_eq_true_iff.mp h
      have hpq : p.x = q.x ∨ p.y = q.y := by
        simpa only [Bool.or_eq_true, decide_eq_true_eq] using hparts.1
      apply Bool.and_eq_true_iff.mpr
      refine ⟨?_, ih hparts.2⟩
      change decide (p.x + dx = q.x + dx) || decide (p.y + dy = q.y + dy) = true
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      rcases hpq with hx | hy
      · exact Or.inl (congrArg (· + dx) hx)
      · exact Or.inr (congrArg (· + dy) hy)

theorem plan_shift_orthogonal {p : Lanes.Timeline.Plan} (dx dy : Int)
    (h : RoutesOrthogonal p.routes) : RoutesOrthogonal (p.shift dx dy).routes := by
  intro paths hp points hpoints
  obtain ⟨rawPaths, hpaths, he⟩ := List.mem_map.mp hp
  subst paths
  obtain ⟨rawPoints, hraw, he⟩ := List.mem_map.mp hpoints
  subst points
  exact shift_orthogonal dx dy rawPoints (h rawPaths hpaths rawPoints hraw)

theorem native_routes_orthogonal {g : Family} {profile : Profile}
    {r : Lanes.Timeline.Result} (h : Lanes.Timeline.layout g profile = .ok r) :
    RoutesOrthogonal r.geometry.routes := by
  obtain ⟨hgeometry, _hcanvas⟩ := native_layout_geometry h
  rw [hgeometry]
  exact plan_shift_orthogonal _ _ (plan_orthogonal g (Lanes.TimelineConsts.load profile))

theorem scene_orthogonal {m : Model} {s : Scene} (h : scene m = .ok s) :
    Validator.C4 s.layoutDump := by
  intro route hroute _horthogonal
  obtain ⟨g, r, _mr, period, paths, event, _hg, hr, _hmr, _hcorr, hp, he, _hid⟩ :=
    scene_route_source h hroute
  exact native_routes_orthogonal hr paths (List.of_mem_zip hp).2 route.points
    (List.of_mem_zip he).2

theorem layout_orthogonal {m : Model} {r : Layered.FamilyResult}
    (h : layout m = .ok r) : Validator.C4 r.scene.layoutDump := by
  obtain ⟨s, hs, hd⟩ := layout_scene h
  rw [hd]
  exact scene_orthogonal hs

theorem Correspond.map_eq {α β γ : Type} {rel : α → β → Prop}
    {input : List α} {output : List β} (h : Correspond rel input output)
    (left : α → γ) (right : β → γ)
    (hfield : ∀ a b, rel a b → left a = right b) :
    input.map left = output.map right := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    simp only [List.map_cons]
    rw [hfield _ _ hab, ih]

theorem scene_boxIds_nodup {m : Model} {s : Scene} (hwf : WellFormed m)
    (h : scene m = .ok s) : (s.boxes.map (·.id)).Nodup := by
  obtain ⟨_g, _r, _hg, _hr, _hc, _hl, hboxes, _hroutes⟩ := scene_execution h
  have hids := hboxes.map_eq (fun b => b.id) (fun b => b.id)
    (fun _ _ hc => hc.1.symm)
  rw [← hids]
  exact Model.boxIds_nodup hwf

private theorem box_lookup_self {boxes : List Box} {box : Box}
    (hunique : (boxes.map (·.id)).Nodup) (hmem : box ∈ boxes) :
    boxes.find? (fun candidate => candidate.id == box.id) = some box := by
  induction boxes with
  | nil => cases hmem
  | cons first rest ih =>
    obtain ⟨hfresh, hrest⟩ := List.nodup_cons.mp hunique
    rcases List.mem_cons.mp hmem with he | hm
    · subst box
      simp
    · have hne : first.id ≠ box.id := by
        intro he
        exact hfresh (List.mem_map.mpr ⟨box, hm, he.symm⟩)
      simpa [hne] using ih hrest hm

theorem scene_box_lookup {m : Model} {s : Scene} (hwf : WellFormed m)
    (h : scene m = .ok s) {box : ModelBox} (hbox : box ∈ m.boxes) :
    ∃ g r out, decode m = .ok g ∧ Lanes.Timeline.layout g m.profile = .ok r ∧
      s.layoutDump.box? box.id = some out ∧ BoxCorrespond g r.geometry box out ∧
      RectSource g r.geometry box.id out.rect := by
  obtain ⟨g, r, out, hg, hr, hout, hcorr, hsource⟩ := scene_box_rectFor h hbox
  have hlookup := box_lookup_self (scene_boxIds_nodup hwf h) hout
  rw [hcorr.1] at hlookup
  exact ⟨g, r, out, hg, hr, hlookup, hcorr, hsource⟩

def EventLinks (m : Model) : String → List Lanes.Timeline.Event → Prop
  | _, [] => True
  | source, event :: rest =>
    (∃ route ∈ m.routes, route.id = event.link ∧ route.fromId = source ∧
      route.toId = event.id) ∧
    EventLinks m (if m.options.direction == .LR then event.id else source) rest

theorem eventLinks_append {m : Model} {event : Lanes.Timeline.Event}
    {route : ModelRoute} (hr : route ∈ m.routes) (hid : route.id = event.link)
    (hto : route.toId = event.id) :
    ∀ (events : List Lanes.Timeline.Event) (source : String),
      EventLinks m source events →
      route.fromId = (if m.options.direction == .LR then
        ((events.getLast?).map (·.id)).getD source else source) →
      EventLinks m source (events ++ [event]) := by
  intro events
  induction events with
  | nil =>
    intro source _ hfrom
    have hs : route.fromId = source := by simpa only [List.getLast?_nil,
      Option.map_none, Option.getD_none, ite_self] using hfrom
    exact ⟨⟨route, hr, hid, hs, hto⟩, trivial⟩
  | cons first rest ih =>
    intro source hlinks hfrom
    refine ⟨hlinks.1, ih _ hlinks.2 ?_⟩
    cases rest with
    | nil =>
      by_cases hdir : (m.options.direction == .LR) = true
      all_goals simpa only [hdir, Bool.false_eq_true, ↓reduceIte, List.getLast?_singleton, List.getLast?_nil,
        Option.map_some, Option.map_none, Option.getD_some, Option.getD_none] using hfrom
    | cons second tail =>
      by_cases hd : m.options.direction == .LR
      · cases hl : (second :: tail).getLast? with
        | none =>
          have hempty := List.getLast?_eq_none_iff.mp hl
          cases hempty
        | some last =>
          simpa only [hd, ↓reduceIte, List.getLast?_cons_cons, hl,
            Option.map_some, Option.getD_some] using hfrom
      · simpa only [hd, Bool.false_eq_true, ↓reduceIte] using hfrom

def DecodedLinks (m : Model) (g : Family) : Prop :=
  ∀ period ∈ g.periods, EventLinks m period.id period.events

private theorem forIn_preserves {α β : Type} (inputs : List α)
    (step : α → β → Except LayoutError (ForInStep β)) (P : β → Prop)
    (initial final : β) (hi : P initial)
    (hstep : ∀ item ∈ inputs, ∀ state next, P state →
      step item state = .ok next → P next.value)
    (h : forIn inputs initial step = .ok final) : P final := by
  induction inputs generalizing initial with
  | nil =>
    have he : initial = final := by
      simpa only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] using h
    simpa only [← he] using hi
  | cons item rest ih =>
    rw [List.forIn_cons] at h
    cases hs : step item initial with
    | error err => simp [hs, Bind.bind, Except.bind] at h
    | ok next =>
      have hn := hstep item (List.mem_cons_self ..) initial next hi hs
      cases next with
      | done state =>
        dsimp only [ForInStep.value] at hn
        have he : state = final := by
          simpa [hs, Bind.bind, Except.bind, pure, Except.pure] using h
        simpa only [← he] using hn
      | yield state =>
        have htail : forIn rest state step = .ok final := by
          simpa [hs, Bind.bind, Except.bind, pure, Except.pure] using h
        exact ih state hn
          (fun item hm state next hp hnext =>
            hstep item (List.mem_cons_of_mem _ hm) state next hp hnext) htail

theorem decode_links {m : Model} {g : Family} (h : decode m = .ok g) :
    DecodedLinks m g := by
  have hp := decode_parentsRooted h
  unfold decode at h
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨final, hloop, hret⟩ := bind_ok h
  have hfinal : final = g := by
    simpa only [pure, Except.pure, Except.ok.injEq] using hret
  subst g
  refine forIn_preserves _ _ (DecodedLinks m) _ _ ?_ ?_ hloop
  · intro period hm
    cases hm
  · intro box _hbox state next hs hstep
    split at hstep
    · obtain ⟨caption, _hcaption, hstep⟩ := bind_ok hstep
      have he : ForInStep.yield
          ({ state with title := some { id := box.id, caption } } : Family) = next := by
        simpa only [pure, Except.pure, Except.ok.injEq] using hstep
      subst next
      exact hs
    · obtain ⟨caption, _hcaption, hstep⟩ := bind_ok hstep
      have he : ForInStep.yield
          ({ state with sections := state.sections ++ [{ id := box.id, caption }] } : Family) =
          next := by
        simpa only [pure, Except.pure, Except.ok.injEq] using hstep
      subst next
      exact hs
    · obtain ⟨sectionIndex, _hsection, hstep⟩ := bind_ok hstep
      split at hstep
      · change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
          .ok next at hstep
        cases hstep
      · obtain ⟨caption, _hcaption, hstep⟩ := bind_ok hstep
        have he : ForInStep.yield
            ({ state with periods := state.periods ++
              [{ id := box.id, caption, sectionIndex, events := [] }] } : Family) = next := by
          simpa only [pure, Except.pure, Except.ok.injEq] using hstep
        subst next
        intro period hm
        rcases List.mem_append.mp hm with hold | hnew
        · exact hs period hold
        · have he : period = { id := box.id, caption, sectionIndex, events := [] } := by
            simpa only [List.mem_singleton] using hnew
          subst period
          trivial
    · cases hprevious : state.periods.getLast? with
      | none =>
        simp only [hprevious] at hstep
        change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
          .ok next at hstep
        cases hstep
      | some previous =>
        simp only [hprevious] at hstep
        cases hroute : m.routes.find? (·.toId == box.id) with
        | none =>
          simp only [hroute] at hstep
          change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
            .ok next at hstep
          cases hstep
        | some route =>
          simp only [hroute] at hstep
          let expected := if m.options.direction == .LR then
            ((previous.events.getLast?).map (·.id)).getD previous.id else previous.id
          by_cases hbad : (route.fromId != expected) = true
          · dsimp only [expected] at hbad
            simp only [hbad, ↓reduceIte] at hstep
            change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
              .ok next at hstep
            cases hstep
          · have hfrom : route.fromId = expected := by
              by_cases heq : route.fromId = expected
              · exact heq
              · exact False.elim (hbad (by simp [heq]))
            dsimp only [expected] at hbad
            simp only [hbad] at hstep
            obtain ⟨caption, _hcaption, hstep⟩ := bind_ok hstep
            let event : Lanes.Timeline.Event := { id := box.id, caption, link := route.id }
            let updated := { previous with events := previous.events ++ [event] }
            have he : ForInStep.yield
                ({ state with periods := state.periods.set (state.periods.length - 1) updated } :
                  Family) = next := by
              simpa only [pure, Except.pure, Except.ok.injEq] using hstep
            subst next
            intro period hm
            rcases List.mem_or_eq_of_mem_set hm with hold | hnew
            · exact hs period hold
            · subst period
              have hpreviousMem := List.mem_of_getLast? hprevious
              have hpred := List.find?_some hroute
              have hto : route.toId = box.id := beq_iff_eq.mp hpred
              exact eventLinks_append (List.mem_of_find?_eq_some hroute) rfl hto
                previous.events previous.id (hs previous hpreviousMem) hfrom
    · change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
        .ok next at hstep
      cases hstep

theorem eventLinks_member {m : Model} {event : Lanes.Timeline.Event} :
    ∀ (events : List Lanes.Timeline.Event) (source : String),
      EventLinks m source events → event ∈ events →
      ∃ before after route, events = before ++ event :: after ∧ route ∈ m.routes ∧
        route.id = event.link ∧ route.toId = event.id ∧
        route.fromId = (if m.options.direction == .LR then
          ((before.getLast?).map (·.id)).getD source else source) := by
  intro events
  induction events with
  | nil => intro source _ hm; cases hm
  | cons first rest ih =>
    intro source hlinks hm
    rcases List.mem_cons.mp hm with he | hrest
    · subst first
      obtain ⟨route, hr, hid, hfrom, hto⟩ := hlinks.1
      refine ⟨[], rest, route, rfl, hr, hid, hto, ?_⟩
      simpa only [List.getLast?_nil, Option.map_none, Option.getD_none, ite_self] using hfrom
    · obtain ⟨before, after, route, hevents, hr, hid, hto, hfrom⟩ :=
        ih _ hlinks.2 hrest
      refine ⟨first :: before, after, route, ?_, hr, hid, hto, ?_⟩
      · simp only [List.cons_append, hevents]
      · cases before with
        | nil =>
          by_cases hdir : (m.options.direction == .LR) = true
          all_goals simpa only [hdir, Bool.false_eq_true, ↓reduceIte, List.getLast?_singleton, List.getLast?_nil,
            Option.map_some, Option.getD_some, Option.map_none, Option.getD_none] using hfrom
        | cons second tail =>
          by_cases hd : m.options.direction == .LR
          · cases hl : (second :: tail).getLast? with
            | none =>
              have hempty := List.getLast?_eq_none_iff.mp hl
              cases hempty
            | some last =>
              simpa only [hd, ↓reduceIte, List.getLast?_cons_cons, hl,
                Option.map_some, Option.getD_some] using hfrom
          · simpa only [hd, Bool.false_eq_true, ↓reduceIte] using hfrom

theorem scene_decoded_event_link {m : Model} {s : Scene} (h : scene m = .ok s)
    {out : Route} (hout : out ∈ s.routes) :
    ∃ g r period event before after route,
      decode m = .ok g ∧ Lanes.Timeline.layout g m.profile = .ok r ∧
      period ∈ g.periods ∧ event ∈ period.events ∧
      period.events = before ++ event :: after ∧
      route ∈ m.routes ∧ route.id = out.id ∧ route.toId = event.id ∧
      route.fromId = (if m.options.direction == .LR then
        ((before.getLast?).map (·.id)).getD period.id else period.id) := by
  obtain ⟨g, r, publicRoute, period, paths, event, hg, hr, _hpublic, hcorr, hp, he, hid⟩ :=
    scene_route_source h hout
  have hperiod : period ∈ g.periods := (List.of_mem_zip hp).1
  have hevent : event ∈ period.events := (List.of_mem_zip he).1
  obtain ⟨before, after, route, hsplit, hroute, hlink, hto, hfrom⟩ :=
    eventLinks_member period.events period.id (decode_links hg period hperiod) hevent
  refine ⟨g, r, period, event, before, after, route, hg, hr, hperiod, hevent,
    hsplit, hroute, ?_, hto, hfrom⟩
  exact hlink.trans (hid.trans hcorr.1.symm)

private theorem route_eq_of_id {routes : List ModelRoute}
    (hu : (routes.map (·.id)).Nodup) {a b : ModelRoute}
    (ha : a ∈ routes) (hb : b ∈ routes) (hid : a.id = b.id) : a = b := by
  induction routes with
  | nil => cases ha
  | cons first rest ih =>
    obtain ⟨hfresh, hrest⟩ := List.nodup_cons.mp hu
    rcases List.mem_cons.mp ha with he | ha
    · subst a
      rcases List.mem_cons.mp hb with he | hb
      · exact he.symm
      · exact False.elim (hfresh (List.mem_map.mpr ⟨b, hb, hid.symm⟩))
    · rcases List.mem_cons.mp hb with he | hb
      · subst b
        exact False.elim (hfresh (List.mem_map.mpr ⟨a, ha, hid⟩))
      · exact ih hrest ha hb

theorem scene_route_model_endpoints {m : Model} {s : Scene}
    (hwf : WellFormed m) (h : scene m = .ok s)
    {out : Route} (hout : out ∈ s.routes) :
    ∃ g r period paths event before after,
      decode m = .ok g ∧ Lanes.Timeline.layout g m.profile = .ok r ∧
      (period, paths) ∈ g.periods.zip r.geometry.routes ∧
      (event, out.points) ∈ period.events.zip paths ∧
      period.events = before ++ event :: after ∧ out.toId = event.id ∧
      out.fromId = (if m.options.direction == .LR then
        ((before.getLast?).map (·.id)).getD period.id else period.id) := by
  obtain ⟨g, r, publicRoute, period, paths, event, hg, hr, hpublic, hcorr, hp, he, hid⟩ :=
    scene_route_source h hout
  have hperiod : period ∈ g.periods := (List.of_mem_zip hp).1
  have hevent : event ∈ period.events := (List.of_mem_zip he).1
  obtain ⟨before, after, route, hsplit, hroute, hlink, hto, hfrom⟩ :=
    eventLinks_member period.events period.id (decode_links hg period hperiod) hevent
  have heq : route = publicRoute := route_eq_of_id (Model.routeIds_nodup hwf)
    hroute hpublic (hlink.trans hid)
  subst route
  exact ⟨g, r, period, paths, event, before, after, hg, hr, hp, he, hsplit,
    hcorr.2.2.1.trans hto, hcorr.2.1.trans hfrom⟩

theorem horizontal_routes_fold_geometry (x : Int) :
    ∀ (rects : List Rect) (initial : Rect) (acc : List (List Point)),
      (rects.foldl (fun (state : Rect × List (List Point)) box =>
        (box, state.2 ++ [[⟨x, state.1.y + state.1.h⟩, ⟨x, box.y⟩]])) (initial, acc)).2 =
      acc ++ (((initial :: rects).zip rects).map fun (source, target) =>
        [⟨x, source.y + source.h⟩, ⟨x, target.y⟩]) := by
  intro rects
  induction rects with
  | nil => intro initial acc; simp
  | cons first rest ih =>
    intro initial acc
    simp only [List.foldl_cons]
    rw [ih]
    simp only [List.zip_cons_cons, List.map_cons, List.append_assoc, List.singleton_append]

theorem bottom_midpoint_boundary (rect : Rect) (hw : 0 ≤ rect.w) (hh : 0 ≤ rect.h) :
    Validator.onBoundary ⟨rect.x + Lanes.half rect.w, rect.y + rect.h⟩ rect := by
  have hlo : 0 ≤ Lanes.half rect.w := Int.fdiv_nonneg hw (by decide)
  have hhi : Lanes.half rect.w ≤ rect.w := Int.fdiv_le_self 2 hw
  unfold Validator.onBoundary
  dsimp only
  omega

theorem top_midpoint_boundary (rect : Rect) (hw : 0 ≤ rect.w) (hh : 0 ≤ rect.h) :
    Validator.onBoundary ⟨rect.x + Lanes.half rect.w, rect.y⟩ rect := by
  have hlo : 0 ≤ Lanes.half rect.w := Int.fdiv_nonneg hw (by decide)
  have hhi : Lanes.half rect.w ≤ rect.w := Int.fdiv_le_self 2 hw
  unfold Validator.onBoundary
  dsimp only
  omega

theorem right_midpoint_boundary (rect : Rect) (hw : 0 ≤ rect.w) (hh : 0 ≤ rect.h) :
    Validator.onBoundary ⟨rect.x + rect.w, rect.y + Lanes.half rect.h⟩ rect := by
  have hlo : 0 ≤ Lanes.half rect.h := Int.fdiv_nonneg hh (by decide)
  have hhi : Lanes.half rect.h ≤ rect.h := Int.fdiv_le_self 2 hh
  unfold Validator.onBoundary
  dsimp only
  omega

theorem left_midpoint_boundary (rect : Rect) (hw : 0 ≤ rect.w) (hh : 0 ≤ rect.h) :
    Validator.onBoundary ⟨rect.x, rect.y + Lanes.half rect.h⟩ rect := by
  have hlo : 0 ≤ Lanes.half rect.h := Int.fdiv_nonneg hh (by decide)
  have hhi : Lanes.half rect.h ≤ rect.h := Int.fdiv_le_self 2 hh
  unfold Validator.onBoundary
  dsimp only
  omega

theorem horizontal_routes_fold_ports (x : Int) (rects : List Rect) (initial : Rect)
    (hmid : ∀ rect ∈ initial :: rects, rect.x + Lanes.half rect.w = x)
    (hsize : ∀ rect ∈ initial :: rects, 0 ≤ rect.w ∧ 0 ≤ rect.h) :
    ∀ points ∈ (rects.foldl (fun (state : Rect × List (List Point)) box =>
      (box, state.2 ++ [[⟨x, state.1.y + state.1.h⟩, ⟨x, box.y⟩]])) (initial, [])).2,
      ∃ source ∈ initial :: rects, ∃ target ∈ rects, ∃ first last,
        points.head? = some first ∧ points.getLast? = some last ∧
        Validator.onBoundary first source ∧ Validator.onBoundary last target := by
  rw [horizontal_routes_fold_geometry]
  simp only [List.nil_append]
  intro points hp
  obtain ⟨⟨source, target⟩, hpair, he⟩ := List.mem_map.mp hp
  subst points
  have hsource := (List.of_mem_zip hpair).1
  have htarget := (List.of_mem_zip hpair).2
  have htarget' := List.mem_cons_of_mem initial htarget
  refine ⟨source, hsource, target, htarget,
    ⟨x, source.y + source.h⟩, ⟨x, target.y⟩, rfl, rfl, ?_, ?_⟩
  · rw [← hmid source hsource]
    exact bottom_midpoint_boundary source (hsize source hsource).1 (hsize source hsource).2
  · rw [← hmid target htarget']
    exact top_midpoint_boundary target (hsize target htarget').1 (hsize target htarget').2

theorem elbow_ports (a b : Point) (x : Int) :
    (Lanes.Timeline.elbow a b x).head? = some a ∧
      (Lanes.Timeline.elbow a b x).getLast? = some b := by
  unfold Lanes.Timeline.elbow
  split <;> exact ⟨rfl, rfl⟩

theorem verticalRow_ports (g : Family) (c : Lanes.TimelineConsts) (i : Nat)
    (state : Lanes.Timeline.VerticalState)
    (hi : i < state.routes.length)
    (hw : 0 ≤ Lanes.Timeline.cardWidth g c)
    (hh : 0 ≤ Lanes.Timeline.periodHeight g c)
    (heights : ∀ event ∈ ((g.periods[i]?).map (·.events)).getD [],
      0 ≤ Lanes.Timeline.eventHeight c event) :
    ∀ paths, (Lanes.Timeline.verticalRow g c i state).routes[i]? = some paths →
      ∀ points ∈ paths,
      ∃ target, target ∈ Lanes.Timeline.eventRects c
          (c.leftMargin + Lanes.Timeline.cardWidth g c + c.columnGap)
          (Lanes.Timeline.cardWidth g c) state.y
          (((g.periods[i]?).map (·.events)).getD []) ∧
        ∃ first last, points.head? = some first ∧ points.getLast? = some last ∧
          Validator.onBoundary first
            ⟨c.leftMargin, state.y, Lanes.Timeline.cardWidth g c, Lanes.Timeline.periodHeight g c⟩ ∧
          Validator.onBoundary last target := by
  have hrects : ∀ (events : List Lanes.Timeline.Event) (top : Int),
      (∀ event ∈ events, 0 ≤ Lanes.Timeline.eventHeight c event) →
      ∀ rect ∈ Lanes.Timeline.eventRects c
        (c.leftMargin + Lanes.Timeline.cardWidth g c + c.columnGap)
        (Lanes.Timeline.cardWidth g c) top events,
        rect.w = Lanes.Timeline.cardWidth g c ∧ 0 ≤ rect.h := by
    intro events
    induction events with
    | nil => intro top _ rect hm; cases hm
    | cons event rest ih =>
      intro top hs rect hm
      rcases List.mem_cons.mp hm with he | hm
      · subst rect
        exact ⟨rfl, hs event (List.mem_cons_self ..)⟩
      · exact ih _ (fun e he => hs e (List.mem_cons_of_mem _ he)) rect hm
  intro paths hpaths points hp
  simp only [Lanes.Timeline.verticalRow, List.getElem?_set_self hi, Option.some.injEq] at hpaths
  subst paths
  obtain ⟨target, htarget, he⟩ := List.mem_map.mp hp
  subst points
  obtain ⟨hfirst, hlast⟩ := elbow_ports
    (⟨c.leftMargin + Lanes.Timeline.cardWidth g c,
      state.y + Lanes.half (Lanes.Timeline.periodHeight g c)⟩ : Point)
    ⟨target.x, target.y + Lanes.half target.h⟩
    (c.leftMargin + Lanes.Timeline.cardWidth g c + Lanes.half c.columnGap)
  refine ⟨target, htarget, _, _, hfirst, hlast, ?_, ?_⟩
  · exact right_midpoint_boundary _ hw hh
  · obtain ⟨hwidth, hheight⟩ := hrects _ state.y heights target htarget
    exact left_midpoint_boundary target (hwidth.symm ▸ hw) hheight

theorem verticalRow_box_lookup (g : Family) (c : Lanes.TimelineConsts) (i : Nat)
    (state : Lanes.Timeline.VerticalState)
    (hp : i < state.periods.length) (he : i < state.events.length) :
    (Lanes.Timeline.verticalRow g c i state).periods[i]? =
        some ⟨c.leftMargin, state.y, Lanes.Timeline.cardWidth g c,
          Lanes.Timeline.periodHeight g c⟩ ∧
      (Lanes.Timeline.verticalRow g c i state).events[i]? =
        some (Lanes.Timeline.eventRects c
          (c.leftMargin + Lanes.Timeline.cardWidth g c + c.columnGap)
          (Lanes.Timeline.cardWidth g c) state.y
          (((g.periods[i]?).map (·.events)).getD [])) := by
  simp only [Lanes.Timeline.verticalRow, List.getElem?_set_self hp,
    List.getElem?_set_self he, and_self]

theorem eventRects_horizontal (c : Lanes.TimelineConsts) (x w : Int) :
    ∀ (events : List Lanes.Timeline.Event) (top : Int),
      ∀ rect ∈ Lanes.Timeline.eventRects c x w top events,
        rect.x = x ∧ rect.w = w := by
  intro events
  induction events with
  | nil => intro top rect hm; cases hm
  | cons event rest ih =>
    intro top rect hm
    rcases List.mem_cons.mp hm with he | hm
    · subst rect
      exact ⟨rfl, rfl⟩
    · exact ih _ rect hm

theorem verticalRow_period_event_separation
    (g : Family) (c : Lanes.TimelineConsts) (i : Nat)
    (state : Lanes.Timeline.VerticalState)
    (hp : i < state.periods.length) (he : i < state.events.length)
    (hgap : 0 ≤ c.columnGap)
    {period : Rect} {events : List Rect}
    (hperiod : (Lanes.Timeline.verticalRow g c i state).periods[i]? = some period)
    (hevents : (Lanes.Timeline.verticalRow g c i state).events[i]? = some events) :
    ∀ event ∈ events, period.x + period.w ≤ event.x := by
  obtain ⟨hpLookup, heLookup⟩ := verticalRow_box_lookup g c i state hp he
  have hpEq := Option.some.inj (hpLookup.symm.trans hperiod)
  have heEq := Option.some.inj (heLookup.symm.trans hevents)
  subst period
  subst events
  intro event hm
  have hx := (eventRects_horizontal c _ _ _ state.y event hm).1
  dsimp only
  omega

theorem verticalRow_lookup_ports (g : Family) (c : Lanes.TimelineConsts) (i : Nat)
    (state : Lanes.Timeline.VerticalState)
    (hp : i < state.periods.length) (he : i < state.events.length)
    (hr : i < state.routes.length)
    (hw : 0 ≤ Lanes.Timeline.cardWidth g c)
    (hh : 0 ≤ Lanes.Timeline.periodHeight g c)
    (heights : ∀ event ∈ ((g.periods[i]?).map (·.events)).getD [],
      0 ≤ Lanes.Timeline.eventHeight c event)
    {period : Rect} {events : List Rect} {paths : List (List Point)}
    (hperiod : (Lanes.Timeline.verticalRow g c i state).periods[i]? = some period)
    (hevents : (Lanes.Timeline.verticalRow g c i state).events[i]? = some events)
    (hpaths : (Lanes.Timeline.verticalRow g c i state).routes[i]? = some paths) :
    ∀ points ∈ paths, ∃ target ∈ events,
      ∃ first last, points.head? = some first ∧ points.getLast? = some last ∧
        Validator.onBoundary first period ∧ Validator.onBoundary last target := by
  obtain ⟨hpLookup, heLookup⟩ := verticalRow_box_lookup g c i state hp he
  have hpEq := Option.some.inj (hpLookup.symm.trans hperiod)
  have heEq := Option.some.inj (heLookup.symm.trans hevents)
  subst period
  subst events
  exact verticalRow_ports g c i state hr hw hh heights paths hpaths

theorem elbow_horizontal_corridor (a b : Point) (x : Int)
    (hleft : a.x ≤ x) (hright : x ≤ b.x) :
    ∀ point ∈ Lanes.Timeline.elbow a b x, a.x ≤ point.x ∧ point.x ≤ b.x := by
  intro point hm
  unfold Lanes.Timeline.elbow at hm
  split at hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> (try dsimp only) <;> omega

theorem verticalRow_route_corridor (g : Family) (c : Lanes.TimelineConsts) (i : Nat)
    (state : Lanes.Timeline.VerticalState)
    (hr : i < state.routes.length) (hgap : 0 ≤ c.columnGap)
    {paths : List (List Point)}
    (hpaths : (Lanes.Timeline.verticalRow g c i state).routes[i]? = some paths) :
    ∀ points ∈ paths, ∀ point ∈ points,
      c.leftMargin + Lanes.Timeline.cardWidth g c ≤ point.x ∧
        point.x ≤ c.leftMargin + Lanes.Timeline.cardWidth g c + c.columnGap := by
  simp only [Lanes.Timeline.verticalRow, List.getElem?_set_self hr,
    Option.some.injEq] at hpaths
  subst paths
  intro points hp point hm
  obtain ⟨target, ht, heq⟩ := List.mem_map.mp hp
  subst points
  have hx := (eventRects_horizontal c _ _ _ state.y target ht).1
  have hhalf : 0 ≤ Lanes.half c.columnGap ∧ Lanes.half c.columnGap ≤ c.columnGap := by
    unfold Lanes.half
    rw [Int.fdiv_eq_ediv_of_nonneg c.columnGap (by decide : (0 : Int) ≤ 2)]
    omega
  have bounds := elbow_horizontal_corridor
    (⟨c.leftMargin + Lanes.Timeline.cardWidth g c,
      state.y + Lanes.half (Lanes.Timeline.periodHeight g c)⟩ : Point)
    ⟨target.x, target.y + Lanes.half target.h⟩
    (c.leftMargin + Lanes.Timeline.cardWidth g c + Lanes.half c.columnGap)
    (by dsimp; omega) (by dsimp; omega) point hm
  simpa only [hx] using bounds

theorem measureCaption_height_positive {fontFamily : Bool} {profile : Profile} {role : TextRole}
    {target : Int} {text : String} {caption : Lanes.Caption}
    (h : measureCaption profile role target text fontFamily = .ok caption) : 0 < caption.h := by
  have positive (lines : List Measure.Line) (lh : Int) (hlh : 0 < lh) :
      0 < ((max 1 lines.length : Nat) : Int) * lh := by
    have hcount : 0 < ((max 1 lines.length : Nat) : Int) := by omega
    exact Int.mul_pos hcount hlh
  unfold measureCaption at h
  dsimp only at h
  cases profile with
  | cell =>
    cases hw : StyledMeasure.wrap Measure.Metric.cell target text.toList with
    | error e =>
      simp only [hw, Bind.bind, Except.bind, Pure.pure, Except.pure,
        throw, throwThe, MonadExceptOf.throw] at h
      cases h
    | ok lines =>
      simp only [hw, Bind.bind, Except.bind, Pure.pure, Except.pure,
        Except.ok.injEq] at h
      subst caption
      exact positive lines 1 (by decide)
  | vector =>
    let mr := match role with
      | .title => Measure.Role.title
      | .body => Measure.Role.body
      | _ => Measure.Role.label
    cases hm : mr.metric fontFamily with
    | error e =>
      simp only [mr] at hm
      simp only [hm, Bind.bind, Except.bind] at h
      cases h
    | ok metric =>
      simp only [mr] at hm
      simp only [hm, Bind.bind, Except.bind] at h
      cases hw : StyledMeasure.wrap metric target text.toList with
      | error e =>
        simp only [hw, throw, throwThe, MonadExceptOf.throw] at h
        cases h
      | ok lines =>
        simp only [hw, Pure.pure, Except.pure, Except.ok.injEq] at h
        subst caption
        apply positive
        cases role <;> decide

theorem verticalRow_lookup_corridor (g : Family) (c : Lanes.TimelineConsts) (i : Nat)
    (state : Lanes.Timeline.VerticalState)
    (hp : i < state.periods.length) (he : i < state.events.length)
    (hr : i < state.routes.length) (hgap : 0 ≤ c.columnGap)
    {period : Rect} {events : List Rect} {paths : List (List Point)}
    (hperiod : (Lanes.Timeline.verticalRow g c i state).periods[i]? = some period)
    (hevents : (Lanes.Timeline.verticalRow g c i state).events[i]? = some events)
    (hpaths : (Lanes.Timeline.verticalRow g c i state).routes[i]? = some paths) :
    ∀ points ∈ paths, ∀ point ∈ points, ∀ event ∈ events,
      period.x + period.w ≤ point.x ∧ point.x ≤ event.x := by
  obtain ⟨hpLookup, heLookup⟩ := verticalRow_box_lookup g c i state hp he
  have hpEq := Option.some.inj (hpLookup.symm.trans hperiod)
  have heEq := Option.some.inj (heLookup.symm.trans hevents)
  subst period
  subst events
  intro points hpoints point hpoint event hevent
  have bounds := verticalRow_route_corridor g c i state hr hgap hpaths
    points hpoints point hpoint
  have hx := (eventRects_horizontal c _ _ _ state.y event hevent).1
  constructor
  · exact bounds.1
  · rw [hx]
    exact bounds.2

theorem verticalRow_lengths (g : Family) (c : Lanes.TimelineConsts) (i : Nat)
    (state : Lanes.Timeline.VerticalState) :
    (Lanes.Timeline.verticalRow g c i state).periods.length = state.periods.length ∧
      (Lanes.Timeline.verticalRow g c i state).events.length = state.events.length ∧
      (Lanes.Timeline.verticalRow g c i state).routes.length = state.routes.length := by
  simp only [Lanes.Timeline.verticalRow, List.length_set, and_self]

theorem verticalRows_lengths (g : Family) (c : Lanes.TimelineConsts)
    (indices : List Nat) (state : Lanes.Timeline.VerticalState) :
    (indices.foldl (fun st i => Lanes.Timeline.verticalRow g c i st) state).periods.length =
        state.periods.length ∧
      (indices.foldl (fun st i => Lanes.Timeline.verticalRow g c i st) state).events.length =
        state.events.length ∧
      (indices.foldl (fun st i => Lanes.Timeline.verticalRow g c i st) state).routes.length =
        state.routes.length := by
  induction indices generalizing state with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons i indices ih =>
    obtain ⟨hp, he, hr⟩ := ih (Lanes.Timeline.verticalRow g c i state)
    obtain ⟨hpStep, heStep, hrStep⟩ := verticalRow_lengths g c i state
    exact ⟨hp.trans hpStep, he.trans heStep, hr.trans hrStep⟩

theorem verticalRows_lookup_ports (g : Family) (c : Lanes.TimelineConsts)
    (indices : List Nat) (state : Lanes.Timeline.VerticalState)
    (hw : 0 ≤ Lanes.Timeline.cardWidth g c)
    (hh : 0 ≤ Lanes.Timeline.periodHeight g c)
    (heights : ∀ (i : Nat), ∀ event ∈ ((g.periods[i]?).map (fun p => p.events)).getD [],
      0 ≤ Lanes.Timeline.eventHeight c event)
    (bounds : ∀ i ∈ indices, i < state.periods.length ∧
      i < state.events.length ∧ i < state.routes.length)
    (initial : ∀ (i : Nat) (period : Rect) (events : List Rect) (paths : List (List Point)),
      state.periods[i]? = some period → state.events[i]? = some events →
      state.routes[i]? = some paths →
      ∀ (points : List Point), points ∈ paths → ∃ target ∈ events,
        ∃ first last, points.head? = some first ∧ points.getLast? = some last ∧
          Validator.onBoundary first period ∧ Validator.onBoundary last target) :
    let final := indices.foldl (fun st i => Lanes.Timeline.verticalRow g c i st) state
    ∀ (i : Nat) (period : Rect) (events : List Rect) (paths : List (List Point)),
      final.periods[i]? = some period → final.events[i]? = some events →
      final.routes[i]? = some paths →
      ∀ (points : List Point), points ∈ paths → ∃ target ∈ events,
        ∃ first last, points.head? = some first ∧ points.getLast? = some last ∧
          Validator.onBoundary first period ∧ Validator.onBoundary last target := by
  induction indices generalizing state with
  | nil => exact initial
  | cons index rest ih =>
    obtain ⟨hp, he, hr⟩ := bounds index (List.mem_cons_self ..)
    apply ih (Lanes.Timeline.verticalRow g c index state)
    · intro i hi
      obtain ⟨hip, hie, hir⟩ := bounds i (List.mem_cons_of_mem _ hi)
      obtain ⟨hlp, hle, hlr⟩ := verticalRow_lengths g c index state
      exact ⟨hlp.symm ▸ hip, hle.symm ▸ hie, hlr.symm ▸ hir⟩
    · intro i period events paths hperiod hevents hpaths
      by_cases same : i = index
      · subst i
        exact verticalRow_lookup_ports g c index state hp he hr hw hh
          (heights index) hperiod hevents hpaths
      · simp only [Lanes.Timeline.verticalRow, List.getElem?_set_ne (Ne.symm same)] at hperiod hevents hpaths
        exact initial i period events paths hperiod hevents hpaths

theorem verticalRows_lookup_corridor (g : Family) (c : Lanes.TimelineConsts)
    (indices : List Nat) (state : Lanes.Timeline.VerticalState)
    (hgap : 0 ≤ c.columnGap)
    (bounds : ∀ i ∈ indices, i < state.periods.length ∧
      i < state.events.length ∧ i < state.routes.length)
    (initial : ∀ (i : Nat) (period : Rect) (events : List Rect) (paths : List (List Point)),
      state.periods[i]? = some period → state.events[i]? = some events →
      state.routes[i]? = some paths →
      ∀ (points : List Point), points ∈ paths → ∀ (point : Point), point ∈ points → ∀ (event : Rect), event ∈ events →
        period.x + period.w ≤ point.x ∧ point.x ≤ event.x) :
    let final := indices.foldl (fun st i => Lanes.Timeline.verticalRow g c i st) state
    ∀ (i : Nat) (period : Rect) (events : List Rect) (paths : List (List Point)),
      final.periods[i]? = some period → final.events[i]? = some events →
      final.routes[i]? = some paths →
      ∀ (points : List Point), points ∈ paths → ∀ (point : Point), point ∈ points → ∀ (event : Rect), event ∈ events →
        period.x + period.w ≤ point.x ∧ point.x ≤ event.x := by
  induction indices generalizing state with
  | nil => exact initial
  | cons index rest ih =>
    obtain ⟨hp, he, hr⟩ := bounds index (List.mem_cons_self ..)
    apply ih (Lanes.Timeline.verticalRow g c index state)
    · intro i hi
      obtain ⟨hip, hie, hir⟩ := bounds i (List.mem_cons_of_mem _ hi)
      obtain ⟨hlp, hle, hlr⟩ := verticalRow_lengths g c index state
      exact ⟨hlp.symm ▸ hip, hle.symm ▸ hie, hlr.symm ▸ hir⟩
    · intro i period events paths hperiod hevents hpaths
      by_cases same : i = index
      · subst i
        exact verticalRow_lookup_corridor g c index state hp he hr hgap
          hperiod hevents hpaths
      · simp only [Lanes.Timeline.verticalRow, List.getElem?_set_ne (Ne.symm same)] at hperiod hevents hpaths
        exact initial i period events paths hperiod hevents hpaths

theorem verticalRows_period_event_separation
    (g : Family) (c : Lanes.TimelineConsts)
    (indices : List Nat) (state : Lanes.Timeline.VerticalState)
    (hgap : 0 ≤ c.columnGap)
    (bounds : ∀ i ∈ indices, i < state.periods.length ∧ i < state.events.length)
    (initial : ∀ (i : Nat) (period : Rect) (events : List Rect),
      state.periods[i]? = some period → state.events[i]? = some events →
      ∀ (event : Rect), event ∈ events → period.x + period.w ≤ event.x) :
    let final := indices.foldl (fun st i => Lanes.Timeline.verticalRow g c i st) state
    ∀ (i : Nat) (period : Rect) (events : List Rect),
      final.periods[i]? = some period → final.events[i]? = some events →
      ∀ (event : Rect), event ∈ events → period.x + period.w ≤ event.x := by
  induction indices generalizing state with
  | nil => exact initial
  | cons index rest ih =>
    obtain ⟨hp, he⟩ := bounds index (List.mem_cons_self ..)
    apply ih (Lanes.Timeline.verticalRow g c index state)
    · intro i hi
      obtain ⟨hip, hie⟩ := bounds i (List.mem_cons_of_mem _ hi)
      obtain ⟨hlp, hle, _hlr⟩ := verticalRow_lengths g c index state
      exact ⟨hlp.symm ▸ hip, hle.symm ▸ hie⟩
    · intro i period events hperiod hevents
      by_cases same : i = index
      · subst i
        exact verticalRow_period_event_separation g c index state hp he hgap
          hperiod hevents
      · simp only [Lanes.Timeline.verticalRow, List.getElem?_set_ne (Ne.symm same)] at hperiod hevents
        exact initial i period events hperiod hevents

theorem verticalPlan_arrays_invariant (g : Family) (c : Lanes.TimelineConsts)
    (P : List Rect → List (List Rect) → List (List (List Point)) → Prop)
    (initial : P (List.replicate g.periods.length Lanes.zeroRect)
      (List.replicate g.periods.length []) (List.replicate g.periods.length []))
    (rows : ∀ (indices : List Nat) (state : Lanes.Timeline.VerticalState),
      state.periods.length = g.periods.length →
      state.events.length = g.periods.length →
      state.routes.length = g.periods.length →
      (∀ i ∈ indices, i < g.periods.length) →
      P state.periods state.events state.routes →
      let final := indices.foldl (fun st i => Lanes.Timeline.verticalRow g c i st) state
      P final.periods final.events final.routes) :
    P (Lanes.Timeline.verticalPlan g c).periods
      (Lanes.Timeline.verticalPlan g c).events
      (Lanes.Timeline.verticalPlan g c).routes := by
  have members_bound (s : Int) (i : Nat) (hi : i ∈ Lanes.Timeline.members g s) :
      i < g.periods.length := by
    obtain ⟨⟨p, j⟩, hj, he⟩ := List.mem_filterMap.mp hi
    have hji : j = i := by
      split at he <;> simp_all
    subst j
    exact (List.mem_zipIdx' hj).1
  let Good := fun st : Lanes.Timeline.VerticalState =>
    st.periods.length = g.periods.length ∧
    st.events.length = g.periods.length ∧
    st.routes.length = g.periods.length ∧ P st.periods st.events st.routes
  have run (s : Int) (st : Lanes.Timeline.VerticalState) (hs : Good st) :
      Good ((Lanes.Timeline.members g s).foldl
        (fun st i => Lanes.Timeline.verticalRow g c i st) st) := by
    obtain ⟨hp, he, hr⟩ := verticalRows_lengths g c (Lanes.Timeline.members g s) st
    exact ⟨hp.trans hs.1, he.trans hs.2.1, hr.trans hs.2.2.1,
      rows _ st hs.1 hs.2.1 hs.2.2.1 (members_bound s) hs.2.2.2⟩
  let start : Lanes.Timeline.VerticalState :=
    { y := Lanes.Timeline.contentTop g c
      sections := List.replicate g.sections.length Lanes.zeroRect
      periods := List.replicate g.periods.length Lanes.zeroRect
      events := List.replicate g.periods.length []
      routes := List.replicate g.periods.length [] }
  have hstart : Good start := by
    exact ⟨List.length_replicate, List.length_replicate, List.length_replicate, initial⟩
  let step := fun (st : Lanes.Timeline.VerticalState) (s : Nat) =>
    let rect : Rect := ⟨c.leftMargin, st.y, Lanes.Timeline.cardWidth g c,
      Lanes.Timeline.sectionHeight g c⟩
    let next := { st with
      y := st.y + Lanes.Timeline.sectionHeight g c + c.sectionGap
      sections := st.sections.set s rect }
    (Lanes.Timeline.members g (s : Int)).foldl
      (fun st i => Lanes.Timeline.verticalRow g c i st) next
  have hstep (st : Lanes.Timeline.VerticalState) (s : Nat) (hs : Good st) :
      Good (step st s) := by
    exact run (s : Int) _ hs
  have final := foldl_preserves step Good hstep (List.range g.sections.length) _
    (run (-1) start hstart)
  exact final.2.2.2

theorem verticalPlan_lookup_ports (g : Family) (c : Lanes.TimelineConsts)
    (hw : 0 ≤ Lanes.Timeline.cardWidth g c)
    (hh : 0 ≤ Lanes.Timeline.periodHeight g c)
    (heights : ∀ (i : Nat), ∀ event ∈
      ((g.periods[i]?).map (fun p => p.events)).getD [],
      0 ≤ Lanes.Timeline.eventHeight c event) :
    ∀ (i : Nat) (period : Rect) (events : List Rect) (paths : List (List Point)),
      (Lanes.Timeline.verticalPlan g c).periods[i]? = some period →
      (Lanes.Timeline.verticalPlan g c).events[i]? = some events →
      (Lanes.Timeline.verticalPlan g c).routes[i]? = some paths →
      ∀ (points : List Point), points ∈ paths → ∃ target ∈ events,
        ∃ first last, points.head? = some first ∧ points.getLast? = some last ∧
          Validator.onBoundary first period ∧ Validator.onBoundary last target := by
  apply verticalPlan_arrays_invariant g c
    (fun periods events routes =>
      ∀ (i : Nat) (period : Rect) (es : List Rect) (paths : List (List Point)),
        periods[i]? = some period → events[i]? = some es → routes[i]? = some paths →
        ∀ points ∈ paths, ∃ target ∈ es,
          ∃ first last, points.head? = some first ∧ points.getLast? = some last ∧
            Validator.onBoundary first period ∧ Validator.onBoundary last target)
  · intro i period events paths _hp _he hr points hm
    have empty : paths = [] := (List.mem_replicate.mp (List.mem_of_getElem? hr)).2
    subst paths
    cases hm
  · intro indices state hp he hr bounds hi
    apply verticalRows_lookup_ports g c indices state hw hh heights
    · intro i hm
      have hb := bounds i hm
      exact ⟨hp.symm ▸ hb, he.symm ▸ hb, hr.symm ▸ hb⟩
    · exact hi

theorem verticalPlan_lookup_corridor (g : Family) (c : Lanes.TimelineConsts)
    (hgap : 0 ≤ c.columnGap) :
    ∀ (i : Nat) (period : Rect) (events : List Rect) (paths : List (List Point)),
      (Lanes.Timeline.verticalPlan g c).periods[i]? = some period →
      (Lanes.Timeline.verticalPlan g c).events[i]? = some events →
      (Lanes.Timeline.verticalPlan g c).routes[i]? = some paths →
      ∀ points ∈ paths, ∀ point ∈ points, ∀ event ∈ events,
        period.x + period.w ≤ point.x ∧ point.x ≤ event.x := by
  apply verticalPlan_arrays_invariant g c
    (fun periods events routes =>
      ∀ (i : Nat) (period : Rect) (es : List Rect) (paths : List (List Point)),
        periods[i]? = some period → events[i]? = some es → routes[i]? = some paths →
        ∀ points ∈ paths, ∀ point ∈ points, ∀ event ∈ es,
          period.x + period.w ≤ point.x ∧ point.x ≤ event.x)
  · intro i period events paths _hp _he hr points hm
    have empty : paths = [] := (List.mem_replicate.mp (List.mem_of_getElem? hr)).2
    subst paths
    cases hm
  · intro indices state hp he hr bounds hi
    apply verticalRows_lookup_corridor g c indices state hgap
    · intro i hm
      have hb := bounds i hm
      exact ⟨hp.symm ▸ hb, he.symm ▸ hb, hr.symm ▸ hb⟩
    · exact hi

theorem verticalPlan_period_event_separation (g : Family) (c : Lanes.TimelineConsts)
    (hgap : 0 ≤ c.columnGap) :
    ∀ (i : Nat) (period : Rect) (events : List Rect),
      (Lanes.Timeline.verticalPlan g c).periods[i]? = some period →
      (Lanes.Timeline.verticalPlan g c).events[i]? = some events →
      ∀ event ∈ events, period.x + period.w ≤ event.x := by
  apply verticalPlan_arrays_invariant g c
    (fun periods events _routes =>
      ∀ (i : Nat) (period : Rect) (es : List Rect),
        periods[i]? = some period → events[i]? = some es →
        ∀ event ∈ es, period.x + period.w ≤ event.x)
  · intro i period events _hp he event hm
    have empty : events = [] := (List.mem_replicate.mp (List.mem_of_getElem? he)).2
    subst events
    cases hm
  · intro indices state hp he _hr bounds hi
    apply verticalRows_period_event_separation g c indices state hgap
    · intro i hm
      have hb := bounds i hm
      exact ⟨hp.symm ▸ hb, he.symm ▸ hb⟩
    · exact hi

theorem boundary_shift (dx dy : Int) (point : Point) (rect : Rect)
    (h : Validator.onBoundary point rect) :
    Validator.onBoundary (Lanes.shiftPoint dx dy point) (Lanes.shiftRect dx dy rect) := by
  unfold Validator.onBoundary Lanes.shiftPoint Lanes.shiftRect at *
  dsimp only at *
  omega

theorem route_ports_shift (dx dy : Int) (points : List Point)
    (source target : Rect) (first last : Point)
    (hfirst : points.head? = some first) (hlast : points.getLast? = some last)
    (hsource : Validator.onBoundary first source)
    (htarget : Validator.onBoundary last target) :
    ∃ shiftedFirst shiftedLast,
      (points.map (Lanes.shiftPoint dx dy)).head? = some shiftedFirst ∧
      (points.map (Lanes.shiftPoint dx dy)).getLast? = some shiftedLast ∧
      Validator.onBoundary shiftedFirst (Lanes.shiftRect dx dy source) ∧
      Validator.onBoundary shiftedLast (Lanes.shiftRect dx dy target) := by
  refine ⟨Lanes.shiftPoint dx dy first, Lanes.shiftPoint dx dy last, ?_, ?_,
    boundary_shift dx dy first source hsource, boundary_shift dx dy last target htarget⟩
  · cases points with
    | nil => cases hfirst
    | cons point rest =>
      have he : point = first := Option.some.inj hfirst
      subst point
      rfl
  · simp only [List.getLast?_map, hlast, Option.map_some]

theorem verticalPlan_shifted_ports (g : Family) (c : Lanes.TimelineConsts)
    (dx dy : Int) (hw : 0 ≤ Lanes.Timeline.cardWidth g c)
    (hh : 0 ≤ Lanes.Timeline.periodHeight g c)
    (heights : ∀ (i : Nat), ∀ event ∈
      ((g.periods[i]?).map (fun p => p.events)).getD [],
      0 ≤ Lanes.Timeline.eventHeight c event)
    (i : Nat) (period : Rect) (events : List Rect) (paths : List (List Point))
    (hp : (Lanes.Timeline.verticalPlan g c).periods[i]? = some period)
    (he : (Lanes.Timeline.verticalPlan g c).events[i]? = some events)
    (hr : (Lanes.Timeline.verticalPlan g c).routes[i]? = some paths) :
    ∀ points ∈ paths, ∃ target ∈ events, ∃ first last,
      (points.map (Lanes.shiftPoint dx dy)).head? = some first ∧
      (points.map (Lanes.shiftPoint dx dy)).getLast? = some last ∧
      Validator.onBoundary first (Lanes.shiftRect dx dy period) ∧
      Validator.onBoundary last (Lanes.shiftRect dx dy target) := by
  intro points hm
  obtain ⟨target, ht, first, last, hf, hl, hs, hb⟩ :=
    verticalPlan_lookup_ports g c hw hh heights i period events paths hp he hr points hm
  exact ⟨target, ht, route_ports_shift dx dy points period target first last hf hl hs hb⟩

theorem verticalPlan_shifted_period_event_separation
    (g : Family) (c : Lanes.TimelineConsts) (dx dy : Int)
    (hgap : 0 ≤ c.columnGap) (i : Nat) (period : Rect) (events : List Rect)
    (hp : (Lanes.Timeline.verticalPlan g c).periods[i]? = some period)
    (he : (Lanes.Timeline.verticalPlan g c).events[i]? = some events)
    (event : Rect) (hm : event ∈ events) :
    (Lanes.shiftRect dx dy period).x + (Lanes.shiftRect dx dy period).w ≤
      (Lanes.shiftRect dx dy event).x := by
  have h := verticalPlan_period_event_separation g c hgap i period events hp he event hm
  dsimp only [Lanes.shiftRect]
  omega

theorem scene_rectFor_lookup {m : Model} {s : Scene} {g : Family}
    {r : Lanes.Timeline.Result} (hwf : WellFormed m)
    (hs : scene m = .ok s) (hg : decode m = .ok g)
    (hr : Lanes.Timeline.layout g m.profile = .ok r)
    {box : ModelBox} (hb : box ∈ m.boxes) {rect : Rect}
    (hrect : rectFor g r.geometry box.id = some rect) :
    ∃ out, s.layoutDump.box? box.id = some out ∧ out.rect = rect := by
  obtain ⟨g', r', out, hg', hr', hlookup, hcorr, _hsource⟩ :=
    scene_box_lookup hwf hs hb
  have hge : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have hre : r' = r := Except.ok.inj (hr'.symm.trans hr)
  subst r'
  have he : out.rect = rect :=
    Option.some.inj (hcorr.2.2.2.2.symm.trans hrect)
  exact ⟨out, hlookup, he⟩

theorem layout_rectFor_lookup {m : Model} {result : Layered.FamilyResult}
    {g : Family} {r : Lanes.Timeline.Result} (hwf : WellFormed m)
    (h : layout m = .ok result) (hg : decode m = .ok g)
    (hr : Lanes.Timeline.layout g m.profile = .ok r)
    {box : ModelBox} (hb : box ∈ m.boxes) {rect : Rect}
    (hrect : rectFor g r.geometry box.id = some rect) :
    ∃ out, result.scene.layoutDump.box? box.id = some out ∧ out.rect = rect := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact scene_rectFor_lookup hwf hs hg hr hb hrect

theorem horizontalPlan_shifted_periods_separated
    {g : Family} {profile : Profile} {i j : Nat}
    {p q : Lanes.Timeline.Period} {a b : Rect}
    (dx dy : Int)
    (hi : g.periods[i]? = some p) (hj : g.periods[j]? = some q)
    (ha : (Lanes.Timeline.horizontalPlan g
      (Lanes.TimelineConsts.load profile)).periods[i]? = some a)
    (hb : (Lanes.Timeline.horizontalPlan g
      (Lanes.TimelineConsts.load profile)).periods[j]? = some b)
    (hslots : Lanes.Timeline.slot g i p < Lanes.Timeline.slot g j q) :
    (Lanes.shiftRect dx dy a).x < (Lanes.shiftRect dx dy b).x ∧
    (Lanes.shiftRect dx dy a).x + (Lanes.shiftRect dx dy a).w ≤
      (Lanes.shiftRect dx dy b).x ∧
    Disjoint (Lanes.shiftRect dx dy a) (Lanes.shiftRect dx dy b) := by
  obtain ⟨hleft, hright, _hdisjoint⟩ :=
    Lanes.Timeline.horizontal_periods_separated hi hj ha hb hslots
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [Lanes.shiftRect]
    omega
  · dsimp only [Lanes.shiftRect]
    omega
  · unfold Disjoint Rect.meetsInterior
    dsimp only [Lanes.shiftRect]
    omega

theorem horizontalPlan_events_stack_disjoint
    (g : Family) (c : Lanes.TimelineConsts)
    (hgap : 0 ≤ c.eventGap)
    (heights : ∀ period ∈ g.periods, ∀ event ∈ period.events,
      0 ≤ Lanes.Timeline.eventHeight c event)
    {events : List Rect} (hm : events ∈ (Lanes.Timeline.horizontalPlan g c).events) :
    events.Pairwise (fun a b => a.y + a.h ≤ b.y ∧ Disjoint a b) := by
  change events ∈ ((g.periods.zip
    (Lanes.Timeline.horizontalPlan g c).periods).map fun (period, rect) =>
      Lanes.Timeline.eventRects c rect.x (Lanes.Timeline.cardWidth g c)
        (Lanes.Timeline.contentTop g c +
          (if g.sections.isEmpty then 0 else Lanes.Timeline.sectionHeight g c + c.sectionGap) +
          Lanes.Timeline.periodHeight g c + c.sectionGap) period.events) at hm
  obtain ⟨⟨period, rect⟩, hpair, heq⟩ := List.mem_map.mp hm
  subst events
  exact Lanes.Timeline.timeline_events_stack_disjoint c _ _ _ period.events hgap
    (heights period (List.of_mem_zip hpair).1)

theorem horizontalPlan_section_y (g : Family) (c : Lanes.TimelineConsts)
    {band : Rect} (hm : band ∈ (Lanes.Timeline.horizontalPlan g c).sections) :
    band.y = Lanes.Timeline.contentTop g c := by
  unfold Lanes.Timeline.horizontalPlan at hm
  dsimp only at hm
  obtain ⟨⟨_card, _index⟩, _hmem, heq⟩ := List.mem_map.mp hm
  exact congrArg Rect.y heq.symm

theorem horizontalPlan_title_section_separation
    (g : Family) (c : Lanes.TimelineConsts) (hgap : 0 ≤ c.eventGap)
    {title : Lanes.Timeline.Card} (ht : g.title = some title)
    {band : Rect} (hm : band ∈ (Lanes.Timeline.horizontalPlan g c).sections) :
    (Lanes.Timeline.horizontalPlan g c).title.y +
      (Lanes.Timeline.horizontalPlan g c).title.h ≤ band.y := by
  have hy := horizontalPlan_section_y g c hm
  have hbottom : (Lanes.Timeline.horizontalPlan g c).title.y +
      (Lanes.Timeline.horizontalPlan g c).title.h = title.caption.h := by
    simp [Lanes.Timeline.horizontalPlan, ht]
  have htop : Lanes.Timeline.contentTop g c = title.caption.h + c.eventGap := by
    simp [Lanes.Timeline.contentTop, ht]
  omega

def ModelId (m : Model) (id : String) : Prop :=
  ∃ box ∈ m.boxes, box.id = id

def DecodedIds (m : Model) (g : Family) : Prop :=
  (∀ card, g.title = some card → ModelId m card.id) ∧
  (∀ card ∈ g.sections, ModelId m card.id) ∧
  (∀ period ∈ g.periods, ModelId m period.id ∧
    ∀ event ∈ period.events, ModelId m event.id)

theorem decode_ids {m : Model} {g : Family} (h : decode m = .ok g) :
    DecodedIds m g := by
  have hp := decode_parentsRooted h
  unfold decode at h
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨final, hloop, hret⟩ := bind_ok h
  have hfinal : final = g := by
    simpa only [pure, Except.pure, Except.ok.injEq] using hret
  subst g
  refine forIn_preserves _ _ (DecodedIds m) _ _ ?_ ?_ hloop
  · refine ⟨?_, ?_, ?_⟩
    · intro card hc
      cases hc
    · intro card hc
      cases hc
    · intro period hp
      cases hp
  · intro box hbox state next hs hstep
    have hboxId : ModelId m box.id := ⟨box, hbox, rfl⟩
    split at hstep
    · obtain ⟨caption, _hcaption, hstep⟩ := bind_ok hstep
      have he : ForInStep.yield
          ({ state with title := some { id := box.id, caption } } : Family) = next := by
        simpa only [pure, Except.pure, Except.ok.injEq] using hstep
      subst next
      refine ⟨?_, hs.2.1, hs.2.2⟩
      intro card hc
      have he : ({ id := box.id, caption } : Lanes.Timeline.Card) = card :=
        Option.some.inj hc
      subst card
      exact hboxId
    · obtain ⟨caption, _hcaption, hstep⟩ := bind_ok hstep
      have he : ForInStep.yield
          ({ state with sections := state.sections ++ [{ id := box.id, caption }] } :
            Family) = next := by
        simpa only [pure, Except.pure, Except.ok.injEq] using hstep
      subst next
      refine ⟨hs.1, ?_, hs.2.2⟩
      intro card hc
      rcases List.mem_append.mp hc with hold | hnew
      · exact hs.2.1 card hold
      · have he : card = ({ id := box.id, caption } : Lanes.Timeline.Card) :=
          List.mem_singleton.mp hnew
        subst card
        exact hboxId
    · obtain ⟨sectionIndex, _hsection, hstep⟩ := bind_ok hstep
      split at hstep
      · change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
          .ok next at hstep
        cases hstep
      · obtain ⟨caption, _hcaption, hstep⟩ := bind_ok hstep
        have he : ForInStep.yield
            ({ state with periods := state.periods ++
              [{ id := box.id, caption, sectionIndex, events := [] }] } : Family) = next := by
          simpa only [pure, Except.pure, Except.ok.injEq] using hstep
        subst next
        refine ⟨hs.1, hs.2.1, ?_⟩
        intro period hm
        rcases List.mem_append.mp hm with hold | hnew
        · exact hs.2.2 period hold
        · have he : period = { id := box.id, caption, sectionIndex, events := [] } :=
            List.mem_singleton.mp hnew
          subst period
          exact ⟨hboxId, fun _ hm => False.elim (List.not_mem_nil hm)⟩
    · cases hprevious : state.periods.getLast? with
      | none =>
        simp only [hprevious] at hstep
        change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
          .ok next at hstep
        cases hstep
      | some previous =>
        simp only [hprevious] at hstep
        cases hroute : m.routes.find? (·.toId == box.id) with
        | none =>
          simp only [hroute] at hstep
          change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
            .ok next at hstep
          cases hstep
        | some route =>
          simp only [hroute] at hstep
          by_cases hbad : (route.fromId != (if m.options.direction == .LR then
              ((previous.events.getLast?).map (·.id)).getD previous.id else previous.id)) = true
          · simp only [hbad, ↓reduceIte] at hstep
            change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
              .ok next at hstep
            cases hstep
          · simp only [hbad] at hstep
            obtain ⟨caption, _hcaption, hstep⟩ := bind_ok hstep
            let event : Lanes.Timeline.Event := { id := box.id, caption, link := route.id }
            let updated := { previous with events := previous.events ++ [event] }
            have he : ForInStep.yield
                ({ state with periods := state.periods.set (state.periods.length - 1) updated } :
                  Family) = next := by
              simpa only [pure, Except.pure, Except.ok.injEq] using hstep
            subst next
            refine ⟨hs.1, hs.2.1, ?_⟩
            intro period hm
            rcases List.mem_or_eq_of_mem_set hm with hold | hnew
            · exact hs.2.2 period hold
            · subst period
              have hpreviousId := hs.2.2 previous (List.mem_of_getLast? hprevious)
              refine ⟨hpreviousId.1, ?_⟩
              intro e hevent
              rcases List.mem_append.mp hevent with hold | hnew
              · exact hpreviousId.2 e hold
              · have he : e = event := List.mem_singleton.mp hnew
                subst e
                exact hboxId
    · change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
        .ok next at hstep
      cases hstep

theorem rectSource_model_id {m : Model} {g : Family} {p : Lanes.Timeline.Plan}
    (hg : decode m = .ok g) {id : String} {rect : Rect}
    (hsource : RectSource g p id rect) : ModelId m id := by
  have hids := decode_ids hg
  rcases hsource with ⟨card, ht, hid, _hr⟩ |
    ⟨i, card, hc, hid, _hr⟩ | ⟨i, period, hp, hid, _hr⟩ |
    ⟨period, rects, event, hp, he, hid⟩
  · rw [← hid]
    exact hids.1 card ht
  · rw [← hid]
    exact hids.2.1 card (List.mem_of_getElem? hc)
  · rw [← hid]
    exact (hids.2.2 period (List.mem_of_getElem? hp)).1
  · rw [← hid]
    exact (hids.2.2 period (List.of_mem_zip hp).1).2 event (List.of_mem_zip he).1

theorem modelId_unique {m : Model} (hwf : WellFormed m)
    {a b : ModelBox} (ha : a ∈ m.boxes) (hb : b ∈ m.boxes)
    (hid : a.id = b.id) : a = b := by
  have unique : ∀ (boxes : List ModelBox), (boxes.map (·.id)).Nodup →
      a ∈ boxes → b ∈ boxes → a = b := by
    intro boxes
    induction boxes with
    | nil => intro _ ha _; cases ha
    | cons first rest ih =>
      intro hu ha hb
      obtain ⟨hfresh, hrest⟩ := List.nodup_cons.mp hu
      rcases List.mem_cons.mp ha with he | ha
      · subst a
        rcases List.mem_cons.mp hb with he | hb
        · exact he.symm
        · exact False.elim (hfresh (List.mem_map.mpr ⟨b, hb, hid.symm⟩))
      · rcases List.mem_cons.mp hb with he | hb
        · subst b
          exact False.elim (hfresh (List.mem_map.mpr ⟨a, ha, hid⟩))
        · exact ih hrest ha hb
  exact unique m.boxes (Model.boxIds_nodup hwf) ha hb

theorem rectSource_unique_model_box {m : Model} {g : Family}
    {p : Lanes.Timeline.Plan} (hwf : WellFormed m) (hg : decode m = .ok g)
    {id : String} {rect : Rect} (hsource : RectSource g p id rect) :
    ∃ box ∈ m.boxes, box.id = id ∧
      ∀ other ∈ m.boxes, other.id = id → other = box := by
  obtain ⟨box, hb, hid⟩ := rectSource_model_id hg hsource
  refine ⟨box, hb, hid, ?_⟩
  intro other ho hoid
  exact modelId_unique hwf ho hb (hoid.trans hid.symm)

theorem scene_route_endpoint_lookup {m : Model} {s : Scene}
    (hwf : WellFormed m) (hs : scene m = .ok s)
    {out : Route} (hout : out ∈ s.routes) :
    ∃ source target, s.layoutDump.box? out.fromId = some source ∧
      s.layoutDump.box? out.toId = some target := by
  obtain ⟨_g, _r, route, _period, _paths, _event,
    _hg, _hr, hroute, hcorr, _hp, _he, _hid⟩ := scene_route_source hs hout
  have hwell := hwf
  unfold WellFormed modelWellFormed at hwell
  simp only [Bool.and_eq_true] at hwell
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hrefs⟩, _⟩, _⟩ := hwell
  have hendpoints := List.all_eq_true.mp hrefs route hroute
  obtain ⟨hfrom, hto⟩ := Bool.and_eq_true_iff.mp hendpoints
  have hfromMem : route.fromId ∈ m.boxes.map (·.id) := by
    simpa only [List.contains_iff_mem] using hfrom
  have htoMem : route.toId ∈ m.boxes.map (·.id) := by
    simpa only [List.contains_iff_mem] using hto
  obtain ⟨fromBox, hfromBox, hfromId⟩ := List.mem_map.mp hfromMem
  obtain ⟨toBox, htoBox, htoId⟩ := List.mem_map.mp htoMem
  obtain ⟨_gs, _rs, source, _hgs, _hrs, hsource, _hcs, _hss⟩ :=
    scene_box_lookup hwf hs hfromBox
  obtain ⟨_gt, _rt, targetBox, _hgt, _hrt, htarget, _hct, _hst⟩ :=
    scene_box_lookup hwf hs htoBox
  refine ⟨source, targetBox, ?_, ?_⟩
  · rw [hcorr.2.1, ← hfromId]
    exact hsource
  · rw [hcorr.2.2.1, ← htoId]
    exact htarget

theorem layout_route_model_endpoints {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result)
    {out : Route} (hout : out ∈ result.scene.layoutDump.routes) :
    ∃ g r period paths event before after,
      decode m = .ok g ∧ Lanes.Timeline.layout g m.profile = .ok r ∧
      (period, paths) ∈ g.periods.zip r.geometry.routes ∧
      (event, out.points) ∈ period.events.zip paths ∧
      period.events = before ++ event :: after ∧ out.toId = event.id ∧
      out.fromId = (if m.options.direction == .LR then
        ((before.getLast?).map (·.id)).getD period.id else period.id) := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump] at hout
  exact scene_route_model_endpoints hwf hs hout

theorem layout_route_endpoint_lookup {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result)
    {out : Route} (hout : out ∈ result.scene.layoutDump.routes) :
    ∃ source target, result.scene.layoutDump.box? out.fromId = some source ∧
      result.scene.layoutDump.box? out.toId = some target := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump] at hout ⊢
  exact scene_route_endpoint_lookup hwf hs hout

theorem scene_modelId_rectFor_lookup {m : Model} {s : Scene} {g : Family}
    {r : Lanes.Timeline.Result} (hwf : WellFormed m)
    (hs : scene m = .ok s) (hg : decode m = .ok g)
    (hr : Lanes.Timeline.layout g m.profile = .ok r)
    {id : String} (hid : ModelId m id) :
    ∃ out, s.layoutDump.box? id = some out ∧
      rectFor g r.geometry id = some out.rect := by
  obtain ⟨box, hb, hboxId⟩ := hid
  obtain ⟨g', r', out, hg', hr', hlookup, hcorr, _hsource⟩ :=
    scene_box_lookup hwf hs hb
  have hge : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have hre : r' = r := Except.ok.inj (hr'.symm.trans hr)
  subst r'
  rw [hboxId] at hlookup
  have hrect := hcorr.2.2.2.2
  rw [hboxId] at hrect
  exact ⟨out, hlookup, hrect⟩

theorem layout_modelId_rectFor_lookup {m : Model} {result : Layered.FamilyResult}
    {g : Family} {r : Lanes.Timeline.Result} (hwf : WellFormed m)
    (h : layout m = .ok result) (hg : decode m = .ok g)
    (hr : Lanes.Timeline.layout g m.profile = .ok r)
    {id : String} (hid : ModelId m id) :
    ∃ out, result.scene.layoutDump.box? id = some out ∧
      rectFor g r.geometry id = some out.rect := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact scene_modelId_rectFor_lookup hwf hs hg hr hid

theorem horizontal_routes_fold_pair_ports (x : Int) (rects : List Rect)
    (initial source target : Rect)
    (hpair : (source, target) ∈ (initial :: rects).zip rects)
    (hmid : ∀ rect ∈ initial :: rects, rect.x + Lanes.half rect.w = x)
    (hsize : ∀ rect ∈ initial :: rects, 0 ≤ rect.w ∧ 0 ≤ rect.h) :
    let points : List Point := [⟨x, source.y + source.h⟩, ⟨x, target.y⟩]
    points ∈ (rects.foldl (fun (state : Rect × List (List Point)) box =>
      (box, state.2 ++ [[⟨x, state.1.y + state.1.h⟩, ⟨x, box.y⟩]]))
        (initial, [])).2 ∧
      points.head? = some ⟨x, source.y + source.h⟩ ∧
      points.getLast? = some ⟨x, target.y⟩ ∧
      Validator.onBoundary ⟨x, source.y + source.h⟩ source ∧
      Validator.onBoundary ⟨x, target.y⟩ target := by
  have hs := (List.of_mem_zip hpair).1
  have ht := List.mem_cons_of_mem initial (List.of_mem_zip hpair).2
  refine ⟨?_, rfl, rfl, ?_, ?_⟩
  · rw [horizontal_routes_fold_geometry]
    exact List.mem_map.mpr ⟨(source, target), hpair, rfl⟩
  · rw [← hmid source hs]
    exact bottom_midpoint_boundary source (hsize source hs).1 (hsize source hs).2
  · rw [← hmid target ht]
    exact top_midpoint_boundary target (hsize target ht).1 (hsize target ht).2

theorem zip_member_index {α β : Type} {left : List α} {right : List β}
    {a : α} {b : β} (h : (a, b) ∈ left.zip right) :
    ∃ i : Nat, left[i]? = some a ∧ right[i]? = some b := by
  induction left generalizing right with
  | nil => cases h
  | cons first rest ih =>
    cases right with
    | nil => cases h
    | cons second tail =>
      rcases List.mem_cons.mp h with he | hm
      · have ha : a = first := congrArg Prod.fst he
        have hb : b = second := congrArg Prod.snd he
        subst a
        subst b
        exact ⟨0, rfl, rfl⟩
      · obtain ⟨i, hi, hj⟩ := ih hm
        exact ⟨i + 1, by simpa only [List.getElem?_cons_succ] using hi,
          by simpa only [List.getElem?_cons_succ] using hj⟩

theorem layout_route_event_indices {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result)
    {out : Route} (hout : out ∈ result.scene.layoutDump.routes) :
    ∃ (g : Family) (r : Lanes.Timeline.Result) (period : Lanes.Timeline.Period)
      (paths : List (List Point)) (event : Lanes.Timeline.Event)
      (before after : List Lanes.Timeline.Event) (i j : Nat),
      decode m = .ok g ∧ Lanes.Timeline.layout g m.profile = .ok r ∧
      g.periods[i]? = some period ∧ r.geometry.routes[i]? = some paths ∧
      period.events[j]? = some event ∧ paths[j]? = some out.points ∧
      period.events = before ++ event :: after ∧ out.toId = event.id ∧
      out.fromId = (if m.options.direction == .LR then
        ((before.getLast?).map (·.id)).getD period.id else period.id) := by
  obtain ⟨g, r, period, paths, event, before, after,
    hg, hr, hp, he, hsplit, hto, hfrom⟩ :=
    layout_route_model_endpoints hwf h hout
  obtain ⟨i, hperiod, hpaths⟩ := zip_member_index hp
  obtain ⟨j, hevent, hpoints⟩ := zip_member_index he
  exact ⟨g, r, period, paths, event, before, after, i, j,
    hg, hr, hperiod, hpaths, hevent, hpoints, hsplit, hto, hfrom⟩

theorem shifted_stack_disjoint {rects : List Rect} (dx dy : Int)
    (h : rects.Pairwise (fun a b => a.y + a.h ≤ b.y ∧ Disjoint a b)) :
    (rects.map (Lanes.shiftRect dx dy)).Pairwise
      (fun a b => a.y + a.h ≤ b.y ∧ Disjoint a b) := by
  apply List.pairwise_map.mpr
  apply h.imp
  intro a b hab
  refine ⟨?_, ?_⟩
  · have hy := hab.1
    dsimp only [Lanes.shiftRect]
    omega
  · have hd := hab.2
    unfold Disjoint Rect.meetsInterior at hd ⊢
    dsimp only [Lanes.shiftRect]
    omega

theorem horizontalPlan_shifted_events_stack_disjoint
    (g : Family) (c : Lanes.TimelineConsts) (dx dy : Int)
    (hgap : 0 ≤ c.eventGap)
    (heights : ∀ period ∈ g.periods, ∀ event ∈ period.events,
      0 ≤ Lanes.Timeline.eventHeight c event)
    {events : List Rect}
    (hm : events ∈ ((Lanes.Timeline.horizontalPlan g c).shift dx dy).events) :
    events.Pairwise (fun a b => a.y + a.h ≤ b.y ∧ Disjoint a b) := by
  change events ∈ (Lanes.Timeline.horizontalPlan g c).events.map
    (fun rects => rects.map (Lanes.shiftRect dx dy)) at hm
  obtain ⟨rects, hrects, heq⟩ := List.mem_map.mp hm
  subst events
  exact shifted_stack_disjoint dx dy
    (horizontalPlan_events_stack_disjoint g c hgap heights hrects)

theorem cardRects_shift_disjoint (g : Family) (p : Lanes.Timeline.Plan)
    (dx dy : Int) (h : (cardRects g p).Pairwise Disjoint) :
    (cardRects g (p.shift dx dy)).Pairwise Disjoint := by
  rw [cardRects_shift]
  apply List.pairwise_map.mpr
  apply h.imp
  intro a b hab
  unfold Disjoint Rect.meetsInterior at hab ⊢
  dsimp only [Lanes.shiftRect]
  omega

theorem native_cardRects_disjoint {g : Family} {profile : Profile}
    {r : Lanes.Timeline.Result} (h : Lanes.Timeline.layout g profile = .ok r)
    (hplan : (cardRects g
      (Lanes.Timeline.plan g (Lanes.TimelineConsts.load profile))).Pairwise Disjoint) :
    (cardRects g r.geometry).Pairwise Disjoint := by
  obtain ⟨hgeometry, _hcanvas⟩ := native_layout_geometry h
  rw [hgeometry]
  exact cardRects_shift_disjoint _ _ _ _ hplan

theorem layout_route_indexed_endpoint_rects {m : Model}
    {result : Layered.FamilyResult} (hwf : WellFormed m)
    (h : layout m = .ok result)
    {out : Route} (hout : out ∈ result.scene.layoutDump.routes) :
    ∃ (g : Family) (r : Lanes.Timeline.Result) (period : Lanes.Timeline.Period)
      (paths : List (List Point)) (event : Lanes.Timeline.Event)
      (i j : Nat) (source target : Box),
      decode m = .ok g ∧ Lanes.Timeline.layout g m.profile = .ok r ∧
      g.periods[i]? = some period ∧ r.geometry.routes[i]? = some paths ∧
      period.events[j]? = some event ∧ paths[j]? = some out.points ∧
      out.toId = event.id ∧
      result.scene.layoutDump.box? out.fromId = some source ∧
      result.scene.layoutDump.box? out.toId = some target ∧
      rectFor g r.geometry out.fromId = some source.rect ∧
      rectFor g r.geometry out.toId = some target.rect := by
  obtain ⟨g, r, period, paths, event, _before, _after, i, j,
    hg, hr, hp, hpaths, he, hpoints, _hsplit, hto, _hfrom⟩ :=
    layout_route_event_indices hwf h hout
  obtain ⟨source, target, hsource, htarget⟩ :=
    layout_route_endpoint_lookup hwf h hout
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  obtain ⟨g', r', _hg', _hr', _hc, _hl, hboxes, _hroutes⟩ := scene_execution hs
  have hge : g' = g := Except.ok.inj (_hg'.symm.trans hg)
  subst g'
  have hre : r' = r := Except.ok.inj (_hr'.symm.trans hr)
  subst r'
  have lookup_rect : ∀ (id : String) (box : Box),
      result.scene.layoutDump.box? id = some box →
      rectFor g r.geometry id = some box.rect := by
    intro id box hlookup
    rw [hdump] at hlookup
    have hmem : box ∈ s.boxes := by
      exact List.mem_of_find?_eq_some hlookup
    obtain ⟨b, _hb, hcorr⟩ := forall₂_right_lookup hboxes hmem
    have hid : box.id = id := by
      have hpred := List.find?_some hlookup
      exact beq_iff_eq.mp hpred
    rw [← hid, hcorr.1]
    exact hcorr.2.2.2.2
  exact ⟨g, r, period, paths, event, i, j, source, target,
    hg, hr, hp, hpaths, he, hpoints, hto, hsource, htarget,
    lookup_rect _ _ hsource, lookup_rect _ _ htarget⟩

end Elegant.Kinds.Timeline

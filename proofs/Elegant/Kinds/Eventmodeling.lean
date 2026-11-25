import Elegant.Kinds.Common
import Elegant.Lanes
import Elegant.LanesFacts
import Elegant.StyledMeasure

set_option autoImplicit false

namespace Elegant.Kinds.Eventmodeling

open Common

abbrev Family := Lanes.Eventmodeling.Input

def measureCaption (profile : Profile) (role : TextRole) (target : Int) (text : String)
    (fontFamily : Bool := false) :
    Except LayoutError Lanes.Caption := do
  let metric ← match profile with
    | .cell => pure Measure.Metric.cell
    | .vector => (if role == .body then Measure.Role.body else Measure.Role.label).metric fontFamily
  let lines ← match StyledMeasure.wrap metric target text.toList with
    | .ok ls => pure ls
    | .error _ => throw .overflow
  return ⟨lines, lines.foldl (fun w l => max w l.width) 0,
    (lines.length : Int) * LayoutConst.line_h.get profile, role⟩

def laneIndex (shape : String) : Int :=
  if shape.startsWith "lane:" then ((shape.drop 5).toInt?).getD 0 else 0

def parentsConsistent (m : Model) : Bool :=
  m.boxes.all fun b => if b.role == .group then b.parent == "" else
    !(m.boxes.any fun parent => parent.id == b.parent && parent.role == .node)

def parentDeclarationOrder (m : Model) : Bool :=
  m.boxes.zipIdx.all fun (b, i) =>
    b.role == .group ||
      !(m.boxes.drop (i + 1)).any (fun later => later.id == b.parent && later.role == .group)

def decode (m : Model) : Except LayoutError Family := do
  if !parentsConsistent m then
    throw .domain
  if !parentDeclarationOrder m then throw .domain
  let c := Lanes.EventConsts.load m.profile
  let mut g : Family := { lanes := [], frames := [], relations := [] }
  let mut ids : List String := []
  for b in m.boxes do
    if b.role == .group then
      ids := ids ++ [b.id]
      g := { g with lanes := g.lanes ++ [{ id := b.id, index := laneIndex b.shape, caption := none }] }
    else
      let lane ← match ids.findIdx? (· == b.parent) with
        | some i => pure i
        | none => do
          let i := ids.length
          ids := ids ++ [b.parent]
          g := { g with lanes := g.lanes ++ [{ id := "", index := i, caption := none }] }
          pure i
      let parts := (boxText m b).splitOn "\n\n"
      let name ← measureCaption (fontFamily := m.options.fontFamily) m.profile .label c.boxMaxWidth (parts.headD "")
      let data ← if parts.length ≤ 1 then pure none else do
        let text := (String.intercalate "\n\n" parts.tail).replace "\n" "<br>"
        pure (some (← measureCaption (fontFamily := m.options.fontFamily) m.profile .body c.boxMaxWidth text))
      g := { g with frames := g.frames ++ [{ id := b.id, lane, category := b.shape, name, data }] }
  for r in m.routes do
    let some src := g.frames.findIdx? (·.id == r.fromId) | throw .domain
    let some dst := g.frames.findIdx? (·.id == r.toId) | throw .domain
    g := { g with relations := g.relations ++ [{ id := r.id, src, dst }] }
  for l in m.labels do
    let some i := ids.findIdx? (· == l.owner) | throw .domain
    let some lane := g.lanes[i]? | throw .domain
    let caption ← measureCaption (fontFamily := m.options.fontFamily) m.profile .label (c.contentStartX - 4 * c.lanePadding) l.text
    g := { g with lanes := g.lanes.set i { lane with caption := some caption } }
  return g

def placeBox (g : Family) (r : Lanes.Eventmodeling.Result) (b : ModelBox) :
    Except LayoutError Box := do
  let rect ← if b.role == .group then do
    let some i := g.lanes.findIdx? (·.id == b.id) | throw .domain
    let some rect := r.lanes[i]? | throw .domain
    pure rect
  else do
    let some i := g.frames.findIdx? (·.id == b.id) | throw .domain
    let some rect := r.frames[i]? | throw .domain
    pure rect
  pure (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box)

theorem placeBox_metadata {g : Family} {r : Lanes.Eventmodeling.Result}
    {b : ModelBox} {out : Box} (h : placeBox g r b = .ok out) :
    out.id = b.id ∧ out.parent = b.parent ∧ out.role = b.role.id ∧
      out.exclusive = b.exclusive := by
  by_cases hg : b.role == .group
  · cases hi : g.lanes.findIdx? (·.id == b.id) with
    | none =>
      simp [placeBox, hg, hi, Functor.map, Except.map,
        throw, throwThe, MonadExceptOf.throw] at h
    | some i =>
      cases hr : r.lanes[i]? with
      | none =>
        simp [placeBox, hg, hi, hr, Functor.map, Except.map,
          throw, throwThe, MonadExceptOf.throw] at h
      | some rect =>
        have he : (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box) = out := by
          simpa [placeBox, hg, hi, hr, bind, Except.bind, pure, Except.pure] using h
        cases he
        exact ⟨rfl, rfl, rfl, rfl⟩
  · cases hi : g.frames.findIdx? (·.id == b.id) with
    | none =>
      simp [placeBox, hg, hi, Functor.map, Except.map,
        throw, throwThe, MonadExceptOf.throw] at h
    | some i =>
      cases hr : r.frames[i]? with
      | none =>
        simp [placeBox, hg, hi, hr, Functor.map, Except.map,
          throw, throwThe, MonadExceptOf.throw] at h
      | some rect =>
        have he : (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box) = out := by
          simpa [placeBox, hg, hi, hr, bind, Except.bind, pure, Except.pure] using h
        cases he
        exact ⟨rfl, rfl, rfl, rfl⟩

theorem placeBox_lookup {g : Family} {r : Lanes.Eventmodeling.Result}
    {b : ModelBox} {out : Box} (h : placeBox g r b = .ok out) :
    if b.role == .group then
      ∃ i, g.lanes.findIdx? (·.id == b.id) = some i ∧ r.lanes[i]? = some out.rect
    else
      ∃ i, g.frames.findIdx? (·.id == b.id) = some i ∧ r.frames[i]? = some out.rect := by
  by_cases hg : b.role == .group
  · simp only [hg, ↓reduceIte]
    cases hi : g.lanes.findIdx? (·.id == b.id) with
    | none =>
      simp [placeBox, hg, hi, Functor.map, Except.map,
        throw, throwThe, MonadExceptOf.throw] at h
    | some i =>
      cases hr : r.lanes[i]? with
      | none =>
        simp [placeBox, hg, hi, hr, Functor.map, Except.map,
          throw, throwThe, MonadExceptOf.throw] at h
      | some rect =>
        have he : (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box) = out := by
          simpa [placeBox, hg, hi, hr, bind, Except.bind, pure, Except.pure] using h
        cases he
        exact ⟨i, rfl, hr⟩
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    cases hi : g.frames.findIdx? (·.id == b.id) with
    | none =>
      simp [placeBox, hg, hi, Functor.map, Except.map,
        throw, throwThe, MonadExceptOf.throw] at h
    | some i =>
      cases hr : r.frames[i]? with
      | none =>
        simp [placeBox, hg, hi, hr, Functor.map, Except.map,
          throw, throwThe, MonadExceptOf.throw] at h
      | some rect =>
        have he : (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box) = out := by
          simpa [placeBox, hg, hi, hr, bind, Except.bind, pure, Except.pure] using h
        cases he
        exact ⟨i, rfl, hr⟩

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem placeBoxes_correspond (g : Family) (r : Lanes.Eventmodeling.Result) :
    ∀ (input : List ModelBox) (output : List Box),
      input.mapM (placeBox g r) = .ok output →
      input.length = output.length ∧
        ∀ pair ∈ input.zip output, placeBox g r pair.1 = .ok pair.2 := by
  intro input
  induction input with
  | nil =>
    intro output h
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst output
    exact ⟨rfl, by simp⟩
  | cons b bs ih =>
    intro output h
    rw [List.mapM_cons] at h
    obtain ⟨out, hb, h⟩ := bind_ok h
    obtain ⟨outs, hbs, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst output
    obtain ⟨hlen, hrel⟩ := ih outs hbs
    refine ⟨by simpa using hlen, ?_⟩
    intro pair hp
    rcases List.mem_cons.mp hp with he | hp
    · cases he
      exact hb
    · exact hrel pair hp

def scene (m : Model) : Except LayoutError Scene := do
  let g ← decode m
  let r ← Lanes.Eventmodeling.layout g m.profile
  let boxes ← m.boxes.mapM (placeBox g r)
  let routes := (m.routes.zip r.routes).map fun (route, points) =>
    (⟨route.id, route.fromId, route.toId, route.orthogonal, points⟩ : Route)
  let labels ← m.labels.mapM fun l => do
    let some i := g.lanes.findIdx? (·.id == l.owner) | throw .domain
    let some lane := g.lanes[i]? | throw .domain
    let some cap := lane.caption | throw .domain
    let some rect := r.labels[i]? | throw .domain
    let lines := cap.lines.map fun line => String.ofList line.text
    pure ({ id := l.id, owner := l.owner, text := l.text, rect, lines } : SceneLabel)
  return { kind := m.kind, profile := m.profile, options := m.options, canvas := r.canvas, boxes, routes, labels, items := r.groups }

theorem scene_boxes_correspond {m : Model} {s : Scene} (h : scene m = .ok s) :
    ∃ g r, decode m = .ok g ∧ Lanes.Eventmodeling.layout g m.profile = .ok r ∧
      (m.boxes.length = s.boxes.length ∧
        ∀ pair ∈ m.boxes.zip s.boxes, placeBox g r pair.1 = .ok pair.2) := by
  unfold scene at h
  obtain ⟨g, hg, h⟩ := bind_ok h
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨boxes, hb, h⟩ := bind_ok h
  obtain ⟨labels, _, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst s
  exact ⟨g, r, hg, hr, placeBoxes_correspond g r m.boxes boxes hb⟩

theorem scene_boxes_metadata {m : Model} {s : Scene} (h : scene m = .ok s) :
    m.boxes.length = s.boxes.length ∧
      ∀ pair ∈ m.boxes.zip s.boxes,
        pair.2.id = pair.1.id ∧ pair.2.parent = pair.1.parent ∧
          pair.2.role = pair.1.role.id ∧ pair.2.exclusive = pair.1.exclusive := by
  obtain ⟨g, r, _, _, hlen, hc⟩ := scene_boxes_correspond h
  exact ⟨hlen, fun pair hp => placeBox_metadata (hc pair hp)⟩

theorem scene_box_at {m : Model} {s : Scene} (h : scene m = .ok s)
    {i : Nat} {b : ModelBox} (hb : m.boxes[i]? = some b) :
    ∃ g r out, decode m = .ok g ∧ Lanes.Eventmodeling.layout g m.profile = .ok r ∧
      s.boxes[i]? = some out ∧ placeBox g r b = .ok out ∧
      out.id = b.id ∧ out.parent = b.parent ∧ out.role = b.role.id ∧
        out.exclusive = b.exclusive := by
  obtain ⟨g, r, hg, hr, hlen, hc⟩ := scene_boxes_correspond h
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hb
  have ho : i < s.boxes.length := by omega
  have hout : s.boxes[i]? = some s.boxes[i] := List.getElem?_eq_getElem ho
  have hz : (m.boxes.zip s.boxes)[i]? = some (b, s.boxes[i]) :=
    List.getElem?_zip_eq_some.mpr ⟨hb, hout⟩
  have hp := hc (b, s.boxes[i]) (List.mem_of_getElem? hz)
  exact ⟨g, r, s.boxes[i], hg, hr, hout, hp, placeBox_metadata hp⟩

theorem family_frame_lane_bound {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r)
    {f : Lanes.Eventmodeling.Frame} (hf : f ∈ g.frames) :
    f.lane < g.lanes.length := by
  have hall : (g.frames.all fun frame => decide (frame.lane < g.lanes.length)) = true := by
    cases ha : g.frames.all (fun frame => decide (frame.lane < g.lanes.length)) with
    | true => rfl
    | false =>
      simp [Lanes.Eventmodeling.layout, ha, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw] at h
  exact of_decide_eq_true ((List.all_eq_true.mp hall) f hf)

theorem scene_decoded_frame_lanes {m : Model} {s : Scene} (h : scene m = .ok s) :
    ∃ g r, decode m = .ok g ∧ Lanes.Eventmodeling.layout g m.profile = .ok r ∧
      ∀ f ∈ g.frames, f.lane < g.lanes.length := by
  obtain ⟨g, r, hg, hr, _⟩ := scene_boxes_correspond h
  exact ⟨g, r, hg, hr, fun _ hf => family_frame_lane_bound hr hf⟩

private theorem bandWalk_height (height : Nat → Int) (gap width top : Int)
    (indices : List Nat) :
    ∀ pair ∈ Lanes.Eventmodeling.bandWalk height gap width top indices,
      pair.2.h = height pair.1 := by
  induction indices generalizing top with
  | nil => simp [Lanes.Eventmodeling.bandWalk]
  | cons i indices ih =>
    intro pair hp
    rcases List.mem_cons.mp hp with he | hp
    · cases he
      rfl
    · exact ih _ pair hp

private theorem bandWalk_indices (height : Nat → Int) (gap width top : Int)
    (indices : List Nat) :
    (Lanes.Eventmodeling.bandWalk height gap width top indices).map Prod.fst = indices := by
  induction indices generalizing top with
  | nil => rfl
  | cons i indices ih =>
    simp only [Lanes.Eventmodeling.bandWalk, List.map_cons]
    rw [ih]

private theorem bandFold_height (height : Nat → Int) (offset : Int) (bands : List (Nat × Rect))
    (hh : ∀ pair ∈ bands, pair.2.h = height pair.1)
    (state : List Int × List Int × List Int) (i : Nat) (hi : i < state.2.1.length) :
    let final := bands.foldl
      (fun (st : List Int × List Int × List Int) (j, b) =>
        (st.1.set j b.y, st.2.1.set j b.h, st.2.2 ++ [b.y + b.h + offset])) state
    final.2.1.length = state.2.1.length ∧
      final.2.1.getD i 0 =
        if i ∈ bands.map Prod.fst then height i else state.2.1.getD i 0 := by
  induction bands generalizing state with
  | nil => simp
  | cons pair bands ih =>
    obtain ⟨j, b⟩ := pair
    have hj := hh (j, b) (by simp)
    have ht := ih (fun pair hp => hh pair (by simp [hp]))
      (state.1.set j b.y, state.2.1.set j b.h, state.2.2 ++ [b.y + b.h + offset]) (by simpa using hi)
    dsimp only at ht ⊢
    rw [List.foldl_cons]
    refine ⟨by simpa using ht.1, ?_⟩
    rw [ht.2]
    by_cases hm : i ∈ bands.map Prod.fst
    · simp [hm]
    · by_cases he : i = j
      · subst j
        simp only [List.map_cons, List.mem_cons, hm, or_false, ↓reduceIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]
        exact hj
      · simp only [List.map_cons, List.mem_cons, hm, or_false, he, ↓reduceIte]
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_set_ne (fun hji => he hji.symm),
          ← List.getD_eq_getElem?_getD]

theorem rows_lane_height (g : Family) (c : Lanes.EventConsts) (frames : List Rect)
    {i : Nat} (hi : i < g.lanes.length) :
    (Lanes.Eventmodeling.rows g c frames).laneH.getD i 0 =
      Lanes.Eventmodeling.laneHeight g c frames i := by
  have hmem : i ∈ Lanes.Eventmodeling.order g := by
    have hp : (Lanes.Eventmodeling.order g).Perm (List.range g.lanes.length) :=
      List.mergeSort_perm _ _
    exact hp.mem_iff.mpr (List.mem_range.mpr hi)
  have hh : ∀ pair ∈ Lanes.Eventmodeling.laneBands g c frames,
      pair.2.h = Lanes.Eventmodeling.laneHeight g c frames pair.1 :=
    bandWalk_height _ _ _ _ _
  have hind : (Lanes.Eventmodeling.laneBands g c frames).map Prod.fst =
      Lanes.Eventmodeling.order g := bandWalk_indices _ _ _ _ _
  have ht := bandFold_height (Lanes.Eventmodeling.laneHeight g c frames)
    (Lanes.half c.laneGap) (Lanes.Eventmodeling.laneBands g c frames) hh
    (List.replicate g.lanes.length (0 : Int),
      List.replicate g.lanes.length (0 : Int), [Lanes.half c.lanePadding]) i
    (by simpa using hi)
  simpa only [Lanes.Eventmodeling.rows, hind, ite_eq_left hmem] using ht.2

private theorem frameHeight_fold (f : Lanes.Eventmodeling.Frame) (rect : Rect)
    (pairs : List (Lanes.Eventmodeling.Frame × Rect)) (initial : Int)
    (hmem : (f, rect) ∈ pairs) :
    rect.h ≤ pairs.foldl (fun h pair =>
      if pair.1.lane == f.lane then max h pair.2.h else h) initial := by
  induction pairs generalizing initial with
  | nil => simp at hmem
  | cons pair pairs ih =>
    rcases List.mem_cons.mp hmem with he | hm
    · cases he
      rw [List.foldl_cons]
      have hs := Lanes.Eventmodeling.foldl_ge_initial
        (fun h (pair : Lanes.Eventmodeling.Frame × Rect) =>
          if pair.1.lane == f.lane then max h pair.2.h else h)
        (by intro h pair; split <;> first | exact Int.le_max_left _ _ | exact Int.le_refl _)
        pairs (max initial rect.h)
      simpa only [beq_self_eq_true, ↓reduceIte] using
        Int.le_trans (Int.le_max_right initial rect.h) hs
    · rw [List.foldl_cons]
      exact ih _ hm

theorem laneHeight_contains_frame (g : Family) (c : Lanes.EventConsts)
    (frames : List Rect) {f : Lanes.Eventmodeling.Frame} {rect : Rect}
    (hmem : (f, rect) ∈ g.frames.zip frames) :
    rect.h + 2 * c.lanePadding ≤ Lanes.Eventmodeling.laneHeight g c frames f.lane := by
  have h := frameHeight_fold f rect (g.frames.zip frames)
    (max c.laneMinHeight
      ((((g.lanes[f.lane]?).bind (·.caption)).map (·.h)).getD 0)) hmem
  change rect.h + 2 * c.lanePadding ≤
    (g.frames.zip frames).foldl
      (fun height pair => if pair.1.lane == f.lane then max height pair.2.h else height)
      (max c.laneMinHeight
        ((((g.lanes[f.lane]?).bind (·.caption)).map (·.h)).getD 0)) + 2 * c.lanePadding
  exact Int.add_le_add_right h (2 * c.lanePadding)

theorem rows_frame_vertical_containment (g : Family) (c : Lanes.EventConsts)
    (frames : List Rect) {i : Nat} {f : Lanes.Eventmodeling.Frame} {rect : Rect}
    (hf : g.frames[i]? = some f) (hr : frames[i]? = some rect)
    (hlane : f.lane < g.lanes.length) (hpad : 0 < c.lanePadding) :
    ∃ placed, (Lanes.Eventmodeling.rows g c frames).frames[i]? = some placed ∧
      (Lanes.Eventmodeling.laneRect c (Lanes.Eventmodeling.rows g c frames) f.lane).y <
        placed.y ∧
      placed.y + placed.h <
        (Lanes.Eventmodeling.laneRect c (Lanes.Eventmodeling.rows g c frames) f.lane).y +
        (Lanes.Eventmodeling.laneRect c (Lanes.Eventmodeling.rows g c frames) f.lane).h := by
  let p := Lanes.Eventmodeling.rows g c frames
  let placed := { rect with y := p.laneY.getD f.lane 0 + c.lanePadding }
  have hz : (g.frames.zip frames)[i]? = some (f, rect) :=
    List.getElem?_zip_eq_some.mpr ⟨hf, hr⟩
  have hp : p.frames[i]? = some placed := by
    change ((g.frames.zip frames).map (fun pair =>
      { pair.2 with y := p.laneY.getD pair.1.lane 0 + c.lanePadding }))[i]? = some placed
    rw [List.getElem?_map, hz]
    rfl
  have hh := laneHeight_contains_frame g c frames (List.mem_of_getElem? hz)
  have hheight := rows_lane_height g c frames hlane
  refine ⟨placed, hp, ?_, ?_⟩
  · change p.laneY.getD f.lane 0 < p.laneY.getD f.lane 0 + c.lanePadding
    omega
  · change p.laneY.getD f.lane 0 + c.lanePadding + rect.h <
      p.laneY.getD f.lane 0 + p.laneH.getD f.lane 0
    change p.laneH.getD f.lane 0 = _ at hheight
    omega

private theorem columnWalk_length (c : Lanes.EventConsts) (reach : Int)
    (floor : List Int) (frames : List Lanes.Eventmodeling.Frame) :
    (Lanes.Eventmodeling.columnWalk c reach floor frames).length = frames.length := by
  induction frames generalizing reach floor with
  | nil => rfl
  | cons f frames ih =>
    simp only [Lanes.Eventmodeling.columnWalk, List.length_cons]
    rw [ih]

theorem family_raw_frame_vertical_containment {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r)
    {i : Nat} {f : Lanes.Eventmodeling.Frame} (hf : g.frames[i]? = some f) :
    let c := Lanes.EventConsts.load profile
    let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
    ∃ placed, raw.frames[i]? = some placed ∧
      (Lanes.Eventmodeling.laneRect c raw f.lane).y < placed.y ∧
      placed.y + placed.h < (Lanes.Eventmodeling.laneRect c raw f.lane).y +
        (Lanes.Eventmodeling.laneRect c raw f.lane).h := by
  dsimp only
  let c := Lanes.EventConsts.load profile
  have hlen : (Lanes.Eventmodeling.columns g c).length = g.frames.length :=
    columnWalk_length c _ _ _
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hf
  have hcol : i < (Lanes.Eventmodeling.columns g c).length := by omega
  have hrect := List.getElem?_eq_getElem hcol
  have hlane := family_frame_lane_bound h (List.mem_of_getElem? hf)
  have hpad : 0 < c.lanePadding := by cases profile <;> decide
  exact rows_frame_vertical_containment g c _ hf hrect hlane hpad

private theorem frameRight_fold (padding : Int) (rect : Rect) (frames : List Rect)
    (initial : Int) (hmem : rect ∈ frames) :
    rect.x + rect.w + padding ≤
      frames.foldl (fun a r => max a (r.x + r.w + padding)) initial := by
  induction frames generalizing initial with
  | nil => simp at hmem
  | cons r frames ih =>
    rcases List.mem_cons.mp hmem with he | hm
    · subst r
      rw [List.foldl_cons]
      exact Int.le_trans (Int.le_max_right _ _)
        (Lanes.Eventmodeling.foldl_ge_initial
          (fun a r => max a (r.x + r.w + padding))
          (fun _ _ => Int.le_max_left _ _) frames _)
    · rw [List.foldl_cons]
      exact ih _ hm

theorem raw_frame_horizontal_containment (g : Family) (profile : Profile)
    {placed : Rect}
    (hp : placed ∈
      (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
        (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))).frames) :
    let c := Lanes.EventConsts.load profile
    let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
    0 < placed.x ∧ placed.x + placed.w < raw.maxR + c.lanePadding := by
  dsimp only
  let c := Lanes.EventConsts.load profile
  let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
  have hright := frameRight_fold c.boxPadding placed raw.frames 0 hp
  change placed.x + placed.w + c.boxPadding ≤ raw.maxR at hright
  have hpadding := (Lanes.event_constants_positive profile).2.2.2.1
  have hlane := (Lanes.event_constants_positive profile).2.1
  change placed ∈ (g.frames.zip (Lanes.Eventmodeling.columns g c)).map
    (fun pair => { pair.2 with y := raw.laneY.getD pair.1.lane 0 + c.lanePadding }) at hp
  obtain ⟨pair, hpair, he⟩ := List.mem_map.mp hp
  have hcolumn := (List.of_mem_zip hpair).2
  have hlow := Lanes.Eventmodeling.columnWalk_lower c
    (Lanes.event_constants_positive profile).2.2.2.2.1
    (Int.le_of_lt hpadding) g.frames
    (Lanes.Eventmodeling.gutter g c + c.boxOverlap - c.boxPadding)
    (List.replicate g.lanes.length 0) pair.2 hcolumn
  have hgutter : c.contentStartX ≤ Lanes.Eventmodeling.gutter g c := by
    apply Lanes.Eventmodeling.foldl_ge_initial
    intro width lane
    cases lane.caption with
    | none => exact Int.le_refl _
    | some cap => exact Int.le_max_left _ _
  have hstart : 0 < c.contentStartX := by cases profile <;> decide
  have hx : pair.2.x = placed.x := by
    have hx := congrArg (fun rect : Rect => rect.x) he
    simpa only using hx
  change 0 < c.boxPadding at hpadding
  change 0 ≤ c.lanePadding at hlane
  change 0 < placed.x ∧ placed.x + placed.w < raw.maxR + c.lanePadding
  exact ⟨by omega, by omega⟩

theorem family_raw_frame_containment {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r)
    {i : Nat} {f : Lanes.Eventmodeling.Frame} (hf : g.frames[i]? = some f) :
    let c := Lanes.EventConsts.load profile
    let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
    ∃ placed, raw.frames[i]? = some placed ∧
      (Lanes.Eventmodeling.laneRect c raw f.lane).Contained placed := by
  obtain ⟨placed, hp, htop, hbottom⟩ := family_raw_frame_vertical_containment h hf
  have hhorizontal := raw_frame_horizontal_containment g profile (List.mem_of_getElem? hp)
  refine ⟨placed, hp, ?_⟩
  unfold Rect.Contained Lanes.Eventmodeling.laneRect
  dsimp only [Lanes.Eventmodeling.laneRect] at htop hbottom hhorizontal ⊢
  omega

theorem family_geometry {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r) :
    ∃ points : List (List Point),
    let c := Lanes.EventConsts.load profile
    let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
    let p := { raw with routes := points }
    let ext := Lanes.Eventmodeling.extent g c p
    let dx := c.canvasMargin - ext.x
    let dy := c.canvasMargin - ext.y
    r.canvas = ⟨ext.w + 2 * c.canvasMargin, ext.h + 2 * c.canvasMargin⟩ ∧
      r.frames = raw.frames.map (Lanes.shiftRect dx dy) ∧
      r.lanes = (List.range g.lanes.length).map
        (fun i => Lanes.shiftRect dx dy (Lanes.Eventmodeling.laneRect c raw i)) := by
  unfold Lanes.Eventmodeling.layout at h
  by_cases hg : ((!g.frames.all (fun f => decide (f.lane < g.lanes.length))) ||
      !g.relations.all (fun r => decide (r.src < g.frames.length ∧ r.dst < g.frames.length))) = true
  · simp only [hg, ↓reduceIte, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw] at h
    cases h
  · simp only [hg, bind, Except.bind] at h
    obtain ⟨points, _, h⟩ := bind_ok h
    let c := Lanes.EventConsts.load profile
    let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
    let p := { raw with routes := points }
    let ext := Lanes.Eventmodeling.extent g c p
    let dx := c.canvasMargin - ext.x
    let dy := c.canvasMargin - ext.y
    let lanes := (List.range g.lanes.length).map
      (fun i => Lanes.shiftRect dx dy (Lanes.Eventmodeling.laneRect c p i))
    let labels := (List.range g.lanes.length).map
      (fun i => Lanes.shiftRect dx dy (Lanes.Eventmodeling.labelRect g c p i))
    let frames := p.frames.map (Lanes.shiftRect dx dy)
    let shiftedRoutes := points.map (List.map (Lanes.shiftPoint dx dy))
    let canvas : Size := ⟨ext.w + 2 * c.canvasMargin, ext.h + 2 * c.canvasMargin⟩
    let values := [canvas.w, canvas.h] ++ (lanes ++ labels ++ frames).flatMap (Lanes.rectValues 0 0) ++
      shiftedRoutes.flatten.flatMap (Lanes.pointValues 0 0) ++
      (List.range g.frames.length).flatMap (fun i =>
        let ts := Lanes.Eventmodeling.frameTexts g c p i
        Lanes.rectValues dx dy ts.1 ++ Lanes.rectValues dx dy ts.2)
    by_cases hv : values.all Lanes.withinLimit = true
    · have hv' := hv
      dsimp only [values, canvas, lanes, labels, frames, shiftedRoutes, dx, dy, ext, p, raw, c] at hv'
      simp only [hv', Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at h
      subst r
      exact ⟨points, rfl, rfl, rfl⟩
    · have hv' : values.all Lanes.withinLimit = false := Bool.eq_false_iff.mpr hv
      dsimp only [values, canvas, lanes, labels, frames, shiftedRoutes, dx, dy, ext, p, raw, c] at hv'
      simp only [hv', Bool.not_false, ↓reduceIte,
        throw, throwThe, MonadExceptOf.throw] at h
      cases h

theorem family_frame_translation {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r) :
    let c := Lanes.EventConsts.load profile
    let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
    ∃ dx dy, r.frames = raw.frames.map (Lanes.shiftRect dx dy) ∧
      r.lanes = (List.range g.lanes.length).map
        (fun i => Lanes.shiftRect dx dy (Lanes.Eventmodeling.laneRect c raw i)) := by
  obtain ⟨points, _, hframes, hlanes⟩ := family_geometry h
  exact ⟨_, _, hframes, hlanes⟩

private theorem extent_contains_frame (g : Family) (c : Lanes.EventConsts)
    (p : Lanes.Eventmodeling.Plan) {i : Nat} {rect : Rect}
    (hi : i < g.frames.length) (hp : p.frames[i]? = some rect) :
    (Lanes.Eventmodeling.extent g c p).Contained rect := by
  unfold Lanes.Eventmodeling.extent
  refine (Lanes.foldl_union _ _).2 rect ?_
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, hp]

private theorem extent_contains_lane (g : Family) (c : Lanes.EventConsts)
    (p : Lanes.Eventmodeling.Plan) {i : Nat} (hi : i < g.lanes.length) :
    (Lanes.Eventmodeling.extent g c p).Contained
      (Lanes.Eventmodeling.laneRect c p i) := by
  unfold Lanes.Eventmodeling.extent
  refine (Lanes.foldl_union _ _).2 _ ?_
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, by simp⟩

private theorem shifted_extent_contains {extent rect : Rect} {margin : Int}
    (hm : 0 ≤ margin) (hc : extent.Contained rect) :
    (⟨0, 0, extent.w + 2 * margin, extent.h + 2 * margin⟩ : Rect).Contained
      (Lanes.shiftRect (margin - extent.x) (margin - extent.y) rect) := by
  simp only [Rect.Contained, Lanes.shiftRect] at hc ⊢
  omega

theorem family_frames_canvas {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r) :
    ∀ rect ∈ r.frames, (⟨0, 0, r.canvas.w, r.canvas.h⟩ : Rect).Contained rect := by
  obtain ⟨points, hcanvas, hframes, _⟩ := family_geometry h
  let c := Lanes.EventConsts.load profile
  let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
  let p := { raw with routes := points }
  have hlength : raw.frames.length = g.frames.length := by
    simp only [raw, Lanes.Eventmodeling.rows, List.length_map, List.length_zip,
      Lanes.Eventmodeling.columns, columnWalk_length, Nat.min_self]
  intro rect hm
  rw [hframes] at hm
  obtain ⟨original, horiginal, he⟩ := List.mem_map.mp hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp horiginal
  obtain ⟨hib, _⟩ := List.getElem?_eq_some_iff.mp hi
  have hif : i < g.frames.length := by
    change i < raw.frames.length at hib
    omega
  have hc := extent_contains_frame g c p hif hi
  have hmargin : 0 ≤ c.canvasMargin := by cases profile <;> decide
  have hshift := shifted_extent_contains hmargin hc
  rw [hcanvas, ← he]
  exact hshift

theorem family_lanes_canvas {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r) :
    ∀ rect ∈ r.lanes, (⟨0, 0, r.canvas.w, r.canvas.h⟩ : Rect).Contained rect := by
  obtain ⟨points, hcanvas, _, hlanes⟩ := family_geometry h
  let c := Lanes.EventConsts.load profile
  let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
  let p := { raw with routes := points }
  intro rect hm
  rw [hlanes] at hm
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hm
  have hc := extent_contains_lane g c p (List.mem_range.mp hi)
  have hmargin : 0 ≤ c.canvasMargin := by cases profile <;> decide
  have hshift := shifted_extent_contains hmargin hc
  rw [hcanvas, ← he]
  exact hshift

theorem family_frame_containment {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r)
    {i : Nat} {f : Lanes.Eventmodeling.Frame} (hf : g.frames[i]? = some f) :
    ∃ placed lane, r.frames[i]? = some placed ∧ r.lanes[f.lane]? = some lane ∧
      lane.Contained placed := by
  obtain ⟨rawFrame, hp, hcontained⟩ := family_raw_frame_containment h hf
  obtain ⟨dx, dy, hframes, hlanes⟩ := family_frame_translation h
  have hlane := family_frame_lane_bound h (List.mem_of_getElem? hf)
  refine ⟨Lanes.shiftRect dx dy rawFrame,
    Lanes.shiftRect dx dy (Lanes.Eventmodeling.laneRect (Lanes.EventConsts.load profile)
      (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
        (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))) f.lane), ?_, ?_, ?_⟩
  · rw [hframes, List.getElem?_map, hp]
    rfl
  · rw [hlanes, List.getElem?_map, List.getElem?_range hlane]
    rfl
  · exact (Lanes.shiftRect_contained dx dy).mpr hcontained

/-- Admission guard: a group box needs a nonempty id.  An empty id aliases the group
lane with the fallback lane that parentless frames create, so the group frame would
share a lane with foreign frames instead of standing clear of them. -/
def hasEmptyGroupId (m : Model) : Bool :=
  m.boxes.any fun b => b.role == .group && b.id == ""

/-- Admission guard: an orthogonal route in the vector profile must keep both endpoints in
one lane.  The vector-profile shortcut of `Lanes.Eventmodeling.route` returns the straight
segment between the two ports; that segment is diagonal unless the two ports happen to
align, so a cross-lane orthogonal route is not an orthogonal polyline.  Same-lane routes
always take the tidy corridor polyline, which is orthogonal. -/
def crossLaneOrthogonalRoute (m : Model) : Bool :=
  m.profile == .vector && m.routes.any fun r =>
    r.orthogonal &&
      (match m.boxes.find? (fun b => b.id == r.fromId),
             m.boxes.find? (fun b => b.id == r.toId) with
       | some srcBox, some dstBox => srcBox.parent != dstBox.parent
       | _, _ => true)

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  if hasEmptyGroupId m then
    .error (.geometry .domain)
  else if crossLaneOrthogonalRoute m then
    .error (.geometry .domain)
  else
    match scene m with
    | .error e => .error (.geometry e)
    | .ok s => .ok { scene := s.projectCellAttachments (routeMarkers m), budgetExhausted := false }

theorem layout_group_ids_nonempty (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) : ∀ b ∈ m.boxes, b.role = .group → b.id ≠ "" := by
  unfold layout at h
  by_cases hbad : hasEmptyGroupId m = true
  · simp only [hbad, ↓reduceIte] at h
    cases h
  · intro b hb hrole hid
    exact hbad (List.any_eq_true.mpr ⟨b, hb, by simp [hrole, hid]⟩)

theorem layout_orthogonal_routes_same_lane (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) :
    m.profile = .vector → ∀ r ∈ m.routes, r.orthogonal = true →
      ∀ srcBox dstBox : ModelBox,
        m.boxes.find? (fun b => b.id == r.fromId) = some srcBox →
        m.boxes.find? (fun b => b.id == r.toId) = some dstBox →
        srcBox.parent = dstBox.parent := by
  unfold layout at h
  by_cases hg : hasEmptyGroupId m = true
  · simp only [hg, ↓reduceIte] at h
    cases h
  · simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hcross : crossLaneOrthogonalRoute m = true
    · simp only [hcross, ↓reduceIte] at h
      cases h
    · intro hprofile r hr horth srcBox dstBox hsrc hdst
      have hvector : (m.profile == Profile.vector) = true := by simpa using hprofile
      have hany : (m.routes.any fun r =>
          r.orthogonal &&
            (match m.boxes.find? (fun b => b.id == r.fromId),
                   m.boxes.find? (fun b => b.id == r.toId) with
             | some srcBox, some dstBox => srcBox.parent != dstBox.parent
             | _, _ => true)) = false := by
        simpa [crossLaneOrthogonalRoute, hvector] using hcross
      have hroute := List.any_eq_false.mp hany r hr
      rw [horth] at hroute
      simp only [hsrc, hdst, Bool.true_and] at hroute
      simpa using hroute

theorem decode_parentsConsistent {m : Model} {g : Family} (h : decode m = .ok g) :
    parentsConsistent m = true := by
  cases hp : parentsConsistent m with
  | true => rfl
  | false => simp [decode, hp, Bind.bind, Except.bind] at h

theorem decode_group_parent {m : Model} {g : Family} (h : decode m = .ok g)
    {b : ModelBox} (hb : b ∈ m.boxes) (hr : b.role = .group) : b.parent = "" := by
  have hp := decode_parentsConsistent h
  unfold parentsConsistent at hp
  have hg := (List.all_eq_true.mp hp) b hb
  simpa [hr] using hg

theorem decode_parentDeclarationOrder {m : Model} {g : Family}
    (h : decode m = .ok g) : parentDeclarationOrder m = true := by
  cases hp : parentsConsistent m with
  | false => simp [decode, hp, Bind.bind, Except.bind] at h
  | true =>
    cases ho : parentDeclarationOrder m with
    | true => rfl
    | false => simp [decode, hp, ho, Bind.bind, Except.bind] at h

theorem decode_parent_not_later {m : Model} {g : Family}
    (h : decode m = .ok g) {b : ModelBox} {i : Nat}
    (hb : (b, i) ∈ m.boxes.zipIdx) (hr : b.role ≠ .group)
    {parent : ModelBox} (hp : parent ∈ m.boxes.drop (i + 1))
    (hgroup : parent.role = .group) : parent.id ≠ b.parent := by
  have ho := decode_parentDeclarationOrder h
  unfold parentDeclarationOrder at ho
  have hi := (List.all_eq_true.mp ho) (b, i) hb
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hi
  have hn : (m.boxes.drop (i + 1)).any
      (fun later => later.id == b.parent && later.role == .group) = false :=
    hi.resolve_left hr
  intro he
  have hy : (m.boxes.drop (i + 1)).any
      (fun later => later.id == b.parent && later.role == .group) = true :=
    List.any_eq_true.mpr ⟨parent, hp, by simp [he, hgroup]⟩
  rw [hn] at hy
  cases hy

theorem decode_parent_not_node {m : Model} {g : Family}
    (h : decode m = .ok g) {b parent : ModelBox}
    (hb : b ∈ m.boxes) (hp : parent ∈ m.boxes)
    (hr : b.role ≠ .group) (hn : parent.role = .node) :
    parent.id ≠ b.parent := by
  have hc := decode_parentsConsistent h
  unfold parentsConsistent at hc
  have hi := (List.all_eq_true.mp hc) b hb
  simp only [hr, beq_iff_eq, ↓reduceIte, Bool.not_eq_true'] at hi
  intro he
  have hy : m.boxes.any
      (fun p => p.id == b.parent && p.role == .node) = true :=
    List.any_eq_true.mpr ⟨parent, hp, by simp [he, hn]⟩
  rw [hi] at hy
  cases hy

theorem scene_c1 {m : Model} {s : Scene} (h : scene m = .ok s) :
    Validator.C1 s.layoutDump := by
  unfold scene at h
  obtain ⟨g, _, h⟩ := bind_ok h
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨boxes, hb, h⟩ := bind_ok h
  obtain ⟨labels, _, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst s
  obtain ⟨hlen, hc⟩ := placeBoxes_correspond g r m.boxes boxes hb
  intro out hout
  change out ∈ boxes at hout
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hout
  obtain ⟨hib, _⟩ := List.getElem?_eq_some_iff.mp hi
  have him : i < m.boxes.length := by omega
  have hinput : m.boxes[i]? = some m.boxes[i] := List.getElem?_eq_getElem him
  have hz : (m.boxes.zip boxes)[i]? = some (m.boxes[i], out) :=
    List.getElem?_zip_eq_some.mpr ⟨hinput, hi⟩
  have hp := hc (m.boxes[i], out) (List.mem_of_getElem? hz)
  have hl := placeBox_lookup hp
  change (⟨0, 0, r.canvas.w, r.canvas.h⟩ : Rect).Contained out.rect
  split at hl
  · obtain ⟨_, _, hrect⟩ := hl
    exact family_lanes_canvas hr out.rect (List.mem_of_getElem? hrect)
  · obtain ⟨_, _, hrect⟩ := hl
    exact family_frames_canvas hr out.rect (List.mem_of_getElem? hrect)

theorem layout_scene {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    ∃ s, scene m = .ok s ∧ result.scene.layoutDump = s.layoutDump := by
  unfold layout at h
  by_cases hg : hasEmptyGroupId m = true
  · simp only [hg, ↓reduceIte] at h
    cases h
  · simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hcross : crossLaneOrthogonalRoute m = true
    · simp only [hcross, ↓reduceIte] at h
      cases h
    · simp only [hcross, Bool.false_eq_true, ↓reduceIte] at h
      cases hs : scene m with
      | error e => simp [hs] at h
      | ok s =>
        have he : result =
            { scene := s.projectCellAttachments (routeMarkers m), budgetExhausted := false } := by
          simpa [hs] using h.symm
        refine ⟨s, rfl, ?_⟩
        rw [he]
        exact Scene.projectCellAttachments_layoutDump s (routeMarkers m)

theorem eventmodeling_c1 {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : Validator.C1 result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact scene_c1 hs

theorem scene_output_origin {m : Model} {s : Scene} (h : scene m = .ok s)
    {out : Box} (hout : out ∈ s.boxes) :
    ∃ g r b, decode m = .ok g ∧ Lanes.Eventmodeling.layout g m.profile = .ok r ∧
      b ∈ m.boxes ∧ placeBox g r b = .ok out := by
  obtain ⟨g, r, hg, hr, hlen, hc⟩ := scene_boxes_correspond h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hout
  obtain ⟨hib, _⟩ := List.getElem?_eq_some_iff.mp hi
  have him : i < m.boxes.length := by omega
  have hb : m.boxes[i]? = some m.boxes[i] := List.getElem?_eq_getElem him
  have hz : (m.boxes.zip s.boxes)[i]? = some (m.boxes[i], out) :=
    List.getElem?_zip_eq_some.mpr ⟨hb, hi⟩
  exact ⟨g, r, m.boxes[i], hg, hr, List.getElem_mem him,
    hc (m.boxes[i], out) (List.mem_of_getElem? hz)⟩

theorem scene_group_rooted {m : Model} {s : Scene} (h : scene m = .ok s)
    {out : Box} (hout : out ∈ s.boxes) (hrole : out.role = "group") :
    out.parent = "" := by
  obtain ⟨g, r, b, hg, _, hb, hp⟩ := scene_output_origin h hout
  obtain ⟨_, hparent, hroles, _⟩ := placeBox_metadata hp
  have hgroup : b.role = .group := by
    cases hr : b.role with
    | node => simp [hr, BoxRole.id, hrole] at hroles
    | group => rfl
  exact hparent.trans (decode_group_parent hg hb hgroup)

theorem family_frames_length {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r) :
    r.frames.length = g.frames.length := by
  obtain ⟨_, _, hframes, _⟩ := family_geometry h
  rw [hframes]
  simp only [List.length_map, Lanes.Eventmodeling.rows, List.length_zip,
    Lanes.Eventmodeling.columns, columnWalk_length, Nat.min_self]

theorem family_lanes_length {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r) :
    r.lanes.length = g.lanes.length := by
  obtain ⟨_, _, _, hlanes⟩ := family_geometry h
  rw [hlanes]
  simp only [List.length_map, List.length_range]

theorem placeBox_node_lane_containment {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} {b : ModelBox} {out : Box}
    (hr : Lanes.Eventmodeling.layout g profile = .ok r)
    (hb : b.role ≠ .group) (hp : placeBox g r b = .ok out) :
    ∃ i f lane, g.frames.findIdx? (·.id == b.id) = some i ∧
      g.frames[i]? = some f ∧ r.lanes[f.lane]? = some lane ∧
      lane.Contained out.rect := by
  have hlookup := placeBox_lookup hp
  simp only [show (b.role == .group) = false from by simpa using hb,
    Bool.false_eq_true, ↓reduceIte] at hlookup
  obtain ⟨i, hi, hout⟩ := hlookup
  obtain ⟨hib, _⟩ := List.getElem?_eq_some_iff.mp hout
  have hif : i < g.frames.length := by
    rw [family_frames_length hr] at hib
    exact hib
  have hf : g.frames[i]? = some g.frames[i] := List.getElem?_eq_getElem hif
  obtain ⟨placed, lane, hplaced, hlane, hc⟩ := family_frame_containment hr hf
  have he : placed = out.rect := by
    rw [hout] at hplaced
    exact (Option.some.inj hplaced).symm
  exact ⟨i, g.frames[i], lane, hi, hf, hlane, he ▸ hc⟩

theorem scene_node_lane_containment {m : Model} {s : Scene}
    (h : scene m = .ok s) {out : Box} (hout : out ∈ s.boxes)
    (hrole : out.role = "node") :
    ∃ g r f lane, decode m = .ok g ∧
      Lanes.Eventmodeling.layout g m.profile = .ok r ∧
      f ∈ g.frames ∧ r.lanes[f.lane]? = some lane ∧ lane.Contained out.rect := by
  obtain ⟨g, r, b, hg, hr, _, hp⟩ := scene_output_origin h hout
  have hmetadata := placeBox_metadata hp
  have hb : b.role ≠ .group := by
    intro he
    simpa [he, BoxRole.id, hrole] using hmetadata.2.2.1
  obtain ⟨_, f, lane, _, hf, hlane, hc⟩ :=
    placeBox_node_lane_containment hr hb hp
  exact ⟨g, r, f, lane, hg, hr, List.mem_of_getElem? hf, hlane, hc⟩

theorem scene_node_parent_is_group {m : Model} {s : Scene}
    (h : scene m = .ok s) {out parent : Box}
    (hout : out ∈ s.boxes) (hparent : parent ∈ s.boxes)
    (hrole : out.role = "node") (hid : parent.id = out.parent) :
    parent.role = "group" := by
  obtain ⟨g, _, b, hg, _, hb, hp⟩ := scene_output_origin h hout
  obtain ⟨_, _, p, _, _, hpmem, hpp⟩ := scene_output_origin h hparent
  obtain ⟨_, hbparent, hbrole, _⟩ := placeBox_metadata hp
  obtain ⟨hpid, _, hprole, _⟩ := placeBox_metadata hpp
  have hbnode : b.role ≠ .group := by
    intro he
    simp [he, BoxRole.id, hrole] at hbrole
  have hpeq : p.id = b.parent := hpid.symm.trans (hid.trans hbparent)
  have hpgroup : p.role = .group := by
    cases he : p.role with
    | group => rfl
    | node => exact False.elim ((decode_parent_not_node hg hb hpmem hbnode he) hpeq)
  simpa [hpgroup, BoxRole.id] using hprole

theorem decode_parent_precedes_node {m : Model} {g : Family}
    (h : decode m = .ok g) {b parent : ModelBox} {i j : Nat}
    (hb : (b, i) ∈ m.boxes.zipIdx) (hr : b.role ≠ .group)
    (hp : m.boxes[j]? = some parent) (hgroup : parent.role = .group)
    (hid : parent.id = b.parent) : j ≤ i := by
  apply Decidable.byContradiction
  intro hn
  have hij : i + 1 ≤ j := by omega
  have hdrop : (m.boxes.drop (i + 1))[j - (i + 1)]? = some parent := by
    rw [List.getElem?_drop]
    have he : i + 1 + (j - (i + 1)) = j := by omega
    simpa only [he] using hp
  exact (decode_parent_not_later h hb hr (List.mem_of_getElem? hdrop) hgroup) hid

theorem lane_caption_update_ids (lanes : List Lanes.Eventmodeling.Lane)
    (i : Nat) (lane : Lanes.Eventmodeling.Lane) (caption : Lanes.Caption)
    (hi : lanes[i]? = some lane) :
    (lanes.set i { lane with caption := some caption }).map (·.id) =
      lanes.map (·.id) := by
  induction lanes generalizing i with
  | nil => simp at hi
  | cons first rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst lane
      rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      simpa only [List.set_cons_succ, List.map_cons] using
        congrArg (List.cons first.id) (ih i hi)

private theorem zip_rows_x (frames : List Lanes.Eventmodeling.Frame)
    (rects : List Rect) (laneY : List Int) (padding : Int)
    (hlen : frames.length = rects.length) :
    ((frames.zip rects).map (fun pair =>
      { pair.2 with y := laneY.getD pair.1.lane 0 + padding })).map (·.x) =
      rects.map (·.x) := by
  induction frames generalizing rects with
  | nil =>
    have he : rects = [] := List.length_eq_zero_iff.mp hlen.symm
    subst rects
    rfl
  | cons frame frames ih =>
    cases rects with
    | nil => simp at hlen
    | cons rect rects =>
      have ht : frames.length = rects.length := by simpa using hlen
      simpa only [List.zip_cons_cons, List.map_cons] using
        congrArg (List.cons rect.x) (ih rects ht)

theorem family_frames_x_ordered {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r) :
    r.frames.Pairwise (fun a b => a.x < b.x) := by
  let c := Lanes.EventConsts.load profile
  let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
  have hx : raw.frames.map (·.x) =
      (Lanes.Eventmodeling.columns g c).map (·.x) := by
    exact zip_rows_x g.frames (Lanes.Eventmodeling.columns g c) _ _
      (columnWalk_length c _ _ _).symm
  have hcolumns := Lanes.Eventmodeling.eventmodeling_timeframes_ordered g profile
  have hraw : raw.frames.Pairwise (fun a b => a.x < b.x) := by
    have hm : ((Lanes.Eventmodeling.columns g c).map (·.x)).Pairwise
        (fun a b => a < b) := by
      simpa only [List.pairwise_map] using hcolumns
    rw [← hx] at hm
    simpa only [List.pairwise_map] using hm
  obtain ⟨dx, dy, hframes, _⟩ := family_frame_translation h
  rw [hframes, List.pairwise_map]
  exact hraw.imp (by
    intro a b hab
    simp only [Lanes.shiftRect]
    omega)

private theorem zip_metadata_ids (input : List ModelBox) (output : List Box)
    (hlen : input.length = output.length)
    (hids : ∀ pair ∈ input.zip output, pair.2.id = pair.1.id) :
    output.map (·.id) = input.map (·.id) := by
  induction input generalizing output with
  | nil =>
    have he : output = [] := List.length_eq_zero_iff.mp hlen.symm
    subst output
    rfl
  | cons b bs ih =>
    cases output with
    | nil => simp at hlen
    | cons out outs =>
      have hh : out.id = b.id := hids (b, out) (by simp)
      have ht : outs.map (·.id) = bs.map (·.id) :=
        ih outs (by simpa using hlen)
          (fun pair hp => hids pair (by simp [hp]))
      simp only [List.map_cons, hh, ht]

theorem scene_boxIds {m : Model} {s : Scene} (h : scene m = .ok s) :
    s.boxes.map (·.id) = m.boxes.map (·.id) := by
  obtain ⟨hlen, hmetadata⟩ := scene_boxes_metadata h
  exact zip_metadata_ids m.boxes s.boxes hlen
    (fun pair hp => (hmetadata pair hp).1)

theorem scene_boxIds_nodup {m : Model} {s : Scene}
    (hwf : WellFormed m) (h : scene m = .ok s) :
    (s.boxes.map (·.id)).Nodup := by
  rw [scene_boxIds h]
  exact Model.boxIds_nodup hwf

theorem scene_parent_lookup_is_group {m : Model} {s : Scene}
    (h : scene m = .ok s) {out parent : Box}
    (hout : out ∈ s.boxes) (hrole : out.role = "node")
    (hp : s.layoutDump.box? out.parent = some parent) :
    parent.role = "group" := by
  have hfind : s.boxes.find? (fun b => b.id == out.parent) = some parent := hp
  have hmem := List.mem_of_find?_eq_some hfind
  have hid : parent.id = out.parent := by
    have ht := List.find?_some hfind
    simpa only [beq_iff_eq] using ht
  exact scene_node_parent_is_group h hout hmem hrole hid

theorem lane_append_lookup (lanes suffix : List Lanes.Eventmodeling.Lane)
    {i : Nat} {lane : Lanes.Eventmodeling.Lane} (hi : lanes[i]? = some lane) :
    (lanes ++ suffix)[i]? = some lane := by
  induction lanes generalizing i with
  | nil => simp at hi
  | cons first rest ih =>
    cases i with
    | zero =>
      simpa only [List.cons_append, List.getElem?_cons_zero] using hi
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      simpa only [List.cons_append, List.getElem?_cons_succ] using ih hi

theorem lane_append_frame_parent
    (lanes suffix : List Lanes.Eventmodeling.Lane)
    (frame : Lanes.Eventmodeling.Frame) (parent : String)
    (hparent : (lanes[frame.lane]?).map (·.id) = some parent) :
    ((lanes ++ suffix)[frame.lane]?).map (·.id) = some parent := by
  cases hlane : lanes[frame.lane]? with
  | none => simp only [hlane, Option.map_none, reduceCtorEq] at hparent
  | some lane =>
    rw [lane_append_lookup lanes suffix hlane]
    simpa only [hlane] using hparent

theorem lane_caption_update_lookup (lanes : List Lanes.Eventmodeling.Lane)
    (i j : Nat) (lane : Lanes.Eventmodeling.Lane) (caption : Lanes.Caption)
    (hi : lanes[i]? = some lane) :
    ((lanes.set i { lane with caption := some caption })[j]?).map (·.id) =
      (lanes[j]?).map (·.id) := by
  have hids := congrArg (fun ids : List String => ids[j]?)
    (lane_caption_update_ids lanes i lane caption hi)
  simpa only [List.getElem?_map] using hids

theorem lane_caption_update_frame_parent
    (lanes : List Lanes.Eventmodeling.Lane)
    (i : Nat) (lane : Lanes.Eventmodeling.Lane) (caption : Lanes.Caption)
    (frame : Lanes.Eventmodeling.Frame) (parent : String)
    (hi : lanes[i]? = some lane)
    (hparent : (lanes[frame.lane]?).map (·.id) = some parent) :
    ((lanes.set i { lane with caption := some caption })[frame.lane]?).map
      (·.id) = some parent := by
  rw [lane_caption_update_lookup lanes i frame.lane lane caption hi]
  exact hparent

theorem scene_node_source_lane_containment {m : Model} {s : Scene}
    (h : scene m = .ok s) {out : Box} (hout : out ∈ s.boxes)
    (hrole : out.role = "node") :
    ∃ g r b i f lane, decode m = .ok g ∧
      Lanes.Eventmodeling.layout g m.profile = .ok r ∧
      b ∈ m.boxes ∧ b.role ≠ .group ∧
      out.parent = b.parent ∧
      g.frames.findIdx? (·.id == b.id) = some i ∧
      g.frames[i]? = some f ∧ r.lanes[f.lane]? = some lane ∧
      lane.Contained out.rect := by
  obtain ⟨g, r, b, hg, hr, hbmem, hp⟩ := scene_output_origin h hout
  obtain ⟨_, hparent, hroles, _⟩ := placeBox_metadata hp
  have hb : b.role ≠ .group := by
    intro he
    simp [he, BoxRole.id, hrole] at hroles
  obtain ⟨i, f, lane, hi, hf, hlane, hc⟩ :=
    placeBox_node_lane_containment hr hb hp
  exact ⟨g, r, b, i, f, lane, hg, hr, hbmem, hb, hparent,
    hi, hf, hlane, hc⟩

def FrameParents (sources : List ModelBox) (g : Family) : Prop :=
  ∀ f ∈ g.frames, ∀ b ∈ sources, b.role ≠ .group →
    f.id = b.id → b.parent ≠ "" →
    (g.lanes[f.lane]?).map (·.id) = some b.parent

theorem frameParents_empty (sources : List ModelBox) :
    FrameParents sources { lanes := [], frames := [], relations := [] } := by
  intro f hf
  simp at hf

theorem frameParents_append_lanes {sources : List ModelBox} {g : Family}
    (h : FrameParents sources g) (suffix : List Lanes.Eventmodeling.Lane) :
    FrameParents sources { g with lanes := g.lanes ++ suffix } := by
  intro f hf b hb hrole hid hparent
  exact lane_append_frame_parent g.lanes suffix f b.parent
    (h f hf b hb hrole hid hparent)

theorem frameParents_append_frame {sources : List ModelBox} {g : Family}
    (h : FrameParents sources g) (frame : Lanes.Eventmodeling.Frame)
    (hframe : ∀ b ∈ sources, b.role ≠ .group →
      frame.id = b.id → b.parent ≠ "" →
      (g.lanes[frame.lane]?).map (·.id) = some b.parent) :
    FrameParents sources { g with frames := g.frames ++ [frame] } := by
  intro f hf b hb hrole hid hparent
  rcases List.mem_append.mp hf with hf | hf
  · exact h f hf b hb hrole hid hparent
  · have he : f = frame := by simpa only [List.mem_singleton] using hf
    subst f
    exact hframe b hb hrole hid hparent

theorem nonempty_lane_ids_append_fallback (g : Family) (index : Int)
    (hids : ((g.lanes.map (·.id)).filter (· != "")).Nodup) :
    ((((g.lanes ++ [({ id := "", index := index, caption := none } :
      Lanes.Eventmodeling.Lane)]).map (·.id)).filter
      (· != "")).Nodup) := by
  simpa using hids

theorem frameParents_append_fallback {sources : List ModelBox} {g : Family}
    (hparents : FrameParents sources g)
    (hids : ((g.lanes.map (·.id)).filter (· != "")).Nodup) (index : Int) :
    let output : Family :=
      { g with lanes := g.lanes ++ [{ id := "", index := index, caption := none }] }
    FrameParents sources output ∧
      ((output.lanes.map (·.id)).filter (· != "")).Nodup := by
  exact ⟨frameParents_append_lanes hparents _,
    nonempty_lane_ids_append_fallback g index hids⟩

theorem frameParents_relations {sources : List ModelBox} {g : Family}
    (h : FrameParents sources g) (relations : List Lanes.Eventmodeling.Relation) :
    FrameParents sources { g with relations := relations } := by
  exact h

theorem frameParents_caption {sources : List ModelBox} {g : Family}
    (h : FrameParents sources g) (i : Nat) (lane : Lanes.Eventmodeling.Lane)
    (caption : Lanes.Caption) (hi : g.lanes[i]? = some lane) :
    FrameParents sources
      { g with lanes := g.lanes.set i { lane with caption := some caption } } := by
  intro f hf b hb hrole hid hparent
  exact lane_caption_update_frame_parent g.lanes i lane caption f b.parent hi
    (h f hf b hb hrole hid hparent)

theorem placeBox_group_lane_rect {g : Family} {r : Lanes.Eventmodeling.Result}
    {b : ModelBox} {out : Box} {i : Nat}
    (hrole : b.role = .group) (hp : placeBox g r b = .ok out)
    (hi : g.lanes.findIdx? (·.id == b.id) = some i) :
    r.lanes[i]? = some out.rect := by
  have hl := placeBox_lookup hp
  simp only [hrole, show (BoxRole.group == BoxRole.group) = true from rfl,
    ↓reduceIte] at hl
  obtain ⟨j, hj, hrect⟩ := hl
  have he : j = i := Option.some.inj (hj.symm.trans hi)
  simpa only [he] using hrect

theorem placeBox_parent_lane_containment
    {g : Family} {profile : Profile} {r : Lanes.Eventmodeling.Result}
    {b parent : ModelBox} {out parentOut : Box}
    (hr : Lanes.Eventmodeling.layout g profile = .ok r)
    (hb : b.role ≠ .group) (hp : placeBox g r b = .ok out)
    (hgroup : parent.role = .group)
    (hpp : placeBox g r parent = .ok parentOut)
    (hindex : ∀ i f, g.frames.findIdx? (·.id == b.id) = some i →
      g.frames[i]? = some f →
      g.lanes.findIdx? (·.id == parent.id) = some f.lane) :
    parentOut.rect.Contained out.rect := by
  obtain ⟨i, f, lane, hi, hf, hlane, hc⟩ :=
    placeBox_node_lane_containment hr hb hp
  have hparent := placeBox_group_lane_rect hgroup hpp (hindex i f hi hf)
  have he : lane = parentOut.rect := Option.some.inj (hlane.symm.trans hparent)
  exact he ▸ hc

theorem columnWalk_lane_floor (c : Lanes.EventConsts)
    (hsize : ∀ f, 0 ≤ (Lanes.Eventmodeling.frameSize c f).w + c.boxPadding)
    (frames : List Lanes.Eventmodeling.Frame) (reach : Int) (floor : List Int)
    {k : Nat} (hk : k < floor.length) :
    ∀ pair ∈ frames.zip (Lanes.Eventmodeling.columnWalk c reach floor frames),
      pair.1.lane = k → floor.getD k 0 ≤ pair.2.x := by
  induction frames generalizing reach floor with
  | nil => simp
  | cons frame frames ih =>
    intro pair hp hsame
    simp only [Lanes.Eventmodeling.columnWalk, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with he | hp
    · cases he
      dsimp only at hsame ⊢
      rw [hsame]
      exact Int.le_max_right _ _
    · let x := max (reach - c.boxOverlap + c.boxPadding) (floor.getD frame.lane 0)
      let right := x + (Lanes.Eventmodeling.frameSize c frame).w + c.boxPadding
      have hfloor : floor.getD k 0 ≤ (floor.set frame.lane right).getD k 0 := by
        by_cases he : k = frame.lane
        · have hlen : frame.lane < floor.length := he ▸ hk
          have hset : (floor.set frame.lane right).getD frame.lane 0 = right := by
            simp [List.getD_eq_getElem?_getD, hlen]
          have hx : floor.getD frame.lane 0 ≤ x := Int.le_max_right _ _
          have hw := hsize frame
          rw [he, hset]
          dsimp only [right]
          omega
        · have hne : (floor.set frame.lane right).getD k 0 = floor.getD k 0 := by
            simp [List.getD_eq_getElem?_getD, Ne.symm he]
          rw [hne]
          exact Int.le_refl _
      have ht := ih right (floor.set frame.lane right)
        (by simpa only [List.length_set] using hk) pair hp hsame
      exact Int.le_trans hfloor ht

theorem columnWalk_same_lane_disjoint (c : Lanes.EventConsts)
    (hsize : ∀ f, 0 ≤ (Lanes.Eventmodeling.frameSize c f).w + c.boxPadding)
    (hpadding : 0 ≤ c.boxPadding)
    (frames : List Lanes.Eventmodeling.Frame) (reach : Int) (floor : List Int)
    (hvalid : ∀ f ∈ frames, f.lane < floor.length) :
    (frames.zip (Lanes.Eventmodeling.columnWalk c reach floor frames)).Pairwise
      (fun a b => a.1.lane = b.1.lane →
        a.2.x + a.2.w ≤ b.2.x ∧ Disjoint a.2 b.2) := by
  induction frames generalizing reach floor with
  | nil => simp
  | cons frame frames ih =>
    rw [Lanes.Eventmodeling.columnWalk, List.zip_cons_cons, List.pairwise_cons]
    constructor
    · intro pair hp hsame
      have hk := hvalid frame (by simp)
      let x := max (reach - c.boxOverlap + c.boxPadding) (floor.getD frame.lane 0)
      let right := x + (Lanes.Eventmodeling.frameSize c frame).w + c.boxPadding
      have ht := columnWalk_lane_floor c hsize frames right
        (floor.set frame.lane right)
        (k := frame.lane) (by simpa only [List.length_set] using hk)
        pair hp hsame.symm
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hk] at ht
      change right ≤ pair.2.x at ht
      change frame.lane = pair.1.lane at hsame
      constructor
      · change x + (Lanes.Eventmodeling.frameSize c frame).w ≤ pair.2.x
        dsimp only [right] at ht
        omega
      · unfold Disjoint Rect.meetsInterior
        dsimp only
        dsimp only [right, x] at ht
        omega
    · apply ih
      intro f hf
      simpa only [List.length_set] using hvalid f (by simp [hf])

theorem family_columns_same_lane_disjoint {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r) :
    (g.frames.zip (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))).Pairwise
      (fun a b => a.1.lane = b.1.lane →
        a.2.x + a.2.w ≤ b.2.x ∧ Disjoint a.2 b.2) := by
  let c := Lanes.EventConsts.load profile
  have hpadding : 0 ≤ c.boxPadding :=
    Int.le_of_lt (Lanes.event_constants_positive profile).2.2.2.1
  have hsize : ∀ f, 0 ≤ (Lanes.Eventmodeling.frameSize c f).w + c.boxPadding := by
    intro f
    have hw := Lanes.Eventmodeling.frameSize_width_lower c f
    have hmin : 0 ≤ c.boxMinWidth := by cases profile <;> decide
    omega
  apply columnWalk_same_lane_disjoint c hsize hpadding
  intro f hf
  simpa only [List.length_replicate] using family_frame_lane_bound h hf

private theorem zip_placed_frames
    (frames : List Lanes.Eventmodeling.Frame) (rects : List Rect)
    (place : Lanes.Eventmodeling.Frame → Rect → Rect) :
    frames.zip ((frames.zip rects).map (fun pair => place pair.1 pair.2)) =
      (frames.zip rects).map (fun pair => (pair.1, place pair.1 pair.2)) := by
  induction frames generalizing rects with
  | nil => rfl
  | cons frame frames ih =>
    cases rects with
    | nil => rfl
    | cons rect rects =>
      simp only [List.zip_cons_cons, List.map_cons]
      rw [ih]

private theorem same_lane_disjoint_transport
    (pairs : List (Lanes.Eventmodeling.Frame × Rect))
    (place : Lanes.Eventmodeling.Frame → Rect → Rect)
    (hx : ∀ f rect, (place f rect).x = rect.x)
    (hw : ∀ f rect, (place f rect).w = rect.w)
    (h : pairs.Pairwise (fun a b => a.1.lane = b.1.lane →
      a.2.x + a.2.w ≤ b.2.x ∧ Disjoint a.2 b.2)) :
    (pairs.map (fun pair => (pair.1, place pair.1 pair.2))).Pairwise
      (fun a b => a.1.lane = b.1.lane →
        a.2.x + a.2.w ≤ b.2.x ∧ Disjoint a.2 b.2) := by
  induction pairs with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp h
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih hrest⟩
    intro pair hp hsame
    obtain ⟨original, hm, he⟩ := List.mem_map.mp hp
    subst pair
    have hsep := (hfirst original hm hsame).1
    dsimp only at hsep ⊢
    rw [hx, hw, hx]
    refine ⟨hsep, ?_⟩
    unfold Disjoint Rect.meetsInterior
    have hleft := hx first.1 first.2
    have hwidth := hw first.1 first.2
    have hright := hx original.1 original.2
    omega

theorem family_rows_same_lane_disjoint {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r) :
    (g.frames.zip
      (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
        (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))).frames).Pairwise
      (fun a b => a.1.lane = b.1.lane →
        a.2.x + a.2.w ≤ b.2.x ∧ Disjoint a.2 b.2) := by
  let c := Lanes.EventConsts.load profile
  let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
  change (g.frames.zip ((g.frames.zip (Lanes.Eventmodeling.columns g c)).map
    (fun pair => { pair.2 with y := raw.laneY.getD pair.1.lane 0 + c.lanePadding }))).Pairwise _
  rw [zip_placed_frames g.frames (Lanes.Eventmodeling.columns g c)
    (fun frame rect => { rect with y := raw.laneY.getD frame.lane 0 + c.lanePadding })]
  exact same_lane_disjoint_transport _
    (fun frame rect => { rect with y := raw.laneY.getD frame.lane 0 + c.lanePadding })
    (by intros; rfl) (by intros; rfl) (family_columns_same_lane_disjoint h)

private theorem same_lane_disjoint_shift
    (pairs : List (Lanes.Eventmodeling.Frame × Rect)) (dx dy : Int)
    (h : pairs.Pairwise (fun a b => a.1.lane = b.1.lane →
      a.2.x + a.2.w ≤ b.2.x ∧ Disjoint a.2 b.2)) :
    (pairs.map (fun pair => (pair.1, Lanes.shiftRect dx dy pair.2))).Pairwise
      (fun a b => a.1.lane = b.1.lane →
        a.2.x + a.2.w ≤ b.2.x ∧ Disjoint a.2 b.2) := by
  induction pairs with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp h
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih hrest⟩
    intro pair hp hsame
    obtain ⟨original, hm, he⟩ := List.mem_map.mp hp
    subst pair
    have hsep := (hfirst original hm hsame).1
    dsimp only [Lanes.shiftRect] at hsep ⊢
    constructor
    · omega
    · unfold Disjoint Rect.meetsInterior
      dsimp only [Lanes.shiftRect]
      omega

private theorem zip_shift_frames
    (frames : List Lanes.Eventmodeling.Frame) (rects : List Rect) (dx dy : Int) :
    frames.zip (rects.map (Lanes.shiftRect dx dy)) =
      (frames.zip rects).map (fun pair => (pair.1, Lanes.shiftRect dx dy pair.2)) := by
  induction frames generalizing rects with
  | nil => rfl
  | cons frame frames ih =>
    cases rects with
    | nil => rfl
    | cons rect rects =>
      simp only [List.map_cons, List.zip_cons_cons]
      rw [ih]

theorem family_frames_same_lane_disjoint {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r) :
    (g.frames.zip r.frames).Pairwise
      (fun a b => a.1.lane = b.1.lane →
        a.2.x + a.2.w ≤ b.2.x ∧ Disjoint a.2 b.2) := by
  obtain ⟨dx, dy, hframes, _⟩ := family_frame_translation h
  rw [hframes, zip_shift_frames]
  exact same_lane_disjoint_shift _ dx dy (family_rows_same_lane_disjoint h)

theorem scene_exclusive_is_node {m : Model} {s : Scene}
    (hwf : WellFormed m) (h : scene m = .ok s)
    {out : Box} (hout : out ∈ s.boxes) (hexclusive : out.exclusive = true) :
    out.role = "node" := by
  obtain ⟨_, _, b, _, _, hb, hp⟩ := scene_output_origin h hout
  obtain ⟨_, _, hrole, hexc⟩ := placeBox_metadata hp
  unfold WellFormed modelWellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  have hadmit := (List.all_eq_true.mp hwf.2) b hb
  cases hr : b.role with
  | node => simpa only [hr, BoxRole.id] using hrole
  | group =>
    have he : b.exclusive = true := hexc.symm.trans hexclusive
    simp [hr, he] at hadmit

private theorem forIn_preserves {α β : Type} (xs : List α)
    (initial output : β) (step : α → β → Except LayoutError (ForInStep β))
    (P : β → Prop) (hinit : P initial)
    (hstep : ∀ a state next, P state → step a state = .ok next → P next.value)
    (h : ForIn.forIn xs initial step = .ok output) : P output := by
  induction xs generalizing initial with
  | nil =>
    change Except.ok initial = Except.ok output at h
    cases h
    exact hinit
  | cons a xs ih =>
    rw [List.forIn_cons] at h
    cases hs : step a initial with
    | error e => simp [hs, Bind.bind, Except.bind] at h
    | ok next =>
      have hp := hstep a initial next hinit hs
      cases next with
      | done state =>
        simp only [hs, Bind.bind, Except.bind] at h
        cases h
        exact hp
      | yield state =>
        simp only [hs, Bind.bind, Except.bind] at h
        exact ih state hp h

theorem decode_route_loop_invariants {sources : List ModelBox}
    (routes : List ModelRoute) (initial output : Family)
    (hparents : FrameParents sources initial)
    (hids : ((initial.lanes.map (·.id)).filter (· != "")).Nodup)
    (h : ForIn.forIn (m := Except LayoutError) routes initial (fun route state => do
      let some src := state.frames.findIdx? (·.id == route.fromId) | throw .domain
      let some dst := state.frames.findIdx? (·.id == route.toId) | throw .domain
      pure (.yield { state with relations := state.relations ++ [{ id := route.id, src, dst }] }))
        = .ok output) :
    FrameParents sources output ∧ ((output.lanes.map (·.id)).filter (· != "")).Nodup := by
  apply forIn_preserves routes initial output _
    (fun state => FrameParents sources state ∧
      ((state.lanes.map (·.id)).filter (· != "")).Nodup)
    ⟨hparents, hids⟩ _ h
  intro route state next hp hs
  cases hsrc : state.frames.findIdx? (·.id == route.fromId) with
  | none =>
    simp [hsrc, throw, throwThe, MonadExceptOf.throw] at hs
  | some src =>
    cases hdst : state.frames.findIdx? (·.id == route.toId) with
    | none =>
      simp [hsrc, hdst, throw, throwThe, MonadExceptOf.throw] at hs
    | some dst =>
      have he : ForInStep.yield
          { state with relations := state.relations ++ [{ id := route.id, src, dst }] }
            = next := by
        simpa [hsrc, hdst, Bind.bind, Except.bind, pure, Except.pure] using hs
      cases he
      exact ⟨frameParents_relations hp.1 _, hp.2⟩

theorem decode_label_loop_invariants {sources : List ModelBox}
    (m : Model) (ids : List String) (labels : List ModelLabel)
    (initial output : Family) (hparents : FrameParents sources initial)
    (hids : ((initial.lanes.map (·.id)).filter (· != "")).Nodup)
    (h : ForIn.forIn (m := Except LayoutError) labels initial (fun label state => do
      let some i := ids.findIdx? (· == label.owner) | throw .domain
      let some lane := state.lanes[i]? | throw .domain
      let c := Lanes.EventConsts.load m.profile
      let caption ← measureCaption (fontFamily := m.options.fontFamily) m.profile .label
        (c.contentStartX - 4 * c.lanePadding) label.text
      pure (.yield { state with lanes := state.lanes.set i { lane with caption := some caption } }))
        = .ok output) :
    FrameParents sources output ∧ ((output.lanes.map (·.id)).filter (· != "")).Nodup := by
  apply forIn_preserves labels initial output _
    (fun state => FrameParents sources state ∧
      ((state.lanes.map (·.id)).filter (· != "")).Nodup)
    ⟨hparents, hids⟩ _ h
  intro label state next hp hs
  cases hi : ids.findIdx? (· == label.owner) with
  | none =>
    simp [hi, throw, throwThe, MonadExceptOf.throw] at hs
  | some i =>
    cases hlane : state.lanes[i]? with
    | none =>
      simp [hi, hlane, throw, throwThe, MonadExceptOf.throw] at hs
    | some lane =>
      cases hcap : measureCaption (fontFamily := m.options.fontFamily) m.profile .label
          ((Lanes.EventConsts.load m.profile).contentStartX -
            4 * (Lanes.EventConsts.load m.profile).lanePadding) label.text with
      | error e =>
        simp [hi, hlane, hcap, Bind.bind, Except.bind] at hs
      | ok caption =>
        have he : ForInStep.yield
            { state with lanes := state.lanes.set i { lane with caption := some caption } }
              = next := by
          simpa [hi, hlane, hcap, Bind.bind, Except.bind, pure, Except.pure] using hs
        cases he
        refine ⟨frameParents_caption hp.1 i lane caption hlane, ?_⟩
        change (((state.lanes.set i { lane with caption := some caption }).map (·.id)).filter
          (· != "")).Nodup
        rw [lane_caption_update_ids state.lanes i lane caption hlane]
        exact hp.2

theorem lane_findIdx_of_get
    {lanes : List Lanes.Eventmodeling.Lane}
    (hids : (lanes.map (·.id)).Nodup) {i : Nat}
    {lane : Lanes.Eventmodeling.Lane} (hi : lanes[i]? = some lane) :
    lanes.findIdx? (·.id == lane.id) = some i := by
  induction lanes generalizing i with
  | nil => simp at hi
  | cons first rest ih =>
    obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hids
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst lane
      rw [List.findIdx?_cons]
      simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have hne : first.id ≠ lane.id := by
        intro he
        apply hnot
        exact List.mem_map.mpr ⟨lane, List.mem_of_getElem? hi, he.symm⟩
      rw [List.findIdx?_cons]
      simp only [show (first.id == lane.id) = false from by simpa using hne,
        Bool.false_eq_true, ↓reduceIte, ih (i := i) hrest hi, Option.map_some]

theorem lane_findIdx_of_get_nonempty
    {lanes : List Lanes.Eventmodeling.Lane}
    (hids : ((lanes.map (·.id)).filter (· != "")).Nodup) {i : Nat}
    {lane : Lanes.Eventmodeling.Lane} (hi : lanes[i]? = some lane)
    (hnonempty : lane.id ≠ "") :
    lanes.findIdx? (·.id == lane.id) = some i := by
  induction lanes generalizing i with
  | nil => simp at hi
  | cons first rest ih =>
    have htail : ((rest.map (·.id)).filter (· != "")).Nodup := by
      by_cases he : first.id = ""
      · simpa [he] using hids
      · have hc : (first.id :: ((rest.map (·.id)).filter (· != ""))).Nodup := by
          simpa [he] using hids
        exact (List.nodup_cons.mp hc).2
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst lane
      rw [List.findIdx?_cons]
      simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have hne : first.id ≠ lane.id := by
        intro he
        have hfirst : first.id ≠ "" := he.symm ▸ hnonempty
        have hc : (first.id :: ((rest.map (·.id)).filter (· != ""))).Nodup := by
          simpa [hfirst] using hids
        apply (List.nodup_cons.mp hc).1
        apply List.mem_filter.mpr
        refine ⟨List.mem_map.mpr ⟨lane, List.mem_of_getElem? hi, he.symm⟩, ?_⟩
        simpa using hfirst
      rw [List.findIdx?_cons]
      simp only [show (first.id == lane.id) = false from by simpa using hne,
        Bool.false_eq_true, ↓reduceIte, ih (i := i) htail hi, Option.map_some]
theorem frameParents_parent_index {sources : List ModelBox} {g : Family}
    (hparents : FrameParents sources g)
    (hids : ((g.lanes.map (·.id)).filter (· != "")).Nodup)
    {b : ModelBox} (hb : b ∈ sources) (hrole : b.role ≠ .group)
    (hparent : b.parent ≠ "") {f : Lanes.Eventmodeling.Frame}
    (hf : f ∈ g.frames) (hid : f.id = b.id) :
    g.lanes.findIdx? (·.id == b.parent) = some f.lane := by
  have hp := hparents f hf b hb hrole hid hparent
  cases hlane : g.lanes[f.lane]? with
  | none => simp only [hlane, Option.map_none, reduceCtorEq] at hp
  | some lane =>
    have he : lane.id = b.parent := by
      simpa only [hlane, Option.map_some, Option.some.injEq] using hp
    rw [← he]
    exact lane_findIdx_of_get_nonempty hids hlane (he.symm ▸ hparent)

theorem placeBox_parent_containment_of_frameParents
    {sources : List ModelBox} {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result}
    (hparents : FrameParents sources g)
    (hids : ((g.lanes.map (·.id)).filter (· != "")).Nodup)
    (hr : Lanes.Eventmodeling.layout g profile = .ok r)
    {b parent : ModelBox} {out parentOut : Box}
    (hb : b ∈ sources) (hrole : b.role ≠ .group) (hparent : b.parent ≠ "")
    (hid : parent.id = b.parent) (hgroup : parent.role = .group)
    (hp : placeBox g r b = .ok out) (hpp : placeBox g r parent = .ok parentOut) :
    parentOut.rect.Contained out.rect := by
  apply placeBox_parent_lane_containment hr hrole hp hgroup hpp
  intro i f hi hf
  obtain ⟨hib, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
  have he : g.frames[i] = f := by
    have hget : g.frames[i]? = some g.frames[i] := List.getElem?_eq_getElem hib
    exact Option.some.inj (hget.symm.trans hf)
  have hfid : f.id = b.id := by
    rw [he] at hmatch
    exact beq_iff_eq.mp hmatch
  rw [hid]
  exact frameParents_parent_index hparents hids hb hrole hparent
    (List.mem_of_getElem? hf) hfid

theorem scene_c3_of_decode_invariants {m : Model} {s : Scene}
    (h : scene m = .ok s)
    (hdecode : ∀ g, decode m = .ok g →
      FrameParents m.boxes g ∧ ((g.lanes.map (·.id)).filter (· != "")).Nodup) :
    Validator.C3 s.layoutDump := by
  obtain ⟨g, r, hg, hr, _⟩ := scene_boxes_correspond h
  obtain ⟨hparents, hids⟩ := hdecode g hg
  intro out hout hnonempty parent hlookup
  have houtmem : out ∈ s.boxes := hout
  have hfind : s.boxes.find? (fun b => b.id == out.parent) = some parent := hlookup
  have hparentmem := List.mem_of_find?_eq_some hfind
  have hparentid : parent.id = out.parent := by
    simpa only [beq_iff_eq] using List.find?_some hfind
  obtain ⟨g', r', b, hg', hr', hb, hp⟩ := scene_output_origin h houtmem
  have heg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have her : r' = r := Except.ok.inj (hr'.symm.trans hr)
  subst r'
  obtain ⟨g', r', p, hg', hr', _, hpp⟩ := scene_output_origin h hparentmem
  have heg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have her : r' = r := Except.ok.inj (hr'.symm.trans hr)
  subst r'
  obtain ⟨_, hbparent, _, _⟩ := placeBox_metadata hp
  obtain ⟨hpid, _, hprole, _⟩ := placeBox_metadata hpp
  have hrole : b.role ≠ .group := by
    intro he
    exact hnonempty (hbparent.trans (decode_group_parent hg hb he))
  have hnoderole : out.role = "node" := by
    have hm := (placeBox_metadata hp).2.2.1
    cases he : b.role with
    | node => simpa only [he, BoxRole.id] using hm
    | group => exact False.elim (hrole he)
  have hpgroup : p.role = .group := by
    have hs := scene_node_parent_is_group h houtmem hparentmem hnoderole hparentid
    cases he : p.role with
    | group => rfl
    | node => simp [he, BoxRole.id, hs] at hprole
  exact placeBox_parent_containment_of_frameParents hparents hids hr hb hrole
    (fun he => hnonempty (hbparent.trans he))
    (hpid.symm.trans (hparentid.trans hbparent)) hpgroup hp hpp


theorem frameParents_parent_index_nonempty {sources : List ModelBox} {g : Family}
    (hparents : FrameParents sources g)
    (hids : ((g.lanes.map (·.id)).filter (· != "")).Nodup)
    {b : ModelBox} (hb : b ∈ sources) (hrole : b.role ≠ .group)
    (hparent : b.parent ≠ "") {f : Lanes.Eventmodeling.Frame}
    (hf : f ∈ g.frames) (hid : f.id = b.id) :
    g.lanes.findIdx? (·.id == b.parent) = some f.lane := by
  have hp := hparents f hf b hb hrole hid hparent
  cases hlane : g.lanes[f.lane]? with
  | none => simp only [hlane, Option.map_none, reduceCtorEq] at hp
  | some lane =>
    have he : lane.id = b.parent := by
      simpa only [hlane, Option.map_some, Option.some.injEq] using hp
    rw [← he]
    exact lane_findIdx_of_get_nonempty hids hlane (he.symm ▸ hparent)

theorem eventmodeling_c3_of_decode_invariants
    {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result)
    (hdecode : ∀ g, decode m = .ok g →
      FrameParents m.boxes g ∧ ((g.lanes.map (·.id)).filter (· != "")).Nodup) :
    Validator.C3 result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact scene_c3_of_decode_invariants hs hdecode


private theorem same_lane_pairwise_members
    (pairs : List (Lanes.Eventmodeling.Frame × Rect))
    (h : pairs.Pairwise (fun a b => a.1.lane = b.1.lane →
      a.2.x + a.2.w ≤ b.2.x ∧ Disjoint a.2 b.2))
    {a b : Lanes.Eventmodeling.Frame × Rect}
    (ha : a ∈ pairs) (hb : b ∈ pairs) (hne : a ≠ b)
    (hlane : a.1.lane = b.1.lane) : Disjoint a.2 b.2 := by
  induction pairs with
  | nil => simp at ha
  | cons first rest ih =>
    obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with he | ha
    · subst a
      rcases List.mem_cons.mp hb with he | hb
      · exact False.elim (hne he.symm)
      · exact (hfirst b hb hlane).2
    · rcases List.mem_cons.mp hb with he | hb
      · subst b
        exact (Disjoint.comm first.2 a.2).mp (hfirst a ha hlane.symm).2
      · exact ih hrest ha hb

theorem family_same_lane_disjoint {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r)
    {i j : Nat} {f f' : Lanes.Eventmodeling.Frame} {rect rect' : Rect}
    (hf : g.frames[i]? = some f) (hf' : g.frames[j]? = some f')
    (hr : r.frames[i]? = some rect) (hr' : r.frames[j]? = some rect')
    (hid : f.id ≠ f'.id) (hlane : f.lane = f'.lane) :
    Disjoint rect rect' := by
  have ha : (f, rect) ∈ g.frames.zip r.frames :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hf, hr⟩)
  have hb : (f', rect') ∈ g.frames.zip r.frames :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hf', hr'⟩)
  apply same_lane_pairwise_members _ (family_frames_same_lane_disjoint h) ha hb
    (fun he => hid (congrArg (fun pair : Lanes.Eventmodeling.Frame × Rect =>
      pair.1.id) he)) hlane

theorem placeBox_same_lane_disjoint
    {g : Family} {profile : Profile} {r : Lanes.Eventmodeling.Result}
    {b b' : ModelBox} {out out' : Box}
    (hr : Lanes.Eventmodeling.layout g profile = .ok r)
    (hb : b.role ≠ .group) (hb' : b'.role ≠ .group)
    (hp : placeBox g r b = .ok out) (hp' : placeBox g r b' = .ok out')
    (hid : b.id ≠ b'.id)
    (hlane : ∀ i j f f',
      g.frames.findIdx? (·.id == b.id) = some i →
      g.frames.findIdx? (·.id == b'.id) = some j →
      g.frames[i]? = some f → g.frames[j]? = some f' → f.lane = f'.lane) :
    Disjoint out.rect out'.rect := by
  have hlookup := placeBox_lookup hp
  have hlookup' := placeBox_lookup hp'
  simp only [show (b.role == .group) = false from by simpa using hb,
    Bool.false_eq_true, ↓reduceIte] at hlookup
  simp only [show (b'.role == .group) = false from by simpa using hb',
    Bool.false_eq_true, ↓reduceIte] at hlookup'
  obtain ⟨i, hi, hrect⟩ := hlookup
  obtain ⟨j, hj, hrect'⟩ := hlookup'
  obtain ⟨hib, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
  obtain ⟨hjb, hmatch', _⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
  have hf : g.frames[i]? = some g.frames[i] := List.getElem?_eq_getElem hib
  have hf' : g.frames[j]? = some g.frames[j] := List.getElem?_eq_getElem hjb
  have hfid : g.frames[i].id = b.id := beq_iff_eq.mp hmatch
  have hfid' : g.frames[j].id = b'.id := beq_iff_eq.mp hmatch'
  exact family_same_lane_disjoint hr hf hf' hrect hrect'
    (fun he => hid (hfid.symm.trans (he.trans hfid')))
    (hlane i j g.frames[i] g.frames[j] hi hj hf hf')

theorem contained_rects_disjoint {lane lane' rect rect' : Rect}
    (h : Disjoint lane lane') (hc : lane.Contained rect)
    (hc' : lane'.Contained rect') : Disjoint rect rect' := by
  unfold Disjoint Rect.meetsInterior at h ⊢
  unfold Rect.Contained at hc hc'
  omega

def orthogonalVectorWitness : Model :=
  { kind := "eventmodeling"
    profile := .vector
    boxes :=
      [{ id := "g0", role := .group, exclusive := false, shape := "lane:0" },
       { id := "g1", role := .group, exclusive := false, shape := "lane:1" },
       { id := "n0", parent := "g0", shape := "event", text := some "A" },
       { id := "n1", parent := "g1", shape := "event", text := some "B" }]
    routes := [{ id := "e", fromId := "n0", toId := "n1", orthogonal := true }] }

theorem orthogonalVectorWitness_wellFormed : WellFormed orthogonalVectorWitness := by
  decide

theorem orthogonalVectorWitness_withinLimits : WithinLimits orthogonalVectorWitness := by
  decide

end Elegant.Kinds.Eventmodeling

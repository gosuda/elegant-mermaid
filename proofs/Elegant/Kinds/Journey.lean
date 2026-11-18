import Elegant.Kinds.Common
import Elegant.Kinds.Timeline
import Elegant.LanesJourney

set_option autoImplicit false
namespace Elegant.Kinds.Journey
open Common Lanes
open Lanes.Journey

def styledRuns (p : Profile) (source : String) (lines : List Measure.Line) :
    List (List TextRun) :=
  let tagged := (Label.regions source.toList).flatMap fun region =>
    (region.runs.flatMap fun r => r.text.map fun ch =>
      ((if p == .cell then StyledMeasure.normalizeCellChar ch else ch), r.bold, r.italic)) ++
      region.separator.map (fun ch => (ch, false, false))
  (lines.foldl (fun (state : Nat × List (List TextRun)) line =>
    let chars := (tagged.drop state.1).take line.text.length
    let runs := chars.foldl (fun (acc : List TextRun) (ch, bold, italic) =>
      match acc with
      | r :: rest =>
        if r.bold == bold && r.italic == italic then
          { r with text := r.text.push ch } :: rest
        else { text := String.singleton ch, bold, italic } :: acc
      | [] => [{ text := String.singleton ch, bold, italic }]) []
    (state.1 + line.text.length + line.sep.length, state.2 ++ [runs.reverse]))
    (0, [])).2

def textItem (m : Model) (id : String) (cap : Caption) (rect : Rect) (align : Align) :
    Primitive :=
  let source := ((m.boxes.find? (·.id == id)).map (boxText m)).getD ""
  .text { rect := rect, role := cap.role, size := if cap.role == .title then 16 else 14, align := align, style := "text", lines := styledRuns m.profile source cap.lines }

def shapeKind (b : ModelBox) : String :=
  let k := (b.shape.splitOn ":").headD ""
  if k == "" then "task" else k

/-- A box declares the people card by shape `people` or a `people:`-prefixed form. This is the
decidable classification the decoder's `shapeKind` match resolves to for every people box. -/
def isPeople (b : ModelBox) : Bool :=
  b.shape == "people" || b.shape.startsWith "people:"

def load (m : Model) : Except LayoutError Constants := do
  let mut c := constants m.profile
  if m.profile == .vector then
    for (key, value) in m.options.config do
      let px ← match value with
        | .integer n => pure n
        | .string s => match s.toInt? with
          | some n => pure n
          | none => throw .overflow
        | _ => throw .overflow
      if px < 0 || px * 64 > COORD_LIMIT then throw .overflow
      if px > 0 then
        if key == "width" then c := { c with taskWidth := px * 64 }
        if key == "height" then c := { c with taskHeight := px * 64, bandHeight := px * 64 }
        if key == "diagramMarginX" then c := { c with columnGap := px * 64 }
  return c

def target (c : Constants) (n : Nat) : Int :=
  let slots : Int := max 1 n
  max (slots * c.taskWidth + (slots - 1) * c.columnGap - 2 * c.padX) 1

def decode (m : Model) (c : Constants) : Except LayoutError Input := do
  let mut g : Input := {}
  for b in m.boxes do
    match shapeKind b with
    | "title" =>
      if b.parent != "" then throw .domain
      let caption ← Timeline.measureCaption m.profile .title I32_MAX (boxText m b)
      g := { g with title := some { id := b.id, caption } }
    | "section" =>
      if b.parent != "" then throw .domain
      let n := (m.boxes.filter fun t => shapeKind t == "task" && t.parent == b.id).length
      let caption ← Timeline.measureCaption m.profile .label (target c n) (boxText m b)
      g := { g with sections := g.sections ++ [{ id := b.id, caption }] }
    | "task" =>
      let score ← if b.shape == "" then pure 1 else
        match (b.shape.splitOn ":").tail.head? >>= String.toInt? with
        | some n => pure n
        | none => throw .domain
      if score < 1 || score > 5 then throw .domain
      let band ← if b.parent == "" then pure (-1) else
        match g.sections.findIdx? (·.id == b.parent) with
        | some i => pure (i : Int)
        | none => throw .domain
      let caption ← Timeline.measureCaption m.profile .label (target c 1) (boxText m b)
      g := { g with tasks := g.tasks ++ [{ id := b.id, caption, band, score }] }
    | "people" =>
      let some t := g.tasks.getLast? | throw .domain
      if t.id != b.parent then throw .domain
      let cap ← Timeline.measureCaption m.profile .body (target c 1) (boxText m b)
      g := { g with tasks := g.tasks.set (g.tasks.length - 1) { t with people := some cap } }
    | _ => throw .domain
  return g

def finish (m : Model) (canvas : Size) (boxes : List Box) (items : List Group) :
    Except LayoutError Scene :=
  if ([canvas.w, canvas.h] ++ boxes.flatMap (fun b => rectValues 0 0 b.rect)).all withinLimit then
    pure {
      kind := m.kind
      profile := m.profile
      options := m.options
      canvas := canvas
      boxes := boxes
      routes := []
      labels := []
      items := items }
  else throw .overflow

def scene (m : Model) : Except LayoutError Scene := do
  let c ← load m
  let g ← decode m c
  let bandH := g.sections.foldl (fun h s => max h (s.caption.h + 2 * c.padY)) c.bandHeight
  let taskH := g.tasks.foldl (fun h t => max h
    (t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY)) c.taskHeight
  let top := (g.title.map fun t => t.caption.h + c.scoreStep).getD 0
  let taskTop := top + bandH + 6 * c.scoreStep
  let tasks := g.tasks.zipIdx.map fun (_, i) => taskRect c taskTop taskH i
  let faces := g.tasks.zipIdx.map fun (t, i) =>
    (⟨column c i + half c.taskWidth, faceY c (top + bandH) t.score⟩ : Point)
  let mut frames : List Rect := []
  let mut bands : List Rect := []
  for (_, i) in g.sections.zipIdx do
    let indices := (g.tasks.zipIdx.filter fun (t, _) => t.band == (i : Int)).map (·.2)
    let some first := indices.head? | throw .domain
    let last := indices.getLast?.getD first
    if !(g.tasks.zipIdx.all fun (t, k) =>
        decide (first ≤ k ∧ k ≤ last) == (t.band == (i : Int))) then throw .domain
    frames := frames ++ [sectionRect c top (taskTop + taskH - top) first last]
    bands := bands ++ [sectionRect c top bandH first last]
  let title : Rect := (g.title.map fun t => ⟨0, 0, t.caption.w, t.caption.h⟩).getD zeroRect
  let faceBoxes := faces.map fun p => if m.profile == .cell then
      (⟨p.x, p.y, 1, 1⟩ : Rect) else ⟨p.x-c.radius, p.y-c.radius, 2*c.radius, 2*c.radius⟩
  let all := g.title.toList.map (fun _ => title) ++ frames ++ tasks ++ faceBoxes
  let ext := match all with
    | [] => zeroRect
    | r :: rs => rs.foldl Rect.unionRaw r
  let dx := c.margin - ext.x
  let dy := c.margin - ext.y
  let shift := shiftRect dx dy
  let mut assigned : List (String × Rect) := []
  let mut items : List Group := []
  for (s, i) in g.sections.zipIdx do
    let band := bands.getD i zeroRect
    assigned := assigned ++ [(s.id, shift (frames.getD i zeroRect))]
    let bandItems := [Primitive.roundRect (shift band) c.corner { style := "series-tint", series := fin12 i, width := .emphasis }, textItem m s.id s.caption (shift (centred c band s.caption.h)) .middle]
    items := items ++ [{ role := .group, owner := s.id, items := bandItems }]
  if let some t := g.title then
    assigned := assigned ++ [(t.id, shift title)]
    items := items ++ [{ role := .node, owner := t.id, items := [textItem m t.id t.caption (shift title) .middle] }]
  for (t, i) in g.tasks.zipIdx do
    let card := tasks.getD i zeroRect
    let block := centred c card (t.caption.h + (t.people.map (·.h)).getD 0)
    let name := { block with h := t.caption.h }
    let people := { block with y := block.y + t.caption.h, h := (t.people.map (·.h)).getD 0 }
    assigned := assigned ++ [(t.id, shift card)]
    for b in m.boxes do
      if shapeKind b == "people" && b.parent == t.id then
        assigned := assigned ++ [(b.id, shift people)]

    let paint : Paint := if t.band < 0 then plain "node" else
      { style := "series-tint", series := fin12 t.band.toNat }
    let peopleId := ((m.boxes.find? fun b => shapeKind b == "people" && b.parent == t.id).map (·.id)).getD ""
    let personItems := t.people.toList.map fun cap =>
      match textItem m peopleId cap (shift people) .middle with
      | .text txt => Primitive.text { txt with style := "text-muted" }
      | other => other
    let taskItems := [Primitive.roundRect (shift card) c.corner paint] ++ face m.profile c (shiftPoint dx dy (faces.getD i ⟨0,0⟩)) t.score ++ [textItem m t.id t.caption (shift name) .middle] ++ personItems
    items := items ++ [{ role := .node, owner := t.id, items := taskItems }]
  let boxes ← m.boxes.mapM fun b => do
    let some (_, rect) := assigned.find? (fun p => p.1 == b.id) | throw .domain
    pure (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box)
  finish m ⟨ext.w + 2*c.margin, ext.h + 2*c.margin⟩ boxes items

def uniquePeopleParents (m : Model) : Bool :=
  decide (((m.boxes.filter isPeople).map (·.parent)).Nodup)

/-- The same uniqueness test over the decoder's own `shapeKind` classification. The two
spellings agree, so admitting both changes no accepted input. -/
def uniqueDecodedPeopleParents (m : Model) : Bool :=
  decide (((m.boxes.filter fun b => shapeKind b == "people").map (·.parent)).Nodup)

/-- A box id must not be the empty root marker: the adapter keys people attachments by a
task's id, so an empty task id would make the attachment look like a root sibling. -/
def emptyBoxId (m : Model) : Bool :=
  m.boxes.any fun b => b.id == ""

/-- The adapter's admission test: no box id is the empty root marker, and at most one people
attachment names each parent, under both the declared-shape and decoded classifications. -/
def admitted (m : Model) : Bool :=
  !emptyBoxId m && (uniquePeopleParents m && uniqueDecodedPeopleParents m)

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  if admitted m then
    match scene m with
    | .error e => .error (.geometry e)
    | .ok s => .ok { scene := s, budgetExhausted := false }
  else .error (.geometry .domain)


def repeatedPeopleWitness : Model :=
  { kind := "journey"
    profile := .vector
    boxes :=
      [{ id := "task", shape := "task:3" },
       { id := "people0", parent := "task", shape := "people" },
       { id := "people1", parent := "task", shape := "people" }]
    labels :=
      [{ id := "task.label", owner := "task", text := "Task" },
       { id := "people0.label", owner := "people0", text := "Alice" },
       { id := "people1.label", owner := "people1", text := "Bob" }] }

theorem repeatedPeopleWitness_wellFormed : WellFormed repeatedPeopleWitness := by
  decide

theorem repeatedPeopleWitness_withinLimits : WithinLimits repeatedPeopleWitness := by
  decide

def repeatedPeopleGroupWitness : Model :=
  { repeatedPeopleWitness with
    boxes :=
      [{ id := "task", shape := "task:3" },
       { id := "people0", role := .group, exclusive := false,
         parent := "task", shape := "people" },
       { id := "people1", role := .group, exclusive := false,
         parent := "task", shape := "people" }] }

theorem repeatedPeopleGroupWitness_wellFormed :
    WellFormed repeatedPeopleGroupWitness := by
  decide

theorem repeatedPeopleGroupWitness_withinLimits :
    WithinLimits repeatedPeopleGroupWitness := by
  decide

theorem repeatedPeopleGroupWitness_nonsection_group :
    ∃ b ∈ repeatedPeopleGroupWitness.boxes,
      b.role = .group ∧ b.shape = "people" := by
  decide


theorem wellFormed_group_nonexclusive {m : Model} (hw : WellFormed m)
    {b : ModelBox} (hb : b ∈ m.boxes) (hr : b.role = .group) :
    b.exclusive = false := by
  unfold WellFormed modelWellFormed at hw
  simp only [Bool.and_eq_true] at hw
  have h := List.all_eq_true.mp hw.2 b hb
  simpa [hr] using h


private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : (x >>= f) = .ok y) :
    ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem finish_ok {m : Model} {canvas : Size} {boxes : List Box} {items : List Group}
    {s : Scene} (h : finish m canvas boxes items = .ok s) :
    s.routes = [] ∧ s.labels = [] ∧ s.canvas = canvas ∧ s.boxes = boxes ∧
      ([canvas.w, canvas.h] ++ boxes.flatMap (fun b => rectValues 0 0 b.rect)).all
        withinLimit = true := by
  unfold finish at h
  split at h
  · rename_i hc
    cases h
    exact ⟨rfl, rfl, rfl, rfl, hc⟩
  · cases h

theorem scene_routes_labels_empty {m : Model} {s : Scene}
    (h : scene m = .ok s) : s.routes = [] ∧ s.labels = [] := by
  unfold scene at h
  obtain ⟨c, _, h⟩ := bind_ok h
  obtain ⟨g, _, h⟩ := bind_ok h
  obtain ⟨framesBands, _, h⟩ := bind_ok h
  obtain ⟨assignedItems, _, h⟩ := bind_ok h
  rcases ht : g.title with _ | titleVal <;> simp only [ht] at h
  all_goals
    obtain ⟨assignedItems2, _, h⟩ := bind_ok h
    obtain ⟨boxes, _, h⟩ := bind_ok h
    obtain ⟨hr, hl, _⟩ := finish_ok h
    exact ⟨hr, hl⟩

theorem layout_admitted {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : admitted m = true := by
  unfold layout at h
  split at h
  · rename_i ha
    exact ha
  · cases h

theorem layout_scene {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : scene m = .ok result.scene := by
  unfold layout at h
  split at h
  · split at h
    · cases h
    · rename_i hs
      simp only [Except.ok.injEq] at h
      cases h
      exact hs
  · cases h

/-- The adapter admits no box whose id is the empty root marker. -/
theorem layout_box_ids_nonempty {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : ∀ box ∈ m.boxes, box.id ≠ "" := by
  have ha := layout_admitted h
  intro box hbox hid
  have hany : emptyBoxId m = true := by
    apply List.any_eq_true.mpr
    exact ⟨box, hbox, by simpa [emptyBoxId] using hid⟩
  unfold admitted at ha
  rw [hany] at ha
  exact absurd ha (by simp)

/-- The adapter admits at most one people attachment per parent id. -/
theorem layout_unique_people_parents {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : uniquePeopleParents m = true := by
  have ha := layout_admitted h
  unfold admitted at ha
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
  exact ha.2.1

/-- The decoder's own people classification also names at most one attachment per parent. -/
theorem layout_unique_decoded_people_parents {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : uniqueDecodedPeopleParents m = true := by
  have ha := layout_admitted h
  unfold admitted at ha
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
  exact ha.2.2

theorem repeatedPeopleWitness_rejected :
    layout repeatedPeopleWitness = .error (.geometry .domain) := by
  have hp : uniquePeopleParents repeatedPeopleWitness = false := by decide
  have hadm : admitted repeatedPeopleWitness = false := by simp [admitted, hp]
  simp only [layout, hadm, Bool.false_eq_true, ↓reduceIte]

theorem repeatedPeopleGroupWitness_rejected :
    layout repeatedPeopleGroupWitness = .error (.geometry .domain) := by
  have hp : uniquePeopleParents repeatedPeopleGroupWitness = false := by decide
  have hadm : admitted repeatedPeopleGroupWitness = false := by simp [admitted, hp]
  simp only [layout, hadm, Bool.false_eq_true, ↓reduceIte]

theorem journey_c4 {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : Validator.C4 result.scene.layoutDump := by
  have he := (scene_routes_labels_empty (layout_scene h)).1
  simp [Validator.C4, Scene.layoutDump, he]

theorem journey_c5 {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : Validator.C5 result.scene.layoutDump := by
  have he := (scene_routes_labels_empty (layout_scene h)).1
  simp [Validator.C5, Scene.layoutDump, he]

theorem journey_c6 {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : Validator.C6 result.scene.layoutDump := by
  have he := (scene_routes_labels_empty (layout_scene h)).1
  simp [Validator.C6, Scene.layoutDump, he]

theorem journey_c7 {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : Validator.C7 result.scene.layoutDump := by
  have hr := (scene_routes_labels_empty (layout_scene h)).1
  have hl := (scene_routes_labels_empty (layout_scene h)).2
  simp [Validator.C7, Scene.layoutDump, hr, hl]

theorem journey_c8b {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : Validator.C8b result.scene.layoutDump := by
  have hl := (scene_routes_labels_empty (layout_scene h)).2
  simp [Validator.C8b, Scene.layoutDump, hl]

theorem scene_coordinates_checked {m : Model} {s : Scene}
    (h : scene m = .ok s) :
    ([s.canvas.w, s.canvas.h] ++
      s.boxes.flatMap (fun b => rectValues 0 0 b.rect)).all withinLimit = true := by
  unfold scene at h
  obtain ⟨c, _, h⟩ := bind_ok h
  obtain ⟨g, _, h⟩ := bind_ok h
  obtain ⟨framesBands, _, h⟩ := bind_ok h
  obtain ⟨assignedItems, _, h⟩ := bind_ok h
  rcases ht : g.title with _ | titleVal <;> simp only [ht] at h
  all_goals
    obtain ⟨assignedItems2, _, h⟩ := bind_ok h
    obtain ⟨boxes, _, h⟩ := bind_ok h
    obtain ⟨_, _, hcanvas, hboxes, hc⟩ := finish_ok h
    rw [hcanvas, hboxes]
    exact hc

theorem journey_coordinates_checked {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    ([result.scene.canvas.w, result.scene.canvas.h] ++
      result.scene.boxes.flatMap (fun b => rectValues 0 0 b.rect)).all withinLimit = true :=
  scene_coordinates_checked (layout_scene h)

theorem journey_unique_people_parents {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    ((m.boxes.filter isPeople).map (·.parent)).Nodup :=
  of_decide_eq_true (layout_unique_people_parents h)

theorem scene_finish_witness {m : Model} {s : Scene}
    (h : scene m = .ok s) :
    ∃ canvas boxes items, finish m canvas boxes items = .ok s := by
  unfold scene at h
  obtain ⟨c, _, h⟩ := bind_ok h
  obtain ⟨g, _, h⟩ := bind_ok h
  obtain ⟨framesBands, _, h⟩ := bind_ok h
  obtain ⟨assignedItems, _, h⟩ := bind_ok h
  rcases ht : g.title with _ | titleVal <;> simp only [ht] at h
  all_goals
    obtain ⟨assignedItems2, _, h⟩ := bind_ok h
    obtain ⟨boxes, _, h⟩ := bind_ok h
    exact ⟨_, boxes, _, h⟩

theorem journey_route_label_constraints {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) :
    Validator.C4 result.scene.layoutDump ∧
    Validator.C5 result.scene.layoutDump ∧
    Validator.C6 result.scene.layoutDump ∧
    Validator.C7 result.scene.layoutDump ∧
    Validator.C8b result.scene.layoutDump :=
  ⟨journey_c4 h, journey_c5 h, journey_c6 h, journey_c7 h, journey_c8b h⟩
theorem journey_box_coordinates_checked {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) {b : Box} (hb : b ∈ result.scene.boxes) :
    (rectValues 0 0 b.rect).all withinLimit = true := by
  have hc := journey_coordinates_checked h
  have hall := List.all_eq_true.mp hc
  apply List.all_eq_true.mpr
  intro v hv
  apply hall v
  apply List.mem_append.mpr
  right
  exact List.mem_flatMap.mpr ⟨b, hb, hv⟩

theorem journey_canvas_coordinates_checked {m : Model}
    {result : Layered.FamilyResult} (h : layout m = .ok result) :
    withinLimit result.scene.canvas.w = true ∧
      withinLimit result.scene.canvas.h = true := by
  have hc := journey_coordinates_checked h
  have hall := List.all_eq_true.mp hc
  constructor
  · apply hall
    exact List.mem_append.mpr (Or.inl (by simp))
  · apply hall
    exact List.mem_append.mpr (Or.inl (by simp))

end Elegant.Kinds.Journey

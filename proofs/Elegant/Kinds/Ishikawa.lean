import Elegant.Kinds.Common
import Elegant.Ishikawa
import Elegant.StyledMeasure
import Elegant.TreeValid

set_option autoImplicit false
namespace Elegant.Kinds.Ishikawa
open Common

def params (p : Profile) : Elegant.Ishikawa.Params :=
  ⟨LayoutConst.ishikawa_spine_base_length.get p, LayoutConst.ishikawa_rib_min_length.get p,
   LayoutConst.ishikawa_rib_pool.get p, LayoutConst.ishikawa_cause_min_spacing.get p,
   LayoutConst.ishikawa_bone_stub.get p, LayoutConst.ishikawa_bone_base.get p,
   LayoutConst.ishikawa_bone_per_child.get p, LayoutConst.ishikawa_spine_inset.get p,
   LayoutConst.ishikawa_rib_cos_q15.get p, LayoutConst.ishikawa_rib_sin_q15.get p⟩

structure Input where
  nodes : List Tree.Node := []
  depths : List Nat := []
  lines : List (List Measure.Line) := []
  source : List String := []

def styledLines (profile : Profile) (source : String) (lines : List Measure.Line) :
    List (List TextRun) := Id.run do
  let chars := (Label.regions source.toList).flatMap fun region =>
    (region.runs.flatMap fun r =>
      let text := if profile == .cell then StyledMeasure.normalizeCellText r.text else r.text
      text.map fun c => (c, r.bold, r.italic)) ++
      region.separator.map (fun c => (c, false, false))
  let mut offset := 0
  let mut result := []
  for line in lines do
    let slice := (chars.drop offset).take line.text.length
    let runs := slice.foldl (fun (out : List TextRun) (c, bold, italic) =>
      match out.getLast? with
      | some last => if last.bold == bold && last.italic == italic then
          out.set (out.length - 1) { last with text := last.text ++ String.singleton c }
        else out ++ [⟨String.singleton c, bold, italic⟩]
      | none => [⟨String.singleton c, bold, italic⟩]) []
    result := result ++ [runs]
    offset := offset + line.text.length + line.sep.length
  return result

def decode (m : Model) : Except LayoutError Input := do
  let metric ← labelMetric m.profile
  let target := if m.profile == .vector then 12800 else if m.options.maxWidth > 0 then m.options.maxWidth else 32
  let mut input : Input := {}
  let mut path : List Nat := []
  let mut anchors := false
  for (b, i) in m.boxes.zipIdx do
    if b.shape == "anchor" then anchors := true
    else
      if anchors then throw .domain
      let depth ← if i == 0 && (b.shape == "effect" || b.shape == "") then pure 0 else do
        match b.shape.splitOn ":" with
        | ["cause", d] => match d.toNat? with
          | some n => if 1 ≤ n && n ≤ 64 then pure n else throw .domain
          | none => throw .domain
        | _ => throw .domain
      if depth > path.length then throw .domain
      let parent := if depth == 0 then none else path[depth - 1]?
      path := path.take depth ++ [i]
      let text := (m.labels.find? (·.owner == b.id)).map (·.text) |>.getD b.id
      let lines ← StyledMeasure.wrap metric target text.toList
      let pad := LayoutConst.node_pad_x.get m.profile
      let border := LayoutConst.node_border.get m.profile
      let lh := LayoutConst.line_h.get m.profile
      let w := widest lines + 2 * pad
      let h := (max 1 lines.length : Nat) * lh
      let w := if depth ≤ 1 then max (w + 2 * border) (LayoutConst.node_min_w.get m.profile) else w
      let h := if depth ≤ 1 then max (h + 2 * LayoutConst.node_pad_y.get m.profile + 2 * border) (LayoutConst.node_min_h.get m.profile) else h
      if w > COORD_LIMIT || h > COORD_LIMIT then throw .overflow
      input := {
        nodes := input.nodes ++ [⟨parent, max w 1, max h 1⟩]
        depths := input.depths ++ [depth]
        lines := input.lines ++ [lines]
        source := input.source ++ [text] }
  return input

theorem decoded_cause_depth_bounds (shape : String) (depth : Nat)
    (h : ((match shape.splitOn ":" with
      | ["cause", d] => match d.toNat? with
        | some n => if 1 ≤ n && n ≤ 64 then pure n
          else throw LayoutError.domain
        | none => throw LayoutError.domain
      | _ => throw LayoutError.domain) : Except LayoutError Nat) = .ok depth) :
    1 ≤ depth ∧ depth ≤ 64 := by
  generalize shape.splitOn ":" = parts at h
  cases parts with
  | nil => cases h
  | cons tag rest =>
    cases rest with
    | nil => simp at h
    | cons digits rest =>
      cases rest with
      | cons extra tail => simp at h
      | nil =>
        by_cases htag : tag = "cause"
        · subst tag
          cases hn : digits.toNat? with
          | none => simp only [hn] at h; cases h
          | some n =>
            simp only [hn] at h
            by_cases hb : (1 ≤ n && n ≤ 64) = true
            · simp only [hb, ite_true, pure, Except.pure, Except.ok.injEq] at h
              subst depth
              simpa only [Bool.and_eq_true, decide_eq_true_eq] using hb
            · simp only [hb] at h
              cases h
        · simp [htag] at h

theorem decoded_first_cause_depth (shape : String) (depth : Nat)
    (h : ((match shape.splitOn ":" with
      | ["cause", d] => match d.toNat? with
        | some n => if 1 ≤ n && n ≤ 64 then pure n
          else throw LayoutError.domain
        | none => throw LayoutError.domain
      | _ => throw LayoutError.domain) : Except LayoutError Nat) = .ok depth)
    (hpath : ¬ depth > 1) : depth = 1 := by
  have hb := decoded_cause_depth_bounds shape depth h
  omega

def axis (a b : Point) : MarkerAxis :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  if max dx (-dx) ≥ max dy (-dy) then if dx < 0 then .negativeX else .positiveX
  else if dy < 0 then .negativeY else .positiveY
def consistentOrthogonal (depth : Nat) (orthogonal : Bool) : Bool :=
  !orthogonal || depth % 2 == 0

theorem consistentOrthogonal_spine : consistentOrthogonal 0 true = true := by decide

theorem consistentOrthogonal_even (depth : Nat) (h : depth % 2 = 0) :
    consistentOrthogonal depth true = true := by
  simp [consistentOrthogonal, h]

theorem consistentOrthogonal_odd (depth : Nat) (h : depth % 2 ≠ 0) :
    consistentOrthogonal depth true = false := by
  simp [consistentOrthogonal, h]

theorem consistentOrthogonal_unmarked (depth : Nat) :
    consistentOrthogonal depth false = true := by
  simp [consistentOrthogonal]

theorem consistentOrthogonal_marked (depth : Nat)
    (h : consistentOrthogonal depth true = true) : depth % 2 = 0 := by
  simpa [consistentOrthogonal] using h

theorem accepted_orthogonal_depth (depth : Nat) (orthogonal : Bool)
    (hguard : (!consistentOrthogonal depth orthogonal) ≠ true)
    (hmarked : orthogonal = true) : depth % 2 = 0 := by
  subst orthogonal
  apply consistentOrthogonal_marked
  cases hc : consistentOrthogonal depth true with
  | false => simp only [hc, Bool.not_false] at hguard; exact False.elim (hguard rfl)
  | true => rfl


def scene (m : Model) : Except LayoutError Scene := do
  let input ← decode m
  let raw ← Elegant.Ishikawa.layout input.nodes (params m.profile)
  let (canvas, placed) ← Tree.normalize (LayoutConst.canvas_margin.get m.profile) raw
  let mut boxes : List Box := []
  for (b, i) in m.boxes.zipIdx do
    let rect := (placed.boxes[i]?).getD ⟨0,0,0,0⟩
    boxes := boxes ++ [⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩]
  let mut routes : List Route := []
  let mut groups : List Group := []
  for (r, j) in m.routes.zipIdx do
    let some k := (m.boxes.take input.nodes.length).findIdx? (·.id == r.toId) | throw .domain
    let some depth := input.depths[k]? | throw .domain
    if !consistentOrthogonal depth r.orthogonal then throw .domain
    let some anchor := boxes[input.nodes.length + j]? | throw .domain
    let some points := placed.routes[k]? | throw .domain
    let a :: b :: _ := points | throw .domain
    if anchor.id != r.fromId then throw .domain
    boxes := boxes.set (input.nodes.length + j) { anchor with rect := ⟨a.x,a.y,0,0⟩ }
    routes := routes ++ [⟨r.id,r.fromId,r.toId,r.orthogonal,points⟩]
    let marks := if r.markerStart == "" then [] else [Primitive.markerRef r.markerStart a (axis b a)]
    groups := groups ++ [⟨.edge,r.id,[.polyline points 0 { style := "edge" }] ++ marks⟩]
  for i in List.range input.nodes.length do
    let some b := boxes[i]? | throw .domain
    let depth := (input.depths[i]?).getD 0
    let lines := (input.lines[i]?).getD []
    let paint : Paint := { style := "node", width := if depth == 0 then .emphasis else .normal }
    let outline := if depth > 1 then [] else if depth == 0 && m.profile == .vector then
      [Primitive.roundRect b.rect (LayoutConst.corner_radius.get m.profile) paint] else [.rect b.rect paint]
    let h := (lines.length : Int) * LayoutConst.line_h.get m.profile
    let text : SceneText := {
      rect := ⟨b.rect.x,b.rect.y + Int.fdiv (b.rect.h-h) 2,b.rect.w,h⟩
      role := .label
      size := 14
      align := .middle
      style := "text"
      lines := styledLines m.profile ((input.source[i]?).getD "") lines }
    groups := groups ++ [⟨.node,b.id,outline ++ [.text text]⟩]
  return { kind := m.kind, profile := m.profile, options := m.options, canvas, boxes, routes, items := groups }

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  if !(m.boxes.all (fun b => b.parent == "")) then
    .error (.geometry .domain)
  else
    match scene m with
    | .error e => .error (.geometry e)
    | .ok s => .ok { scene := s.projectCellAttachments (routeMarkers m), budgetExhausted := false }

theorem cause_endpoint_boundary (x y width height : Int) (up : Bool)
    (hw : 0 ≤ width) (hh : 0 ≤ height) :
    Validator.onBoundary ⟨x, y⟩
      ⟨x - Int.fdiv width 2, if up then y - height else y, width, height⟩ := by
  rw [Tree.fdiv2]
  cases up <;> simp [Validator.onBoundary] <;> omega

theorem subcause_endpoint_boundary (b : Elegant.Ishikawa.Bone) (spine : Int)
    (up : Bool) (width height : Int) (hw : 0 ≤ width) (hh : 0 ≤ height) :
    let y := Elegant.Ishikawa.ordinate spine up b.t1
    Validator.onBoundary ⟨b.x1, y⟩
      ⟨b.x1 - width, y - Int.fdiv height 2, width, height⟩ := by
  dsimp only
  rw [Tree.fdiv2]
  unfold Validator.onBoundary
  simp only
  omega

theorem even_subcause_orthogonal (p : Elegant.Ishikawa.Params)
    (par : Elegant.Ishikawa.Bone) (depth : Nat) (t count margin spine : Int)
    (up : Bool) (h : depth % 2 = 0) :
    let b := Elegant.Ishikawa.depthBone p par depth t count margin
    Polyline.isOrthogonal
      [⟨b.x0, Elegant.Ishikawa.ordinate spine up b.t0⟩,
       ⟨b.x1, Elegant.Ishikawa.ordinate spine up b.t1⟩] = true := by
  have ht := Elegant.Ishikawa.depthBone_even_endpoints p par depth t count margin h
  dsimp only
  simp [Polyline.isOrthogonal, ht.1, ht.2.1]

theorem layout_success_scene (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) :
    ∃ s, scene m = .ok s ∧ result.scene.layoutDump = s.layoutDump := by
  unfold layout at h
  split at h
  · cases h
  · cases hs : scene m with
    | error e => simp only [hs] at h; cases h
    | ok s =>
      simp only [hs, Except.ok.injEq] at h
      subst result
      exact ⟨s, rfl, Scene.projectCellAttachments_layoutDump s (routeMarkers m)⟩

theorem nonempty_parent_rejected (m : Model) (b : ModelBox)
    (hb : b ∈ m.boxes) (hp : b.parent ≠ "") :
    layout m = .error (.geometry .domain) := by
  have hall : m.boxes.all (fun box => box.parent == "") = false := by
    cases he : m.boxes.all (fun box => box.parent == "") with
    | false => rfl
    | true =>
      have parents : ∀ box ∈ m.boxes, box.parent = "" := by
        simpa only [List.all_eq_true, beq_iff_eq] using he
      exact False.elim (hp (parents b hb))
  simp only [layout, hall, Bool.not_false, ite_true]

theorem successful_empty_parents (m : Model) (result : Layered.FamilyResult)
    (h : layout m = .ok result) :
    m.boxes.all (fun b => b.parent == "") = true := by
  cases hp : m.boxes.all (fun b => b.parent == "") with
  | false =>
    simp only [layout, hp, Bool.not_false, ite_true] at h
    cases h
  | true => rfl

theorem successful_first_parent_empty (m : Model) (result : Layered.FamilyResult)
    (first : ModelBox) (hfirst : m.boxes.head? = some first)
    (h : layout m = .ok result) : first.parent = "" := by
  have hp : ∀ b ∈ m.boxes, b.parent = "" := by
    simpa only [List.all_eq_true, beq_iff_eq] using successful_empty_parents m result h
  cases hb : m.boxes with
  | nil => simp only [hb, List.head?_nil] at hfirst; cases hfirst
  | cons b bs =>
    simp only [hb, List.head?_cons, Option.some.injEq] at hfirst
    subst first
    apply hp b
    rw [hb]
    exact List.mem_cons_self ..

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem forIn_preserves {α β : Type} (xs : List α)
    (step : α → β → Except LayoutError (ForInStep β)) (invariant : β → Prop)
    (initial final : β) (hinit : invariant initial)
    (hstep : ∀ a ∈ xs, ∀ state next, invariant state →
      step a state = .ok next → invariant next.value)
    (hrun : forIn xs initial step = .ok final) : invariant final := by
  induction xs generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hrun
    subst final
    exact hinit
  | cons a xs ih =>
    rw [List.forIn_cons] at hrun
    cases hs : step a initial with
    | error err => simp [hs, bind, Except.bind] at hrun
    | ok next =>
      have hn := hstep a (List.mem_cons_self ..) initial next hinit hs
      cases next with
      | done state =>
        simp only [hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hrun
        subst final
        exact hn
      | yield state =>
        simp only [hs, bind, Except.bind] at hrun
        exact ih state hn (fun b hb => hstep b (List.mem_cons_of_mem a hb)) hrun

private theorem empty_parents_set (boxes : List Box) (i : Nat) (replacement : Box)
    (hboxes : ∀ b ∈ boxes, b.parent = "") (hparent : replacement.parent = "") :
    ∀ b ∈ boxes.set i replacement, b.parent = "" := by
  induction boxes generalizing i with
  | nil => simp
  | cons first rest ih =>
    cases i with
    | zero => simpa using And.intro hparent (fun b hb =>
        hboxes b (List.mem_cons_of_mem first hb))
    | succ i =>
      simp only [List.set, List.mem_cons]
      intro b hb
      rcases hb with rfl | hb
      · exact hboxes b (List.mem_cons_self ..)
      · exact ih i (fun b hb => hboxes b (List.mem_cons_of_mem first hb)) b hb

theorem scene_empty_parents (m : Model) (s : Scene)
    (hparents : m.boxes.all (fun b => b.parent == "") = true)
    (h : scene m = .ok s) : ∀ b ∈ s.boxes, b.parent = "" := by
  have hp : ∀ b ∈ m.boxes, b.parent = "" := by
    simpa only [List.all_eq_true, beq_iff_eq] using hparents
  unfold scene at h
  obtain ⟨input, _, h⟩ := bind_ok h
  obtain ⟨raw, _, h⟩ := bind_ok h
  obtain ⟨pair, _, h⟩ := bind_ok h
  obtain ⟨boxes0, hb, h⟩ := bind_ok h
  have hbparents : ∀ b ∈ boxes0, b.parent = "" := by
    apply forIn_preserves _ _ (fun boxes => ∀ b ∈ boxes, b.parent = "") [] boxes0
      (by simp) _ hb
    intro entry he boxes next hi hs
    simp only [pure, Except.pure, Except.ok.injEq] at hs
    subst next
    simp only [ForInStep.value, List.mem_append, List.mem_singleton]
    intro b hmem
    rcases hmem with hmem | rfl
    · exact hi b hmem
    · exact hp entry.1 (List.fst_mem_of_mem_zipIdx he)
  obtain ⟨triple, ht, h⟩ := bind_ok h
  have htparents : ∀ b ∈ triple.1, b.parent = "" := by
    apply forIn_preserves _ _ (fun state => ∀ b ∈ state.1, b.parent = "")
      _ triple hbparents _ ht
    intro entry _ state next hi hs
    cases hfind : (m.boxes.take input.nodes.length).findIdx? (·.id == entry.1.toId) with
    | none => simp only [hfind, bind, Except.bind] at hs; cases hs
    | some k =>
      cases hdepth : input.depths[k]? with
      | none => simp only [hfind, hdepth, bind, Except.bind] at hs; cases hs
      | some depth =>
        by_cases horth : (!consistentOrthogonal depth entry.1.orthogonal) = true
        · simp only [hfind, hdepth, horth, bind, Except.bind, ite_true] at hs
          cases hs
        · cases hanchor : state.1[input.nodes.length + entry.2]? with
          | none =>
            simp only [hfind, hdepth, horth, hanchor, bind, Except.bind] at hs
            cases hs
          | some anchor =>
            cases hpoints : pair.2.routes[k]? with
            | none =>
              simp only [hfind, hdepth, horth, hanchor, hpoints,
                bind, Except.bind] at hs
              cases hs
            | some points =>
              cases points with
              | nil =>
                simp only [hfind, hdepth, horth, hanchor, hpoints,
                  bind, Except.bind] at hs
                cases hs
              | cons a tail =>
                cases tail with
                | nil =>
                  simp only [hfind, hdepth, horth, hanchor, hpoints,
                    bind, Except.bind] at hs
                  cases hs
                | cons b rest =>
                  by_cases hid : (anchor.id != entry.1.fromId) = true
                  · simp only [hfind, hdepth, horth, hanchor, hpoints, hid,
                      bind, Except.bind, ite_true] at hs
                    cases hs
                  · simp only [hfind, hdepth, horth, hanchor, hpoints, hid,
                      bind, Except.bind, pure, Except.pure] at hs
                    cases hs
                    apply empty_parents_set _ _ _ hi
                    exact hi anchor (List.mem_of_getElem? hanchor)
  obtain ⟨groups, _, h⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst s
  exact htparents

theorem ishikawa_c3_of_empty_parents (m : Model) (result : Layered.FamilyResult)
    (hparents : m.boxes.all (fun b => b.parent == "") = true)
    (h : layout m = .ok result) : Validator.C3 result.scene.layoutDump := by
  obtain ⟨s, hs, hd⟩ := layout_success_scene m result h
  rw [hd]
  intro b hb hparent
  exact False.elim (hparent (scene_empty_parents m s hparents hs b hb))

theorem ishikawa_c3 (m : Model) (result : Layered.FamilyResult)
    (_wf : WellFormed m) (_limits : WithinLimits m)
    (h : layout m = .ok result) : Validator.C3 result.scene.layoutDump := by
  exact ishikawa_c3_of_empty_parents m result (successful_empty_parents m result h) h

theorem scene_labels_empty (m : Model) (s : Scene)
    (h : scene m = .ok s) : s.labels = [] := by
  unfold scene at h
  obtain ⟨input, _, h⟩ := bind_ok h
  obtain ⟨raw, _, h⟩ := bind_ok h
  obtain ⟨pair, _, h⟩ := bind_ok h
  obtain ⟨boxes0, _, h⟩ := bind_ok h
  obtain ⟨triple, _, h⟩ := bind_ok h
  obtain ⟨groups, _, h⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst s
  rfl

theorem ishikawa_c7 (m : Model) (result : Layered.FamilyResult)
    (_wf : WellFormed m) (_limits : WithinLimits m)
    (h : layout m = .ok result) :
    Validator.C7 result.scene.layoutDump := by
  obtain ⟨s, hs, hd⟩ := layout_success_scene m result h
  rw [hd]
  have labels := scene_labels_empty m s hs
  simp [Validator.C7, Scene.layoutDump, labels]

theorem normalized_box_contained (raw placed : Tree.Layout) (canvas : Size)
    (profile : Profile)
    (hn : Tree.normalize (LayoutConst.canvas_margin.get profile) raw =
      .ok (canvas, placed))
    (rect : Rect) (hr : rect ∈ placed.boxes) :
    Rect.Contained ⟨0, 0, canvas.w, canvas.h⟩ rect := by
  apply Tree.normalized_box_inside _ hn hr
  cases profile <;> decide

theorem normalized_route_orthogonal (raw placed : Tree.Layout) (canvas : Size)
    (margin : Int)
    (hn : Tree.normalize margin raw = .ok (canvas, placed))
    (points : List Point) (hp : points ∈ placed.routes)
    (hraw : ∀ route ∈ raw.routes, Polyline.isOrthogonal route = true) :
    Polyline.isOrthogonal points = true := by
  obtain ⟨dx, dy, he⟩ := Tree.normalize_translate hn
  subst placed
  obtain ⟨route, hr, rfl⟩ := List.mem_map.mp hp
  rw [Tree.orthogonal_translate]
  exact hraw route hr

def containmentWitness : Model := {
  kind := "ishikawa"
  profile := .cell
  boxes := [
    { id := "effect", shape := "effect", parent := "cause", exclusive := false },
    { id := "cause", shape := "cause:1", exclusive := false }
  ]
}

theorem containmentWitness_wellFormed : WellFormed containmentWitness := by
  decide

theorem containmentWitness_withinLimits : WithinLimits containmentWitness := by
  decide

theorem upper_cause_cannot_contain_effect
    (spine rise effectHeight causeHeight effectX causeX effectWidth causeWidth dx dy : Int)
    (hrise : 0 < rise) (hheight : 0 ≤ effectHeight) :
    ¬ Rect.Contained
      ⟨causeX + dx, spine - rise - causeHeight + dy,
        causeWidth, causeHeight⟩
      ⟨effectX + dx, spine - Int.fdiv effectHeight 2 + dy,
        effectWidth, effectHeight⟩ := by
  rw [Tree.fdiv2]
  unfold Rect.Contained
  simp only
  omega

private theorem split_cause_one : "cause:1".splitOn ":" = ["cause", "1"] := by
  unfold String.splitOn
  rw [ite_eq_right (by decide)]
  rw [String.splitOnAux.eq_1, ite_eq_right (by decide), ite_eq_right (by decide)]
  rw [String.splitOnAux.eq_1, ite_eq_right (by decide), ite_eq_right (by decide)]
  rw [String.splitOnAux.eq_1, ite_eq_right (by decide), ite_eq_right (by decide)]
  rw [String.splitOnAux.eq_1, ite_eq_right (by decide), ite_eq_right (by decide)]
  rw [String.splitOnAux.eq_1, ite_eq_right (by decide), ite_eq_right (by decide)]
  rw [String.splitOnAux.eq_1, ite_eq_right (by decide), ite_eq_left (by decide),
    ite_eq_left (by decide)]
  rw [String.splitOnAux.eq_1, ite_eq_right (by decide), ite_eq_right (by decide)]
  rw [String.splitOnAux.eq_1, ite_eq_left (by decide)]
  decide

theorem containmentWitness_rejected :
    layout containmentWitness = .error (.geometry .domain) := by
  simp [layout, containmentWitness]


private theorem contained_of_bounds (cw ch x y w h : Int)
    (h1 : 0 ≤ x) (h2 : x + w ≤ cw) (h3 : 0 ≤ y) (h4 : y + h ≤ ch) :
    Rect.Contained ⟨0, 0, cw, ch⟩ ⟨x, y, w, h⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h1
  · show x + w ≤ 0 + cw
    omega
  · exact h3
  · show y + h ≤ 0 + ch
    omega

private theorem margin_nonneg (profile : Profile) :
    0 ≤ LayoutConst.canvas_margin.get profile := by
  cases profile <;> decide

theorem normalized_canvas_nonneg (raw placed : Tree.Layout) (canvas : Size) (margin : Int)
    (hm : 0 ≤ margin) (hn : Tree.normalize margin raw = .ok (canvas, placed)) :
    0 ≤ canvas.w ∧ 0 ≤ canvas.h := by
  unfold Tree.normalize at hn
  split at hn
  · have hc := (Prod.mk.inj (Except.ok.inj hn)).1
    subst hc
    exact ⟨by show (0 : Int) ≤ 2 * margin; omega, by show (0 : Int) ≤ 2 * margin; omega⟩
  · rename_i hE
    dsimp only at hn
    split at hn
    · cases hn
    · have hc := (Prod.mk.inj (Except.ok.inj hn)).1
      subst hc
      obtain ⟨r, hr⟩ : ∃ r : Rect, r ∈ raw.boxes := by
        cases hb : raw.boxes with
        | nil => simp [hb] at hE
        | cons r rs => exact ⟨r, List.mem_cons_self ..⟩
      have hcov := Tree.Layout.bounds_box raw hr
      unfold Tree.Bounds.Covers at hcov
      constructor
      · show 0 ≤ raw.bounds.maxX - raw.bounds.minX + 2 * margin
        omega
      · show 0 ≤ raw.bounds.maxY - raw.bounds.minY + 2 * margin
        omega

theorem normalized_point_contained (raw placed : Tree.Layout) (canvas : Size) (margin : Int)
    (hm : 0 ≤ margin)
    (hraw : ∀ pts ∈ raw.routes, pts ≠ [] → raw.boxes.isEmpty = false)
    (hn : Tree.normalize margin raw = .ok (canvas, placed))
    (points : List Point) (hp : points ∈ placed.routes) (point : Point) (hpt : point ∈ points) :
    Rect.Contained ⟨0, 0, canvas.w, canvas.h⟩ ⟨point.x, point.y, 0, 0⟩ := by
  unfold Tree.normalize at hn
  split at hn
  · rename_i hE
    have hpl : raw = placed := (Prod.mk.inj (Except.ok.inj hn)).2
    rw [← hpl] at hp
    have hne : points ≠ [] := by
      intro hnil
      rw [hnil] at hpt
      simp at hpt
    have hfalse := hraw points hp hne
    rw [hfalse] at hE
    cases hE
  · dsimp only at hn
    split at hn
    · cases hn
    · have hcanvas := (Prod.mk.inj (Except.ok.inj hn)).1
      have hpl := (Prod.mk.inj (Except.ok.inj hn)).2
      subst hpl
      obtain ⟨route, hr, hroute⟩ := List.mem_map.mp hp
      subst hroute
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hpt
      have hcov := Tree.Layout.bounds_point raw hr hq
      unfold Tree.Bounds.Covers at hcov
      have hx : point.x = q.x + (margin - raw.bounds.minX) := by
        subst hqe
        rfl
      have hy : point.y = q.y + (margin - raw.bounds.minY) := by
        subst hqe
        rfl
      have hw : canvas.w = raw.bounds.maxX - raw.bounds.minX + 2 * margin := by
        subst hcanvas
        rfl
      have hh : canvas.h = raw.bounds.maxY - raw.bounds.minY + 2 * margin := by
        subst hcanvas
        rfl
      exact contained_of_bounds canvas.w canvas.h point.x point.y 0 0
        (by omega) (by omega) (by omega) (by omega)

private theorem getD_contained (canvas : Size) (rects : List Rect)
    (hw : 0 ≤ canvas.w) (hh : 0 ≤ canvas.h)
    (hc : ∀ r ∈ rects, Rect.Contained ⟨0, 0, canvas.w, canvas.h⟩ r) (i : Nat) :
    Rect.Contained ⟨0, 0, canvas.w, canvas.h⟩ ((rects[i]?).getD ⟨0, 0, 0, 0⟩) := by
  cases hi : rects[i]? with
  | some r => exact hc r (List.mem_of_getElem? hi)
  | none =>
    exact contained_of_bounds canvas.w canvas.h 0 0 0 0 (Int.le_refl 0) (by omega)
      (Int.le_refl 0) (by omega)

private theorem contained_set (canvas : Size) (boxes : List Box) (i : Nat) (replacement : Box)
    (hboxes : ∀ b ∈ boxes, Rect.Contained ⟨0, 0, canvas.w, canvas.h⟩ b.rect)
    (hrep : Rect.Contained ⟨0, 0, canvas.w, canvas.h⟩ replacement.rect) :
    ∀ b ∈ boxes.set i replacement, Rect.Contained ⟨0, 0, canvas.w, canvas.h⟩ b.rect := by
  induction boxes generalizing i with
  | nil => simp
  | cons first rest ih =>
    cases i with
    | zero =>
      intro b hb
      change b ∈ replacement :: rest at hb
      rcases List.mem_cons.mp hb with hbe | hb
      · rw [hbe]
        exact hrep
      · exact hboxes b (List.mem_cons_of_mem first hb)
    | succ i =>
      intro b hb
      change b ∈ first :: rest.set i replacement at hb
      rcases List.mem_cons.mp hb with hbe | hb
      · rw [hbe]
        exact hboxes first (List.mem_cons_self ..)
      · exact ih i (fun b hb => hboxes b (List.mem_cons_of_mem first hb)) b hb

theorem scene_boxes_contained (m : Model) (s : Scene)
    (hraw : ∀ (input : Input) (raw : Tree.Layout),
      decode m = .ok input →
      Elegant.Ishikawa.layout input.nodes (params m.profile) = .ok raw →
      ∀ pts ∈ raw.routes, pts ≠ [] → raw.boxes.isEmpty = false)
    (h : scene m = .ok s) :
    ∀ b ∈ s.boxes, Rect.Contained ⟨0, 0, s.canvas.w, s.canvas.h⟩ b.rect := by
  unfold scene at h
  obtain ⟨input, hinput, h⟩ := bind_ok h
  obtain ⟨raw, hrawok, h⟩ := bind_ok h
  obtain ⟨pair, hpair, h⟩ := bind_ok h
  have hn : Tree.normalize (LayoutConst.canvas_margin.get m.profile) raw =
      .ok (pair.1, pair.2) := hpair
  have hm := margin_nonneg m.profile
  have hcanvas := normalized_canvas_nonneg raw pair.2 pair.1 _ hm hn
  have hcont : ∀ r ∈ pair.2.boxes, Rect.Contained ⟨0, 0, pair.1.w, pair.1.h⟩ r :=
    fun r hr => normalized_box_contained raw pair.2 pair.1 m.profile hn r hr
  have hpoint : ∀ points ∈ pair.2.routes, ∀ point ∈ points,
      Rect.Contained ⟨0, 0, pair.1.w, pair.1.h⟩ ⟨point.x, point.y, 0, 0⟩ :=
    fun points hp point hpt => normalized_point_contained raw pair.2 pair.1 _ hm
      (hraw input raw hinput hrawok) hn points hp point hpt
  obtain ⟨boxes0, hb, h⟩ := bind_ok h
  have hb0 : ∀ b ∈ boxes0, Rect.Contained ⟨0, 0, pair.1.w, pair.1.h⟩ b.rect := by
    apply forIn_preserves _ _
      (fun boxes => ∀ b ∈ boxes, Rect.Contained ⟨0, 0, pair.1.w, pair.1.h⟩ b.rect) [] boxes0
      (by simp) _ hb
    intro entry _ boxes next hi hs
    simp only [pure, Except.pure, Except.ok.injEq] at hs
    subst next
    simp only [ForInStep.value, List.mem_append, List.mem_singleton]
    intro b hmem
    rcases hmem with hmem | rfl
    · exact hi b hmem
    · exact getD_contained pair.1 pair.2.boxes hcanvas.1 hcanvas.2 hcont entry.2
  obtain ⟨triple, ht, h⟩ := bind_ok h
  have ht0 : ∀ b ∈ triple.1, Rect.Contained ⟨0, 0, pair.1.w, pair.1.h⟩ b.rect := by
    apply forIn_preserves _ _
      (fun state => ∀ b ∈ state.1, Rect.Contained ⟨0, 0, pair.1.w, pair.1.h⟩ b.rect)
      _ triple hb0 _ ht
    intro entry _ state next hi hs
    cases hfind : (m.boxes.take input.nodes.length).findIdx? (·.id == entry.1.toId) with
    | none => simp only [hfind, bind, Except.bind] at hs; cases hs
    | some k =>
      cases hdepth : input.depths[k]? with
      | none => simp only [hfind, hdepth, bind, Except.bind] at hs; cases hs
      | some depth =>
        by_cases horth : (!consistentOrthogonal depth entry.1.orthogonal) = true
        · simp only [hfind, hdepth, horth, bind, Except.bind, ite_true] at hs
          cases hs
        · cases hanchor : state.1[input.nodes.length + entry.2]? with
          | none =>
            simp only [hfind, hdepth, horth, hanchor, bind, Except.bind] at hs
            cases hs
          | some anchor =>
            cases hpoints : pair.2.routes[k]? with
            | none =>
              simp only [hfind, hdepth, horth, hanchor, hpoints,
                bind, Except.bind] at hs
              cases hs
            | some points =>
              cases points with
              | nil =>
                simp only [hfind, hdepth, horth, hanchor, hpoints,
                  bind, Except.bind] at hs
                cases hs
              | cons a tail =>
                cases tail with
                | nil =>
                  simp only [hfind, hdepth, horth, hanchor, hpoints,
                    bind, Except.bind] at hs
                  cases hs
                | cons b rest =>
                  by_cases hid : (anchor.id != entry.1.fromId) = true
                  · simp only [hfind, hdepth, horth, hanchor, hpoints, hid,
                      bind, Except.bind, ite_true] at hs
                    cases hs
                  · simp only [hfind, hdepth, horth, hanchor, hpoints, hid,
                      bind, Except.bind, pure, Except.pure] at hs
                    cases hs
                    apply contained_set _ _ _ _ hi
                    exact hpoint _ (List.mem_of_getElem? hpoints) a (List.mem_cons_self ..)
  obtain ⟨groups, _, h⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst s
  exact ht0

theorem ishikawa_c1_of_raw_nonempty (m : Model) (result : Layered.FamilyResult)
    (hraw : ∀ (input : Input) (raw : Tree.Layout),
      decode m = .ok input →
      Elegant.Ishikawa.layout input.nodes (params m.profile) = .ok raw →
      ∀ pts ∈ raw.routes, pts ≠ [] → raw.boxes.isEmpty = false)
    (h : layout m = .ok result) : Validator.C1 result.scene.layoutDump := by
  obtain ⟨s, hs, hd⟩ := layout_success_scene m result h
  rw [hd]
  intro b hb
  exact scene_boxes_contained m s hraw hs b hb
end Elegant.Kinds.Ishikawa

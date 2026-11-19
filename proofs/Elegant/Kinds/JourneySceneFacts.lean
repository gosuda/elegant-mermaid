import Elegant.Kinds.JourneyValid
import Elegant.TreeFacts

set_option autoImplicit false

namespace Elegant.Kinds.JourneySceneFacts

open Elegant Kinds Lanes
open Lanes.Journey
open Journey Common JourneyValid

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩


private theorem forIn_inv {α β : Type} (xs : List α) (init out : β)
    (step : α → β → Except LayoutError (ForInStep β)) (P : β → Prop)
    (hinit : P init)
    (hstep : ∀ a ∈ xs, ∀ state next,
      P state → step a state = .ok next → P next.value)
    (hrun : ForIn.forIn xs init step = .ok out) : P out := by
  induction xs generalizing init with
  | nil =>
    change Except.ok init = Except.ok out at hrun
    cases hrun
    exact hinit
  | cons a rest ih =>
    rw [List.forIn_cons] at hrun
    cases he : step a init with
    | error e =>
      simp only [he, Bind.bind, Except.bind] at hrun
      cases hrun
    | ok next =>
      have hp := hstep a (by simp) init next hinit he
      cases next with
      | done state =>
        simp only [he, Bind.bind, Except.bind] at hrun
        cases hrun
        exact hp
      | yield state =>
        simp only [he, Bind.bind, Except.bind] at hrun
        exact ih state hp
          (fun b hb => hstep b (List.mem_cons_of_mem a hb)) hrun

theorem foldl_max_bound {α : Type} (f : α → Int) (xs : List α)
    (initial : Int) :
    initial ≤ xs.foldl (fun h a => max h (f a)) initial ∧
      ∀ a ∈ xs, f a ≤ xs.foldl (fun h a => max h (f a)) initial := by
  induction xs generalizing initial with
  | nil => exact ⟨Int.le_refl _, by simp⟩
  | cons a rest ih =>
    obtain ⟨hinit, hrest⟩ := ih (max initial (f a))
    constructor
    · exact Int.le_trans (Int.le_max_left _ _) hinit
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Int.le_trans (Int.le_max_right _ _) hinit
      · exact hrest b hb

private theorem forIn_length {α β : Type} (xs : List α) (init out : β)
    (step : α → β → Except LayoutError (ForInStep β)) (length : β → Nat)
    (hstep : ∀ a state next, step a state = .ok next →
      ∃ value, next = .yield value ∧ length value = length state + 1)
    (hrun : ForIn.forIn xs init step = .ok out) :
    length out = length init + xs.length := by
  induction xs generalizing init with
  | nil =>
    change Except.ok init = Except.ok out at hrun
    cases hrun
    simp
  | cons a rest ih =>
    rw [List.forIn_cons] at hrun
    cases he : step a init with
    | error e =>
      simp only [he, Bind.bind, Except.bind] at hrun
      cases hrun
    | ok next =>
      obtain ⟨value, rfl, hv⟩ := hstep a init next he
      simp only [he, Bind.bind, Except.bind] at hrun
      have hrest := ih value hrun
      simp only [List.length_cons]
      omega

private theorem mapM_inv {α β : Type} (xs : List α)
    (f : α → Except LayoutError β) (P : β → Prop) {out : List β}
    (hstep : ∀ a ∈ xs, ∀ b, f a = .ok b → P b)
    (hrun : xs.mapM f = .ok out) : ∀ b ∈ out, P b := by
  induction xs generalizing out with
  | nil =>
    have he : [] = out := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using hrun
    simp [← he]
  | cons a rest ih =>
    cases ha : f a with
    | error e =>
      simp only [List.mapM_cons, ha, Bind.bind, Except.bind] at hrun
      cases hrun
    | ok b =>
      cases hr : rest.mapM f with
      | error e =>
        simp only [List.mapM_cons, ha, hr, Bind.bind, Except.bind] at hrun
        cases hrun
      | ok bs =>
        have he : b :: bs = out := by
          simpa only [List.mapM_cons, ha, hr, Bind.bind, Except.bind,
            Pure.pure, Except.pure, Functor.map, Except.map, Except.ok.injEq] using hrun
        subst out
        intro v hv
        rcases List.mem_cons.mp hv with hv | hv
        · subst v
          exact hstep a (by simp) b ha
        · exact ih (fun x hx => hstep x (List.mem_cons_of_mem a hx)) hr v hv

private theorem task_height_bound (g : Input) (c : Constants)
    {t : Task} (ht : t ∈ g.tasks) :
    t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY ≤
      g.tasks.foldl (fun h t => max h
        (t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY))
        c.taskHeight :=
  (foldl_max_bound
    (fun t : Task => t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY)
    g.tasks c.taskHeight).2 t ht

private theorem extent_member_canvas (rs : List Rect) {r : Rect}
    (hr : r ∈ rs) (margin : Int) (hm : 0 ≤ margin) :
    let ext := match rs with
      | [] => zeroRect
      | seed :: rest => rest.foldl Rect.unionRaw seed
    (⟨0, 0, ext.w + 2 * margin, ext.h + 2 * margin⟩ : Rect).Contained
      (shiftRect (margin - ext.x) (margin - ext.y) r) := by
  cases rs with
  | nil => simp at hr
  | cons seed rest =>
    exact journey_shifted_extent_member seed rest r margin hm hr

private theorem extent_member (rs : List Rect) {r : Rect} (hr : r ∈ rs) :
    (match rs with
      | [] => zeroRect
      | seed :: rest => rest.foldl Rect.unionRaw seed).Contained r := by
  cases rs with
  | nil => simp at hr
  | cons seed rest =>
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      exact (journey_extent_contains rest seed).1
    · exact (journey_extent_contains rest seed).2 r hr

theorem zipIdx_mem_bounds {α : Type} (xs : List α)
    {a : α} {i : Nat} (hi : (a, i) ∈ xs.zipIdx) :
    i < xs.length ∧ a ∈ xs := by
  have he := List.mem_zipIdx_iff_getElem?.mp hi
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp he
  refine ⟨hlt, ?_⟩
  have hm : xs[i] ∈ xs := List.getElem_mem hlt
  simpa only [he] using hm

private theorem getD_mem {α : Type} (xs : List α) (i : Nat) (fallback : α)
    (hi : i < xs.length) : xs.getD i fallback ∈ xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hi' : i < rest.length := by simpa using hi
      simpa using List.mem_cons_of_mem a (ih i hi')

private theorem find_mem {α : Type} (xs : List α) (p : α → Bool)
    {a : α} (h : xs.find? p = some a) : a ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons b rest ih =>
    simp only [List.find?_cons] at h
    split at h
    · cases h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem b (ih h)

private theorem assigned_boxes_contained (m : Model) (assigned : List (String × Rect))
    (canvas : Rect) {boxes : List Box}
    (hassigned : ∀ pair ∈ assigned, canvas.Contained pair.2)
    (hboxes : (m.boxes.mapM fun (b : ModelBox) => (do
      let some (_, rect) := assigned.find? (fun (p : String × Rect) => p.1 == b.id)
        | throw LayoutError.domain
      pure (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box) :
        Except LayoutError Box)) = .ok boxes) :
    ∀ b ∈ boxes, canvas.Contained b.rect := by
  apply mapM_inv m.boxes _ (fun b : Box => canvas.Contained b.rect) _ hboxes
  intro b _ out hout
  cases hp : assigned.find? (fun p => p.1 == b.id) with
  | none => simp [hp] at hout
  | some pair =>
    rcases pair with ⟨id, rect⟩
    have he : (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box) = out := by
      simpa [hp, Pure.pure, Except.pure] using hout
    subst out
    exact hassigned (id, rect) (find_mem assigned _ hp)

private theorem decoded_people_contained (m : Model) (c : Constants)
    (g : Input) (hinv : DecodeInv m c m.boxes g) (hpos : LoadPos c)
    (ext card : Rect) (hext : ext.Contained card)
    (hcard : card.h = g.tasks.foldl (fun h t => max h
      (t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY)) c.taskHeight)
    {t : Task} (ht : t ∈ g.tasks) :
    let block := centred c card (t.caption.h + (t.people.map (·.h)).getD 0)
    (⟨0, 0, ext.w + 2 * c.margin, ext.h + 2 * c.margin⟩ : Rect).Contained
      (shiftRect (c.margin - ext.x) (c.margin - ext.y)
        { block with y := block.y + t.caption.h, h := (t.people.map (·.h)).getD 0 }) := by
  have hcaption := hinv.taskCapPos t.caption
    (List.mem_map.mpr ⟨t, ht, rfl⟩)
  have hheight := task_height_bound g c ht
  obtain ⟨_, _, _, _, _, _, hpadX, hpadY, hmargin⟩ := hpos
  apply journey_shifted_people_inside_extent c ext card t.caption.h
    ((t.people.map (·.h)).getD 0) hext hmargin hpadX (by omega)
  omega

theorem successful_decode {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : Journey.layout m = .ok result) :
    ∃ c g, Journey.load m = .ok c ∧ Journey.decode m c = .ok g ∧
      LoadPos c ∧ DecodeInv m c m.boxes g := by
  have hs := Journey.layout_scene h
  unfold Journey.scene at hs
  obtain ⟨c, hc, hs⟩ := bind_ok hs
  obtain ⟨g, hg, _⟩ := bind_ok hs
  exact ⟨c, g, hc, hg, load_pos hc, decode_ok m c hwf hg⟩

theorem successful_task_origins {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : Journey.layout m = .ok result) :
    ∃ c g, Journey.load m = .ok c ∧ Journey.decode m c = .ok g ∧
      g.tasks.map (·.id) = (m.boxes.filter isTaskBox).map (·.id) ∧
      g.sections.map (·.id) = (m.boxes.filter isSecBox).map (·.id) ∧
      g.title.map (·.id) = ((m.boxes.filter isTitleBox).map (·.id)).getLast? := by
  obtain ⟨c, g, hc, hg, _, hi⟩ := successful_decode hwf h
  exact ⟨c, g, hc, hg, hi.taskIds, hi.secIds, hi.titleId⟩

theorem successful_people_origins {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : Journey.layout m = .ok result) :
    ∃ c g, Journey.load m = .ok c ∧ Journey.decode m c = .ok g ∧
      (∀ b ∈ m.boxes, isPeopleBox b →
        ∃ j, ∃ _ : j < g.tasks.length, g.tasks[j].id == b.parent) ∧
      (∀ (i : Nat) (_hlt : i < g.tasks.length),
        g.tasks[i].people.isSome ↔
          (∃ b ∈ m.boxes, isPeopleBox b ∧ b.parent == g.tasks[i].id)) := by
  obtain ⟨c, g, hc, hg, _, hi⟩ := successful_decode hwf h
  exact ⟨c, g, hc, hg, hi.peopleParents, hi.taskPeople⟩

theorem successful_caption_extents {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : Journey.layout m = .ok result) :
    ∃ c g, Journey.load m = .ok c ∧ Journey.decode m c = .ok g ∧
      (∀ cap ∈ g.sections.map (·.caption), 0 < cap.h ∧ 0 ≤ cap.w) ∧
      (∀ cap ∈ g.tasks.map (·.caption), 0 < cap.h ∧ 0 ≤ cap.w) ∧
      (∀ t ∈ g.tasks, ∀ cap ∈ t.people.toList, 0 < cap.h ∧ 0 ≤ cap.w) ∧
      (∀ cap ∈ g.title.toList.map (·.caption), 0 < cap.h ∧ 0 ≤ cap.w) := by
  obtain ⟨c, g, hc, hg, _, hi⟩ := successful_decode hwf h
  exact ⟨c, g, hc, hg, hi.secCapPos, hi.taskCapPos, hi.peopleCapPos, hi.titleCapPos⟩

theorem successful_parent_origins {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : Journey.layout m = .ok result) :
    ∃ c g, Journey.load m = .ok c ∧ Journey.decode m c = .ok g ∧
      (∀ b ∈ m.boxes, (isTitleBox b ∨ isSecBox b) → b.parent = "") ∧
      (∀ (i : Nat) (_hlt : i < g.tasks.length)
        (_hlen : i < (m.boxes.filter isTaskBox).length),
        (m.boxes.filter isTaskBox)[i].parent = "" ∨
          (m.boxes.filter isTaskBox)[i].parent ∈ g.sections.map (·.id)) := by
  obtain ⟨c, g, hc, hg, _, hi⟩ := successful_decode hwf h
  exact ⟨c, g, hc, hg, hi.parentRoots, hi.taskParentOK⟩

theorem journey_c1 {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : Journey.layout m = .ok result) :
    Validator.C1 result.scene.layoutDump := by
  classical
  have hs := Journey.layout_scene h
  unfold Journey.scene at hs
  obtain ⟨c, hc, hs⟩ := bind_ok hs
  obtain ⟨g, hg, hs⟩ := bind_ok hs
  have hpos := load_pos hc
  have hinv := decode_ok m c hwf hg
  let bandH := g.sections.foldl (fun h s => max h (s.caption.h + 2 * c.padY))
    c.bandHeight
  let taskH := g.tasks.foldl (fun h t => max h
    (t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY)) c.taskHeight
  let top := (g.title.map fun t => t.caption.h + c.scoreStep).getD 0
  let taskTop := top + bandH + 6 * c.scoreStep
  let tasks := g.tasks.zipIdx.map fun (_, i) => taskRect c taskTop taskH i
  let faces := g.tasks.zipIdx.map fun (t, i) =>
    (⟨column c i + half c.taskWidth, faceY c (top + bandH) t.score⟩ : Point)
  obtain ⟨framesBands, hframes, hs⟩ := bind_ok hs
  rcases framesBands with ⟨frames, bands⟩
  have hframeslen : frames.length = g.sections.length := by
    have hh : frames.length = 0 + g.sections.zipIdx.length := by
      apply forIn_length g.sections.zipIdx
        (([], []) : List Rect × List Rect) (frames, bands) _
        (fun state => state.1.length) (hrun := hframes)
      intro entry state next hstep
      rcases entry with ⟨sec, i⟩
      rcases state with ⟨oldFrames, oldBands⟩
      dsimp only at hstep
      split at hstep
      · split at hstep
        · simp only [Bind.bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw] at hstep
          cases hstep
        · simp only [Pure.pure, Except.pure] at hstep
          cases hstep
          exact ⟨_, rfl, by simp⟩
      · simp only [Bind.bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw] at hstep
        cases hstep
    simpa using hh
  let title : Rect :=
    (g.title.map fun t => ⟨0, 0, t.caption.w, t.caption.h⟩).getD zeroRect
  let faceBoxes := faces.map fun p =>
    if m.profile == .cell then (⟨p.x, p.y, 1, 1⟩ : Rect)
    else ⟨p.x - c.radius, p.y - c.radius, 2 * c.radius, 2 * c.radius⟩
  let all := g.title.toList.map (fun _ => title) ++ frames ++ tasks ++ faceBoxes
  let ext := match all with
    | [] => zeroRect
    | seed :: rest => rest.foldl Rect.unionRaw seed
  let shift := shiftRect (c.margin - ext.x) (c.margin - ext.y)
  let canvas : Rect := ⟨0, 0, ext.w + 2 * c.margin, ext.h + 2 * c.margin⟩
  have hmargin : 0 ≤ c.margin := hpos.2.2.2.2.2.2.2.2
  have hmember : ∀ r ∈ all, canvas.Contained (shift r) := by
    intro r hr
    exact extent_member_canvas all hr c.margin hmargin
  have hframe : ∀ i, i < g.sections.length →
      canvas.Contained (shift (frames.getD i zeroRect)) := by
    intro i hi
    apply hmember
    have hm := getD_mem frames i zeroRect (by omega)
    simp only [all, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hm))
  have hcard : ∀ i, i < g.tasks.length →
      tasks.getD i zeroRect ∈ tasks := by
    intro i hi
    exact getD_mem tasks i zeroRect (by simpa [tasks] using hi)
  have htask : ∀ i, i < g.tasks.length →
      canvas.Contained (shift (tasks.getD i zeroRect)) := by
    intro i hi
    apply hmember
    simp only [all, List.mem_append]
    exact Or.inl (Or.inr (hcard i hi))
  have hpeople : ∀ t i, (t, i) ∈ g.tasks.zipIdx →
      let card := tasks.getD i zeroRect
      let block := centred c card (t.caption.h + (t.people.map (·.h)).getD 0)
      canvas.Contained (shift
        { block with y := block.y + t.caption.h, h := (t.people.map (·.h)).getD 0 }) := by
    intro t i hi
    obtain ⟨hib, htm⟩ := zipIdx_mem_bounds g.tasks hi
    have hcm := hcard i hib
    have hcext : ext.Contained (tasks.getD i zeroRect) := by
      apply extent_member all
      simp only [all, List.mem_append]
      exact Or.inl (Or.inr hcm)
    have hch : (tasks.getD i zeroRect).h = taskH := by
      obtain ⟨entry, _, he⟩ := List.mem_map.mp hcm
      rw [← he]
      rcases entry with ⟨task, j⟩
      rfl
    exact decoded_people_contained m c g hinv hpos ext
      (tasks.getD i zeroRect) hcext hch htm
  obtain ⟨assignedItems, hsections, hs⟩ := bind_ok hs
  have hsectionsGood : ∀ pair ∈ assignedItems.1, canvas.Contained pair.2 := by
    refine forIn_inv g.sections.zipIdx _ assignedItems _
      (fun state => ∀ pair ∈ state.1, canvas.Contained pair.2) ?_ ?_ hsections
    · simp
    · intro entry hentry state next hstate hstep
      rcases entry with ⟨sec, i⟩
      rcases state with ⟨assigned, items⟩
      dsimp only at hstep
      cases hstep
      dsimp only [ForInStep.value]
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hstate pair hp
      · have he := List.mem_singleton.mp hp
        subst pair
        exact hframe i (zipIdx_mem_bounds g.sections hentry).1
  have htitleGood : ∀ pair ∈
      (match g.title with
        | some t => assignedItems.1 ++ [(t.id, shift title)]
        | none => assignedItems.1), canvas.Contained pair.2 := by
    cases ht : g.title with
    | none => exact hsectionsGood
    | some titleCard =>
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hsectionsGood pair hp
      · have he := List.mem_singleton.mp hp
        subst pair
        apply hmember
        simp only [all, List.mem_append]
        exact Or.inl (Or.inl (Or.inl (by simp [ht])))
  cases ht : g.title <;> simp only [ht] at hs
  all_goals
    dsimp only [shift, ext, all, title, faceBoxes, faces, tasks, taskTop,
      top, taskH, bandH] at htask hpeople htitleGood
    simp only [ht] at htask hpeople htitleGood
    obtain ⟨finalAssignedItems, htasks, hs⟩ := bind_ok hs
    have hfinal : ∀ pair ∈ finalAssignedItems.1, canvas.Contained pair.2 := by
      refine forIn_inv g.tasks.zipIdx _ finalAssignedItems _
        (fun state => ∀ pair ∈ state.1, canvas.Contained pair.2) ?_ ?_ htasks
      · exact htitleGood
      · intro entry hentry state next hstate hstep
        rcases entry with ⟨task, i⟩
        rcases state with ⟨assigned, items⟩
        dsimp only at hstep
        obtain ⟨peopleAssigned, hinner, hstep⟩ := bind_ok hstep
        have hp : ∀ pair ∈ peopleAssigned, canvas.Contained pair.2 := by
          refine forIn_inv m.boxes _ peopleAssigned _
            (fun state => ∀ pair ∈ state, canvas.Contained pair.2) ?_ ?_ hinner
          · intro pair hpair
            rcases List.mem_append.mp hpair with hpair | hpair
            · exact hstate pair hpair
            · have he := List.mem_singleton.mp hpair
              subst pair
              exact htask i (zipIdx_mem_bounds g.tasks hentry).1
          · intro box _ old next hgood hbox
            split at hbox
            · cases hbox
              dsimp only [ForInStep.value]
              intro pair hpair
              rcases List.mem_append.mp hpair with hpair | hpair
              · exact hgood pair hpair
              · have he := List.mem_singleton.mp hpair
                subst pair
                exact hpeople task i hentry
            · cases hbox
              exact hgood
        cases hstep
        exact hp
    obtain ⟨boxes, hboxes, hs⟩ := bind_ok hs
    obtain ⟨_, _, hcanvas, hsceneBoxes, _⟩ := Journey.finish_ok hs
    change ∀ b ∈ result.scene.boxes,
      (⟨0, 0, result.scene.canvas.w, result.scene.canvas.h⟩ : Rect).Contained b.rect
    rw [hcanvas, hsceneBoxes]
    have hcontained :=
      assigned_boxes_contained m finalAssignedItems.1 canvas hfinal hboxes
    dsimp only [canvas, ext, all, title, faceBoxes, faces, tasks, taskTop,
      top, taskH, bandH] at hcontained
    simp [ht] at hcontained ⊢
    split at hcontained <;> rename_i hextCase
    all_goals simpa [hextCase] using hcontained

private theorem forIn_append_trace {α β γ : Type} (xs : List α) (init out : β)
    (step : α → β → Except LayoutError (ForInStep β))
    (values : β → List γ) (value : α → γ) (P : α → Prop)
    (hstep : ∀ a state next, step a state = .ok next →
      ∃ state', next = .yield state' ∧
        values state' = values state ++ [value a] ∧ P a)
    (hrun : ForIn.forIn xs init step = .ok out) :
    values out = values init ++ xs.map value ∧ ∀ a ∈ xs, P a := by
  induction xs generalizing init with
  | nil =>
    change Except.ok init = Except.ok out at hrun
    cases hrun
    exact ⟨by simp, by simp⟩
  | cons a rest ih =>
    rw [List.forIn_cons] at hrun
    cases he : step a init with
    | error e =>
      simp only [he, Bind.bind, Except.bind] at hrun
      cases hrun
    | ok next =>
      obtain ⟨state', rfl, hv, hp⟩ := hstep a init next he
      simp only [he, Bind.bind, Except.bind] at hrun
      obtain ⟨hvalues, hrest⟩ := ih state' hrun
      constructor
      · simpa only [hv, List.map_cons, List.append_assoc,
          List.singleton_append] using hvalues
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hp
        · exact hrest b hb

def sectionIndices (g : Input) (i : Nat) : List Nat :=
  (g.tasks.zipIdx.filter fun (t, _) => t.band == (i : Int)).map (·.2)

def sectionFrame (g : Input) (c : Constants)
    (top taskTop taskH : Int) (i : Nat) : Rect :=
  let indices := sectionIndices g i
  let first := indices.head?.getD 0
  sectionRect c top (taskTop + taskH - top) first (indices.getLast?.getD first)

private def sectionFrameStep (g : Input) (c : Constants)
    (top taskTop taskH bandH : Int) (entry : Card × Nat)
    (state : List Rect × List Rect) :
    Except LayoutError (ForInStep (List Rect × List Rect)) := do
  let indices := sectionIndices g entry.2
  let some first := indices.head? | throw LayoutError.domain
  let last := indices.getLast?.getD first
  if !(g.tasks.zipIdx.all fun (t, k) =>
      decide (first ≤ k ∧ k ≤ last) == (t.band == (entry.2 : Int))) then
    throw LayoutError.domain
  pure (.yield
    (state.1 ++ [sectionRect c top (taskTop + taskH - top) first last],
     state.2 ++ [sectionRect c top bandH first last]))

theorem section_frames_trace (g : Input) (c : Constants)
    (top taskTop taskH bandH : Int) {frames bands : List Rect}
    (h : ForIn.forIn g.sections.zipIdx
      (([], []) : List Rect × List Rect)
      (sectionFrameStep g c top taskTop taskH bandH) = .ok (frames, bands)) :
    frames = g.sections.zipIdx.map (fun entry =>
      sectionFrame g c top taskTop taskH entry.2) ∧
    ∀ entry ∈ g.sections.zipIdx,
      ∃ first, (sectionIndices g entry.2).head? = some first ∧
        (g.tasks.zipIdx.all fun (t, k) =>
          decide (first ≤ k ∧ k ≤ (sectionIndices g entry.2).getLast?.getD first) ==
            (t.band == (entry.2 : Int))) = true := by
  apply forIn_append_trace g.sections.zipIdx
    (([], []) : List Rect × List Rect) (frames, bands)
    (sectionFrameStep g c top taskTop taskH bandH)
    (fun state => state.1)
    (fun entry => sectionFrame g c top taskTop taskH entry.2)
    (fun entry => ∃ first, (sectionIndices g entry.2).head? = some first ∧
      (g.tasks.zipIdx.all fun (t, k) =>
        decide (first ≤ k ∧ k ≤ (sectionIndices g entry.2).getLast?.getD first) ==
          (t.band == (entry.2 : Int))) = true)
    (hrun := h)
  intro entry state next hstep
  unfold sectionFrameStep at hstep
  dsimp only at hstep
  split at hstep
  · rename_i first hfirst
    split at hstep
    · simp only [Bind.bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw] at hstep
      cases hstep
    · rename_i hvalid
      simp only [Pure.pure, Except.pure] at hstep
      cases hstep
      refine ⟨_, rfl, ?_, first, hfirst, ?_⟩
      · simp only [sectionFrame, hfirst, Option.getD_some]
      · simpa using hvalid
  · simp only [throw, throwThe, MonadExceptOf.throw] at hstep
    cases hstep

private theorem section_frames_contain_tasks (g : Input) (c : Constants)
    (top taskTop taskH bandH dx dy : Int) {frames bands : List Rect}
    (h : ForIn.forIn g.sections.zipIdx
      (([], []) : List Rect × List Rect)
      (sectionFrameStep g c top taskTop taskH bandH) = .ok (frames, bands))
    (hcolumns : 0 ≤ c.taskWidth + c.columnGap) (htop : top ≤ taskTop)
    {s : Card} {j : Nat} (hs : (s, j) ∈ g.sections.zipIdx)
    {t : Task} {i : Nat} (ht : (t, i) ∈ g.tasks.zipIdx)
    (hband : t.band = (j : Int)) :
    (shiftRect dx dy (frames.getD j zeroRect)).Contained
      (shiftRect dx dy (taskRect c taskTop taskH i)) := by
  obtain ⟨he, hguards⟩ := section_frames_trace g c top taskTop taskH bandH h
  obtain ⟨first, hfirst, hguard⟩ := hguards (s, j) hs
  have hlookup : frames.getD j zeroRect = sectionFrame g c top taskTop taskH j := by
    rw [he]
    have hj := (zipIdx_mem_bounds g.sections hs).1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_zipIdx, List.getElem?_eq_getElem hj,
      Option.map_some, Option.getD_some, Nat.zero_add]
  rw [hlookup]
  simp only [sectionFrame, hfirst, Option.getD_some]
  exact admitted_section_contains_task g c j first
    ((sectionIndices g j).getLast?.getD first) top taskTop taskH dx dy
    hguard hcolumns htop ht hband

theorem successful_section_containment {m : Model} {result : Layered.FamilyResult}
    (h : Journey.layout m = .ok result) :
    ∃ c g, ∃ frames _bands : List Rect,
      Journey.load m = .ok c ∧ Journey.decode m c = .ok g ∧
      ∀ (s : Card) (j : Nat), (s, j) ∈ g.sections.zipIdx →
        ∀ (t : Task) (i : Nat), (t, i) ∈ g.tasks.zipIdx →
          t.band = (j : Int) →
          ∀ dx dy,
            (shiftRect dx dy (frames.getD j zeroRect)).Contained
              (shiftRect dx dy (taskRect c
                ((g.title.map fun t => t.caption.h + c.scoreStep).getD 0 +
                  g.sections.foldl (fun h s => max h (s.caption.h + 2 * c.padY))
                    c.bandHeight + 6 * c.scoreStep)
                (g.tasks.foldl (fun h t => max h
                  (t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY))
                  c.taskHeight) i)) := by
  have hs := Journey.layout_scene h
  unfold Journey.scene at hs
  obtain ⟨c, hc, hs⟩ := bind_ok hs
  obtain ⟨g, hg, hs⟩ := bind_ok hs
  obtain ⟨framesBands, hframes, _⟩ := bind_ok hs
  rcases framesBands with ⟨frames, bands⟩
  refine ⟨c, g, frames, bands, hc, hg, ?_⟩
  intro s j hsec t i htask hband dx dy
  have hp := load_pos hc
  obtain ⟨hw, _, hb, hgap, hscore, _, _, _, _⟩ := hp
  have hbandHeight := (foldl_max_bound (fun s : Card =>
    s.caption.h + 2 * c.padY) g.sections c.bandHeight).1
  exact section_frames_contain_tasks g c _ _ _ _ dx dy
    hframes (by omega) (by omega) hsec htask hband

private theorem assigned_boxes_origins (m : Model) (assigned : List (String × Rect))
    {boxes : List Box}
    (hboxes : (m.boxes.mapM fun (b : ModelBox) => (do
      let some (_, rect) := assigned.find? (fun (p : String × Rect) => p.1 == b.id)
        | throw LayoutError.domain
      pure (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box) :
        Except LayoutError Box)) = .ok boxes) :
    ∀ out ∈ boxes, ∃ source ∈ m.boxes,
      out.id = source.id ∧ out.role = source.role.id ∧
      out.parent = source.parent ∧ out.exclusive = source.exclusive := by
  apply mapM_inv m.boxes _ (fun out : Box => ∃ source ∈ m.boxes,
    out.id = source.id ∧ out.role = source.role.id ∧
    out.parent = source.parent ∧ out.exclusive = source.exclusive) _ hboxes
  intro source hsource out hout
  cases hp : assigned.find? (fun p => p.1 == source.id) with
  | none => simp [hp] at hout
  | some pair =>
    rcases pair with ⟨id, rect⟩
    have he : (⟨source.id, source.role.id, rect, source.parent,
        source.exclusive⟩ : Box) = out := by
      simpa [hp, Pure.pure, Except.pure] using hout
    subst out
    exact ⟨source, hsource, rfl, rfl, rfl, rfl⟩

theorem successful_box_origins {m : Model} {result : Layered.FamilyResult}
    (h : Journey.layout m = .ok result) :
    ∀ out ∈ result.scene.boxes, ∃ source ∈ m.boxes,
      out.id = source.id ∧ out.role = source.role.id ∧
      out.parent = source.parent ∧ out.exclusive = source.exclusive := by
  have hs := Journey.layout_scene h
  unfold Journey.scene at hs
  obtain ⟨c, _, hs⟩ := bind_ok hs
  obtain ⟨g, _, hs⟩ := bind_ok hs
  obtain ⟨framesBands, _, hs⟩ := bind_ok hs
  obtain ⟨assignedItems, _, hs⟩ := bind_ok hs
  cases ht : g.title <;> simp only [ht] at hs
  all_goals
    obtain ⟨finalAssignedItems, _, hs⟩ := bind_ok hs
    obtain ⟨boxes, hboxes, hs⟩ := bind_ok hs
    obtain ⟨_, _, _, he, _⟩ := Journey.finish_ok hs
    rw [he]
    exact assigned_boxes_origins m finalAssignedItems.1 hboxes

theorem successful_label_origins {m : Model} {result : Layered.FamilyResult}
    (h : Journey.layout m = .ok result) :
    result.scene.labels = [] ∧ result.scene.layoutDump.labels = [] := by
  have hl := (Journey.scene_routes_labels_empty (Journey.layout_scene h)).2
  exact ⟨hl, by simp [Scene.layoutDump, hl]⟩

theorem journey_label_owners {m : Model} {result : Layered.FamilyResult}
    (h : Journey.layout m = .ok result) :
    _root_.WF5 result.scene.layoutDump := by
  have hl := (successful_label_origins h).2
  simp [_root_.WF5, hl]

def taskRects (c : Constants) (g : Input) : List Rect :=
  g.tasks.zipIdx.map fun (_, i) => taskRect c
    ((g.title.map fun t => t.caption.h + c.scoreStep).getD 0 +
      g.sections.foldl (fun h s => max h (s.caption.h + 2 * c.padY)) c.bandHeight +
      6 * c.scoreStep)
    (g.tasks.foldl (fun h t => max h
      (t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY)) c.taskHeight) i

def titleBox (g : Input) : Rect :=
  (g.title.map fun t => (⟨0, 0, t.caption.w, t.caption.h⟩ : Rect)).getD zeroRect

def peopleBox (c : Constants) (g : Input) (t : Task) (i : Nat) : Rect :=
  let block := centred c ((taskRects c g).getD i zeroRect)
    (t.caption.h + (t.people.map (·.h)).getD 0)
  { block with y := block.y + t.caption.h, h := (t.people.map (·.h)).getD 0 }

inductive PlacementOrigin (m : Model) (c : Constants) (g : Input)
    (frames : List Rect) (dx dy : Int) : String × Rect → Prop where
  | section (s : Card) (i : Nat) (hi : (s, i) ∈ g.sections.zipIdx) :
      PlacementOrigin m c g frames dx dy
        (s.id, shiftRect dx dy (frames.getD i zeroRect))
  | title (t : Card) (ht : g.title = some t) :
      PlacementOrigin m c g frames dx dy (t.id, shiftRect dx dy (titleBox g))
  | task (t : Task) (i : Nat) (hi : (t, i) ∈ g.tasks.zipIdx) :
      PlacementOrigin m c g frames dx dy
        (t.id, shiftRect dx dy ((taskRects c g).getD i zeroRect))
  | people (b : ModelBox) (hb : b ∈ m.boxes)
      (t : Task) (i : Nat) (hi : (t, i) ∈ g.tasks.zipIdx)
      (hk : shapeKind b = "people") (hp : b.parent = t.id) :
      PlacementOrigin m c g frames dx dy
        (b.id, shiftRect dx dy (peopleBox c g t i))

private theorem assigned_boxes_placements (m : Model) (assigned : List (String × Rect))
    (P : String × Rect → Prop) {boxes : List Box}
    (hassigned : ∀ pair ∈ assigned, P pair)
    (hboxes : (m.boxes.mapM fun (b : ModelBox) => (do
      let some (_, rect) := assigned.find? (fun (p : String × Rect) => p.1 == b.id)
        | throw LayoutError.domain
      pure (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box) :
        Except LayoutError Box)) = .ok boxes) :
    ∀ b ∈ boxes, P (b.id, b.rect) := by
  apply mapM_inv m.boxes _ (fun b : Box => P (b.id, b.rect)) _ hboxes
  intro b _ out hout
  cases hp : assigned.find? (fun p => p.1 == b.id) with
  | none => simp [hp] at hout
  | some pair =>
    rcases pair with ⟨id, rect⟩
    have he : (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box) = out := by
      simpa [hp, Pure.pure, Except.pure] using hout
    subst out
    have hmem := find_mem assigned _ hp
    have hid : id = b.id := by
      have hpred := List.find?_some hp
      exact beq_iff_eq.mp hpred
    simpa only [hid] using hassigned (id, rect) hmem

theorem task_rect_lookup (c : Constants) (g : Input)
    {t : Task} {i : Nat} (ht : (t, i) ∈ g.tasks.zipIdx) :
    (taskRects c g).getD i zeroRect =
      taskRect c
        ((g.title.map fun t => t.caption.h + c.scoreStep).getD 0 +
          g.sections.foldl (fun h s => max h (s.caption.h + 2 * c.padY))
            c.bandHeight + 6 * c.scoreStep)
        (g.tasks.foldl (fun h t => max h
          (t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY)) c.taskHeight) i := by
  have hi := (zipIdx_mem_bounds g.tasks ht).1
  simp only [taskRects, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_zipIdx, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some, Nat.zero_add]

private def FrameContainsTasks (c : Constants) (g : Input)
    (frames : List Rect) (dx dy : Int) : Prop :=
  ∀ (s : Card) (j : Nat), (s, j) ∈ g.sections.zipIdx →
    ∀ (t : Task) (i : Nat), (t, i) ∈ g.tasks.zipIdx → t.band = (j : Int) →
      (shiftRect dx dy (frames.getD j zeroRect)).Contained
        (shiftRect dx dy ((taskRects c g).getD i zeroRect))

private theorem successful_placement_data {m : Model} {result : Layered.FamilyResult}
    (h : Journey.layout m = .ok result) :
    ∃ c g, ∃ frames : List Rect, ∃ dx dy : Int,
      Journey.load m = .ok c ∧ Journey.decode m c = .ok g ∧
      FrameContainsTasks c g frames dx dy ∧
      ∀ b ∈ result.scene.boxes, PlacementOrigin m c g frames dx dy (b.id, b.rect) := by
  have hs := Journey.layout_scene h
  unfold Journey.scene at hs
  obtain ⟨c, hc, hs⟩ := bind_ok hs
  obtain ⟨g, hg, hs⟩ := bind_ok hs
  obtain ⟨framesBands, hframes, hs⟩ := bind_ok hs
  rcases framesBands with ⟨frames, bands⟩
  let faces := g.tasks.zipIdx.map fun (t, i) =>
    (⟨column c i + half c.taskWidth,
      faceY c ((g.title.map fun (t : Card) => t.caption.h + c.scoreStep).getD 0 +
        g.sections.foldl (fun h (s : Card) => max h (s.caption.h + 2 * c.padY))
          c.bandHeight) t.score⟩ : Point)
  let faceBoxes := faces.map fun p =>
    if m.profile == .cell then (⟨p.x, p.y, 1, 1⟩ : Rect)
    else ⟨p.x - c.radius, p.y - c.radius, 2 * c.radius, 2 * c.radius⟩
  let all := g.title.toList.map (fun _ => titleBox g) ++ frames ++
    taskRects c g ++ faceBoxes
  let ext := match all with
    | [] => zeroRect
    | r :: rs => rs.foldl Rect.unionRaw r
  let dx := c.margin - ext.x
  let dy := c.margin - ext.y
  let P := PlacementOrigin m c g frames dx dy
  have hframesGood : FrameContainsTasks c g frames dx dy := by
    intro s j hsec t i htask hband
    rw [task_rect_lookup c g htask]
    obtain ⟨hw, _, hb, hgap, hscore, _, _, _, _⟩ := load_pos hc
    have hbandHeight := (foldl_max_bound (fun s : Card =>
      s.caption.h + 2 * c.padY) g.sections c.bandHeight).1
    exact section_frames_contain_tasks g c _ _ _ _ dx dy
      hframes (by omega) (by omega) hsec htask hband
  obtain ⟨sectionState, hsections, hs⟩ := bind_ok hs
  have hsectionsGood : ∀ pair ∈ sectionState.1, P pair := by
    refine forIn_inv g.sections.zipIdx _ sectionState _
      (fun state => ∀ pair ∈ state.1, P pair) ?_ ?_ hsections
    · simp
    · intro entry hentry state next hstate hstep
      rcases entry with ⟨s, i⟩
      rcases state with ⟨assigned, items⟩
      dsimp only at hstep
      cases hstep
      dsimp only [ForInStep.value]
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hstate pair hp
      · have he := List.mem_singleton.mp hp
        subst pair
        exact PlacementOrigin.section (m := m) (c := c) (frames := frames)
          (dx := dx) (dy := dy) s i hentry
  refine ⟨c, g, frames, dx, dy, hc, hg, hframesGood, ?_⟩
  dsimp only at hs
  split at hs
  all_goals
    obtain ⟨taskState, htasks, hs⟩ := bind_ok hs
    have htasksGood : ∀ pair ∈ taskState.1, P pair := by
      refine forIn_inv g.tasks.zipIdx _ taskState _
        (fun state => ∀ pair ∈ state.1, P pair) ?_ ?_ htasks
      · intro pair hp
        first
        | exact hsectionsGood pair hp
        | rcases List.mem_append.mp hp with hp | hp
          · exact hsectionsGood pair hp
          · have he := List.mem_singleton.mp hp
            subst pair
            apply PlacementOrigin.title (m := m) (c := c) (frames := frames)
              (dx := dx) (dy := dy)
            assumption
      · intro entry hentry state next hstate hstep
        rcases entry with ⟨t, i⟩
        rcases state with ⟨assigned, items⟩
        dsimp only at hstep
        obtain ⟨peopleAssigned, hpeople, hstep⟩ := bind_ok hstep
        have hpeopleGood : ∀ pair ∈ peopleAssigned, P pair := by
          refine forIn_inv m.boxes _ peopleAssigned _
            (fun assigned => ∀ pair ∈ assigned, P pair) ?_ ?_ hpeople
          · intro pair hp
            rcases List.mem_append.mp hp with hp | hp
            · exact hstate pair hp
            · have he := List.mem_singleton.mp hp
              subst pair
              exact PlacementOrigin.task (m := m) (c := c) (frames := frames)
                (dx := dx) (dy := dy) t i hentry
          · intro b hb assigned next hgood hbox
            split at hbox
            · rename_i hkind
              cases hbox
              dsimp only [ForInStep.value]
              intro pair hp
              rcases List.mem_append.mp hp with hp | hp
              · exact hgood pair hp
              · have he := List.mem_singleton.mp hp
                subst pair
                have hk : (shapeKind b == "people") = true ∧
                    (b.parent == t.id) = true := by
                  simpa only [Bool.and_eq_true] using hkind
                exact PlacementOrigin.people (m := m) (c := c) (frames := frames)
                  (dx := dx) (dy := dy) b hb t i hentry
                  (beq_iff_eq.mp hk.1) (beq_iff_eq.mp hk.2)
            · cases hbox
              exact hgood
        cases hstep
        exact hpeopleGood
    obtain ⟨boxes, hboxes, hs⟩ := bind_ok hs
    obtain ⟨_, _, _, he, _⟩ := Journey.finish_ok hs
    rw [he]
    exact assigned_boxes_placements m taskState.1 P htasksGood hboxes

/-- The full successful scene execution, keeping the raw section-band `forIn` equation so
callers can recover the per-section index guards. -/
theorem successful_journey_scene {m : Model} {result : Layered.FamilyResult}
    (h : Journey.layout m = .ok result) :
    ∃ c g, ∃ frames bands : List Rect, ∃ dx dy : Int,
      Journey.load m = .ok c ∧ Journey.decode m c = .ok g ∧
      ForIn.forIn g.sections.zipIdx (([], []) : List Rect × List Rect)
        (sectionFrameStep g c
          ((g.title.map fun t => t.caption.h + c.scoreStep).getD 0)
          ((g.title.map fun t => t.caption.h + c.scoreStep).getD 0 +
            (g.sections.foldl (fun h s => max h (s.caption.h + 2 * c.padY))
              c.bandHeight) + 6 * c.scoreStep)
          (g.tasks.foldl (fun h t => max h
            (t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY))
            c.taskHeight)
          (g.sections.foldl (fun h s => max h (s.caption.h + 2 * c.padY))
            c.bandHeight)) = .ok (frames, bands) ∧
      FrameContainsTasks c g frames dx dy ∧
      ∀ b ∈ result.scene.boxes, PlacementOrigin m c g frames dx dy (b.id, b.rect) := by
  have hs := Journey.layout_scene h
  unfold Journey.scene at hs
  obtain ⟨c, hc, hs⟩ := bind_ok hs
  obtain ⟨g, hg, hs⟩ := bind_ok hs
  obtain ⟨framesBands, hframes, hs⟩ := bind_ok hs
  rcases framesBands with ⟨frames, bands⟩
  let faces := g.tasks.zipIdx.map fun (t, i) =>
    (⟨column c i + half c.taskWidth,
      faceY c ((g.title.map fun (t : Card) => t.caption.h + c.scoreStep).getD 0 +
        g.sections.foldl (fun h (s : Card) => max h (s.caption.h + 2 * c.padY))
          c.bandHeight) t.score⟩ : Point)
  let faceBoxes := faces.map fun p =>
    if m.profile == .cell then (⟨p.x, p.y, 1, 1⟩ : Rect)
    else ⟨p.x - c.radius, p.y - c.radius, 2 * c.radius, 2 * c.radius⟩
  let all := g.title.toList.map (fun _ => titleBox g) ++ frames ++
    taskRects c g ++ faceBoxes
  let ext := match all with
    | [] => zeroRect
    | r :: rs => rs.foldl Rect.unionRaw r
  let dx := c.margin - ext.x
  let dy := c.margin - ext.y
  let P := PlacementOrigin m c g frames dx dy
  have hframesGood : FrameContainsTasks c g frames dx dy := by
    intro s j hsec t i htask hband
    rw [task_rect_lookup c g htask]
    obtain ⟨hw, _, hb, hgap, hscore, _, _, _, _⟩ := load_pos hc
    have hbandHeight := (foldl_max_bound (fun s : Card =>
      s.caption.h + 2 * c.padY) g.sections c.bandHeight).1
    exact section_frames_contain_tasks g c _ _ _ _ dx dy
      hframes (by omega) (by omega) hsec htask hband
  obtain ⟨sectionState, hsections, hs⟩ := bind_ok hs
  have hsectionsGood : ∀ pair ∈ sectionState.1, P pair := by
    refine forIn_inv g.sections.zipIdx _ sectionState _
      (fun state => ∀ pair ∈ state.1, P pair) ?_ ?_ hsections
    · simp
    · intro entry hentry state next hstate hstep
      rcases entry with ⟨s, i⟩
      rcases state with ⟨assigned, items⟩
      dsimp only at hstep
      cases hstep
      dsimp only [ForInStep.value]
      intro pair hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hstate pair hp
      · have he := List.mem_singleton.mp hp
        subst pair
        exact PlacementOrigin.section (m := m) (c := c) (frames := frames)
          (dx := dx) (dy := dy) s i hentry
  refine ⟨c, g, frames, bands, dx, dy, hc, hg, hframes, hframesGood, ?_⟩
  dsimp only at hs
  split at hs
  all_goals
    obtain ⟨taskState, htasks, hs⟩ := bind_ok hs
    have htasksGood : ∀ pair ∈ taskState.1, P pair := by
      refine forIn_inv g.tasks.zipIdx _ taskState _
        (fun state => ∀ pair ∈ state.1, P pair) ?_ ?_ htasks
      · intro pair hp
        first
        | exact hsectionsGood pair hp
        | rcases List.mem_append.mp hp with hp | hp
          · exact hsectionsGood pair hp
          · have he := List.mem_singleton.mp hp
            subst pair
            apply PlacementOrigin.title (m := m) (c := c) (frames := frames)
              (dx := dx) (dy := dy)
            assumption
      · intro entry hentry state next hstate hstep
        rcases entry with ⟨t, i⟩
        rcases state with ⟨assigned, items⟩
        dsimp only at hstep
        obtain ⟨peopleAssigned, hpeople, hstep⟩ := bind_ok hstep
        have hpeopleGood : ∀ pair ∈ peopleAssigned, P pair := by
          refine forIn_inv m.boxes _ peopleAssigned _
            (fun assigned => ∀ pair ∈ assigned, P pair) ?_ ?_ hpeople
          · intro pair hp
            rcases List.mem_append.mp hp with hp | hp
            · exact hstate pair hp
            · have he := List.mem_singleton.mp hp
              subst pair
              exact PlacementOrigin.task (m := m) (c := c) (frames := frames)
                (dx := dx) (dy := dy) t i hentry
          · intro b hb assigned next hgood hbox
            split at hbox
            · rename_i hkind
              cases hbox
              dsimp only [ForInStep.value]
              intro pair hp
              rcases List.mem_append.mp hp with hp | hp
              · exact hgood pair hp
              · have he := List.mem_singleton.mp hp
                subst pair
                have hk : (shapeKind b == "people") = true ∧
                    (b.parent == t.id) = true := by
                  simpa only [Bool.and_eq_true] using hkind
                exact PlacementOrigin.people (m := m) (c := c) (frames := frames)
                  (dx := dx) (dy := dy) b hb t i hentry
                  (beq_iff_eq.mp hk.1) (beq_iff_eq.mp hk.2)
            · cases hbox
              exact hgood
        cases hstep
        exact hpeopleGood
    obtain ⟨boxes, hboxes, hs⟩ := bind_ok hs
    obtain ⟨_, _, _, he, _⟩ := Journey.finish_ok hs
    rw [he]
    exact assigned_boxes_placements m taskState.1 P htasksGood hboxes
theorem successful_placement_origins {m : Model} {result : Layered.FamilyResult}
    (h : Journey.layout m = .ok result) :
    ∃ c g, ∃ frames : List Rect, ∃ dx dy : Int,
      Journey.load m = .ok c ∧ Journey.decode m c = .ok g ∧
      ∀ b ∈ result.scene.boxes, PlacementOrigin m c g frames dx dy (b.id, b.rect) := by
  obtain ⟨c, g, frames, dx, dy, hc, hg, _, hp⟩ := successful_placement_data h
  exact ⟨c, g, frames, dx, dy, hc, hg, hp⟩


theorem source_id_unique (xs : List ModelBox)
    (hn : (xs.map (·.id)).Nodup) {a b : ModelBox}
    (ha : a ∈ xs) (hb : b ∈ xs) (hid : a.id = b.id) : a = b := by
  obtain ⟨i, hia⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨j, hjb⟩ := List.mem_iff_getElem?.mp hb
  have he : i = j := by
    apply Tree.nodup_getElem?_inj hn (c := a.id)
    · simp only [List.getElem?_map, hia, Option.map_some]
    · simp only [List.getElem?_map, hjb, Option.map_some, hid]
  subst j
  exact Option.some.inj (hia.symm.trans hjb)

theorem section_source (m : Model) (c : Constants) (g : Input)
    (hi : DecodeInv m c m.boxes g) {s : Card} {i : Nat}
    (hs : (s, i) ∈ g.sections.zipIdx) :
    ∃ b ∈ m.boxes, isSecBox b ∧ b.id = s.id := by
  have hm : s.id ∈ g.sections.map (·.id) :=
    List.mem_map.mpr ⟨s, (zipIdx_mem_bounds g.sections hs).2, rfl⟩
  rw [hi.secIds] at hm
  obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
  obtain ⟨hb, hk⟩ := List.mem_filter.mp hb
  exact ⟨b, hb, hk, he⟩

theorem title_source (m : Model) (c : Constants) (g : Input)
    (hi : DecodeInv m c m.boxes g) {t : Card} (ht : g.title = some t) :
    ∃ b ∈ m.boxes, isTitleBox b ∧ b.id = t.id := by
  have he : ((m.boxes.filter isTitleBox).map (·.id)).getLast? = some t.id := by
    rw [← hi.titleId]
    simp only [ht, Option.map_some]
  obtain ⟨b, hb, hid⟩ := List.mem_map.mp (List.mem_of_getLast? he)
  obtain ⟨hb, hk⟩ := List.mem_filter.mp hb
  exact ⟨b, hb, hk, hid⟩

theorem task_source (m : Model) (c : Constants) (g : Input)
    (hi : DecodeInv m c m.boxes g) {t : Task} {i : Nat}
    (ht : (t, i) ∈ g.tasks.zipIdx) :
    ∃ b ∈ m.boxes, isTaskBox b ∧ b.id = t.id ∧
      t.band = bandVal g.sections b.parent ∧
      (b.parent = "" ∨ b.parent ∈ g.sections.map (·.id)) := by
  have htget := List.mem_zipIdx_iff_getElem?.mp ht
  obtain ⟨hit, hteq⟩ := List.getElem?_eq_some_iff.mp htget
  have hlen : g.tasks.length = (m.boxes.filter isTaskBox).length := by
    have he := congrArg List.length hi.taskIds
    simpa only [List.length_map] using he
  have hib : i < (m.boxes.filter isTaskBox).length := by omega
  let b := (m.boxes.filter isTaskBox)[i]
  have hb := List.mem_filter.mp (List.getElem_mem hib)
  have hid : t.id = b.id := by
    have he := congrArg (fun ids : List String => ids[i]?) hi.taskIds
    simpa only [List.getElem?_map, htget, List.getElem?_eq_getElem hib,
      Option.map_some, Option.some.injEq] using he
  refine ⟨b, hb.1, hb.2, hid.symm, ?_, ?_⟩
  · simpa only [hteq] using hi.taskBand i hit hib
  · exact hi.taskParentOK i hit hib

theorem section_id_shape (m : Model) (c : Constants) (g : Input)
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {b : ModelBox} (hb : b ∈ m.boxes) {s : Card} {i : Nat}
    (hs : (s, i) ∈ g.sections.zipIdx) (hid : b.id = s.id) :
    shapeKind b = "section" := by
  obtain ⟨src, hsrc, hk, he⟩ := section_source m c g hi hs
  have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf)
    hb hsrc (hid.trans he.symm)
  subst b
  exact beq_iff_eq.mp hk

theorem title_id_shape (m : Model) (c : Constants) (g : Input)
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {b : ModelBox} (hb : b ∈ m.boxes) {t : Card}
    (ht : g.title = some t) (hid : b.id = t.id) :
    shapeKind b = "title" := by
  obtain ⟨src, hsrc, hk, he⟩ := title_source m c g hi ht
  have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf)
    hb hsrc (hid.trans he.symm)
  subst b
  exact beq_iff_eq.mp hk

theorem task_id_shape (m : Model) (c : Constants) (g : Input)
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {b : ModelBox} (hb : b ∈ m.boxes) {t : Task} {i : Nat}
    (ht : (t, i) ∈ g.tasks.zipIdx) (hid : b.id = t.id) :
    shapeKind b = "task" := by
  obtain ⟨src, hsrc, hk, he, _⟩ := task_source m c g hi ht
  have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf)
    hb hsrc (hid.trans he.symm)
  subst b
  exact beq_iff_eq.mp hk

theorem section_band_index (g : Input) (hi : (g.sections.map (·.id)).Nodup)
    {s : Card} {j : Nat} (hs : (s, j) ∈ g.sections.zipIdx)
    (hne : s.id ≠ "") : bandVal g.sections s.id = (j : Int) := by
  have hsget := List.mem_zipIdx_iff_getElem?.mp hs
  unfold bandVal
  simp only [beq_iff_eq, hne, ↓reduceIte]
  cases hf : g.sections.findIdx? (fun x => x.id == s.id) with
  | none =>
    have hn := List.findIdx?_eq_none_iff.mp hf s
      (zipIdx_mem_bounds g.sections hs).2
    simp at hn
  | some k =>
    obtain ⟨hk, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    have he : k = j := by
      apply Tree.nodup_getElem?_inj hi (c := s.id)
      · simp only [List.getElem?_map, List.getElem?_eq_getElem hk,
          Option.map_some, beq_iff_eq.mp hp]
      · simp only [List.getElem?_map, hsget, Option.map_some]
    subst k
    rfl

theorem zip_id_index {α : Type} (xs : List α) (key : α → String)
    (hn : (xs.map key).Nodup) {a b : α} {i j : Nat}
    (ha : (a, i) ∈ xs.zipIdx) (hb : (b, j) ∈ xs.zipIdx)
    (hid : key a = key b) : i = j := by
  apply Tree.nodup_getElem?_inj hn (c := key a)
  · simp only [List.getElem?_map, List.mem_zipIdx_iff_getElem?.mp ha,
      Option.map_some]
  · simp only [List.getElem?_map, List.mem_zipIdx_iff_getElem?.mp hb,
      Option.map_some, hid]

private theorem section_placement_rect (m : Model) (c : Constants) (g : Input)
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    (frames : List Rect) (dx dy : Int) {s : Card} {j : Nat}
    (hs : (s, j) ∈ g.sections.zipIdx) {id : String} {rect : Rect}
    (horigin : PlacementOrigin m c g frames dx dy (id, rect))
    (hid : id = s.id) : rect = shiftRect dx dy (frames.getD j zeroRect) := by
  obtain ⟨src, hsrc, hkind, hsrcId⟩ := section_source m c g hi hs
  have hsrcShape : shapeKind src = "section" := beq_iff_eq.mp hkind
  cases horigin with
  | «section» other k hk =>
    have he := zip_id_index g.sections (fun s : Card => s.id)
      hi.secIdsNodup hk hs hid
    subst k
    rfl
  | title other ht =>
    have hbad := title_id_shape m c g hwf hi hsrc ht (hsrcId.trans hid.symm)
    simp [hsrcShape] at hbad
  | task other k hk =>
    have hbad := task_id_shape m c g hwf hi hsrc hk (hsrcId.trans hid.symm)
    simp [hsrcShape] at hbad
  | people b hb t i ht hk _ =>
    have hbad := section_id_shape m c g hwf hi hb hs hid
    simp [hk] at hbad

private theorem task_placement_rect (m : Model) (c : Constants) (g : Input)
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    (frames : List Rect) (dx dy : Int) {t : Task} {i : Nat}
    (ht : (t, i) ∈ g.tasks.zipIdx) {id : String} {rect : Rect}
    (horigin : PlacementOrigin m c g frames dx dy (id, rect))
    (hid : id = t.id) :
    rect = shiftRect dx dy ((taskRects c g).getD i zeroRect) := by
  obtain ⟨src, hsrc, hkind, hsrcId, _⟩ := task_source m c g hi ht
  have hsrcShape : shapeKind src = "task" := beq_iff_eq.mp hkind
  cases horigin with
  | «section» other k hk =>
    have hbad := section_id_shape m c g hwf hi hsrc hk (hsrcId.trans hid.symm)
    simp [hsrcShape] at hbad
  | title other ht =>
    have hbad := title_id_shape m c g hwf hi hsrc ht (hsrcId.trans hid.symm)
    simp [hsrcShape] at hbad
  | task other k hk =>
    have he := zip_id_index g.tasks (fun t : Task => t.id)
      hi.taskIdsNodup hk ht hid
    subst k
    rfl
  | people b hb other k hk hkind _ =>
    have hbad := task_id_shape m c g hwf hi hb ht hid
    simp [hkind] at hbad

theorem people_inside_card (m : Model) (c : Constants) (g : Input)
    (hi : DecodeInv m c m.boxes g) (hc : LoadPos c)
    {t : Task} {i : Nat} (ht : (t, i) ∈ g.tasks.zipIdx) :
    ((taskRects c g).getD i zeroRect).Contained (peopleBox c g t i) := by
  have hmem := (zipIdx_mem_bounds g.tasks ht).2
  have hcaption := hi.taskCapPos t.caption (List.mem_map.mpr ⟨t, hmem, rfl⟩)
  have hheight := task_height_bound g c hmem
  have hcardHeight : ((taskRects c g).getD i zeroRect).h =
      g.tasks.foldl (fun h t => max h
        (t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY))
        c.taskHeight := by
    rw [task_rect_lookup c g ht]
    rfl
  obtain ⟨_, _, _, _, _, _, hpadX, hpadY, _⟩ := hc
  exact journey_card_contains_people c _ _ _ hpadX (by omega) (by omega)

theorem journey_c3 {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : Journey.layout m = .ok result) :
    Validator.C3 result.scene.layoutDump := by
  obtain ⟨c, g, frames, dx, dy, hc, hg, hframes, hplaced⟩ :=
    successful_placement_data h
  have hi := decode_ok m c hwf hg
  have hmeta := successful_box_origins h
  have hrel : ∀ pair, PlacementOrigin m c g frames dx dy pair →
      ∀ out ∈ result.scene.boxes, out.id = pair.1 → out.rect = pair.2 →
        out.parent ≠ "" →
        ∀ parent ∈ result.scene.boxes, parent.id = out.parent →
          parent.rect.Contained out.rect := by
    intro pair horigin
    cases horigin with
    | «section» s j hsec =>
      intro out hout hid _ hne parent _ _
      obtain ⟨source, hsource, hsourceId, _, hparent, _⟩ := hmeta out hout
      have hk := section_id_shape m c g hwf hi hsource (hs := hsec)
        (hsourceId.symm.trans hid)
      have hroot := hi.parentRoots source hsource (Or.inr (by
        simp only [isSecBox, hk, beq_self_eq_true]))
      exact False.elim (hne (hparent.trans hroot))
    | title t ht =>
      intro out hout hid _ hne parent _ _
      obtain ⟨source, hsource, hsourceId, _, hparent, _⟩ := hmeta out hout
      have hk := title_id_shape m c g hwf hi hsource ht
        (hsourceId.symm.trans hid)
      have hroot := hi.parentRoots source hsource (Or.inl (by
        simp only [isTitleBox, hk, beq_self_eq_true]))
      exact False.elim (hne (hparent.trans hroot))
    | task t i ht =>
      intro out hout hid hrect hne parent hparent hparentId
      obtain ⟨source, hsource, hsourceId, _, hsourceParent, _⟩ := hmeta out hout
      obtain ⟨taskSrc, htaskSrc, _, htaskId, hband, hparentOK⟩ :=
        task_source m c g hi ht
      have he := source_id_unique m.boxes (Model.boxIds_nodup hwf)
        hsource htaskSrc (hsourceId.symm.trans (hid.trans htaskId.symm))
      subst source
      have hsrcNe : taskSrc.parent ≠ "" := by
        intro he
        exact hne (hsourceParent.trans he)
      rcases hparentOK with hroot | hmember
      · exact False.elim (hsrcNe hroot)
      · obtain ⟨s, hs, hsid⟩ := List.mem_map.mp hmember
        obtain ⟨j, hsj⟩ := List.mem_iff_getElem?.mp hs
        have hsec : (s, j) ∈ g.sections.zipIdx :=
          List.mem_zipIdx_iff_getElem?.mpr hsj
        have hsNe : s.id ≠ "" := by
          intro he
          exact hsrcNe (hsid.symm.trans he)
        have hbandIndex : t.band = (j : Int) := by
          rw [hband, ← hsid]
          exact section_band_index g hi.secIdsNodup hsec hsNe
        have hparentRect := section_placement_rect m c g hwf hi frames dx dy
          hsec (hplaced parent hparent)
          (hparentId.trans (hsourceParent.trans hsid.symm))
        rw [hrect, hparentRect]
        exact hframes s j hsec t i ht hbandIndex
    | people b hb t i ht _ hp =>
      intro out hout hid hrect _ parent hparent hparentId
      obtain ⟨source, hsource, hsourceId, _, hsourceParent, _⟩ := hmeta out hout
      have he := source_id_unique m.boxes (Model.boxIds_nodup hwf)
        hsource hb (hsourceId.symm.trans hid)
      subst source
      have hparentRect := task_placement_rect m c g hwf hi frames dx dy ht
        (hplaced parent hparent) (hparentId.trans (hsourceParent.trans hp))
      rw [hrect, hparentRect]
      exact journey_origin_preserves_containment _ _ dx dy
        (people_inside_card m c g hi (load_pos hc) ht)
  intro out hout hne parent hlookup
  have hout' : out ∈ result.scene.boxes := hout
  have hlookup' : result.scene.boxes.find? (fun b => b.id == out.parent) =
      some parent := hlookup
  have hparent := find_mem result.scene.boxes _ hlookup'
  have hpred := @_root_.List.find?_some Box
    (fun (b : Box) => b.id == out.parent) parent result.scene.boxes hlookup'
  have hid : parent.id = out.parent := beq_iff_eq.mp hpred
  exact hrel (out.id, out.rect) (hplaced out hout') out hout'
    rfl rfl hne parent hparent hid

def narrowPeopleWitness : Model :=
  { kind := "journey"
    profile := .vector
    options := { config := [("width", .integer 1)] }
    boxes :=
      [{ id := "task", shape := "task:3" },
       { id := "people", parent := "task", shape := "people" }]
    labels :=
      [{ id := "task.label", owner := "task", text := "Task" },
       { id := "people.label", owner := "people", text := "Alice" }] }

theorem narrowPeopleWitness_wellFormed : WellFormed narrowPeopleWitness := by
  decide

theorem narrowPeopleWitness_withinLimits : WithinLimits narrowPeopleWitness := by
  decide

theorem journey_c7 {m : Model} {result : Layered.FamilyResult}
    (h : Journey.layout m = .ok result) : Validator.C7 result.scene.layoutDump :=
  Journey.journey_c7 h

/-- C2 falsifier before the admission guard: an empty task id makes the people card, whose
parent is that id, look like a root sibling of its own task. -/
def emptyIdTaskWitness : Model :=
  { kind := "journey"
    profile := .vector
    boxes :=
      [{ id := "", shape := "task:3" },
       { id := "people", parent := "", shape := "people" }]
    labels :=
      [{ id := "people.label", owner := "people", text := "Alice" }] }

theorem emptyIdTaskWitness_wellFormed : WellFormed emptyIdTaskWitness := by
  decide

theorem emptyIdTaskWitness_withinLimits : WithinLimits emptyIdTaskWitness := by
  decide

theorem emptyIdTaskWitness_rejected :
    Journey.layout emptyIdTaskWitness = .error (.geometry .domain) := by
  have hp : Journey.admitted emptyIdTaskWitness = false := by decide
  simp only [Journey.layout, hp, Bool.false_eq_true, ↓reduceIte]

/-- C8a falsifier before the admission guard: the same empty task id, with the task card
declared as a group so the overlapping people card is a foreign box with no ancestor. -/
def emptyIdGroupWitness : Model :=
  { kind := "journey"
    profile := .vector
    boxes :=
      [{ id := "", role := .group, exclusive := false, shape := "task:3" },
       { id := "people", parent := "", shape := "people" }]
    labels :=
      [{ id := "people.label", owner := "people", text := "Alice" }] }

theorem emptyIdGroupWitness_wellFormed : WellFormed emptyIdGroupWitness := by
  decide

theorem emptyIdGroupWitness_withinLimits : WithinLimits emptyIdGroupWitness := by
  decide

theorem emptyIdGroupWitness_rejected :
    Journey.layout emptyIdGroupWitness = .error (.geometry .domain) := by
  have hp : Journey.admitted emptyIdGroupWitness = false := by decide
  simp only [Journey.layout, hp, Bool.false_eq_true, ↓reduceIte]

theorem journey_c8b {m : Model} {result : Layered.FamilyResult}
    (h : Journey.layout m = .ok result) : Validator.C8b result.scene.layoutDump :=
  Journey.journey_c8b h

/-! ### Ancestor lists of the journey dump -/

theorem box?_some {d : LayoutDump} {id : String} {b : Box}
    (h : d.box? id = some b) : b.id = id ∧ b ∈ d.boxes := by
  unfold LayoutDump.box? at h
  revert h
  induction d.boxes with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    simp only [List.find?_cons] at h
    cases hbeq : (x.id == id) with
    | true =>
      rw [hbeq] at h
      simp only at h
      have hx : x = b := Option.some.inj h
      subst hx
      exact ⟨beq_iff_eq.mp hbeq, List.mem_cons_self ..⟩
    | false =>
      rw [hbeq] at h
      simp only at h
      obtain ⟨heq, hm⟩ := ih h
      exact ⟨heq, List.mem_cons_of_mem x hm⟩

private theorem ancestors_nil_parent (d : LayoutDump) {id : String}
    (h : (d.box? id).map (fun b => b.parent) = some "") :
    LayoutDump.ancestors d id = [] := by
  unfold LayoutDump.ancestors
  cases hb : d.box? id with
  | none => simp [hb] at h
  | some b =>
    have hp : b.parent = "" := by
      have h2 := h
      simp only [hb, Option.map_some] at h2
      exact Option.some.inj h2
    cases d.boxes.length with
    | zero => rfl
    | succ n =>
      simp only [LayoutDump.ancestors.go, hb, hp, ite_true]

/-- The frame rectangle stored at section index `j` is the admitted section rectangle over
the section's own task-index interval. -/
theorem frame_rect_eq {frames : List Rect} {g : Input} {c : Constants}
    {top taskTop taskH : Int} {j first : Nat}
    (heq : frames = g.sections.zipIdx.map
      (fun e => sectionFrame g c top taskTop taskH e.2))
    (hj : j < g.sections.length)
    (hhead : (sectionIndices g j).head? = some first) :
    frames.getD j zeroRect =
      sectionRect c top (taskTop + taskH - top) first
        ((sectionIndices g j).getLast?.getD first) := by
  have hlookup : frames.getD j zeroRect =
      sectionFrame g c top taskTop taskH j := by
    rw [heq]
    have hj' := List.getElem?_eq_getElem hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_zipIdx, List.getElem?_eq_getElem hj,
      Option.map_some, Option.getD_some, Nat.zero_add]
  rw [hlookup]
  unfold sectionFrame
  simp [hhead]

/-- Two distinct admitted sections occupy disjoint task-index intervals: an overlapping
index would have to carry two different bands. -/
theorem section_ranges_disjoint {g : Input}
    {j1 j2 first1 last1 first2 last2 : Nat}
    (hj1 : j1 ≠ j2)
    (h1 : (g.tasks.zipIdx.all fun (t, k) =>
      decide (first1 ≤ k ∧ k ≤ last1) == (t.band == (j1 : Int))) = true)
    (h2 : (g.tasks.zipIdx.all fun (t, k) =>
      decide (first2 ≤ k ∧ k ≤ last2) == (t.band == (j2 : Int))) = true)
    (hne1 : first1 ≤ last1) (hne2 : first2 ≤ last2)
    (_hlt1 : last1 < g.tasks.length) (_hlt2 : last2 < g.tasks.length) :
    last1 < first2 ∨ last2 < first1 := by
  apply Classical.byContradiction
  intro hcon
  have hA : first2 ≤ last1 := by
    have := Nat.not_lt.mp (fun h => hcon (Or.inl h))
    omega
  have hB : first1 ≤ last2 := by
    have := Nat.not_lt.mp (fun h => hcon (Or.inr h))
    omega
  have hk1 : first1 ≤ max first1 first2 := Nat.le_max_left _ _
  have hk2 : first2 ≤ max first1 first2 := Nat.le_max_right _ _
  have hkl1 : max first1 first2 ≤ last1 := by omega
  have hkl2 : max first1 first2 ≤ last2 := by omega
  have hklt : max first1 first2 < g.tasks.length := by omega
  have htk : (g.tasks[max first1 first2]'hklt, max first1 first2) ∈ g.tasks.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hklt)
  have hb1 : (g.tasks[max first1 first2]'hklt).band = (j1 : Int) := by
    have hk := (List.all_eq_true.mp h1)
      (g.tasks[max first1 first2]'hklt, max first1 first2) htk
    have hdec : decide (first1 ≤ max first1 first2 ∧ max first1 first2 ≤ last1) =
        ((g.tasks[max first1 first2]'hklt).band == (j1 : Int)) := beq_iff_eq.mp hk
    have hleft : decide (first1 ≤ max first1 first2 ∧ max first1 first2 ≤ last1) = true := by
      simp [hk1, hkl1]
    rw [hleft] at hdec
    exact beq_iff_eq.mp hdec.symm
  have hb2 : (g.tasks[max first1 first2]'hklt).band = (j2 : Int) := by
    have hk := (List.all_eq_true.mp h2)
      (g.tasks[max first1 first2]'hklt, max first1 first2) htk
    have hdec : decide (first2 ≤ max first1 first2 ∧ max first1 first2 ≤ last2) =
        ((g.tasks[max first1 first2]'hklt).band == (j2 : Int)) := beq_iff_eq.mp hk
    have hleft : decide (first2 ≤ max first1 first2 ∧ max first1 first2 ≤ last2) = true := by
      simp [hk2, hkl2]
    rw [hleft] at hdec
    exact beq_iff_eq.mp hdec.symm
  have : (j1 : Int) = (j2 : Int) := hb1.symm.trans hb2
  exact hj1 (by omega)

/-- Column `i` plus one task width stays left of column `j` when `i < j`. -/
private theorem column_far (c : Constants) (i j : Nat)
    (hp : 0 ≤ c.columnGap) (hw : 0 < c.taskWidth) (h : i < j) :
    column c i + c.taskWidth ≤ column c j := by
  have hpos : 0 ≤ c.taskWidth + c.columnGap := by omega
  have hm := Int.mul_le_mul_of_nonneg_right (show (i : Int) + 1 ≤ j by omega) hpos
  unfold column
  simp only [Int.add_mul] at *
  omega
private theorem ancestors_cons_parent (d : LayoutDump) {id : String}
    (h : ∃ b, d.box? id = some b ∧ b.parent ≠ "") :
    ∃ p, p ≠ "" ∧ p ∈ LayoutDump.ancestors d id := by
  unfold LayoutDump.ancestors
  obtain ⟨b, hb, hp⟩ := h
  cases hl : d.boxes.length with
  | zero =>
    have hnil : d.boxes = [] := List.length_eq_zero_iff.mp hl
    simp only [LayoutDump.box?, hnil, List.find?_nil] at hb
    cases hb
  | succ n =>
    simp only [LayoutDump.ancestors.go, hb]
    split
    · rename_i hcond
      exact absurd hcond (by simp [hp])
    · exact ⟨b.parent, hp, List.mem_cons_self ..⟩


/-- `bandVal` of a nonempty section id is a nonnegative section index, never `-1`. -/
private theorem bandVal_ne_neg_one_local {secs : List Card} {p : String}
    (hp : p ≠ "") (hmem : p ∈ secs.map (·.id)) : bandVal secs p ≠ (-1 : Int) := by
  unfold bandVal
  simp only [hp, beq_iff_eq, ite_false]
  cases hf : secs.findIdx? (·.id == p) with
  | none =>
    obtain ⟨s, hs, hid⟩ := List.mem_map.mp hmem
    have ha := List.findIdx?_eq_none_iff.mp hf s hs
    have hb2 : (s.id == p) = true := by simp [hid]
    rw [hb2] at ha
    cases ha
  | some i => simp
/-- The band of a decoded task is `-1` exactly when its source box is unparented. -/
private theorem task_band_neg_iff {m : Model} {c : Constants} {g : Input}
    (_hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {t : Task} {i : Nat} (ht : (t, i) ∈ g.tasks.zipIdx) :
    t.band = (-1 : Int) ↔
      ((m.boxes.filter isTaskBox)[i]?).map (·.parent) = some "" := by
  have hi' := (zipIdx_mem_bounds g.tasks ht).1
  have hlen : g.tasks.length = (m.boxes.filter isTaskBox).length := by
    have he := congrArg List.length hi.taskIds
    simpa only [List.length_map] using he
  have hilt : i < (m.boxes.filter isTaskBox).length := by omega
  have hgetD : (m.boxes.filter isTaskBox)[i]? =
      some ((m.boxes.filter isTaskBox)[i]'hilt) :=
    List.getElem?_eq_getElem hilt
  have hband := hi.taskBand i hi' (by omega)
  have hparentOK := hi.taskParentOK i hi' (by omega)
  have hget : g.tasks[i]'hi' = t := by
    have hm := List.mem_zipIdx_iff_getElem?.mp ht
    rw [List.getElem?_eq_getElem hi'] at hm
    exact Option.some.inj hm
  rw [hget] at hband
  have hsrc : ((m.boxes.filter isTaskBox)[i]?).map (·.parent) =
      some ((m.boxes.filter isTaskBox)[i]'hilt).parent := by
    rw [hgetD]; rfl
  rw [hsrc]
  constructor
  · intro hneg
    apply Classical.byContradiction
    intro hne
    have hparent : ((m.boxes.filter isTaskBox)[i]'hilt).parent ≠ "" := by
      intro h0
      apply hne
      rw [h0]
    have hmem : ((m.boxes.filter isTaskBox)[i]'hilt).parent ∈
        g.sections.map (·.id) := by
      rcases hparentOK with h0 | h1
      · have : ((m.boxes.filter isTaskBox)[i]'hilt).parent = "" := h0
        exact absurd this hparent
      · exact h1
    rw [hband] at hneg
    exact (bandVal_ne_neg_one_local hparent hmem) hneg
  · intro h0
    have hparent : ((m.boxes.filter isTaskBox)[i]'hilt).parent = "" :=
      Option.some.inj h0
    rw [hband, hparent]
    simp [bandVal]

/-- A banded task's band is its parent section's zipIdx index. -/
private theorem task_band_eq_section {m : Model} {c : Constants} {g : Input}
    (_hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {t : Task} {i : Nat} (ht : (t, i) ∈ g.tasks.zipIdx) :
    t.band ≠ (-1 : Int) →
    ∃ s : Card, ∃ j : Nat, (s, j) ∈ g.sections.zipIdx ∧
      s.id = (((m.boxes.filter isTaskBox)[i]?).map ModelBox.parent).getD "" ∧
      t.band = (j : Int) := by
  have hi' := (zipIdx_mem_bounds g.tasks ht).1
  have hlen : g.tasks.length = (m.boxes.filter isTaskBox).length := by
    have he := congrArg List.length hi.taskIds
    simpa only [List.length_map] using he
  have hilt : i < (m.boxes.filter isTaskBox).length := by omega
  have hgetD : (m.boxes.filter isTaskBox)[i]? =
      some ((m.boxes.filter isTaskBox)[i]'hilt) :=
    List.getElem?_eq_getElem hilt
  have hband := hi.taskBand i hi' (by omega)
  have hparentOK := hi.taskParentOK i hi' (by omega)
  have hget : g.tasks[i]'hi' = t := by
    have hm := List.mem_zipIdx_iff_getElem?.mp ht
    rw [List.getElem?_eq_getElem hi'] at hm
    exact Option.some.inj hm
  rw [hget] at hband
  intro hnegband
  have hne : ((m.boxes.filter isTaskBox)[i]'hilt).parent ≠ "" := by
    intro h0
    apply hnegband
    rw [hband]
    simp [h0, bandVal]
  have hmem : ((m.boxes.filter isTaskBox)[i]'hilt).parent ∈
      g.sections.map (·.id) := by
    rcases hparentOK with h0 | h1
    · exact absurd h0 hne
    · exact h1
  obtain ⟨s, hs, hid⟩ := List.mem_map.mp hmem
  obtain ⟨j, hsj⟩ := List.mem_iff_getElem?.mp hs
  have hsec : (s, j) ∈ g.sections.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hsj
  have hsNe : s.id ≠ "" := by
    intro he
    exact hne (he ▸ hid).symm
  have hbval : bandVal g.sections s.id = (j : Int) :=
    section_band_index g hi.secIdsNodup hsec hsNe
  have hsrcid : (((m.boxes.filter isTaskBox)[i]?).map ModelBox.parent).getD "" =
      s.id := by
    rw [hgetD]
    simp [hid]
  exact ⟨s, j, hsec, hsrcid.symm, by rw [hband, ← hid]; exact hbval⟩

/-! ### Generic list and dump helpers -/

theorem map_inj_of_nodup {α β : Type} [DecidableEq β] {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y := by
  intro l
  induction l with
  | nil => intro _ x y hx _; cases hx
  | cons a rest ih =>
    intro hn x y hx hy heq
    simp only [List.map_cons] at hn
    have hpair := List.pairwise_cons.mp hn
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · have hfx : f x ≠ f y := hpair.1 (f y) (List.mem_map_of_mem hy')
        exact absurd heq hfx
    · rcases List.mem_cons.mp hy with rfl | hy'
      · have hfy : f y ≠ f x := hpair.1 (f x) (List.mem_map_of_mem hx')
        exact absurd heq.symm hfy
      · exact ih hpair.2 hx' hy' heq

private theorem find_self_by_id {l : List Box}
    (hn : (l.map (·.id)).Nodup) : ∀ {b : Box}, b ∈ l →
    l.find? (fun x => x.id == b.id) = some b := by
  induction l with
  | nil => intro b hb; cases hb
  | cons x rest ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simp
    · simp only [List.find?_cons]
      have h1 := List.nodup_cons.mp hn
      have hx : (x.id == b.id) = false := by
        apply Bool.eq_false_iff.mpr
        intro he
        have he' : x.id = b.id := beq_iff_eq.mp he
        exact h1.1 (he' ▸ List.mem_map_of_mem hb : x.id ∈ rest.map (·.id))
      rw [hx]
      exact ih h1.2 hb

private theorem mapM_ids (xs : List ModelBox)
    (f : ModelBox → Except LayoutError Box) {ys : List Box}
    (hstep : ∀ a ∈ xs, ∀ b, f a = .ok b → b.id = a.id)
    (hrun : xs.mapM f = .ok ys) : ys.map (·.id) = xs.map (·.id) := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure] at hrun
    cases hrun
    simp
  | cons a rest ih =>
    cases ha : f a with
    | error e =>
      simp only [List.mapM_cons, ha, Bind.bind, Except.bind] at hrun
      cases hrun
    | ok b =>
      cases hr : rest.mapM f with
      | error e =>
        simp only [List.mapM_cons, ha, hr, Bind.bind, Except.bind] at hrun
        cases hrun
      | ok bs =>
        have he : b :: bs = ys := by
          simpa only [List.mapM_cons, ha, hr, Bind.bind, Except.bind,
            Pure.pure, Except.pure, Functor.map, Except.map, Except.ok.injEq]
            using hrun
        subst ys
        rw [List.map_cons, List.map_cons]
        have hb := hstep a (by simp) b ha
        rw [hb]
        congr 1
        exact ih (fun x hx => hstep x (List.mem_cons_of_mem a hx)) hr

private theorem dump_ids_eq {m : Model} {result : Layered.FamilyResult}
    (h : Journey.layout m = .ok result) :
    (result.scene.boxes.map (·.id)) = (m.boxes.map (·.id)) := by
  have hs := Journey.layout_scene h
  unfold Journey.scene at hs
  obtain ⟨c, _, hs⟩ := bind_ok hs
  obtain ⟨g, _, hs⟩ := bind_ok hs
  obtain ⟨framesBands, _, hs⟩ := bind_ok hs
  obtain ⟨sectionState, _, hs⟩ := bind_ok hs
  cases ht : g.title <;> simp only [ht] at hs
  all_goals
    obtain ⟨taskState, _, hs⟩ := bind_ok hs
    obtain ⟨boxes, hboxes, hs⟩ := bind_ok hs
    obtain ⟨_, _, _, he, _⟩ := Journey.finish_ok hs
    rw [he]
    exact mapM_ids m.boxes _ (by
      intro b _ out hout
      cases hp : taskState.1.find? (fun p => p.1 == b.id) with
      | none => simp [hp] at hout
      | some pair =>
        rcases pair with ⟨id, rect⟩
        have heq : (⟨b.id, b.role.id, rect, b.parent, b.exclusive⟩ : Box) = out := by
          simpa [hp, Pure.pure, Except.pure] using hout
        subst out
        rfl) hboxes

private theorem dump_ids_nodup {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : Journey.layout m = .ok result) :
    (result.scene.boxes.map (·.id)).Nodup := by
  rw [dump_ids_eq h]
  exact Model.boxIds_nodup hwf

theorem dump_of_source {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : Journey.layout m = .ok result)
    {src : ModelBox} (hsrc : src ∈ m.boxes) :
    ∃ out ∈ result.scene.boxes, out.id = src.id ∧ out.parent = src.parent := by
  have hback := successful_box_origins h
  have hids := dump_ids_eq h
  have hmem : src.id ∈ result.scene.boxes.map (·.id) := by rw [hids]; exact List.mem_map_of_mem hsrc
  obtain ⟨out, hout, hid⟩ := List.mem_map.mp hmem
  obtain ⟨source, hsource, hsourceId, _, hsourceParent, _⟩ := hback out hout
  have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf)
    hsrc hsource (hid.symm.trans hsourceId)
  exact ⟨out, hout, hid, hsame ▸ hsourceParent⟩

theorem dump_lookup_self {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : Journey.layout m = .ok result)
    (out : Box) (hout : out ∈ result.scene.boxes) :
    result.scene.layoutDump.box? out.id = some out := by
  unfold LayoutDump.box?
  exact find_self_by_id (dump_ids_nodup hwf h) hout

private theorem box_role_group {b : ModelBox} (hr : b.role.id = "group") : b.role = .group := by
  cases hb : b.role <;> simp only [hb, BoxRole.id] at hr <;> simp_all

private theorem box_role_node {b : ModelBox} (hr : b.role = .node) : b.role.id = "node" := by
  simp [BoxRole.id, hr]

private theorem source_exclusive {out : Box} {src : ModelBox}
    (_hid : out.id = src.id) (hex : out.exclusive = src.exclusive) : out.exclusive = src.exclusive :=
  hex

private theorem parents_root (m : Model) (c : Constants) (g : Input)
    (hi : DecodeInv m c m.boxes g) {b : ModelBox} (hb : b ∈ m.boxes)
    (hk : shapeKind b = "section" ∨ shapeKind b = "title") : b.parent = "" := by
  rcases hk with hk | hk
  · exact hi.parentRoots b hb (Or.inr (by simp [isSecBox, hk]))
  · exact hi.parentRoots b hb (Or.inl (by simp [isTitleBox, hk]))

/-! ### Ancestor shapes -/

theorem ancestors_root {d : LayoutDump} {id : String} {b : Box}
    (hb : d.box? id = some b) (hp : b.parent = "") : d.ancestors id = [] := by
  exact ancestors_nil_parent d (by simp [hb, hp])

theorem ancestors_single {d : LayoutDump} {id parent : String} {b c : Box}
    (hb : d.box? id = some b) (hp : b.parent = parent) (hne : parent ≠ "")
    (hs : d.box? parent = some c) (hpc : c.parent = "") :
    d.ancestors id = [parent] := by
  unfold LayoutDump.ancestors
  cases n : d.boxes.length with
  | zero =>
    have hnone : d.box? id = none := by
      simp only [LayoutDump.box?]
      have hboxes : d.boxes = [] := by
        cases h : d.boxes with
        | nil => rfl
        | cons x xs => simp [h] at n
      rw [hboxes]
      simp
    rw [hnone] at hb; cases hb
  | succ fuel =>
    simp only [LayoutDump.ancestors.go.eq_2, hb]
    split
    · rename_i hcond
      rw [hp] at hcond
      exact absurd hcond (by simpa using hne)
    · rw [hp]
      cases fuel with
      | zero =>
        simp only [LayoutDump.ancestors.go.eq_1]
      | succ m =>
        simp only [LayoutDump.ancestors.go.eq_2, hs, hpc, ite_true]

private theorem one_box_false {d : LayoutDump} {id p1 p2 : String} {b c e : Box}
    (hb : d.box? id = some b) (hp : b.parent = p1) (_hne1 : p1 ≠ "")
    (hc : d.box? p1 = some c) (hpc : c.parent = p2) (hne2 : p2 ≠ "")
    (he : d.box? p2 = some e) (hpe : e.parent = "")
    (hlen : d.boxes.length = 1) : False := by
  obtain ⟨hid, hbmem⟩ := box?_some hb
  obtain ⟨hp1, hcmem⟩ := box?_some hc
  obtain ⟨hp2, hemem⟩ := box?_some he
  obtain ⟨x, hxy⟩ : ∃ x : Box, d.boxes = [x] := by
    cases h : d.boxes with
    | nil => rw [h] at hlen; simp at hlen
    | cons x t =>
      cases h2 : t with
      | nil => exact ⟨x, by simp⟩
      | cons y v => rw [h, h2] at hlen; simp [List.length_cons] at hlen
  rw [hxy] at hbmem hcmem hemem
  simp only [List.mem_cons, List.not_mem_nil] at hbmem hcmem hemem
  rcases hbmem with rfl | hbad <;> rcases hcmem with rfl | hbad2 <;>
    rcases hemem with rfl | hbad3 <;> simp_all

theorem ancestors_double {d : LayoutDump} {id p1 p2 : String} {b c e : Box}
    (hb : d.box? id = some b) (hp : b.parent = p1) (hne1 : p1 ≠ "")
    (hc : d.box? p1 = some c) (hpc : c.parent = p2) (hne2 : p2 ≠ "")
    (he : d.box? p2 = some e) (hpe : e.parent = "") :
    d.ancestors id = [p1, p2] := by
  unfold LayoutDump.ancestors
  cases n : d.boxes.length with
  | zero =>
    have hnone : d.box? id = none := by
      simp only [LayoutDump.box?]
      have hboxes : d.boxes = [] := by
        cases h : d.boxes with
        | nil => rfl
        | cons x xs => simp [h] at n
      rw [hboxes]
      simp
    rw [hnone] at hb; cases hb
  | succ fuel =>
    simp only [LayoutDump.ancestors.go.eq_2, hb]
    split
    · rename_i hcond
      rw [hp] at hcond
      exact absurd hcond (by simpa using hne1)
    · rw [hp]
      cases fuel with
      | zero =>
        exfalso
        have hl1 : d.boxes.length = 1 := by omega
        exact one_box_false hb hp hne1 hc hpc hne2 he hpe hl1
      | succ m =>
        simp only [LayoutDump.ancestors.go.eq_2, hc]
        split
        · rename_i hcond2
          rw [hpc] at hcond2
          exact absurd hcond2 (by simpa using hne2)
        · rw [hpc]
          cases m with
          | zero =>
            simp only [LayoutDump.ancestors.go.eq_1]
          | succ k =>
            simp only [LayoutDump.ancestors.go.eq_2, he, hpe, ite_true]

/-! ### Disjointness primitives -/

private theorem disjoint_of_y_le (a b : Rect) (h : a.y + a.h ≤ b.y) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior at *
  omega

theorem shift_disjoint_y {a b : Rect} (dx dy : Int) (h : a.y + a.h ≤ b.y) :
    Disjoint (shiftRect dx dy a) (shiftRect dx dy b) :=
  shift_disjoint dx dy (disjoint_of_y_le a b h)

theorem disjoint_symm {a b : Rect} (h : Disjoint a b) : Disjoint b a := by
  unfold Disjoint at *
  intro hm
  exact h (Rect.meetsInterior_comm b a |>.mp hm)

end Elegant.Kinds.JourneySceneFacts

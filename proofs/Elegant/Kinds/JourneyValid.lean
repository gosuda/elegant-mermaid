import Elegant.Kinds.Journey
import Elegant.Kinds.Timeline

set_option autoImplicit false

/-! Public validity of the `journey` adapter: `journey_valid` derives every hard-constraint
clause of `Validator` from the executed `layout`, the executed `scene` computation, and the
adapter correspondence. No admission premise beyond `WellFormed` and `WithinLimits`. -/

namespace Elegant.Kinds.JourneyValid

open Elegant Kinds Lanes
open Lanes.Journey
open Journey Common

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Constants read by the journey adapter stay in their working ranges. -/
theorem constants_pos (p : Profile) :
    0 < (constants p).taskWidth ∧ 0 < (constants p).taskHeight ∧
      0 < (constants p).bandHeight ∧ 0 < (constants p).columnGap ∧
      0 < (constants p).scoreStep ∧ 0 < (constants p).radius ∧
      0 ≤ (constants p).padX ∧ 0 ≤ (constants p).padY ∧
      0 ≤ (constants p).margin := by
  cases p <;>
    simp only [constants, LayoutConst.journey_task_width, LayoutConst.journey_task_height,
      LayoutConst.journey_band_height, LayoutConst.journey_column_gap,
      LayoutConst.journey_score_step, LayoutConst.journey_face_radius,
      LayoutConst.node_pad_x, LayoutConst.node_pad_y, LayoutConst.node_border,
      LayoutConst.canvas_margin, LayoutConst.Pair.get] <;> constructor <;> omega

/-- Every successful caption measurement has a positive height. -/
theorem caption_h_pos {profile : Profile} {role : TextRole} {target : Int} {text : String}
    {caption : Lanes.Caption} (h : Timeline.measureCaption profile role target text = .ok caption) :
    0 < caption.h := Timeline.measureCaption_height_positive h

theorem foldl_max_width_nonneg : ∀ (l : List Measure.Line) (z : Int),
    z ≤ l.foldl (fun w v => max w v.width) z := by
  intro l
  induction l with
  | nil => intro z; exact Int.le_refl z
  | cons a rest ih =>
    intro z
    have h1 : z ≤ max z a.width := by omega
    exact Int.le_trans h1 (ih (max z a.width))

/-- Every successful caption measurement has a non-negative width. -/
theorem caption_w_nonneg {profile : Profile} {role : TextRole} {target : Int} {text : String}
    {caption : Lanes.Caption} (h : Timeline.measureCaption profile role target text = .ok caption) :
    0 ≤ caption.w := by
  unfold Timeline.measureCaption at h
  dsimp only at h
  cases role <;> cases profile <;> dsimp only at h
  all_goals
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  case label.cell | title.cell | body.cell =>
    cases hw : StyledMeasure.wrap Measure.Metric.cell target text.toList with
    | error e =>
      simp only [hw, throw, throwThe, MonadExceptOf.throw] at h
      cases h
    | ok lines =>
      simp only [hw, Except.ok.injEq] at h
      subst caption
      exact foldl_max_width_nonneg _ 0
  case title.vector =>
    cases hm : Measure.Role.title.metric with
    | error e =>
      simp only [hm] at h
      cases h
    | ok metric =>
      simp only [hm] at h
      cases hw : StyledMeasure.wrap metric target text.toList with
      | error e =>
        simp only [hw, throw, throwThe, MonadExceptOf.throw] at h
        cases h
      | ok lines =>
        simp only [hw, Except.ok.injEq] at h
        subst caption
        exact foldl_max_width_nonneg _ 0
  case label.vector =>
    cases hm : Measure.Role.label.metric with
    | error e =>
      simp only [hm] at h
      cases h
    | ok metric =>
      simp only [hm] at h
      cases hw : StyledMeasure.wrap metric target text.toList with
      | error e =>
        simp only [hw, throw, throwThe, MonadExceptOf.throw] at h
        cases h
      | ok lines =>
        simp only [hw, Except.ok.injEq] at h
        subst caption
        exact foldl_max_width_nonneg _ 0
  case body.vector =>
    cases hm : Measure.Role.body.metric with
    | error e =>
      simp only [hm] at h
      cases h
    | ok metric =>
      simp only [hm] at h
      cases hw : StyledMeasure.wrap metric target text.toList with
      | error e =>
        simp only [hw, throw, throwThe, MonadExceptOf.throw] at h
        cases h
      | ok lines =>
        simp only [hw, Except.ok.injEq] at h
        subst caption
        exact foldl_max_width_nonneg _ 0

/-! ### Bridge from `for` loops to `List.foldlM` -/

private theorem forIn_yield_foldlM {α β : Type} (step : α → β → Except LayoutError β)
    (xs : List α) (init : β) :
    (ForIn.forIn (m := Except LayoutError) xs init
        (fun a s => (step a s).map ForInStep.yield)) =
      List.foldlM (fun acc a => step a acc) init xs := by
  induction xs generalizing init with
  | nil => rfl
  | cons a rest ih =>
    rw [List.forIn_cons, List.foldlM_cons]
    simp only [Bind.bind, Except.bind]
    cases hs : step a init with
    | error e => rfl
    | ok v => exact ih v

/-- A trailing `do let s ← forIn ...; pure s` block is the loop itself. -/
private theorem do_forIn_ok {α β ε : Type} (xs : List α) (init : β)
    (step : α → β → Except ε (ForInStep β)) (out : β)
    (h : (ForIn.forIn xs init step).bind pure = .ok out) :
    ForIn.forIn xs init step = .ok out := by
  cases hx : ForIn.forIn xs init step with
  | error e => rw [hx] at h; cases h
  | ok v =>
    rw [hx] at h
    simp only [Except.bind, pure, Except.pure, Except.ok.injEq] at h
    exact congrArg Except.ok h

/-- An invariant preserved by every successful `forIn` step holds after a successful loop. -/
private theorem forIn_except_inv {α β : Type} (xs : List α) (init out : β)
    (step : α → β → Except LayoutError (ForInStep β)) (P : β → Prop)
    (hinit : P init)
    (hstep : ∀ a state next, P state → step a state = .ok next → P next.value)
    (hrun : ForIn.forIn xs init step = .ok out) : P out := by
  induction xs generalizing init with
  | nil =>
    change Except.ok init = Except.ok out at hrun
    cases hrun
    exact hinit
  | cons a rest ih =>
    rw [List.forIn_cons] at hrun
    cases he : step a init with
    | error e => simp only [he, Bind.bind, Except.bind] at hrun; cases hrun
    | ok next =>
      have hp := hstep a init next hinit he
      cases next with
      | done state =>
        simp only [he, Bind.bind, Except.bind] at hrun
        cases hrun
        exact hp
      | yield state =>
        simp only [he, Bind.bind, Except.bind] at hrun
        exact ih state hp hrun

/-! ### Geometry helpers -/

theorem shift_disjoint {a b : Rect} (dx dy : Int) (h : Disjoint a b) :
    Disjoint (shiftRect dx dy a) (shiftRect dx dy b) := by
  unfold Disjoint Rect.meetsInterior shiftRect at *
  dsimp only at *
  omega

/-- The journey constants keep positive sizes and non-negative paddings. -/
def LoadPos (c : Constants) : Prop :=
  0 < c.taskWidth ∧ 0 < c.taskHeight ∧ 0 < c.bandHeight ∧ 0 < c.columnGap ∧
    0 < c.scoreStep ∧ 0 < c.radius ∧ 0 ≤ c.padX ∧ 0 ≤ c.padY ∧ 0 ≤ c.margin

theorem load_pos {m : Model} {c : Constants} (h : Journey.load m = .ok c) : LoadPos c := by
  unfold Journey.load at h
  dsimp only at h
  split at h
  · refine forIn_except_inv m.options.config (constants m.profile) c _ LoadPos
      (constants_pos m.profile) ?_ (do_forIn_ok _ _ _ _ h)
    intro kv state next hp hstep
    obtain ⟨key, value⟩ := kv
    dsimp only at hstep
    cases value with
    | integer n =>
      simp only [Bind.bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · cases hstep
      · split at hstep
        · rename_i hpos
          split at hstep
          · split at hstep
            · split at hstep
              · rename_i e1 e2 e3
                simp only [Except.ok.injEq] at hstep
                cases hstep
                simp only [LoadPos, ForInStep.value] at hp ⊢
                omega
              · rename_i e1 e2
                simp only [Except.ok.injEq] at hstep
                cases hstep
                simp only [LoadPos, ForInStep.value] at hp ⊢
                omega
            · rename_i e1
              split at hstep
              · rename_i e2
                simp only [Except.ok.injEq] at hstep
                cases hstep
                simp only [LoadPos, ForInStep.value] at hp ⊢
                omega
              · simp only [Except.ok.injEq] at hstep
                cases hstep
                simp only [LoadPos, ForInStep.value] at hp ⊢
                omega
          · split at hstep
            · split at hstep
              · rename_i e2 e3
                simp only [Except.ok.injEq] at hstep
                cases hstep
                simp only [LoadPos, ForInStep.value] at hp ⊢
                omega
              · rename_i e2
                simp only [Except.ok.injEq] at hstep
                cases hstep
                simp only [LoadPos, ForInStep.value] at hp ⊢
                omega
            · split at hstep
              · rename_i e3
                simp only [Except.ok.injEq] at hstep
                cases hstep
                simp only [LoadPos, ForInStep.value] at hp ⊢
                omega
              · simp only [Except.ok.injEq] at hstep
                cases hstep
                exact hp
        · rename_i hnonpos
          simp only [Except.ok.injEq] at hstep
          cases hstep
          exact hp
    | string s' =>
      simp only [Bind.bind, Except.bind, pure, Except.pure] at hstep
      cases hs2 : s'.toInt? with
      | some n =>
        simp only [hs2] at hstep
        split at hstep
        · cases hstep
        · split at hstep
          · rename_i hpos
            split at hstep
            · split at hstep
              · split at hstep
                · rename_i e1 e2 e3
                  simp only [Except.ok.injEq] at hstep
                  cases hstep
                  simp only [LoadPos, ForInStep.value] at hp ⊢
                  omega
                · rename_i e1 e2
                  simp only [Except.ok.injEq] at hstep
                  cases hstep
                  simp only [LoadPos, ForInStep.value] at hp ⊢
                  omega
              · rename_i e1
                split at hstep
                · rename_i e2
                  simp only [Except.ok.injEq] at hstep
                  cases hstep
                  simp only [LoadPos, ForInStep.value] at hp ⊢
                  omega
                · simp only [Except.ok.injEq] at hstep
                  cases hstep
                  simp only [LoadPos, ForInStep.value] at hp ⊢
                  omega
            · split at hstep
              · split at hstep
                · rename_i e2 e3
                  simp only [Except.ok.injEq] at hstep
                  cases hstep
                  simp only [LoadPos, ForInStep.value] at hp ⊢
                  omega
                · rename_i e2
                  simp only [Except.ok.injEq] at hstep
                  cases hstep
                  simp only [LoadPos, ForInStep.value] at hp ⊢
                  omega
              · split at hstep
                · rename_i e3
                  simp only [Except.ok.injEq] at hstep
                  cases hstep
                  simp only [LoadPos, ForInStep.value] at hp ⊢
                  omega
                · simp only [Except.ok.injEq] at hstep
                  cases hstep
                  exact hp
          · rename_i hnonpos
            simp only [Except.ok.injEq] at hstep
            cases hstep
            exact hp
      | none =>
        simp only [hs2] at hstep
        cases hstep
    | boolean _ =>
      simp only [Bind.bind, Except.bind, pure, Except.pure] at hstep
      cases hstep
  · have he : constants m.profile = c := Except.ok.inj h
    rw [← he]
    exact constants_pos m.profile

/-! ### The decode loop as a fold -/

private def decodeStep (m : Model) (c : Constants) : ModelBox → Input → Except LayoutError Input :=
  fun b g =>
    match shapeKind b with
    | "title" =>
      if b.parent != "" then throw .domain
      else do
        let caption ← Timeline.measureCaption m.profile .title I32_MAX (boxText m b)
        pure { title := some { id := b.id, caption }, sections := g.sections, tasks := g.tasks }
    | "section" =>
      if b.parent != "" then throw .domain
      else do
        let n := (m.boxes.filter fun t => shapeKind t == "task" && t.parent == b.id).length
        let caption ← Timeline.measureCaption m.profile .label (target c n) (boxText m b)
        pure { title := g.title, sections := g.sections ++ [{ id := b.id, caption }], tasks := g.tasks }
    | "task" =>
      (if b.shape == "" then pure 1 else
        match (b.shape.splitOn ":").tail.head? >>= String.toInt? with
        | some n => pure n
        | none => throw .domain : Except LayoutError Int).bind fun score => do
        if score < 1 || score > 5 then throw .domain
        (if b.parent == "" then pure (-1) else
          match g.sections.findIdx? (·.id == b.parent) with
          | some i => pure (i : Int)
          | none => throw .domain : Except LayoutError Int).bind fun band => do
          let caption ← Timeline.measureCaption m.profile .label (target c 1) (boxText m b)
          pure { title := g.title, sections := g.sections, tasks := g.tasks ++ [{ id := b.id, caption, band, score }] }
    | "people" =>
      match g.tasks.getLast? with
      | none => throw .domain
      | some t =>
        if t.id != b.parent then throw .domain
        else do
          let cap ← Timeline.measureCaption m.profile .body (target c 1) (boxText m b)
          pure { title := g.title, sections := g.sections, tasks := g.tasks.set (g.tasks.length - 1) { t with people := some cap } }
    | _ => throw .domain

theorem decode_eq_foldl (m : Model) (c : Constants) :
    Journey.decode m c =
      List.foldlM (fun (acc : Input) (b : ModelBox) => decodeStep m c b acc) {} m.boxes := by
  rw [← forIn_yield_foldlM]
  unfold Journey.decode
  simp only [bind_pure]
  congr 1
  funext b g
  change _ = ForInStep.yield <$> decodeStep m c b g
  unfold decodeStep
  split <;> simp_all [Functor.map, Except.map, Bind.bind, Except.bind,
    pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  all_goals repeat (first | rfl | split)
  all_goals cases hl : g.tasks.getLast? <;> grind

/-! ### The decode invariant -/

def isSecBox (b : ModelBox) : Bool := shapeKind b == "section"
def isTaskBox (b : ModelBox) : Bool := shapeKind b == "task"
def isTitleBox (b : ModelBox) : Bool := shapeKind b == "title"
def isPeopleBox (b : ModelBox) : Bool := shapeKind b == "people"

/-- The band a journey task lands in: `-1` for unparented tasks, else the section index. -/
def bandVal (secs : List Card) (p : String) : Int :=
  if p == "" then (-1 : Int) else
    ((secs.findIdx? (·.id == p)).map fun j => (j : Int)).getD (-1)

/-- The state `g` produced by successfully decoding the prefix `pre` of `m.boxes`. -/
structure DecodeInv (m : Model) (c : Constants) (pre : List ModelBox) (g : Input) : Prop where
  secIds : g.sections.map (·.id) = (pre.filter isSecBox).map (·.id)
  taskIds : g.tasks.map (·.id) = (pre.filter isTaskBox).map (·.id)
  titleId : g.title.map (·.id) = ((pre.filter isTitleBox).map (·.id)).getLast?
  secCapPos : ∀ cap ∈ g.sections.map (·.caption), 0 < cap.h ∧ 0 ≤ cap.w
  taskCapPos : ∀ cap ∈ g.tasks.map (·.caption), 0 < cap.h ∧ 0 ≤ cap.w
  peopleCapPos : ∀ t ∈ g.tasks, ∀ cap ∈ t.people.toList, 0 < cap.h ∧ 0 ≤ cap.w
  titleCapPos : ∀ cap ∈ g.title.toList.map (·.caption), 0 < cap.h ∧ 0 ≤ cap.w
  taskBand : ∀ (i : Nat) (_hlt : i < g.tasks.length)
      (_hlen : i < (pre.filter isTaskBox).length),
    g.tasks[i].band = bandVal g.sections ((pre.filter isTaskBox)[i].parent)
  taskScore : ∀ (i : Nat) (_hlt : i < g.tasks.length)
      (_hlen : i < (pre.filter isTaskBox).length),
    1 ≤ g.tasks[i].score ∧ g.tasks[i].score ≤ 5
  taskPeople : ∀ (i : Nat) (_hlt : i < g.tasks.length),
    g.tasks[i].people.isSome ↔ (∃ b ∈ pre, isPeopleBox b ∧ b.parent == g.tasks[i].id)
  peopleParents : ∀ b ∈ pre, isPeopleBox b →
    ∃ j, ∃ _ : j < g.tasks.length, g.tasks[j].id == b.parent
  parentRoots : ∀ b ∈ pre, (isTitleBox b ∨ isSecBox b) → b.parent = ""
  taskParentOK : ∀ (i : Nat) (_hlt : i < g.tasks.length)
      (_hlen : i < (pre.filter isTaskBox).length),
    (pre.filter isTaskBox)[i].parent = "" ∨
      (pre.filter isTaskBox)[i].parent ∈ g.sections.map (·.id)
  taskIdsNodup : (g.tasks.map (·.id)).Nodup
  secIdsNodup : (g.sections.map (·.id)).Nodup

/-! ### List helpers -/

private theorem length_eq_of_map_eq {α β γ : Type} {f : α → γ} {g : β → γ}
    {l : List α} {l' : List β}
    (h : l.map f = l'.map g) : l.length = l'.length := by
  have h2 := congrArg List.length h
  rwa [List.length_map, List.length_map] at h2

private theorem bandVal_append (secs extra : List Card) (parent : String)
    (hp : parent = "" ∨ parent ∈ secs.map (·.id)) :
    bandVal (secs ++ extra) parent = bandVal secs parent := by
  rcases hp with rfl | hp
  · simp [bandVal]
  · unfold bandVal
    by_cases he : parent = ""
    · simp [he]
    · simp only [beq_iff_eq, he, ite_false]
      obtain ⟨card, hmem, hid⟩ := List.mem_map.mp hp
      cases hf : secs.findIdx? (·.id == parent) with
      | none =>
        have ha := List.findIdx?_eq_none_iff.mp hf card hmem
        have hb : (card.id == parent) = true := by simp [hid]
        rw [hb] at ha
        cases ha
      | some i => simp [List.findIdx?_append, hf]

private theorem filter_append_singleton {α : Type} (p : α → Bool) (l : List α) (a : α) :
    (l ++ [a]).filter p = l.filter p ++ (if p a then [a] else []) := by
  rw [List.filter_append]
  cases hp : p a <;> simp [hp]

private theorem getLast?_append_singleton {α : Type} (l : List α) (a : α) :
    (l ++ [a]).getLast? = some a := by
  rw [List.getLast?_append]
  simp

private theorem getElem_append_left {α : Type} {l₁ l₂ : List α} {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂)[i]'(by simp only [List.length_append]; omega) = l₁[i] :=
  List.getElem_append_left h

private theorem getElem_append_right {α : Type} {l₁ l₂ : List α} {i : Nat}
    (h1 : l₁.length ≤ i) (h2 : i < l₁.length + l₂.length) :
    (l₁ ++ l₂)[i]'(by simpa only [List.length_append] using h2) =
      l₂[i - l₁.length]'(by omega) :=
  List.getElem_append_right h1

private theorem getElem_set_of_ne {α : Type} {l : List α} {i j : Nat} {a : α} (hne : i ≠ j)
    (hi : i < l.length) :
    (l.set j a)[i]'(by simpa only [List.length_set] using hi) = l[i] :=
  List.getElem_set_ne hne.symm _

private theorem getElem_set_self {α : Type} (l : List α) (j : Nat) (a : α)
    (hj : j < l.length) :
    (l.set j a)[j]'(by simpa only [List.length_set] using hj) = a :=
  List.getElem_set_self _

private theorem map_set_of_head_eq {α β : Type} (f : α → β) : ∀ (l : List α) (j : Nat) (a : α),
    (hj : j < l.length) → f a = f (l[j]'hj) → (l.set j a).map f = l.map f := by
  intro l
  induction l with
  | nil => intro j a hj _; cases hj
  | cons x rest ih =>
    intro j a hj ha
    cases j with
    | zero =>
      simp only [List.set_cons_zero, List.map_cons]
      exact congrArg (· :: rest.map f) ha
    | succ j' =>
      simp only [List.set_cons_succ, List.map_cons]
      exact congrArg (f x :: ·) (ih j' a (by simpa using hj) ha)

private theorem getElem_ne_of_nodup {α : Type} [DecidableEq α] : ∀ (l : List α), l.Nodup →
    ∀ i j (hi : i < l.length) (hj : j < l.length), i ≠ j → l[i] ≠ l[j] := by
  intro l hn i j hi hj hne he
  exact hne (hn.eq_of_getElem_eq hi hj he)

private theorem nodup_of_map_id_nodup {boxes : List ModelBox}
    (h : (boxes.map (·.id)).Nodup) : boxes.Nodup := by
  induction boxes with
  | nil => exact List.nodup_nil
  | cons box rest ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun hm => h.1 (List.mem_map_of_mem hm), ih h.2⟩

private theorem mem_id_unique {boxes : List ModelBox} (h : (boxes.map (·.id)).Nodup)
    {x y : ModelBox} (hx : x ∈ boxes) (hy : y ∈ boxes) (hid : x.id = y.id) : x = y := by
  induction boxes with
  | nil => cases hx
  | cons a rest ih =>
    have hn := List.nodup_cons.mp h
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · have hy_mem : y.id ∈ rest.map (·.id) := List.mem_map_of_mem hy'
        rw [← hid] at hy_mem
        exact absurd hy_mem hn.1
    · rcases List.mem_cons.mp hy with rfl | hy'
      · have hx_mem : x.id ∈ rest.map (·.id) := List.mem_map_of_mem hx'
        rw [hid] at hx_mem
        exact absurd hx_mem hn.1
      · exact ih hn.2 hx' hy'

private theorem getLast?_eq_some_get {α : Type} {l : List α} {a : α} (h : l.getLast? = some a) :
    l[l.length - 1]'(by
      cases l with
      | nil => cases h
      | cons x xs => simp) = a := by
  have hh := List.getLast?_eq_getElem? (l := l)
  rw [h] at hh
  exact (List.getElem?_eq_some_iff.mp hh.symm).choose_spec

private theorem bandVal_of_step {secs : List Card} {p : String} {band : Int}
    (h : (if p == "" then (pure (-1 : Int) : Except LayoutError Int) else
          match secs.findIdx? (·.id == p) with
          | some i => pure (i : Int)
          | none => throw LayoutError.domain) = .ok band) :
    band = bandVal secs p := by
  unfold bandVal
  by_cases hp : (p == "") = true
  · simpa [hp, pure, Except.pure] using h.symm
  · simp [hp] at h ⊢
    cases hf : secs.findIdx? (·.id == p) with
    | none => simp [hf] at h
    | some j => simpa [hf, pure, Except.pure] using h.symm

/-! ### The decode invariant is preserved by every successful step -/

private theorem decode_inv_nil (m : Model) (c : Constants) : DecodeInv m c [] ({} : Input) := by
  constructor <;> simp

private theorem bool_eq_false_of_not {p : Bool} (h : ¬(p = true)) : p = false := by
  cases p with
  | false => rfl
  | true => exact absurd rfl h

private theorem bool_eq_false_of_eq {p : Bool} (h : (p = true) = false) : p = false := by
  cases p <;> simp_all

private theorem decodeStep_compose (m : Model) (c : Constants) (hwf : WellFormed m)
    {mid s : Input} {pre : List ModelBox} (b : ModelBox)
    (hpre : DecodeInv m c pre mid) (hb : b ∈ m.boxes) (hbpre : b ∉ pre)
    (hprefix : ∀ x ∈ pre, x ∈ m.boxes)
    (h : decodeStep m c b mid = .ok s) : DecodeInv m c (pre ++ [b]) s := by
  obtain ⟨hsecIds, htaskIds, htitleId, hsecCap, htaskCap, hpeopleCap, htitleCap,
    hband, hscore, hpeople, hparents, hroots, hparentOK, htaskNodup, hsecNodup⟩ := hpre
  unfold decodeStep at h
  split at h
  · -- title
    rename_i hk
    have hbSec : (isSecBox b) = false := by simp [isSecBox, hk]
    have hbTask : (isTaskBox b) = false := by simp [isTaskBox, hk]
    have hbTitle : (isTitleBox b) = true := by simp [isTitleBox, hk]
    have hbPeople : (isPeopleBox b) = false := by simp [isPeopleBox, hk]
    split at h
    · cases h
    · rename_i hcond
      have hb2 : (b.parent != "") = false := by
        first
          | exact bool_eq_false_of_not hcond
          | exact bool_eq_false_of_eq hcond
      have hpar : b.parent = "" := by simpa using hb2
      obtain ⟨caption, hcap, h⟩ := bind_ok h
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
      cases h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only
        rw [filter_append_singleton]
        simp [hbSec]
        rw [hsecIds]
      · dsimp only
        rw [filter_append_singleton]
        simp [hbTask]
        rw [htaskIds]
      · dsimp only
        rw [filter_append_singleton]
        simp [hbTitle, List.map_append]
      · exact hsecCap
      · exact htaskCap
      · exact hpeopleCap
      · intro cap2 hc2
        simp only [Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at hc2
        subst cap2
        exact ⟨caption_h_pos hcap, caption_w_nonneg hcap⟩
      · intro i hlt hlen
        dsimp only at hlen ⊢
        simp only [filter_append_singleton, hbTask, Bool.false_eq_true,
          ↓reduceIte, List.append_nil] at hlen ⊢
        exact hband i hlt hlen
      · intro i hlt hlen
        simp only [filter_append_singleton, hbTask, Bool.false_eq_true,
          ↓reduceIte, List.append_nil] at hlen
        exact hscore i hlt hlen
      · intro i hlt
        dsimp only
        rw [hpeople i hlt]
        constructor
        · intro hmem
          obtain ⟨x, hx, hpx, hpar2⟩ := hmem
          exact ⟨x, List.mem_append.mpr (Or.inl hx), hpx, hpar2⟩
        · intro hex
          obtain ⟨x, hx, hpx, hpar2⟩ := hex
          rcases List.mem_append.mp hx with hx' | hx'
          · exact ⟨x, hx', hpx, hpar2⟩
          · have hxb : x = b := by simpa only [List.mem_singleton] using hx'
            subst x
            simp only [hbPeople, Bool.false_eq_true] at hpx
      · intro x hx hpx
        dsimp only
        rcases List.mem_append.mp hx with hx' | hx'
        · obtain ⟨j, hj, hjid⟩ := hparents x hx' hpx
          exact ⟨j, hj, hjid⟩
        · have hxb : x = b := by simpa only [List.mem_singleton] using hx'
          subst x
          simp only [hbPeople, Bool.false_eq_true] at hpx
      · intro x hx hr
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hroots x hx' hr
        · have hxb : x = b := by simpa only [List.mem_singleton] using hx'
          subst x
          exact hpar
      · intro i hlt hlen
        dsimp only at hlen ⊢
        simp only [filter_append_singleton, hbTask, Bool.false_eq_true,
          ↓reduceIte, List.append_nil] at hlen ⊢
        exact hparentOK i hlt hlen
      · dsimp only
        exact htaskNodup
      · dsimp only
        exact hsecNodup
  · -- section
    rename_i hk
    have hbSec : (isSecBox b) = true := by simp [isSecBox, hk]
    have hbTask : (isTaskBox b) = false := by simp [isTaskBox, hk]
    have hbTitle : (isTitleBox b) = false := by simp [isTitleBox, hk]
    have hbPeople : (isPeopleBox b) = false := by simp [isPeopleBox, hk]
    split at h
    · cases h
    · rename_i hcond
      have hb2 : (b.parent != "") = false := by
        first
          | exact bool_eq_false_of_not hcond
          | exact bool_eq_false_of_eq hcond
      have hpar : b.parent = "" := by simpa using hb2
      obtain ⟨caption, hcap, h⟩ := bind_ok h
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
      cases h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only
        rw [filter_append_singleton]
        simp [hbSec, List.map_append, List.map_cons]
        rw [hsecIds]
      · dsimp only
        rw [filter_append_singleton]
        simp [hbTask]
        rw [htaskIds]
      · dsimp only
        rw [filter_append_singleton]
        simp [hbTitle]
        simpa using htitleId
      · intro cap2 hc2
        dsimp only at hc2
        simp only [List.map_append, List.mem_append] at hc2
        rcases hc2 with hc2 | hc2
        · exact hsecCap cap2 hc2
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc2
          subst cap2
          exact ⟨caption_h_pos hcap, caption_w_nonneg hcap⟩
      · exact htaskCap
      · exact hpeopleCap
      · exact htitleCap
      · intro i hlt hlen
        dsimp only at hlen ⊢
        simp only [filter_append_singleton, hbTask, Bool.false_eq_true,
          ↓reduceIte, List.append_nil] at hlen ⊢
        rw [bandVal_append _ _ _ (hparentOK i hlt hlen)]
        exact hband i hlt hlen
      · intro i hlt hlen
        simp only [filter_append_singleton, hbTask, Bool.false_eq_true,
          ↓reduceIte, List.append_nil] at hlen
        exact hscore i hlt hlen
      · intro i hlt
        dsimp only
        rw [hpeople i hlt]
        constructor
        · intro hmem
          obtain ⟨x, hx, hpx, hpar2⟩ := hmem
          exact ⟨x, List.mem_append.mpr (Or.inl hx), hpx, hpar2⟩
        · intro hex
          obtain ⟨x, hx, hpx, hpar2⟩ := hex
          rcases List.mem_append.mp hx with hx' | hx'
          · exact ⟨x, hx', hpx, hpar2⟩
          · have hxb : x = b := by simpa only [List.mem_singleton] using hx'
            subst x
            simp only [hbPeople, Bool.false_eq_true] at hpx
      · intro x hx hpx
        dsimp only
        rcases List.mem_append.mp hx with hx' | hx'
        · obtain ⟨j, hj, hjid⟩ := hparents x hx' hpx
          exact ⟨j, hj, hjid⟩
        · have hxb : x = b := by simpa only [List.mem_singleton] using hx'
          subst x
          simp only [hbPeople, Bool.false_eq_true] at hpx
      · intro x hx hr
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hroots x hx' hr
        · have hxb : x = b := by simpa only [List.mem_singleton] using hx'
          subst x
          exact hpar
      · intro i hlt hlen
        dsimp only at hlen ⊢
        simp only [filter_append_singleton, hbTask, Bool.false_eq_true,
          ↓reduceIte, List.append_nil] at hlen ⊢
        rcases hparentOK i hlt hlen with hp | hp
        · exact Or.inl hp
        · exact Or.inr (by
            simp only [List.map_append, List.mem_append]
            exact Or.inl hp)
      · exact htaskNodup
      · dsimp only
        rw [List.map_append]
        apply List.nodup_append.mpr
        refine ⟨hsecNodup, by simp, ?_⟩
        intro id hid other hother heq
        have hother' : other = b.id := by
          simpa only [List.map_cons, List.map_nil, List.mem_singleton] using hother
        have hmem : b.id ∈ mid.sections.map (·.id) := by
          simpa only [heq, hother'] using hid
        rw [hsecIds] at hmem
        obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hmem
        have hxb : x = b := mem_id_unique (Model.boxIds_nodup hwf)
          (hprefix x (List.mem_filter.mp hx).1) hb hxid
        exact hbpre (hxb ▸ (List.mem_filter.mp hx).1)
  · -- task
    rename_i hk
    have hbSec : (isSecBox b) = false := by simp [isSecBox, hk]
    have hbTask : (isTaskBox b) = true := by simp [isTaskBox, hk]
    have hbTitle : (isTitleBox b) = false := by simp [isTitleBox, hk]
    have hbPeople : (isPeopleBox b) = false := by simp [isPeopleBox, hk]
    obtain ⟨score, -, h⟩ := bind_ok h
    dsimp only at h
    split at h
    · cases h
    · rename_i hguard
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hguard
      obtain ⟨band, hbandOk, h⟩ := bind_ok h
      have hbandEq : band = bandVal mid.sections b.parent := bandVal_of_step hbandOk
      obtain ⟨caption, hcap, h⟩ := bind_ok h
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
      cases h
      have hPlen : mid.tasks.length = (pre.filter isTaskBox).length :=
        length_eq_of_map_eq htaskIds
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only
        rw [filter_append_singleton]
        simp [hbSec]
        exact hsecIds
      · dsimp only
        rw [filter_append_singleton]
        simp [hbTask, List.map_append, List.map_cons]
        rw [htaskIds]
      · dsimp only
        rw [filter_append_singleton]
        simp [hbTitle]
        simpa using htitleId
      · exact hsecCap
      · intro cap2 hc2
        dsimp only at hc2
        simp only [List.map_append, List.mem_append] at hc2
        rcases hc2 with hc2 | hc2
        · exact htaskCap cap2 hc2
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc2
          subst cap2
          exact ⟨caption_h_pos hcap, caption_w_nonneg hcap⟩
      · intro task hmem cap hc
        dsimp only at hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact hpeopleCap task hmem cap hc
        · have ht := List.mem_singleton.mp hmem
          subst task
          simp at hc
      · exact htitleCap
      · intro i hlt hlen
        dsimp only at hlt hlen ⊢
        simp only [filter_append_singleton, hbTask, ite_true] at hlen ⊢
        by_cases hi : i < mid.tasks.length
        · have hi' : i < (pre.filter isTaskBox).length := by omega
          simpa only [List.getElem_append_left hi, List.getElem_append_left hi']
            using hband i hi hi'
        · have he : i = mid.tasks.length := by simp only [List.length_append] at hlt; simp at hlt; omega
          subst i
          simpa [List.getElem_append, hPlen] using hbandEq
      · intro i hlt hlen
        dsimp only at hlt hlen ⊢
        by_cases hi : i < mid.tasks.length
        · have hi' : i < (pre.filter isTaskBox).length := by omega
          simpa only [List.getElem_append_left hi] using hscore i hi hi'
        · have he : i = mid.tasks.length := by simp only [List.length_append] at hlt; simp at hlt; omega
          subst i
          simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem_cons_zero]
          exact ⟨by omega, by omega⟩
      · intro i hlt
        dsimp only at hlt ⊢
        by_cases hi : i < mid.tasks.length
        · simp only [List.getElem_append_left hi]
          rw [hpeople i hi]
          constructor
          · rintro ⟨x, hx, hpx, hpar2⟩
            exact ⟨x, List.mem_append_left _ hx, hpx, hpar2⟩
          · rintro ⟨x, hx, hpx, hpar2⟩
            rcases List.mem_append.mp hx with hx | hx
            · exact ⟨x, hx, hpx, hpar2⟩
            · have hxb := List.mem_singleton.mp hx
              subst x
              simp [hbPeople] at hpx
        · have he : i = mid.tasks.length := by simp only [List.length_append] at hlt; simp at hlt; omega
          subst i
          simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem_cons_zero, Option.isSome_none, Bool.false_eq_true, false_iff]
          rintro ⟨x, hx, hpx, hpar2⟩
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨j, hj, hjid⟩ := hparents x hx hpx
            have hid : mid.tasks[j].id = b.id :=
              (beq_iff_eq.mp hjid).trans (beq_iff_eq.mp hpar2)
            have hmem : b.id ∈ mid.tasks.map (·.id) := by
              rw [← hid]
              exact List.mem_map_of_mem (List.getElem_mem hj)
            rw [htaskIds] at hmem
            obtain ⟨y, hy, hyid⟩ := List.mem_map.mp hmem
            have hyb : y = b := mem_id_unique (Model.boxIds_nodup hwf)
              (hprefix y (List.mem_filter.mp hy).1) hb hyid
            exact hbpre (hyb ▸ (List.mem_filter.mp hy).1)
          · have hxb := List.mem_singleton.mp hx
            subst x
            simp [hbPeople] at hpx
      · intro x hx hpx
        dsimp only
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨j, hj, hjid⟩ := hparents x hx hpx
          refine ⟨j, by simp only [List.length_append]; omega, ?_⟩
          simpa only [List.getElem_append_left hj] using hjid
        · have hxb := List.mem_singleton.mp hx
          subst x
          simp [hbPeople] at hpx
      · intro x hx hr
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hroots x hx' hr
        · have hxb := List.mem_singleton.mp hx'
          subst x
          simp [hbTitle, hbSec] at hr
      · intro i hlt hlen
        dsimp only at hlt hlen ⊢
        simp only [filter_append_singleton, hbTask, ite_true] at hlen ⊢
        by_cases hi : i < mid.tasks.length
        · have hi' : i < (pre.filter isTaskBox).length := by omega
          simpa only [List.getElem_append_left hi'] using hparentOK i hi hi'
        · have he : i = mid.tasks.length := by simp only [List.length_append] at hlt; simp at hlt; omega
          subst i
          simp only [List.getElem_append, ← hPlen, Nat.lt_irrefl, dite_false,
            Nat.sub_self, List.getElem_cons_zero]
          by_cases hp : b.parent = ""
          · exact Or.inl hp
          · right
            have hp' : (b.parent == "") = false := by simp [hp]
            rw [hp'] at hbandOk
            cases hf : mid.sections.findIdx? (·.id == b.parent) with
            | none => simp [hf, throw, throwThe, MonadExceptOf.throw] at hbandOk
            | some j =>
              obtain ⟨hj, hjeq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
              have hid : mid.sections[j].id = b.parent := beq_iff_eq.mp hjeq
              rw [← hid]
              exact List.mem_map_of_mem (List.getElem_mem hj)
      · dsimp only
        rw [List.map_append]
        apply List.nodup_append.mpr
        refine ⟨htaskNodup, by simp, ?_⟩
        intro id hid other hother heq
        have hother' : other = b.id := by
          simpa only [List.map_cons, List.map_nil, List.mem_singleton] using hother
        have hmem : b.id ∈ mid.tasks.map (·.id) := by
          simpa only [heq, hother'] using hid
        rw [htaskIds] at hmem
        obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hmem
        have hxb : x = b := mem_id_unique (Model.boxIds_nodup hwf)
          (hprefix x (List.mem_filter.mp hx).1) hb hxid
        exact hbpre (hxb ▸ (List.mem_filter.mp hx).1)
      · exact hsecNodup
  · -- people
    rename_i hk
    have hbSec : (isSecBox b) = false := by simp [isSecBox, hk]
    have hbTask : (isTaskBox b) = false := by simp [isTaskBox, hk]
    have hbTitle : (isTitleBox b) = false := by simp [isTitleBox, hk]
    have hbPeople : (isPeopleBox b) = true := by simp [isPeopleBox, hk]
    cases hlast0 : mid.tasks.getLast? with
    | none =>
      rw [hlast0] at h
      dsimp only at h
      cases h
    | some t =>
      rw [hlast0] at h
      dsimp only at h
      have hne : mid.tasks ≠ [] := by
        intro hnil
        rw [hnil] at hlast0
        simp at hlast0
      have hlen_pos : 0 < mid.tasks.length := List.length_pos_iff.mpr hne
      have htget : mid.tasks[mid.tasks.length - 1] = t := getLast?_eq_some_get hlast0
      have hPlen : mid.tasks.length = (pre.filter isTaskBox).length :=
        length_eq_of_map_eq htaskIds
      split at h
      · cases h
      · rename_i hcond
        have hb2 : (t.id != b.parent) = false := by
          first
            | exact bool_eq_false_of_not hcond
            | exact bool_eq_false_of_eq hcond
        have hpar : t.id = b.parent := by simpa using hb2
        obtain ⟨cap, hcap, h⟩ := bind_ok h
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
        cases h
        have hlast : mid.tasks.length - 1 < mid.tasks.length := by omega
        have hfields (i : Nat) (hi : i < mid.tasks.length) :
            let now := (mid.tasks.set (mid.tasks.length - 1)
              { t with people := some cap })[i]'(by simpa only [List.length_set] using hi)
            now.id = mid.tasks[i].id ∧ now.caption = mid.tasks[i].caption ∧
              now.band = mid.tasks[i].band ∧ now.score = mid.tasks[i].score := by
          dsimp only
          by_cases hik : i = mid.tasks.length - 1
          · subst i
            rw [getElem_set_self _ _ _ hlast, htget]
            exact ⟨rfl, rfl, rfl, rfl⟩
          · rw [getElem_set_of_ne hik hi]
            exact ⟨rfl, rfl, rfl, rfl⟩
        have hmapid : (mid.tasks.set (mid.tasks.length - 1)
            { t with people := some cap }).map (·.id) = mid.tasks.map (·.id) :=
          map_set_of_head_eq (·.id) mid.tasks (mid.tasks.length - 1)
            { t with people := some cap } hlast (by rw [htget])
        have hmapcap : (mid.tasks.set (mid.tasks.length - 1)
            { t with people := some cap }).map (·.caption) = mid.tasks.map (·.caption) :=
          map_set_of_head_eq (·.caption) mid.tasks (mid.tasks.length - 1)
            { t with people := some cap } hlast (by rw [htget])
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · dsimp only
          simp only [filter_append_singleton, hbSec, Bool.false_eq_true,
            ↓reduceIte, List.append_nil]
          exact hsecIds
        · dsimp only
          simp only [filter_append_singleton, hbTask, Bool.false_eq_true,
            ↓reduceIte, List.append_nil, hmapid]
          exact htaskIds
        · dsimp only
          simp only [filter_append_singleton, hbTitle, Bool.false_eq_true,
            ↓reduceIte, List.append_nil]
          exact htitleId
        · exact hsecCap
        · intro caption hc
          dsimp only at hc
          rw [hmapcap] at hc
          exact htaskCap caption hc
        · intro task hmem caption hc
          dsimp only at hmem
          obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
          subst task
          have hi' : i < mid.tasks.length := by simpa only [List.length_set] using hi
          by_cases hik : i = mid.tasks.length - 1
          · subst i
            simp only [getElem_set_self _ _ _ hlast, Option.toList_some,
              List.mem_singleton] at hc
            subst caption
            exact ⟨caption_h_pos hcap, caption_w_nonneg hcap⟩
          · simp only [getElem_set_of_ne hik hi'] at hc
            exact hpeopleCap _ (List.getElem_mem hi') caption hc
        · exact htitleCap
        · intro i hlt hlen
          dsimp only at hlt hlen ⊢
          have hi : i < mid.tasks.length := by simpa only [List.length_set] using hlt
          simp only [filter_append_singleton, hbTask, Bool.false_eq_true,
            ↓reduceIte, List.append_nil] at hlen ⊢
          rw [(hfields i hi).2.2.1]
          exact hband i hi hlen
        · intro i hlt hlen
          dsimp only at hlt hlen ⊢
          have hi : i < mid.tasks.length := by simpa only [List.length_set] using hlt
          simp only [filter_append_singleton, hbTask, Bool.false_eq_true,
            ↓reduceIte, List.append_nil] at hlen
          rw [(hfields i hi).2.2.2]
          exact hscore i hi hlen
        · intro i hlt
          dsimp only at hlt ⊢
          have hi : i < mid.tasks.length := by simpa only [List.length_set] using hlt
          by_cases hik : i = mid.tasks.length - 1
          · subst i
            simp only [getElem_set_self _ _ _ hlast]
            constructor
            · intro _
              refine ⟨b, List.mem_append_right _ (by simp), hbPeople, ?_⟩
              simpa only [beq_iff_eq] using hpar.symm
            · intro _
              rfl
          · simp only [getElem_set_of_ne hik hi]
            rw [hpeople i hi]
            constructor
            · rintro ⟨x, hx, hpx, hpar2⟩
              exact ⟨x, List.mem_append_left _ hx, hpx, hpar2⟩
            · rintro ⟨x, hx, hpx, hpar2⟩
              rcases List.mem_append.mp hx with hx | hx
              · exact ⟨x, hx, hpx, hpar2⟩
              · have hxb := List.mem_singleton.mp hx
                subst x
                have hneq := getElem_ne_of_nodup (mid.tasks.map (·.id)) htaskNodup
                  i (mid.tasks.length - 1) (by simpa only [List.length_map] using hi)
                  (by simpa only [List.length_map] using hlast) hik
                apply False.elim
                apply hneq
                simpa only [List.getElem_map, htget] using
                  ((beq_iff_eq.mp hpar2).symm.trans hpar.symm)
        · intro x hx hpx
          dsimp only
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨j, hj, hjid⟩ := hparents x hx hpx
            refine ⟨j, by simpa only [List.length_set] using hj, ?_⟩
            rw [(hfields j hj).1]
            exact hjid
          · have hxb := List.mem_singleton.mp hx
            subst x
            refine ⟨mid.tasks.length - 1, by simpa only [List.length_set] using hlast, ?_⟩
            simp only [getElem_set_self _ _ _ hlast, beq_iff_eq]
            exact hpar
        · intro x hx hr
          rcases List.mem_append.mp hx with hx | hx
          · exact hroots x hx hr
          · have hxb := List.mem_singleton.mp hx
            subst x
            simp [hbTitle, hbSec] at hr
        · intro i hlt hlen
          dsimp only at hlt hlen ⊢
          have hi : i < mid.tasks.length := by simpa only [List.length_set] using hlt
          simp only [filter_append_singleton, hbTask, Bool.false_eq_true,
            ↓reduceIte, List.append_nil] at hlen ⊢
          exact hparentOK i hi hlen
        · dsimp only
          rw [hmapid]
          exact htaskNodup
        · exact hsecNodup
  · cases h

private theorem decode_fold_more (m : Model) (c : Constants) (hwf : WellFormed m)
    (pre : List ModelBox) (mid : Input) (hpre : DecodeInv m c pre mid)
    (hprefix : ∀ x ∈ pre, x ∈ m.boxes) :
    ∀ (tl : List ModelBox) (g : Input),
      (∀ x ∈ tl, x ∈ m.boxes) → (∀ x ∈ tl, x ∉ pre) → tl.Nodup →
        List.foldlM (fun (acc : Input) (b : ModelBox) => decodeStep m c b acc) mid tl = .ok g →
        DecodeInv m c (pre ++ tl) g := by
  intro tl
  induction tl generalizing pre mid with
  | nil =>
    intro g _ _ _ h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst g
    rw [List.append_nil]
    exact hpre
  | cons b tl' ih =>
    intro g hboxes hdisj hnodup h
    rw [List.foldlM_cons] at h
    obtain ⟨s, hstep, h⟩ := bind_ok h
    have hstep' : decodeStep m c b mid = .ok s := hstep
    have hinv := decodeStep_compose m c hwf b hpre (hboxes b (List.mem_cons_self ..))
      (hdisj b (List.mem_cons_self ..)) hprefix hstep'
    have hnn := List.nodup_cons.mp hnodup
    have hinv' := ih (pre ++ [b]) s hinv (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact hprefix x hx
        · have hxb : x = b := List.mem_singleton.mp hx
          subst x
          exact hboxes b (List.mem_cons_self ..))
      g (fun x hx => hboxes x (List.mem_cons_of_mem _ hx))
      (fun x hx => by
        have hx_tl := hdisj x (List.mem_cons_of_mem _ hx)
        have hnb : x ≠ b := fun heq => hnn.1 (heq ▸ hx)
        intro hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · exact hx_tl h1
        · exact hnb (List.mem_singleton.mp h2))
      hnn.2 h
    simpa only [List.append_assoc, List.singleton_append] using hinv'

theorem decode_ok (m : Model) (c : Constants) (hwf : WellFormed m) {g : Input}
    (h : Journey.decode m c = .ok g) : DecodeInv m c m.boxes g := by
  rw [decode_eq_foldl] at h
  have hboxes : ∀ x ∈ m.boxes, x ∈ m.boxes := fun _ hx => hx
  have hdisj0 : ∀ x ∈ m.boxes, x ∉ ([] : List ModelBox) := fun _ _ hm => by cases hm
  have hnodup : m.boxes.Nodup := nodup_of_map_id_nodup (Model.boxIds_nodup hwf)
  obtain hinv := decode_fold_more m c hwf [] ({} : Input) (decode_inv_nil m c)
    (by intro x hx; cases hx) m.boxes g hboxes hdisj0 hnodup h
  rwa [List.nil_append] at hinv

end Elegant.Kinds.JourneyValid


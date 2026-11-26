import Elegant.Layered.AttachPipeline
import Elegant.Layered.RegionReduction
import Elegant.Layered.ComposeNotesC8a
import ElegantGeometry.Validator
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Note base foundation: `layoutNotes` execution record and first transported facts.

This is the foundation of the note tower (steps 7-10 of the RN breakdown): it mirrors
`RegionFoundation.lean` (`SceneExecutionR`, `layoutRIds_success_phases`,
`layoutRIds_sceneExecution`, `SceneExecutionR.boxes_eq_mapR`) for the note stage
`layoutNotes` (`AttachPipeline.lean:256-280`).

`layoutNotes base exactIds (fuel + 1) inp o` either runs `base` (no bundles) or threads
one bundle pipeline: `bundleLayout` per bundle (each a fragment layout over
`layoutNotes base exactIds fuel` plus per-note `base` layouts), `contractOne` fold,
`base` on the contracted input, then `composeNotes` placement. `NotesExecution` records
exactly that bundle case; the no-bundle case is definitionally `base` (see
`layoutNotes_noBundles` in `RegionReduction.lean`), so `layoutNotes_execution` takes the
residual hypothesis `bundlesOf ... ≠ []`, strictly narrower than the goal.

Later workers rewrite with `NotesExecution.canvas_eq`, `boxes_ids`, `boxes_mem`,
`routes_ids`, `routes_endpoints`, `labels_eq`, `labels_mem`, `items_eq`, and the
fragment transport facts to discharge the `Flat*B` fields at the note base.
-/

private theorem nf_bind_ok {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β}
    {b : β} (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- Membership from a successful `mapM`, without an `Inhabited` requirement. -/
private theorem nf_mapM_mem {α β : Type} (f : α → Except LayoutError β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y := by
  intro xs
  induction xs with
  | nil =>
    intro ys h y hy
    have h2 : ([] : List β) = ys := by simpa [List.mapM_nil, pure, Except.pure] using h
    subst h2
    cases hy
  | cons a as ih =>
    intro ys h y hy
    simp only [List.mapM_cons, bind, Except.bind] at h
    obtain ⟨b, hfb, h⟩ := nf_bind_ok h
    obtain ⟨bs, hbs, h⟩ := nf_bind_ok h
    have hys : b :: bs = ys := Except.ok.inj h
    subst hys
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨a, List.mem_cons_self, hfb⟩
    · obtain ⟨x, hx, hfx⟩ := ih bs hbs y hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- Map image equations from a successful `mapM`, for id-preserving steps. -/
private theorem nf_mapM_map_ids {α β : Type} (f : α → Except LayoutError β)
    (idA : α → String) (idB : β → String) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      (∀ a ∈ xs, ∀ b, f a = .ok b → idB b = idA a) → ys.map idB = xs.map idA := by
  intro xs
  induction xs with
  | nil =>
    intro ys h _
    have h2 : ([] : List β) = ys := by simpa [List.mapM_nil, pure, Except.pure] using h
    subst h2
    rfl
  | cons a as ih =>
    intro ys h hpres
    simp only [List.mapM_cons, bind, Except.bind] at h
    obtain ⟨b, hfb, h⟩ := nf_bind_ok h
    obtain ⟨bs, hbs, h⟩ := nf_bind_ok h
    have hys : b :: bs = ys := Except.ok.inj h
    subst hys
    simp only [List.map_cons]
    rw [hpres a List.mem_cons_self b hfb]
    exact congrArg _ (ih bs hbs fun a' ha' b' hb' =>
      hpres a' (List.mem_cons_of_mem _ ha') b' hb')

/-- Witness extraction from a successful `findSome?` (prefixed copy: the
`ComposeNotesC8a` helper is private to that module). -/
private theorem nf_findSome?_exists {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : β), l.findSome? f = some r → ∃ x, x ∈ l ∧ f x = some r := by
  intro l
  induction l with
  | nil => intro r h; exact absurd h (by simp)
  | cons a rest ih =>
    intro r h
    simp only [List.findSome?_cons] at h
    cases hfa : f a with
    | some b =>
      rw [hfa] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨a, List.mem_cons_self, hfa⟩
    | none =>
      rw [hfa] at h
      obtain ⟨x, hx, hfx⟩ := ih r h
      exact ⟨x, List.mem_cons_of_mem a hx, hfx⟩

/-- One executed note-base bundle run: the phase equations of a successful
`layoutNotes base exactIds (fuel + 1)` with a nonempty bundle list. No field asserts a
geometric bound. -/
structure NotesExecution (base : List String → Input → Options → Except LayoutError FamilyResult)
    (exactIds : List String) (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult) where
  params : Params
  metric : Measure.Metric
  atts : List Attach
  bundles : List Bundle
  layouts : List BundleLayout
  contractedInput : Input
  contracted : FamilyResult
  placed : List (List Placed)
  fragments : List Placed
  lines : List (List Measure.Line)
  margin : Int
  gap : Int
  checked : checkedParams o.profile inp.kind = .ok params
  metric_eq : metricOf o.profile o.fontFamily = .ok metric
  margin_eq : margin = params.canvasMargin
  gap_eq : gap = 2 * params.slot + 2
  atts_eq : atts = attachmentsOf inp.boxes
  bundles_eq : bundles = bundlesOf inp.boxes atts
  nonempty : bundles ≠ []
  layouts_eq : bundles.mapM
    (bundleLayout (layoutNotes base exactIds fuel) (base exactIds) inp o margin gap) = .ok layouts
  contractedInput_eq : contractedInput = layouts.foldl contractOne inp
  contracted_eq : base (exactIds ++ layouts.map (·.top.id)) contractedInput o = .ok contracted
  lines_eq : boxLines metric
    (Measure.wrapTarget metric.profile params.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
    inp = .ok lines
  placed_eq : layouts.mapM (placedFragments margin contracted.scene) = .ok placed
  fragments_eq : fragments = placed.flatten
  scene_eq : composeNotes params inp o margin lines contracted layouts atts = .ok res.scene
  budget_eq : res.budgetExhausted = (contracted.budgetExhausted ||
    layouts.any fun l => l.part.budgetExhausted || l.notes.any (·.2.budgetExhausted))
  area_eq : res.itemArea = contracted.itemArea + layouts.foldl
    (fun area l => area + l.part.itemArea + l.notes.foldl (fun a n => a + n.2.itemArea) 0) 0

/-- Recover the phases `layoutNotes` used: either there are no bundles and `base` ran, or
every bundle-phase equation holds. -/
theorem layoutNotes_success_phases
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutNotes base exactIds (fuel + 1) inp o = .ok res) :
    ((bundlesOf inp.boxes (attachmentsOf inp.boxes)).isEmpty = true ∧
      base exactIds inp o = .ok res) ∨
      Nonempty (NotesExecution base exactIds fuel inp o res) := by
  simp only [layoutNotes] at h
  split at h
  · rename_i hempty
    exact Or.inl ⟨hempty, h⟩
  · rename_i hempty
    obtain ⟨P, hP, h⟩ := nf_bind_ok h
    obtain ⟨metric, hm, h⟩ := nf_bind_ok h
    obtain ⟨layouts, hlayouts, h⟩ := nf_bind_ok h
    obtain ⟨contracted, hcontracted, h⟩ := nf_bind_ok h
    obtain ⟨lines, hlines, h⟩ := nf_bind_ok h
    obtain ⟨scene, hscene, h⟩ := nf_bind_ok h
    have hres := Except.ok.inj h
    have hcomp := hscene
    unfold composeNotes at hcomp
    obtain ⟨placed, hplaced, _⟩ := nf_bind_ok hcomp
    have hsc : scene = res.scene := congrArg FamilyResult.scene hres
    have hscen : composeNotes P inp o P.canvasMargin lines contracted layouts
        (attachmentsOf inp.boxes) = .ok res.scene := by
      rw [← hsc]
      exact hscene
    have hb : res.budgetExhausted = (contracted.budgetExhausted ||
        layouts.any fun l => l.part.budgetExhausted || l.notes.any (·.2.budgetExhausted)) :=
      (congrArg FamilyResult.budgetExhausted hres).symm
    have ha : res.itemArea = contracted.itemArea + layouts.foldl
        (fun area l => area + l.part.itemArea + l.notes.foldl (fun a n => a + n.2.itemArea) 0) 0 :=
      (congrArg FamilyResult.itemArea hres).symm
    have hne : bundlesOf inp.boxes (attachmentsOf inp.boxes) ≠ [] := by
      intro he
      apply hempty
      simp [he]
    have e : NotesExecution base exactIds fuel inp o res := { params := P, metric := metric, atts := attachmentsOf inp.boxes, bundles := bundlesOf inp.boxes (attachmentsOf inp.boxes), layouts := layouts, contractedInput := layouts.foldl contractOne inp, contracted := contracted, placed := placed, fragments := placed.flatten, lines := lines, margin := P.canvasMargin, gap := 2 * P.slot + 2, checked := hP, metric_eq := hm, margin_eq := rfl, gap_eq := rfl, atts_eq := rfl, bundles_eq := rfl, nonempty := hne, layouts_eq := hlayouts, contractedInput_eq := rfl, contracted_eq := hcontracted, lines_eq := hlines, placed_eq := hplaced, fragments_eq := rfl, scene_eq := hscen, budget_eq := hb, area_eq := ha }
    exact Or.inr (Nonempty.intro e)
/-- Extract the executed bundle phases that `layoutNotes` used. The no-bundle case runs
`base` directly (`layoutNotes_noBundles`), so the residual `hne` is strictly narrower
than the goal. -/
theorem layoutNotes_execution
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutNotes base exactIds (fuel + 1) inp o = .ok res)
    (hne : bundlesOf inp.boxes (attachmentsOf inp.boxes) ≠ []) :
    Nonempty (NotesExecution base exactIds fuel inp o res) := by
  obtain hempty | hex := layoutNotes_success_phases h
  · obtain ⟨hempty, _⟩ := hempty
    cases he : bundlesOf inp.boxes (attachmentsOf inp.boxes) with
    | nil => exact absurd he hne
    | cons hd tl => simp [he] at hempty
  · exact hex

/-!
## First structural facts over `NotesExecution`.

Box, route, and label lists of `res` in terms of the contracted scene and the placed
fragments. Later clause proofs rewrite with these.
-/

/-- The execution's placed list is the `composeNotes` placed list. -/
theorem NotesExecution.placed_is {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) {placed : List (List Placed)}
    (hp : e.layouts.mapM (placedFragments e.margin e.contracted.scene) = .ok placed) :
    e.placed = placed :=
  Except.ok.inj (e.placed_eq.symm.trans hp)

/-- The composed scene keeps the contracted canvas. -/
theorem NotesExecution.canvas_eq {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) :
    res.scene.canvas = e.contracted.scene.canvas := by
  have h := e.scene_eq
  unfold composeNotes at h
  obtain ⟨placed', hplaced, h⟩ := nf_bind_ok h
  obtain ⟨boxes', hboxes, h⟩ := nf_bind_ok h
  obtain ⟨routes', hroutes, h⟩ := nf_bind_ok h
  have hscene := Except.ok.inj h
  exact (congrArg Scene.canvas hscene).symm

/-- The composed boxes have the input boxes' ids in order. -/
theorem NotesExecution.boxes_ids {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) :
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
  obtain ⟨placed, hp, F, hFmem, hFboxes⟩ := composeNotes_boxes e.scene_eq
  have hbb : res.scene.boxes = inp.boxes.map F := hFboxes
  rw [hbb, List.map_map]
  exact List.map_congr_left fun b hb => (outBox_ok_fields (hFmem b hb)).1

/-- Every composed box comes from an input box with role, parent, and exclusivity kept;
its rect is the first-fragment-or-contracted rect. -/
theorem NotesExecution.boxes_mem {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) :
    ∀ fb ∈ res.scene.boxes, ∃ b ∈ inp.boxes,
      fb.id = b.id ∧ fb.role = b.role.id ∧ fb.parent = b.parent ∧ fb.exclusive = b.exclusive ∧
        outRect e.placed e.contracted.scene b.id = some fb.rect := by
  obtain ⟨placed, hp, F, hFmem, hFboxes⟩ := composeNotes_boxes e.scene_eq
  have hpeq : e.placed = placed := e.placed_is hp
  have hbb : res.scene.boxes = inp.boxes.map F := hFboxes
  intro fb hfb
  rw [hbb] at hfb
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hfb
  obtain ⟨hid, hrole, hpar, hexc, hrect⟩ := outBox_ok_fields (hFmem b hb)
  refine ⟨b, hb, hid, hrole, hpar, hexc, ?_⟩
  rw [hpeq]
  exact hrect

/-- The composed routes have the input routes' ids in order. -/
theorem NotesExecution.routes_ids {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) :
    res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  have h := e.scene_eq
  unfold composeNotes at h
  obtain ⟨placed', hplaced, h⟩ := nf_bind_ok h
  obtain ⟨boxes', hboxes, h⟩ := nf_bind_ok h
  obtain ⟨routes', hroutes, h⟩ := nf_bind_ok h
  have hscene := Except.ok.inj h
  have hrr : res.scene.routes = routes' := (congrArg Scene.routes hscene).symm
  rw [hrr]
  refine nf_mapM_map_ids _ _ _ _ _ hroutes ?_
  intro r hr y hy
  have hex : ∃ pts, y = Route.mk r.id r.fromId r.toId r.orthogonal pts := by
    dsimp only at hy
    split at hy
    · split at hy
      · split at hy
        · obtain ⟨pts, _, hj⟩ := nf_bind_ok hy
          exact ⟨pts, (Except.ok.inj hj).symm⟩
        · obtain ⟨pts, _, hj⟩ := nf_bind_ok hy
          exact ⟨pts, (Except.ok.inj hj).symm⟩
      · obtain ⟨pts, _, hj⟩ := nf_bind_ok hy
        exact ⟨pts, (Except.ok.inj hj).symm⟩
    · split at hy
      · obtain ⟨pts, _, hj⟩ := nf_bind_ok hy
        exact ⟨pts, (Except.ok.inj hj).symm⟩
      · obtain ⟨pts, _, hj⟩ := nf_bind_ok hy
        exact ⟨pts, (Except.ok.inj hj).symm⟩
    · obtain ⟨pts, _, hj⟩ := nf_bind_ok hy
      exact ⟨pts, (Except.ok.inj hj).symm⟩
  obtain ⟨pts, hyy⟩ := hex
  rw [hyy]

/-- Every composed route comes from an input route with endpoints and orthogonality kept. -/
theorem NotesExecution.routes_mem {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) :
    ∀ rt ∈ res.scene.routes, ∃ r ∈ inp.routes,
      rt.id = r.id ∧ rt.fromId = r.fromId ∧ rt.toId = r.toId ∧ rt.orthogonal = r.orthogonal := by
  have h := e.scene_eq
  unfold composeNotes at h
  obtain ⟨placed', hplaced, h⟩ := nf_bind_ok h
  obtain ⟨boxes', hboxes, h⟩ := nf_bind_ok h
  obtain ⟨routes', hroutes, h⟩ := nf_bind_ok h
  have hscene := Except.ok.inj h
  have hrr : res.scene.routes = routes' := (congrArg Scene.routes hscene).symm
  rw [hrr]
  intro rt hrt
  obtain ⟨r, hr, hfr⟩ := nf_mapM_mem _ _ _ hroutes rt hrt
  have hex : ∃ pts, rt = Route.mk r.id r.fromId r.toId r.orthogonal pts := by
    dsimp only at hfr
    split at hfr
    · split at hfr
      · split at hfr
        · obtain ⟨pts, _, hj⟩ := nf_bind_ok hfr
          exact ⟨pts, (Except.ok.inj hj).symm⟩
        · obtain ⟨pts, _, hj⟩ := nf_bind_ok hfr
          exact ⟨pts, (Except.ok.inj hj).symm⟩
      · obtain ⟨pts, _, hj⟩ := nf_bind_ok hfr
        exact ⟨pts, (Except.ok.inj hj).symm⟩
    · split at hfr
      · obtain ⟨pts, _, hj⟩ := nf_bind_ok hfr
        exact ⟨pts, (Except.ok.inj hj).symm⟩
      · obtain ⟨pts, _, hj⟩ := nf_bind_ok hfr
        exact ⟨pts, (Except.ok.inj hj).symm⟩
    · obtain ⟨pts, _, hj⟩ := nf_bind_ok hfr
      exact ⟨pts, (Except.ok.inj hj).symm⟩
  obtain ⟨pts, hyy⟩ := hex
  subst hyy
  exact ⟨r, hr, rfl, rfl, rfl, rfl⟩

/-- The composed labels are the input-label filterMap over first-fragment-or-contracted. -/
theorem NotesExecution.labels_eq {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) :
    res.scene.labels = inp.labels.filterMap fun l =>
      match e.fragments.findSome? (·.label l.id) with
      | some label => some label
      | none => e.contracted.scene.labels.find? (·.id == l.id) := by
  have h := e.scene_eq
  unfold composeNotes at h
  obtain ⟨placed', hplaced, h⟩ := nf_bind_ok h
  obtain ⟨boxes', hboxes, h⟩ := nf_bind_ok h
  obtain ⟨routes', hroutes, h⟩ := nf_bind_ok h
  have hscene := Except.ok.inj h
  have hfrag : e.fragments = placed'.flatten := by
    rw [e.fragments_eq, e.placed_is hplaced]
  have h1 := congrArg Scene.labels hscene
  dsimp only at h1
  rw [← hfrag] at h1
  exact h1.symm

/-- Every composed label comes from an input label: either a shifted fragment label or a
contracted-scene label. -/
theorem NotesExecution.labels_mem {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) :
    ∀ lb ∈ res.scene.labels, ∃ m ∈ inp.labels, lb.id = m.id ∧
      ((∃ p ∈ e.fragments, ∃ fl ∈ p.scene.labels,
        fl.id = m.id ∧ lb.rect = shiftRect p.dx p.dy fl.rect) ∨
        lb ∈ e.contracted.scene.labels) := by
  intro lb hlb
  rw [e.labels_eq] at hlb
  obtain ⟨m, hm, hgm⟩ := List.mem_filterMap.mp hlb
  cases hfs : e.fragments.findSome? (·.label m.id) with
  | some v =>
    simp only [hfs] at hgm
    have hvl : v = lb := Option.some.inj hgm
    obtain ⟨p, hp, hpv⟩ := nf_findSome?_exists _ _ _ hfs
    have hpv2 : (p.scene.labels.find? (·.id == m.id)).map
        (fun fl => ({ fl with rect := shiftRect p.dx p.dy fl.rect } : SceneLabel)) = some v := hpv
    obtain ⟨fl, hfl, hflv⟩ := Option.map_eq_some_iff.mp hpv2
    have hpid := List.find?_some hfl
    simp only [beq_iff_eq] at hpid
    have hlbv : lb = { fl with rect := shiftRect p.dx p.dy fl.rect } := (hflv.trans hvl).symm
    refine ⟨m, hm, ?_, Or.inl ⟨p, hp, fl, List.mem_of_find?_eq_some hfl, hpid, ?_⟩⟩
    · rw [hlbv]
      exact hpid
    · rw [hlbv]
  | none =>
    simp only [hfs] at hgm
    have hqpid := List.find?_some hgm
    simp only [beq_iff_eq] at hqpid
    exact ⟨m, hm, hqpid, Or.inr (List.mem_of_find?_eq_some hgm)⟩
theorem NotesExecution.items_eq {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) :
    res.scene.items = applyTitles
      (e.fragments.flatMap (·.titles) ++ groupTitles e.contracted.scene.items)
      (sceneItems e.params inp res.scene.boxes res.scene.routes e.lines
        res.scene.labels) := by
  have h := e.scene_eq
  unfold composeNotes at h
  obtain ⟨placed', hplaced, h⟩ := nf_bind_ok h
  obtain ⟨boxes', hboxes, h⟩ := nf_bind_ok h
  obtain ⟨routes', hroutes, h⟩ := nf_bind_ok h
  have hscene := Except.ok.inj h
  have hfrag : e.fragments = placed'.flatten := by
    rw [e.fragments_eq, e.placed_is hplaced]
  have hbb : res.scene.boxes = boxes' := (congrArg Scene.boxes hscene).symm
  have hrr : res.scene.routes = routes' := (congrArg Scene.routes hscene).symm
  have h1 := congrArg Scene.items hscene
  dsimp only at h1
  rw [← hfrag, ← hbb, ← hrr] at h1
  rw [e.labels_eq]
  exact h1.symm

/-!
## Translation transport within one fragment.

`composeNotes` places each fragment scene with a `Placed` shift. Sizes, containment,
disjointness, and orthogonality are invariant under that shift, so the C2 (positive
sizes, disjointness) and C3 (containment) facts of a fragment scene carry over to the
composed scene. The first-match side conditions stay as explicit hypotheses: discharging
them needs bundle footprint disjointness (next step).
-/

/-- Shifting preserves rect sizes. -/
theorem notesShiftRect_size (r : Rect) (dx dy : Int) :
    (shiftRect dx dy r).w = r.w ∧ (shiftRect dx dy r).h = r.h :=
  ⟨rfl, rfl⟩

/-- Shifting preserves nonnegativity of rect sizes (C2 positive sizes). -/
theorem notesShiftRect_nonneg {r : Rect} (hw : 0 ≤ r.w) (hh : 0 ≤ r.h) (dx dy : Int) :
    0 ≤ (shiftRect dx dy r).w ∧ 0 ≤ (shiftRect dx dy r).h := by
  simp only [shiftRect]
  exact ⟨hw, hh⟩

/-- Shifting preserves containment (C3 box-in-parent within one fragment). -/
theorem notesShiftRect_contained (a b : Rect) (dx dy : Int) :
    (shiftRect dx dy a).Contained (shiftRect dx dy b) ↔ a.Contained b := by
  simp only [shiftRect, Rect.Contained]
  constructor <;> intro h <;> omega

/-- Shifting preserves disjointness (C2 exclusive-sibling disjointness within one
fragment; prefixed copy: the `ComposeNotesC8a` helper is private to that module). -/
theorem notesShiftRect_disjoint (a b : Rect) (dx dy : Int) :
    Disjoint (shiftRect dx dy a) (shiftRect dx dy b) ↔ Disjoint a b := by
  simp only [Disjoint, Rect.meetsInterior, shiftRect]
  constructor <;> intro h <;> omega

/-- Shifting points preserves route orthogonality (C4 within one fragment). -/
theorem notesShiftPoint_orthogonal (dx dy : Int) :
    ∀ pts : List Point,
      Polyline.isOrthogonal (pts.map (shiftPoint dx dy)) = Polyline.isOrthogonal pts
  | [] => rfl
  | [_] => rfl
  | p :: q :: rest => by
    have ih := notesShiftPoint_orthogonal dx dy (q :: rest)
    simp only [List.map_cons, shiftPoint] at ih ⊢
    simp [Polyline.isOrthogonal, ih]

/-- A composed box resolved from a fragment keeps that fragment box's shifted rect. -/
theorem NotesExecution.resBox_of_fragment
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) {p : Placed} (_hp : p ∈ e.fragments)
    {fb : Box} (_hfb : fb ∈ p.scene.boxes)
    (hfind : e.fragments.findSome? (fun q => q.rect fb.id) =
      some (shiftRect p.dx p.dy fb.rect))
    {rb : Box} (hrb : rb ∈ res.scene.boxes) (hid : rb.id = fb.id) :
    rb.rect = shiftRect p.dx p.dy fb.rect := by
  obtain ⟨b, hb, hidb, _, _, _, hrect⟩ := e.boxes_mem rb hrb
  have hbid : b.id = fb.id := hidb.symm.trans hid
  rw [hbid] at hrect
  have hfl : e.placed.flatten = e.fragments := e.fragments_eq.symm
  have hout : outRect e.placed e.contracted.scene fb.id =
      some (shiftRect p.dx p.dy fb.rect) := by
    simp only [outRect, hfl, hfind]
  rw [hout] at hrect
  exact (Option.some.inj hrect).symm

/-- Fragment-internal disjointness carries over to the composed scene (C2 transport). -/
theorem NotesExecution.resC2_of_fragment
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) {p : Placed} (hp : p ∈ e.fragments)
    {a b : Box} (ha : a ∈ p.scene.boxes) (hb : b ∈ p.scene.boxes)
    (hdisj : Disjoint a.rect b.rect)
    {ra rb : Box} (hra : ra ∈ res.scene.boxes) (hida : ra.id = a.id)
    (hrb : rb ∈ res.scene.boxes) (hidb : rb.id = b.id)
    (hfa : e.fragments.findSome? (fun q => q.rect a.id) =
      some (shiftRect p.dx p.dy a.rect))
    (hfb : e.fragments.findSome? (fun q => q.rect b.id) =
      some (shiftRect p.dx p.dy b.rect)) :
    Disjoint ra.rect rb.rect := by
  have ha' : ra.rect = shiftRect p.dx p.dy a.rect :=
    e.resBox_of_fragment hp ha hfa hra hida
  have hb' : rb.rect = shiftRect p.dx p.dy b.rect :=
    e.resBox_of_fragment hp hb hfb hrb hidb
  rw [ha', hb']
  exact (notesShiftRect_disjoint a.rect b.rect p.dx p.dy).mpr hdisj

/-- Fragment-internal containment carries over to the composed scene (C3 transport). -/
theorem NotesExecution.resC3_of_fragment
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) {p : Placed} (hp : p ∈ e.fragments)
    {c par : Box} (hc : c ∈ p.scene.boxes) (hpar : par ∈ p.scene.boxes)
    (hcont : par.rect.Contained c.rect)
    {rc rpar : Box} (hrc : rc ∈ res.scene.boxes) (hidc : rc.id = c.id)
    (hrpar : rpar ∈ res.scene.boxes) (hidpar : rpar.id = par.id)
    (hfc : e.fragments.findSome? (fun q => q.rect c.id) =
      some (shiftRect p.dx p.dy c.rect))
    (hfp : e.fragments.findSome? (fun q => q.rect par.id) =
      some (shiftRect p.dx p.dy par.rect)) :
    rpar.rect.Contained rc.rect := by
  have hc' : rc.rect = shiftRect p.dx p.dy c.rect :=
    e.resBox_of_fragment hp hc hfc hrc hidc
  have hp' : rpar.rect = shiftRect p.dx p.dy par.rect :=
    e.resBox_of_fragment hp hpar hfp hrpar hidpar
  rw [hc', hp']
  exact (notesShiftRect_contained par.rect c.rect p.dx p.dy).mpr hcont


end PipelineImpl
end Layered
end Elegant

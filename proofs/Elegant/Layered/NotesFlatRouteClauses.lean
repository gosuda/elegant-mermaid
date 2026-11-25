import Elegant.Layered.NotesFoundation
import Elegant.Layered.ComposeNotesC8a
import Elegant.Layered.RouteTransport
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Route clauses C4 (orthogonal routes) and C5 (route ends on the boundary of
their end boxes) for the note stage `layoutNotes`
(`AttachPipeline.lean:256-280`), built on `NotesFoundation`.

`composeNotes` classifies every input route by `bundleOf` on its endpoints:

* (a) kept: neither end is in a bundle; the composed points equal the
  contracted-scene route's points;
* (b) fragment-internal: both ends are in the same bundle `a`; the composed
  points equal the fragment scene route's points shifted by the fragment
  placement;
* (c) cross-bundle: any other shape; the composed route is rebuilt by
  `routeAround` on the visibility grid.

`notes_route_cases` proves the points equation for each class. `notes_c4` and
`notes_c5` transport the base (`contracted`) and fragment C4/C5 facts along
those equations. The two router facts (`notesRouterOrtho`, `notesRouterEnds`)
and the two flag bridges (`notesFlagsKept`, `notesFlagsFragment`) stay as
named single-fact residuals about `routeAround` and the base/fragment
results. The two first-match side conditions (`notesKeptBoxContracted`,
`notesFragBoxFirst`) stay as named execution residuals, in the style of
`NotesExecution.resC2_of_fragment`. None of them mentions `res` validity.

Probe: `proofs/wip/Probe/NotesFlatRouteRouterProbe.lean` evaluates
`routeAround` on a cross-bundle edge, a note on a composite state, and a
self-loop on a noted state, plus a synthetic first-match miniature.
-/

/-! ### Private list/except helpers (prefixed copies; siblings stay private) -/

private theorem nfr_bind_ok {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β}
    {b : β} (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem nfr_mapM_mem {α β : Type} (f : α → Except LayoutError β) :
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
    obtain ⟨b, hfb, h⟩ := nfr_bind_ok h
    obtain ⟨bs, hbs, h⟩ := nfr_bind_ok h
    have hys : b :: bs = ys := Except.ok.inj h
    subst hys
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨a, List.mem_cons_self, hfb⟩
    · obtain ⟨x, hx, hfx⟩ := ih bs hbs y hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

private theorem nfr_findSome?_exists {α β : Type} (f : α → Option β) :
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

/-- Members of a `getD` sublist with the empty default lie in the flatten. -/
private theorem nfr_getD_flatten_mem {α : Type} (l : List (List α)) (a : Nat) {x : α}
    (h : x ∈ List.getD l a []) : x ∈ l.flatten := by
  induction l generalizing a with
  | nil =>
    have hnil : List.getD ([] : List (List α)) a [] = [] := rfl
    rw [hnil] at h
    exact absurd h (by simp)
  | cons s ss ih =>
    cases a with
    | zero =>
      rw [List.getD_cons_zero] at h
      exact List.mem_flatten.mpr ⟨s, List.mem_cons_self, h⟩
    | succ a =>
      rw [List.getD_cons_succ] at h
      have hmem := ih a h
      obtain ⟨t, ht, hxt⟩ := List.mem_flatten.mp hmem
      exact List.mem_flatten.mpr ⟨t, List.mem_cons_of_mem _ ht, hxt⟩

/-- A `find?` returning `some` on a member's key. -/
private theorem nfr_find?_some_of_mem {α : Type} (p : α → Bool) {l : List α} {a : α}
    (hmem : a ∈ l) (hp : p a = true) : ∃ b, l.find? p = some b := by
  induction l with
  | nil => cases hmem
  | cons c cs ih =>
    rcases List.mem_cons.mp hmem with rfl | htail
    · exact ⟨a, by simp only [List.find?_cons, hp]⟩
    · by_cases hc : p c = true
      · exact ⟨c, by simp only [List.find?_cons, hc]⟩
      · obtain ⟨b, hb⟩ := ih htail
        exact ⟨b, by simp only [List.find?_cons, hc]; exact hb⟩

/-- A `lookup` hit yields the first matching box, its rect, and its id. -/
private theorem nfr_first_match {bs : List Box} {k : String} {from_ : Rect}
    (h : (bs.map fun b => (b.id, b.rect)).lookup k = some from_) :
    ∃ rb, bs.find? (fun b => b.id == k) = some rb ∧ rb.rect = from_ ∧ rb.id = k := by
  induction bs with
  | nil =>
    simp only [List.map_nil] at h
    have hnil : List.lookup k ([] : List (String × Rect)) = none := rfl
    rw [hnil] at h
    exact absurd h (by simp)
  | cons c cs ih =>
    simp only [List.map_cons, List.lookup_cons] at h
    by_cases hc : (c.id == k) = true
    · have hc2 : (k == c.id) = true := beq_iff_eq.mpr (beq_iff_eq.mp hc).symm
      simp only [hc2] at h
      have hcr : c.rect = from_ := Option.some.inj h
      have hcid : c.id = k := beq_iff_eq.mp hc
      refine ⟨c, ?_, hcr, hcid⟩
      simp only [List.find?_cons, hc]
    · have hc2 : ¬ (k == c.id) = true := by
        intro hcon
        exact hc (beq_iff_eq.mpr (beq_iff_eq.mp hcon).symm)
      simp only [hc2] at h
      obtain ⟨rb, hrb, hrect, hid⟩ := ih h
      refine ⟨rb, ?_, hrect, hid⟩
      simp only [List.find?_cons, hc]
      exact hrb

/-- The contracted half of `outRect` when no fragment claims the id. -/
private theorem nfr_outRect_contracted {placed : List (List Placed)} {contracted : Scene}
    {id : String} {r : Rect} (h : outRect placed contracted id = some r)
    (hno : ∀ p ∈ placed.flatten, ∀ q : Rect, p.rect id ≠ some q) :
    ∃ cb, contracted.boxes.find? (fun b => b.id == id) = some cb ∧ cb.rect = r := by
  unfold outRect at h
  have hnone : placed.flatten.findSome? (fun x => x.rect id) = none := by
    cases hs : placed.flatten.findSome? (fun x => x.rect id) with
    | none => rfl
    | some R =>
      obtain ⟨p, hp, hpR⟩ := nfr_findSome?_exists _ _ _ hs
      exact absurd hpR (hno p hp R)
  simp only [hnone] at h
  match he : contracted.boxes.find? (fun b => b.id == id) with
  | none => simp [he] at h
  | some cb =>
    simp only [he, Option.map_some] at h
    exact ⟨cb, he, Option.some.inj h⟩

private theorem nfr_mem_input_box_of_contains {inp : Input} {k : String}
    (h : (inp.boxes.map (·.id)).contains k = true) :
    ∃ b ∈ inp.boxes, b.id = k := by
  have hm : k ∈ inp.boxes.map (·.id) := by simpa [List.contains_eq_mem] using h
  obtain ⟨b, hb, hbk⟩ := List.mem_map.mp hm
  exact ⟨b, hb, hbk⟩

/-- Every input box has a composed box with the same id. -/
private theorem nfr_boxes_forward_mem (placed' : List (List Placed)) (contracted : Scene) :
    ∀ (bs : List ModelBox) (ys : List Box),
      bs.mapM (outBox placed' contracted) = .ok ys →
      ∀ b ∈ bs, ∃ y ∈ ys, y.id = b.id := by
  intro bs
  induction bs with
  | nil => intro ys h b hb; cases hb
  | cons c cs ih =>
    intro ys h b hb
    simp only [List.mapM_cons, bind, Except.bind] at h
    obtain ⟨y0, hf0, h1⟩ := nfr_bind_ok h
    obtain ⟨ys0, hfs0, h2⟩ := nfr_bind_ok h1
    have hys : y0 :: ys0 = ys := Except.ok.inj h2
    subst hys
    rcases List.mem_cons.mp hb with rfl | htail
    · exact ⟨y0, List.mem_cons_self, (outBox_ok_fields hf0).1⟩
    · obtain ⟨y, hym, hyid⟩ := ih ys0 hfs0 b htail
      exact ⟨y, List.mem_cons_of_mem _ hym, hyid⟩

/-- Every input box has a composed box with the same id. -/
theorem NotesExecution.boxes_forward
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) :
    ∀ b ∈ inp.boxes, ∃ rb ∈ res.scene.boxes, rb.id = b.id := by
  intro b hb
  have h := e.scene_eq
  unfold composeNotes at h
  obtain ⟨placed', hplaced, h⟩ := nfr_bind_ok h
  obtain ⟨boxes', hboxes, h⟩ := nfr_bind_ok h
  obtain ⟨routes', hroutes, h⟩ := nfr_bind_ok h
  have hscene := Except.ok.inj h
  have hbb : res.scene.boxes = boxes' := (congrArg Scene.boxes hscene).symm
  obtain ⟨y, hym, hyid⟩ := nfr_boxes_forward_mem placed' e.contracted.scene inp.boxes boxes' hboxes b hb
  rw [hbb]
  exact ⟨y, hym, hyid⟩

/-! ### Route classification and `routeAround` argument abbreviations -/

/-- `bundleOf` of `composeNotes`: the first layout whose bundle owns `id`. -/
abbrev notesBundleOf (inp : Input) (layouts : List BundleLayout) (id : String) : Option Nat :=
  layouts.findIdx? fun l => l.top.id == id || Compound.inside inp.boxes l.top.id id

/-- Class (a): neither route end is in a bundle. -/
def notesKept (inp : Input) (layouts : List BundleLayout) (r : ModelRoute) : Prop :=
  notesBundleOf inp layouts r.fromId = none ∧ notesBundleOf inp layouts r.toId = none

/-- Class (b): both route ends are in the same bundle `a`. -/
def notesSameBundleAt (inp : Input) (layouts : List BundleLayout) (a : Nat)
    (r : ModelRoute) : Prop :=
  notesBundleOf inp layouts r.fromId = some a ∧ notesBundleOf inp layouts r.toId = some a

/-- Class (c): every other bundle shape (cross-bundle). -/
def notesCross (inp : Input) (layouts : List BundleLayout) (r : ModelRoute) : Prop :=
  ¬ notesKept inp layouts r ∧ ∀ a : Nat, ¬ notesSameBundleAt inp layouts a r

/-- The `height` local of `composeNotes`, with its four direction arms. -/
def notesFrameHeight (contracted : FamilyResult) (o : Options) (margin : Int) : Int :=
  match o.direction with
  | .TB => contracted.scene.canvas.h - 2 * margin
  | .BT => contracted.scene.canvas.h - 2 * margin
  | .LR => contracted.scene.canvas.w - 2 * margin
  | .RL => contracted.scene.canvas.w - 2 * margin

/-- The `frame` local of `composeNotes`. -/
def notesFrameOf (contracted : FamilyResult) (o : Options) (margin : Int) : Frame :=
  ⟨o.direction, notesFrameHeight contracted o margin, margin⟩

/-- The `rects` local of `composeNotes`, stated on the composed boxes. -/
def notesRectsOf (boxes : List Box) : List (String × Rect) :=
  boxes.map fun b => (b.id, b.rect)

/-- The `labels` local of `composeNotes`, stated on placed fragments. -/
def notesLabelsOf (fragments : List Placed) (contracted : FamilyResult)
    (inp : Input) : List SceneLabel :=
  inp.labels.filterMap fun l =>
    match fragments.findSome? (·.label l.id) with
    | some label => some label
    | none => contracted.scene.labels.find? (·.id == l.id)

/-- The `titles` local of `composeNotes`. -/
def notesTitlesOf (fragments : List Placed) (contracted : FamilyResult) :
    List (String × Rect) :=
  fragments.flatMap (·.titles) ++ groupTitles contracted.scene.items

/-! ### Named residuals: router facts, flag bridges, first-match sides -/

/-- Router residual (C4): every successful `routeAround` output is orthogonal. -/
def notesRouterOrtho (inp : Input) (atts : List Attach) (frame : Frame)
    (rects : List (String × Rect)) (labels : List SceneLabel)
    (titles : List (String × Rect)) : Prop :=
  ∀ r ∈ inp.routes, ∀ pts : List Point,
    routeAround inp atts frame rects labels titles r = .ok pts →
    Polyline.isOrthogonal pts = true

/-- Router residual (C5): every successful `routeAround` output starts and
ends on the boundary of its looked-up end rects. -/
def notesRouterEnds (inp : Input) (atts : List Attach) (frame : Frame)
    (rects : List (String × Rect)) (labels : List SceneLabel)
    (titles : List (String × Rect)) : Prop :=
  ∀ r ∈ inp.routes, ∀ pts : List Point,
    routeAround inp atts frame rects labels titles r = .ok pts →
    ∃ from_ to_ : Rect, ∃ p q : Point,
      rects.lookup r.fromId = some from_ ∧ rects.lookup r.toId = some to_ ∧
      pts.head? = some p ∧ pts.getLast? = some q ∧
      Validator.onBoundary p from_ ∧ Validator.onBoundary q to_

/-- Flag bridge (kept): the contracted scene keeps id, flags, and endpoints
of each kept input route. A single fact about the base result. -/
def notesFlagsKept (inp : Input) (layouts : List BundleLayout)
    (contracted : FamilyResult) : Prop :=
  ∀ r ∈ inp.routes, notesKept inp layouts r →
    ∀ cr ∈ contracted.scene.routes, cr.id = r.id →
      cr.orthogonal = r.orthogonal ∧ cr.fromId = r.fromId ∧ cr.toId = r.toId

/-- Flag bridge (fragment): each fragment scene keeps id, flags, and endpoints
of each same-bundle input route. A single fact about the fragment results. -/
def notesFlagsFragment (inp : Input) (layouts : List BundleLayout)
    (fragments : List Placed) : Prop :=
  ∀ r ∈ inp.routes, ∀ a : Nat, notesSameBundleAt inp layouts a r →
    ∀ p ∈ fragments, ∀ fr ∈ p.scene.routes, fr.id = r.id →
      fr.orthogonal = r.orthogonal ∧ fr.fromId = r.fromId ∧ fr.toId = r.toId

/-- Route ends resolve to input boxes: the well-formedness fragment used for
the C5 end-box lookup. -/
def notesEndsInBoxes (inp : Input) : Prop :=
  ∀ r ∈ inp.routes, ((inp.boxes.map (·.id)).contains r.fromId = true) ∧
    ((inp.boxes.map (·.id)).contains r.toId = true)

/-- First-match side condition (kept): no fragment claims a kept end id, so the
end box resolves to the contracted scene. Later discharged by footprint
disjointness. -/
def notesKeptBoxContracted (placed : List (List Placed)) (r : ModelRoute) : Prop :=
  (∀ p ∈ placed.flatten, ∀ q : Rect, p.rect r.fromId ≠ some q) ∧
  (∀ p ∈ placed.flatten, ∀ q : Rect, p.rect r.toId ≠ some q)

/-- First-match side condition (fragment): the fragment holding an endpoint box
wins the lookup, so the end box is the translated fragment box. Later
discharged by footprint disjointness. -/
def notesFragBoxFirst (fragments : List Placed) (r : ModelRoute) : Prop :=
  ∀ p ∈ fragments, ∀ fb0 ∈ p.scene.boxes, ∀ tb0 ∈ p.scene.boxes,
    fb0.id = r.fromId → tb0.id = r.toId →
    fragments.findSome? (fun q => q.rect fb0.id) = some (shiftRect p.dx p.dy fb0.rect) ∧
    fragments.findSome? (fun q => q.rect tb0.id) = some (shiftRect p.dx p.dy tb0.rect)

/-! ### Points equations per class -/

/-- Every composed route falls in class (a), (b), or (c), with the matching
points equation. Kept points equal the contracted route's points; fragment
points equal the shifted fragment route's points; cross points are the
`routeAround` output. -/
theorem notes_route_cases
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    {rt : Route} (hrt : rt ∈ res.scene.routes) :
    ∃ r ∈ inp.routes, rt.id = r.id ∧ rt.fromId = r.fromId ∧ rt.toId = r.toId ∧
      rt.orthogonal = r.orthogonal ∧
      ((notesKept inp e.layouts r ∧
        ∃ cr ∈ e.contracted.scene.routes, cr.id = r.id ∧ rt.points = cr.points) ∨
       (∃ a : Nat, notesSameBundleAt inp e.layouts a r ∧
        ∃ p ∈ e.fragments, ∃ fr ∈ p.scene.routes,
          fr.id = r.id ∧ rt.points = fr.points.map (shiftPoint p.dx p.dy)) ∨
       (notesCross inp e.layouts r ∧
        ∃ pts : List Point, rt.points = pts ∧
          routeAround inp e.atts (notesFrameOf e.contracted o e.margin)
            (notesRectsOf res.scene.boxes)
            (notesLabelsOf e.fragments e.contracted inp)
            (notesTitlesOf e.fragments e.contracted) r = .ok pts)) := by
  have h := e.scene_eq
  unfold composeNotes at h
  obtain ⟨placed', hplaced, h⟩ := nfr_bind_ok h
  obtain ⟨boxes', hboxes, h⟩ := nfr_bind_ok h
  obtain ⟨routes', hroutes, h⟩ := nfr_bind_ok h
  have hscene := Except.ok.inj h
  have hrr : res.scene.routes = routes' := (congrArg Scene.routes hscene).symm
  have hpeq : e.placed = placed' := e.placed_is hplaced
  rw [hrr] at hrt
  obtain ⟨x, hx, hstep⟩ := nfr_mapM_mem _ _ _ hroutes rt hrt
  dsimp only at hstep
  cases h1 : e.layouts.findIdx? (fun l => l.top.id == x.fromId || Compound.inside inp.boxes l.top.id x.fromId) with
  | none =>
    cases h2 : e.layouts.findIdx? (fun l => l.top.id == x.toId || Compound.inside inp.boxes l.top.id x.toId) with
    | none =>
      simp only [h1, h2] at hstep
      cases hfind : e.contracted.scene.routes.find? (fun y => y.id == x.id) with
      | none =>
        rw [hfind] at hstep
        simp [bind, Except.bind] at hstep
      | some cr =>
        rw [hfind] at hstep
        dsimp only at hstep
        obtain ⟨pts, hptsok, hj⟩ := nfr_bind_ok hstep
        have hmk : Route.mk x.id x.fromId x.toId x.orthogonal pts = rt :=
          Except.ok.inj hj
        have hpp : cr.points = pts := Except.ok.inj hptsok
        subst hpp
        have hcrid : cr.id = x.id := by
          have hbe := List.find?_some hfind
          simpa [beq_iff_eq] using hbe
        have hptseq : rt.points = cr.points := (congrArg Route.points hmk).symm
        exact ⟨x, hx, (congrArg Route.id hmk).symm, (congrArg Route.fromId hmk).symm,
          (congrArg Route.toId hmk).symm, (congrArg Route.orthogonal hmk).symm,
          Or.inl ⟨⟨h1, h2⟩, cr, List.mem_of_find?_eq_some hfind, hcrid, hptseq⟩⟩
    | some b =>
      simp only [h1, h2] at hstep
      have hbb : res.scene.boxes = boxes' := (congrArg Scene.boxes hscene).symm
      have hfeq : placed'.flatten = e.fragments := by
        rw [← hpeq]
        exact e.fragments_eq.symm
      have hroute_raw := hstep
      rw [← hbb, hfeq] at hroute_raw
      obtain ⟨pts, hroute, hj⟩ := nfr_bind_ok hroute_raw
      have hmk : Route.mk x.id x.fromId x.toId x.orthogonal pts = rt :=
        Except.ok.inj hj
      have hptseq : rt.points = pts := (congrArg Route.points hmk).symm
      have hroute : routeAround inp e.atts (notesFrameOf e.contracted o e.margin)
          (notesRectsOf res.scene.boxes)
          (notesLabelsOf e.fragments e.contracted inp)
          (notesTitlesOf e.fragments e.contracted) x = .ok pts := hroute
      have hnkept : ¬ notesKept inp e.layouts x := by
        intro hcon
        obtain ⟨_, k2⟩ := hcon
        simp only [notesBundleOf] at k2
        rw [k2] at h2
        simp at h2
      have hnsame : ∀ a : Nat, ¬ notesSameBundleAt inp e.layouts a x := by
        intro a hcon
        obtain ⟨s1, _⟩ := hcon
        simp only [notesBundleOf] at s1
        rw [s1] at h1
        simp at h1
      exact ⟨x, hx, (congrArg Route.id hmk).symm, (congrArg Route.fromId hmk).symm,
        (congrArg Route.toId hmk).symm, (congrArg Route.orthogonal hmk).symm,
        Or.inr (Or.inr ⟨⟨hnkept, hnsame⟩, pts, hptseq, hroute⟩)⟩
  | some a =>
    cases h2 : e.layouts.findIdx? (fun l => l.top.id == x.toId || Compound.inside inp.boxes l.top.id x.toId) with
    | none =>
      simp only [h1, h2] at hstep
      have hbb : res.scene.boxes = boxes' := (congrArg Scene.boxes hscene).symm
      have hfeq : placed'.flatten = e.fragments := by
        rw [← hpeq]
        exact e.fragments_eq.symm
      have hroute_raw := hstep
      rw [← hbb, hfeq] at hroute_raw
      obtain ⟨pts, hroute, hj⟩ := nfr_bind_ok hroute_raw
      have hmk : Route.mk x.id x.fromId x.toId x.orthogonal pts = rt :=
        Except.ok.inj hj
      have hptseq : rt.points = pts := (congrArg Route.points hmk).symm
      have hroute : routeAround inp e.atts (notesFrameOf e.contracted o e.margin)
          (notesRectsOf res.scene.boxes)
          (notesLabelsOf e.fragments e.contracted inp)
          (notesTitlesOf e.fragments e.contracted) x = .ok pts := hroute
      have hnkept : ¬ notesKept inp e.layouts x := by
        intro hcon
        obtain ⟨k1, _⟩ := hcon
        simp only [notesBundleOf] at k1
        rw [k1] at h1
        simp at h1
      have hnsame : ∀ a : Nat, ¬ notesSameBundleAt inp e.layouts a x := by
        intro a' hcon
        obtain ⟨_, s2⟩ := hcon
        simp only [notesBundleOf] at s2
        rw [s2] at h2
        simp at h2
      exact ⟨x, hx, (congrArg Route.id hmk).symm, (congrArg Route.fromId hmk).symm,
        (congrArg Route.toId hmk).symm, (congrArg Route.orthogonal hmk).symm,
        Or.inr (Or.inr ⟨⟨hnkept, hnsame⟩, pts, hptseq, hroute⟩)⟩
    | some b =>
      simp only [h1, h2] at hstep
      cases hab : (a == b) with
      | true =>
        simp only [hab] at hstep
        rw [← hpeq] at hstep
        cases hf : (e.placed.getD a []).findSome? (fun q => q.route x.id) with
        | none =>
          rw [hf] at hstep
          simp [bind, Except.bind] at hstep
        | some pts =>
          rw [hf] at hstep
          dsimp only at hstep
          obtain ⟨a0, ha0, hj⟩ := nfr_bind_ok hstep
          have haa : pts = a0 := Except.ok.inj ha0
          have hmk : Route.mk x.id x.fromId x.toId x.orthogonal a0 = rt :=
            Except.ok.inj hj
          have hba : a = b := beq_iff_eq.mp hab
          have h1a : notesBundleOf inp e.layouts x.fromId = some a := h1
          have h2a : notesBundleOf inp e.layouts x.toId = some a := by
            rw [← hba] at h2
            exact h2
          obtain ⟨frag, hfragmem, hfrageq⟩ := nfr_findSome?_exists _ _ _ hf
          have hpfrag : frag ∈ e.fragments := by
            have hflat := nfr_getD_flatten_mem e.placed a hfragmem
            rw [← e.fragments_eq] at hflat
            exact hflat
          simp only [Placed.route] at hfrageq
          cases hfr : frag.scene.routes.find? (fun y => y.id == x.id) with
          | none => simp [hfr] at hfrageq
          | some fr =>
            have hfrpts : fr.points.map (shiftPoint frag.dx frag.dy) = pts := by
              simpa [hfr] using hfrageq
            have hfrmem : fr ∈ frag.scene.routes :=
              List.mem_of_find?_eq_some hfr
            have hfrid : fr.id = x.id := by
              have hbe := List.find?_some hfr
              simpa [beq_iff_eq] using hbe
            have hptseq : rt.points = fr.points.map (shiftPoint frag.dx frag.dy) := by
              have hcc := (congrArg Route.points hmk).symm
              rw [hfrpts, haa]
              exact hcc
            exact ⟨x, hx, (congrArg Route.id hmk).symm, (congrArg Route.fromId hmk).symm,
              (congrArg Route.toId hmk).symm, (congrArg Route.orthogonal hmk).symm,
              Or.inr (Or.inl ⟨a, ⟨h1a, h2a⟩, frag, hpfrag, fr, hfrmem, hfrid, hptseq⟩)⟩
      | false =>
        simp only [hab, Bool.false_eq_true] at hstep
        have hbb : res.scene.boxes = boxes' := (congrArg Scene.boxes hscene).symm
        have hfeq : placed'.flatten = e.fragments := by
          rw [← hpeq]
          exact e.fragments_eq.symm
        have hroute_raw := hstep
        rw [← hbb, hfeq] at hroute_raw
        obtain ⟨pts, hroute, hj⟩ := nfr_bind_ok hroute_raw
        have hmk : Route.mk x.id x.fromId x.toId x.orthogonal pts = rt :=
          Except.ok.inj hj
        have hptseq : rt.points = pts := (congrArg Route.points hmk).symm
        have hroute : routeAround inp e.atts (notesFrameOf e.contracted o e.margin)
            (notesRectsOf res.scene.boxes)
            (notesLabelsOf e.fragments e.contracted inp)
            (notesTitlesOf e.fragments e.contracted) x = .ok pts := hroute
        have hnkept : ¬ notesKept inp e.layouts x := by
          intro hcon
          obtain ⟨k1, _⟩ := hcon
          simp only [notesBundleOf] at k1
          rw [k1] at h1
          simp at h1
        have hnsame : ∀ a' : Nat, ¬ notesSameBundleAt inp e.layouts a' x := by
          intro a' hcon
          obtain ⟨s1, s2⟩ := hcon
          simp only [notesBundleOf] at s1 s2
          rw [s1] at h1
          rw [s2] at h2
          have haa : a' = a := Option.some.inj h1
          have hab2 : a' = b := Option.some.inj h2
          have hab3 : a = b := haa.symm.trans hab2
          rw [hab3] at hab
          simp at hab
        exact ⟨x, hx, (congrArg Route.id hmk).symm, (congrArg Route.fromId hmk).symm,
          (congrArg Route.toId hmk).symm, (congrArg Route.orthogonal hmk).symm,
          Or.inr (Or.inr ⟨⟨hnkept, hnsame⟩, pts, hptseq, hroute⟩)⟩

/-! ### Clause C4: orthogonal routes -/

/-- C4 for the note stage: kept routes inherit contracted orthogonality,
fragment routes inherit shifted fragment orthogonality, and cross routes use
the router residual. -/
theorem notes_c4
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hC4b : Validator.C4 e.contracted.scene.layoutDump)
    (hC4f : ∀ p ∈ e.fragments, Validator.C4 p.scene.layoutDump)
    (hfk : notesFlagsKept inp e.layouts e.contracted)
    (hff : notesFlagsFragment inp e.layouts e.fragments)
    (hro : notesRouterOrtho inp e.atts (notesFrameOf e.contracted o e.margin)
      (notesRectsOf res.scene.boxes)
      (notesLabelsOf e.fragments e.contracted inp)
      (notesTitlesOf e.fragments e.contracted)) :
    Validator.C4 res.scene.layoutDump := by
  intro rt hrt
  obtain ⟨x, hx, _, _, _, hort, hcases⟩ :=
    notes_route_cases e hrt
  rcases hcases with ⟨hkept, cr, hcr, hcrid, hpts⟩ | ⟨a, hsame, p, hp, fr, hfrmem, hfrid, hpts⟩ | ⟨_, pts, hpts, hroute⟩
  · intro hortho
    obtain ⟨hortho_eq, _, _⟩ := hfk x hx hkept cr hcr hcrid
    have hflag : cr.orthogonal = true := hortho_eq.trans (hort.symm.trans hortho)
    have horth := hC4b cr hcr hflag
    rw [hpts]
    exact horth
  · intro hortho
    obtain ⟨hortho_eq, _, _⟩ := hff x hx a hsame p hp fr hfrmem hfrid
    have hflag : fr.orthogonal = true := hortho_eq.trans (hort.symm.trans hortho)
    have horth := hC4f p hp fr hfrmem hflag
    rw [hpts, notesShiftPoint_orthogonal]
    exact horth
  · intro _
    rw [hpts]
    exact hro x hx pts hroute

/-! ### Clause C5: route ends on end-box boundaries -/

/-- C5 for the note stage: kept ends use the contracted C5 fact with the
contracted end-box rect, fragment ends use the fragment C5 fact shifted to the
translated end box, and cross ends use the router residual with the
looked-up end boxes. -/
theorem notes_c5
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : notesEndsInBoxes inp)
    (hC5b : Validator.C5 e.contracted.scene.layoutDump)
    (hC5f : ∀ p ∈ e.fragments, Validator.C5 p.scene.layoutDump)
    (hfk : notesFlagsKept inp e.layouts e.contracted)
    (hff : notesFlagsFragment inp e.layouts e.fragments)
    (hkn : ∀ r ∈ inp.routes, notesKept inp e.layouts r →
      notesKeptBoxContracted e.placed r)
    (hfn : ∀ r ∈ inp.routes, ∀ a : Nat, notesSameBundleAt inp e.layouts a r →
      notesFragBoxFirst e.fragments r)
    (hre : notesRouterEnds inp e.atts (notesFrameOf e.contracted o e.margin)
      (notesRectsOf res.scene.boxes)
      (notesLabelsOf e.fragments e.contracted inp)
      (notesTitlesOf e.fragments e.contracted)) :
    Validator.C5 res.scene.layoutDump := by
  intro rt hrt
  obtain ⟨x, hx, _, hfrom, hto, _, hcases⟩ := notes_route_cases e hrt
  obtain ⟨hendf, hendt⟩ := hwf x hx
  obtain ⟨bf, hbfmem, hbfid⟩ := nfr_mem_input_box_of_contains hendf
  obtain ⟨bt, hbtmem, hbtid⟩ := nfr_mem_input_box_of_contains hendt
  obtain ⟨rbf, hrbfmem, hrbfid⟩ := e.boxes_forward bf hbfmem
  obtain ⟨rbt, hrbtmem, hrbtid⟩ := e.boxes_forward bt hbtmem
  have hrbfid : rbf.id = x.fromId := hrbfid.trans hbfid
  have hrbtid : rbt.id = x.toId := hrbtid.trans hbtid
  have hpf : (fun b => b.id == x.fromId) rbf = true := by
    show (rbf.id == x.fromId) = true
    rw [hrbfid]
    exact beq_self_eq_true _
  have hpt : (fun b => b.id == x.toId) rbt = true := by
    show (rbt.id == x.toId) = true
    rw [hrbtid]
    exact beq_self_eq_true _
  obtain ⟨rbf', hboxf⟩ :=
    nfr_find?_some_of_mem (fun b => b.id == x.fromId) hrbfmem hpf
  obtain ⟨rbt', hboxt⟩ :=
    nfr_find?_some_of_mem (fun b => b.id == x.toId) hrbtmem hpt
  have hrbfmem' : rbf' ∈ res.scene.boxes := List.mem_of_find?_eq_some hboxf
  have hrbtmem' : rbt' ∈ res.scene.boxes := List.mem_of_find?_eq_some hboxt
  have hrbfid' : rbf'.id = x.fromId := by
    have hbe := List.find?_some hboxf
    simpa [beq_iff_eq] using hbe
  have hrbtid' : rbt'.id = x.toId := by
    have hbe := List.find?_some hboxt
    simpa [beq_iff_eq] using hbe
  rcases hcases with ⟨hkept, cr, hcr, hcrid, hpts⟩ | ⟨a, hsame, p, hp, fr, hfrmem, hfrid, hpts⟩ | ⟨_, pts, hpts, hroute⟩
  · obtain ⟨hortho_eq, hfrom_eq, hto_eq⟩ := hfk x hx hkept cr hcr hcrid
    obtain ⟨pf, qf, fb, tb, hhead, hlast, hbfb, hbtb, hbp, hbq⟩ := hC5b cr hcr
    rw [hfrom_eq] at hbfb
    rw [hto_eq] at hbtb
    simp only [LayoutDump.box?] at hbfb hbtb
    have hfbid : fb.id = x.fromId := by
      have hbe := List.find?_some hbfb
      simpa [beq_iff_eq] using hbe
    have htbidd : tb.id = x.toId := by
      have hbe := List.find?_some hbtb
      simpa [beq_iff_eq] using hbe
    obtain ⟨bf', hbfmem', hidb', _, _, _, hrect'⟩ := e.boxes_mem rbf' hrbfmem'
    obtain ⟨bt', hbtmem', hidb'', _, _, _, hrect''⟩ := e.boxes_mem rbt' hrbtmem'
    have hbif : bf'.id = x.fromId := hidb'.symm.trans hrbfid'
    have hbit : bt'.id = x.toId := hidb''.symm.trans hrbtid'
    rw [hbif] at hrect'
    rw [hbit] at hrect''
    obtain ⟨cb, hcb, hcbrect⟩ := nfr_outRect_contracted hrect' (hkn x hx hkept).1
    obtain ⟨cb', hcb', hcbrect'⟩ := nfr_outRect_contracted hrect'' (hkn x hx hkept).2
    have hcf : cb = fb := Option.some.inj (hcb.symm.trans hbfb)
    have hct : cb' = tb := Option.some.inj (hcb'.symm.trans hbtb)
    have hrecteq : fb.rect = rbf'.rect :=
      (congrArg Box.rect hcf).symm.trans hcbrect
    have htrecteq : tb.rect = rbt'.rect :=
      (congrArg Box.rect hct).symm.trans hcbrect'
    refine ⟨pf, qf, rbf', rbt', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpts]; exact hhead
    · rw [hpts]; exact hlast
    · rw [hfrom]; simp only [LayoutDump.box?]; exact hboxf
    · rw [hto]; simp only [LayoutDump.box?]; exact hboxt
    · rw [← hrecteq]; exact hbp
    · rw [← htrecteq]; exact hbq
  · obtain ⟨_, hfrom_eq, hto_eq⟩ := hff x hx a hsame p hp fr hfrmem hfrid
    obtain ⟨p0, q0, fb0, tb0, hhead, hlast, hbfb0, hbtb0, hbp0, hbq0⟩ :=
      hC5f p hp fr hfrmem
    rw [hfrom_eq] at hbfb0
    rw [hto_eq] at hbtb0
    simp only [LayoutDump.box?] at hbfb0 hbtb0
    have hfb0id : fb0.id = x.fromId := by
      have hbe := List.find?_some hbfb0
      simpa [beq_iff_eq] using hbe
    have htb0id : tb0.id = x.toId := by
      have hbe := List.find?_some hbtb0
      simpa [beq_iff_eq] using hbe
    have hmem0f : fb0 ∈ p.scene.boxes := List.mem_of_find?_eq_some hbfb0
    have hmem0t : tb0 ∈ p.scene.boxes := List.mem_of_find?_eq_some hbtb0
    obtain ⟨hfindf, hfindt⟩ := hfn x hx a hsame p hp fb0 hmem0f tb0 hmem0t hfb0id htb0id
    have hresf : rbf'.rect = shiftRect p.dx p.dy fb0.rect :=
      e.resBox_of_fragment hp hmem0f hfindf hrbfmem' (hrbfid'.trans hfb0id.symm)
    have hrest : rbt'.rect = shiftRect p.dx p.dy tb0.rect :=
      e.resBox_of_fragment hp hmem0t hfindt hrbtmem' (hrbtid'.trans htb0id.symm)
    refine ⟨shiftPoint p.dx p.dy p0, shiftPoint p.dx p.dy q0, rbf', rbt', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hpts, List.head?_map, hhead, Option.map_some]
    · simp only [hpts, List.getLast?_map, hlast, Option.map_some]
    · rw [hfrom]; simp only [LayoutDump.box?]; exact hboxf
    · rw [hto]; simp only [LayoutDump.box?]; exact hboxt
    · rw [hresf]
      exact (Elegant.Layered.onBoundary_shift p.dx p.dy p0 fb0.rect).mpr hbp0
    · rw [hrest]
      exact (Elegant.Layered.onBoundary_shift p.dx p.dy q0 tb0.rect).mpr hbq0
  · obtain ⟨from_, to_, pf, qf, hlk1, hlk2, hhead, hlast, hbp, hbq⟩ :=
      hre x hx pts hroute
    obtain ⟨rb1, hbox1, hrect1, _⟩ := nfr_first_match hlk1
    obtain ⟨rb2, hbox2, hrect2, _⟩ := nfr_first_match hlk2
    refine ⟨pf, qf, rb1, rb2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpts]; exact hhead
    · rw [hpts]; exact hlast
    · rw [hfrom]; simp only [LayoutDump.box?]; exact hbox1
    · rw [hto]; simp only [LayoutDump.box?]; exact hbox2
    · rw [hrect1]; exact hbp
    · rw [hrect2]; exact hbq

end PipelineImpl
end Layered
end Elegant

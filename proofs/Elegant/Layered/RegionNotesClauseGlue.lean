import Elegant.Layered.RegionNotesFamilyValid
import Elegant.Layered.NotesFoundation
import Elegant.Layered.InsetFit
import Elegant.Layered.RegionPipeline
import Elegant.Layered.AttachPipeline

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Region-and-note clause glue.

`RegionNotesFamilyValid.lean` defines `RegionNotesSeams` and proves
`layoutFamilyRN_valid_of_seams`. Its per-execution clause premises cover
scenes of a note execution: each says a validator clause holds on
`e.contracted.scene` or on a note scene of `e.layouts`, for a
`NotesExecution (rnNotesBase idSets) exactIds fuel inp o res`. Those scenes
are note-wrapped region-base results on sub-inputs (contracted run,
fragment part runs, fragment note runs).

This module derives the eight well-formedness-free per-execution fields
from the region seams instead of assuming them:

- `insetContracted`, `c1Contracted`, `orthoContracted`, `c4Contracted`,
- `insetFragments`, `c1Fragments`, `orthoFragments`, `c4Fragments`,

The region lifts supply those fields. Family C8a is proved separately under
the existing framed and attachment-parent alignment checks.

Executed evidence (`proofs/wip/Probe/RegionNotesClauseGlueT_probe.lean`,
11 `#eval`s, all `Except.ok`): the region-base note wrapper runs on six
inputs (empty boxes `(0, 0)` scenes on a `2048x2048` canvas, single box
`(1, 1)`, self-loop `(1, 1)`, plain pair `(2, 1)`, note-state
`(3, 2, 2, 1)`, note-group `(3, 1, 1)`); contracted and final scenes of
both note inputs satisfy the C1 and orthogonality Bool mirrors
`(true, true, true, true)`; `contractOne` and `subInput` preserve `kind`
(`true`); `reindexRegionSets` filters to `[("S1", ["S2"])]`.

`RegionNotesSeamsCore` keeps the region seams at every id-list extension
because the contracted run uses `exactIds ++ tops`.
`regionNotesSeams_of_core` uses region flats for the inset and orthogonality
towers. Other contracted and fragment clauses below remain separate.
-/

/-- The note-wrapped region base (local copy: `rnNotesBase` is private to
`RegionNotesFamilyValid`, so other modules cannot name it; the bodies are
definitionally equal). -/
abbrev rngNotesBase (idSets : List (String × List String)) :
    List String → Input → Options → Except LayoutError FamilyResult :=
  fun ids sub o => layoutRIds ids (reindexRegionSets idSets sub) sub o

/-- Region-and-note seams core: everything `RegionNotesSeams` needs that
is not derived below. `regionAll` quantifies over id-list extensions
because the contracted run executes at `exactIds ++ tops`. The `resid*`
fields restate the well-formedness-needing per-execution clauses as
explicit residuals, each with its missing lemma. -/
structure RegionNotesSeamsCore (exactIds : List String)
    (idSets : List (String × List String)) : Prop where
  /-- The region seams at every id-list extension. -/
  regionAll : ∀ ext : List String, RegionSeams (exactIds ++ ext) idSets
  /-- Note-stage residuals over every note execution on the region base. -/
  notesFacts : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    NotesFlatFacts e
  /-- OPEN CLAUSE: no finished notes module; the `stepC2` clause itself. -/
  stepC2N : ∀ (outerFuel fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    (∀ m ∈ inp.boxes, m.id ≠ "") →
    ExpandChildCallContextB (layoutNotes (rngNotesBase idSets) exactIds outerFuel)
      fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC2Step P inp o group titleHeight parent child res
  /-- OPEN CLAUSE: no finished notes module; the `stepC6` clause itself. -/
  stepC6N : ∀ (outerFuel fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true →
    ExpandChildCallContextB (layoutNotes (rngNotesBase idSets) exactIds outerFuel)
      fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC6Step P inp o group titleHeight parent child res
  /-- OPEN CLAUSE: no finished notes module; the `stepC7` clause itself. -/
  stepC7N : ∀ (outerFuel fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true → BoxRouteIdsDisjoint inp → InputFixedFit inp o →
    ExpandChildCallContextB (layoutNotes (rngNotesBase idSets) exactIds outerFuel)
      fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC7Step P inp o group titleHeight parent child res
  /-- OPEN CLAUSE: no finished notes module; the `stepC8b` clause itself. -/
  stepC8bN : ∀ (outerFuel fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult),
    expandChild P inp o group titleHeight parent child = .ok res →
    framedParents inp = true → InputFixedFit inp o →
    ExpandChildCallContextB (layoutNotes (rngNotesBase idSets) exactIds outerFuel)
      fuel P inp o group titleLines titleHeight parent child res →
    ExpandChildCallParams P inp o group titleLines titleHeight →
    ExpandChildC8bStep P inp o group titleHeight parent child res
  /-- OPEN CLAUSE (residual): contracted C2. Missing: unconditional
  `WellFormed` of `e.contractedInput` for `flatC2B_layoutRIds`. -/
  residC2Contracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    Validator.C2 e.contracted.scene.layoutDump
  /-- OPEN CLAUSE (residual): fragment C2. Missing: unconditional
  `WellFormed` of part/note sub-inputs, plus joint fuel induction. -/
  residC2Fragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    ∀ l ∈ e.layouts,
      Validator.C2 l.part.scene.layoutDump ∧
        ∀ q ∈ l.notes, Validator.C2 q.2.scene.layoutDump
  /-- OPEN CLAUSE (residual): contracted C3. Missing: unconditional
  `WellFormed` and `framedParents` of `e.contractedInput`. -/
  residC3Contracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    Validator.C3 e.contracted.scene.layoutDump
  /-- OPEN CLAUSE (residual): fragment C3. Missing: unconditional
  `WellFormed`/`framedParents` of part/note sub-inputs, plus induction. -/
  residC3Fragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    ∀ l ∈ e.layouts,
      Validator.C3 l.part.scene.layoutDump ∧
        ∀ q ∈ l.notes, Validator.C3 q.2.scene.layoutDump
  /-- OPEN CLAUSE (residual): contracted C5. Missing: unconditional
  `WellFormed`/`framedParents` of `e.contractedInput` for `FlatC5B`. -/
  residC5Contracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    Validator.C5 e.contracted.scene.layoutDump
  /-- OPEN CLAUSE (residual): fragment C5. Missing: unconditional
  `WellFormed`/`framedParents` of part/note sub-inputs, plus induction. -/
  residC5Fragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    ∀ p ∈ e.fragments, Validator.C5 p.scene.layoutDump
  /-- OPEN CLAUSE (residual): composed group-endpoint invariant. Missing:
  fragment measured-endpoint facts plus composition over the note run. -/
  residGroupEndpoints : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (_ : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    GroupEndpointInvariantMeasured inp res.scene
  /-- OPEN CLAUSE (residual): contracted C6. Missing: unconditional
  `WellFormed` of `e.contractedInput` (region `flatC6` is itself open). -/
  residC6Contracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    Validator.C6 e.contracted.scene.layoutDump
  /-- OPEN CLAUSE (residual): fragment C6. Missing: unconditional
  `WellFormed` of part/note sub-inputs, plus induction. -/
  residC6Fragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    ∀ p ∈ e.fragments, Validator.C6 p.scene.layoutDump
  /-- OPEN CLAUSE (residual): contracted C7. Missing: unconditional
  `WellFormed` of `e.contractedInput` (region `flatC7` is itself open). -/
  residC7Contracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    Validator.C7 e.contracted.scene.layoutDump
  /-- OPEN CLAUSE (residual): fragment C7. Missing: unconditional
  `WellFormed` of part/note sub-inputs, plus induction. -/
  residC7Fragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    ∀ p ∈ e.fragments, Validator.C7 p.scene.layoutDump
  /-- OPEN CLAUSE (residual): contracted C8b. Missing: unconditional
  `WellFormed` of `e.contractedInput`. -/
  residC8bContracted : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    Validator.C8b e.contracted.scene.layoutDump
  /-- OPEN CLAUSE (residual): fragment C8b. Missing: unconditional
  `WellFormed` of part/note sub-inputs, plus induction. -/
  residC8bFragments : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    ∀ p ∈ e.fragments, Validator.C8b p.scene.layoutDump

/-! ### Private plumbing (prefixed copies: other modules' privates do not resolve). -/

private theorem rng_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- Membership in a successful `mapM` gives a successful per-element run,
with the output value identified. -/
private theorem rng_mem_of_mem_mapM {α β : Type} {f : α → Except LayoutError β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ {y : β}, y ∈ ys →
      ∃ x, x ∈ xs ∧ f x = .ok y
  | [], ys, h, _, hy => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp at hy
  | _ :: _, ys, h, _, hy => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    obtain ⟨b, hfb, h⟩ := rng_bind_ok h
    obtain ⟨bs, hbs, hys⟩ := rng_bind_ok h
    have hys' : b :: bs = ys := Except.ok.inj hys
    subst hys'
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hfb⟩
    · obtain ⟨x, hx, hfx⟩ := rng_mem_of_mem_mapM hbs hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- A `contractOne` fold preserves the input kind. -/
private theorem rng_foldl_contractOne_kind (ls : List BundleLayout) (inp : Input) :
    (ls.foldl contractOne inp).kind = inp.kind := by
  induction ls generalizing inp with
  | nil => rfl
  | cons _ _ ih => exact ih _

/-- The region seams at the original ids from the universal form. -/
private theorem rng_regionOrig {exactIds : List String}
    {idSets : List (String × List String)}
    (R : ∀ ext : List String, RegionSeams (exactIds ++ ext) idSets) :
    RegionSeams exactIds idSets := by
  have h := R []
  have h0 : exactIds ++ ([] : List String) = exactIds := by simp
  rwa [h0] at h

/-- Inset containment implies validator C1. -/
private theorem rng_inset_c1 {scene : Scene} {m : Int}
    (h : InsetC1 scene m) (hm : 0 ≤ m) :
    Validator.C1 scene.layoutDump := by
  intro b hb
  have hb' : b ∈ scene.boxes := hb
  exact (insetRect_subset_canvas hm).trans (h b hb')

/-- Every bundle layout comes from a bundle with the matching pipeline run. -/
private theorem rng_layout_of_mem_layouts
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    {l : BundleLayout} (hl : l ∈ e.layouts) :
    ∃ b, b ∈ e.bundles ∧
      bundleLayout (layoutNotes base exactIds fuel) (base exactIds)
        inp o e.margin e.gap b = .ok l :=
  rng_mem_of_mem_mapM e.layouts_eq hl

/-- A member layout splits into its fragment part run and note runs. -/
private theorem rng_part_note_of_mem
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    {l : BundleLayout} (hl : l ∈ e.layouts) :
    ∃ b, b ∈ e.bundles ∧ ∃ top,
      inp.boxes[b.target]? = some top ∧
      layoutNotes base exactIds fuel
        (subInput inp (fun x => x.id == top.id || Compound.inside inp.boxes top.id x.id)
          top.id) o = .ok l.part ∧
      ∀ q ∈ l.notes, ∃ a, a ∈ b.notes ∧ ∃ box,
        inp.boxes[a.note]? = some box ∧
        base exactIds (subInput inp (fun x => x.id == box.id) box.id) o
          = .ok q.2 := by
  obtain ⟨b, hb, hbl⟩ := rng_layout_of_mem_layouts e hl
  unfold bundleLayout at hbl
  cases htb : inp.boxes[b.target]? with
  | none => simp [htb] at hbl
  | some top =>
    simp only [htb] at hbl
    obtain ⟨part, hpart, hbl⟩ := rng_bind_ok hbl
    obtain ⟨notes, hnotes, hleq⟩ := rng_bind_ok hbl
    have hleq' : (⟨top, b, part, notes, _⟩ : BundleLayout) = l :=
      Except.ok.inj hleq
    subst hleq'
    refine ⟨b, hb, top, htb, hpart, ?_⟩
    intro q hq
    obtain ⟨a, ha, hbody⟩ := rng_mem_of_mem_mapM hnotes hq
    cases hnb : inp.boxes[a.note]? with
    | none => simp [hnb] at hbody
    | some box =>
      simp only [hnb] at hbody
      obtain ⟨r, hr, hpr⟩ := rng_bind_ok hbody
      simp only [pure, Except.pure, Except.ok.injEq] at hpr
      subst hpr
      exact ⟨a, ha, box, hnb, hr⟩

/-- A placed fragment scene is a part scene or a note scene. -/
private theorem rng_frag_scene_of_mem
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    {p : Placed} (hp : p ∈ e.fragments) :
    (∃ l, l ∈ e.layouts ∧ p.scene = l.part.scene) ∨
    (∃ l, l ∈ e.layouts ∧ ∃ q, q ∈ l.notes ∧ p.scene = q.2.scene) := by
  rw [e.fragments_eq] at hp
  obtain ⟨pl, hpl, hpm⟩ := List.mem_flatten.mp hp
  obtain ⟨l, hl, hpleq⟩ := rng_mem_of_mem_mapM e.placed_eq hpl
  unfold placedFragments at hpleq
  cases hfind : e.contracted.scene.boxes.find? (fun b => b.id == l.top.id) with
  | none => simp [hfind] at hpleq
  | some env =>
    simp only [hfind, pure, Except.pure, Except.ok.injEq] at hpleq
    subst hpleq
    simp only [List.mem_cons] at hpm
    rcases hpm with rfl | hpm
    · exact Or.inl ⟨l, hl, rfl⟩
    · obtain ⟨qq, hqqmem, hqqeq⟩ := List.mem_map.mp hpm
      obtain ⟨hmem1, _⟩ := List.of_mem_zip hqqmem
      subst hqqeq
      exact Or.inr ⟨l, hl, qq.1, hmem1, rfl⟩
/-- The contracted scene satisfies the inset fact and margin nonnegativity,
from the region flats at the extended ids. -/
private theorem rng_contracted_inset {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (R : ∀ ext : List String, RegionSeams (exactIds ++ ext) idSets)
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res) :
    InsetC1 e.contracted.scene e.margin ∧ 0 ≤ e.margin := by
  have hflat := (regionBaseSeams (R (e.layouts.map (·.top.id)))).flatInset
  obtain ⟨P', hP', hle, hInset⟩ :=
    hflat e.contractedInput o e.contracted e.contracted_eq
  have hkind : e.contractedInput.kind = inp.kind := by
    rw [e.contractedInput_eq]; exact rng_foldl_contractOne_kind _ _
  rw [hkind] at hP'
  have hPm : P' = e.params := Except.ok.inj (hP'.symm.trans e.checked)
  have hmarg : P'.canvasMargin = e.margin := by rw [hPm]; exact e.margin_eq.symm
  rw [hmarg] at hInset hle
  exact ⟨hInset, hle⟩

/-- The contracted scene routes are orthogonal, from the region flats. -/
private theorem rng_contracted_ortho {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (R : ∀ ext : List String, RegionSeams (exactIds ++ ext) idSets)
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res) :
    ∀ cr ∈ e.contracted.scene.routes,
      Polyline.isOrthogonal cr.points = true := by
  have hflat := (regionBaseSeams (R (e.layouts.map (·.top.id)))).flatC4
  exact hflat e.contractedInput o e.contracted e.contracted_eq

/-- Fragment inset facts at one fuel level from the matching flat fact:
parts run the level base, notes run the region base directly. -/
private theorem rng_inset_frags {idSets : List (String × List String)}
    {exactIds : List String}
    (R : ∀ ext : List String, RegionSeams (exactIds ++ ext) idSets)
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (hFlat : FlatInsetB (layoutNotes (rngNotesBase idSets) exactIds fuel))
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res) :
    ∀ l ∈ e.layouts,
      InsetC1 l.part.scene e.margin ∧ ∀ q ∈ l.notes, InsetC1 q.2.scene e.margin := by
  intro l hl
  obtain ⟨b, hb, top, htb, hpart, hnote⟩ := rng_part_note_of_mem e hl
  obtain ⟨P', hP', hle, hInset⟩ := hFlat _ _ _ hpart
  have hkind : (subInput inp
      (fun x => x.id == top.id || Compound.inside inp.boxes top.id x.id)
      top.id).kind = inp.kind := rfl
  rw [hkind] at hP'
  have hPm : P' = e.params := Except.ok.inj (hP'.symm.trans e.checked)
  have hmarg : P'.canvasMargin = e.margin := by rw [hPm]; exact e.margin_eq.symm
  rw [hmarg] at hInset
  refine ⟨hInset, ?_⟩
  intro q hq
  obtain ⟨a, ha, box, hnb, hr⟩ := hnote q hq
  obtain ⟨Q', hQ', hQle, hQInset⟩ :=
    (regionBaseSeams (rng_regionOrig R)).flatInset _ _ _ hr
  have hQkind : (subInput inp (fun x => x.id == box.id) box.id).kind = inp.kind := rfl
  rw [hQkind] at hQ'
  have hQm : Q' = e.params := Except.ok.inj (hQ'.symm.trans e.checked)
  have hQmarg : Q'.canvasMargin = e.margin := by rw [hQm]; exact e.margin_eq.symm
  rw [hQmarg] at hQInset
  exact hQInset
/-- Inset tower: contracted and fragment inset facts at every fuel level.
Parts at level zero run the region base; parts above zero run the lifted
flat fact built from the previous level. -/
private theorem rng_tower_inset {idSets : List (String × List String)}
    {exactIds : List String}
    (R : ∀ ext : List String, RegionSeams (exactIds ++ ext) idSets)
    (F : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
      NotesFlatFacts e) :
    ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    InsetC1 e.contracted.scene e.margin ∧ 0 ≤ e.margin ∧
    (∀ l ∈ e.layouts,
      InsetC1 l.part.scene e.margin ∧
        ∀ q ∈ l.notes, InsetC1 q.2.scene e.margin) := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res e
    have hFlat0 : FlatInsetB (layoutNotes (rngNotesBase idSets) exactIds 0) :=
      (regionBaseSeams (rng_regionOrig R)).flatInset
    exact ⟨(rng_contracted_inset R e).1, (rng_contracted_inset R e).2,
      rng_inset_frags R hFlat0 e⟩
  | succ n ih =>
    intro inp o res e
    have hFlatS : FlatInsetB (layoutNotes (rngNotesBase idSets) exactIds (n + 1)) :=
      notes_flatInsetB exactIds n (F n)
        (regionBaseSeams (rng_regionOrig R)).flatInset
        (fun e' => (ih e').1) (fun e' => (ih e').2.2)
    exact ⟨(rng_contracted_inset R e).1, (rng_contracted_inset R e).2,
      rng_inset_frags R hFlatS e⟩
/-- Placed-fragment orthogonality from layouts-version orthogonality. -/
private theorem rng_ortho_fragments_of {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res)
    (hL : ∀ l ∈ e.layouts,
      (∀ cr ∈ l.part.scene.routes, Polyline.isOrthogonal cr.points = true) ∧
        ∀ q ∈ l.notes, ∀ cr ∈ q.2.scene.routes,
          Polyline.isOrthogonal cr.points = true) :
    ∀ p ∈ e.fragments, ∀ fr ∈ p.scene.routes,
      Polyline.isOrthogonal fr.points = true := by
  intro p hp fr hfr
  rcases rng_frag_scene_of_mem e hp with ⟨l, hl, hps⟩ | ⟨l, hl, q, hq, hps⟩
  · rw [hps] at hfr
    exact (hL l hl).1 fr hfr
  · rw [hps] at hfr
    exact ((hL l hl).2 q hq) fr hfr

/-- Fragment orthogonality at one fuel level from the matching flat fact. -/
private theorem rng_ortho_frags {idSets : List (String × List String)}
    {exactIds : List String}
    (R : ∀ ext : List String, RegionSeams (exactIds ++ ext) idSets)
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (hFlat : FlatC4B (layoutNotes (rngNotesBase idSets) exactIds fuel))
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res) :
    ∀ l ∈ e.layouts,
      (∀ cr ∈ l.part.scene.routes, Polyline.isOrthogonal cr.points = true) ∧
        ∀ q ∈ l.notes, ∀ cr ∈ q.2.scene.routes,
          Polyline.isOrthogonal cr.points = true := by
  intro l hl
  obtain ⟨b, hb, top, htb, hpart, hnote⟩ := rng_part_note_of_mem e hl
  refine ⟨hFlat _ _ _ hpart, ?_⟩
  intro q hq cr hcr
  obtain ⟨a, ha, box, hnb, hr⟩ := hnote q hq
  exact (regionBaseSeams (rng_regionOrig R)).flatC4 _ _ _ hr cr hcr
/-- Orthogonality tower: contracted, layouts, and placed-fragment
orthogonality at every fuel level. -/
private theorem rng_tower_ortho {idSets : List (String × List String)}
    {exactIds : List String}
    (R : ∀ ext : List String, RegionSeams (exactIds ++ ext) idSets) :
    ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (rngNotesBase idSets) exactIds fuel inp o res),
    (∀ cr ∈ e.contracted.scene.routes, Polyline.isOrthogonal cr.points = true) ∧
    (∀ l ∈ e.layouts,
      (∀ cr ∈ l.part.scene.routes, Polyline.isOrthogonal cr.points = true) ∧
        ∀ q ∈ l.notes, ∀ cr ∈ q.2.scene.routes,
          Polyline.isOrthogonal cr.points = true) ∧
    (∀ p ∈ e.fragments, ∀ fr ∈ p.scene.routes,
      Polyline.isOrthogonal fr.points = true) := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res e
    have hFlat0 : FlatC4B (layoutNotes (rngNotesBase idSets) exactIds 0) :=
      (regionBaseSeams (rng_regionOrig R)).flatC4
    have hL := rng_ortho_frags R hFlat0 e
    exact ⟨rng_contracted_ortho R e, hL, rng_ortho_fragments_of e hL⟩
  | succ n ih =>
    intro inp o res e
    have hFlatS : FlatC4B (layoutNotes (rngNotesBase idSets) exactIds (n + 1)) :=
      notes_flatC4B exactIds n
        (regionBaseSeams (rng_regionOrig R)).flatC4
        (fun e' => (ih e').1) (fun e' => (ih e').2.2)
    have hL := rng_ortho_frags R hFlatS e
    exact ⟨rng_contracted_ortho R e, hL, rng_ortho_fragments_of e hL⟩
/-- Assemble region-and-note seams from the core, discharging the inset,
orthogonality, C1, and C4 fields. -/
theorem regionNotesSeams_of_core {exactIds : List String}
    {idSets : List (String × List String)}
    (C : RegionNotesSeamsCore exactIds idSets) :
    RegionNotesSeams exactIds idSets where
  region := rng_regionOrig C.regionAll
  notesFacts := C.notesFacts
  insetContracted := by
    intro fuel inp o res e
    exact (rng_tower_inset C.regionAll C.notesFacts fuel e).1
  insetFragments := by
    intro fuel inp o res e
    exact (rng_tower_inset C.regionAll C.notesFacts fuel e).2.2
  c3Contracted := C.residC3Contracted
  c3Fragments := C.residC3Fragments
  c2Contracted := C.residC2Contracted
  c2Fragments := C.residC2Fragments
  orthoContracted := by
    intro fuel inp o res e
    exact (rng_tower_ortho C.regionAll fuel e).1
  orthoFragments := by
    intro fuel inp o res e
    exact (rng_tower_ortho C.regionAll fuel e).2.2
  groupEndpoints := C.residGroupEndpoints
  c6Contracted := C.residC6Contracted
  c6Fragments := C.residC6Fragments
  c7Contracted := C.residC7Contracted
  c7Fragments := C.residC7Fragments
  c8bContracted := C.residC8bContracted
  c8bFragments := C.residC8bFragments
  c1Contracted := by
    intro fuel inp o res e
    exact rng_inset_c1 (rng_tower_inset C.regionAll C.notesFacts fuel e).1
      (rng_tower_inset C.regionAll C.notesFacts fuel e).2.1
  c1Fragments := by
    intro fuel inp o res e l hl
    exact ⟨rng_inset_c1 ((rng_tower_inset C.regionAll C.notesFacts fuel e).2.2 l hl).1
      (rng_tower_inset C.regionAll C.notesFacts fuel e).2.1,
      fun q hq => rng_inset_c1
        (((rng_tower_inset C.regionAll C.notesFacts fuel e).2.2 l hl).2 q hq)
        (rng_tower_inset C.regionAll C.notesFacts fuel e).2.1⟩
  c4Contracted := by
    intro fuel inp o res e rt hrt _
    exact (rng_tower_ortho C.regionAll fuel e).1 rt hrt
  c4Fragments := by
    intro fuel inp o res e p hp fr hfr _
    exact (rng_tower_ortho C.regionAll fuel e).2.2 p hp fr hfr
  c5Contracted := C.residC5Contracted
  c5Fragments := C.residC5Fragments
  stepC2N := C.stepC2N
  stepC6N := C.stepC6N
  stepC7N := C.stepC7N
  stepC8bN := C.stepC8bN

/-- Region-and-note family validity from the core: the executed
`layoutFamilyRN` run satisfies the hard constraints. -/
theorem layoutFamilyRN_valid_of_core {exactIds : List String}
    {sets : List ModelRegionSet} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (C : RegionNotesSeamsCore exactIds idSets)
    (hgraph : RegionImpl.graphRegions inp sets = .ok idSets)
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "")
    (hfix : InputFixedFit inp o) (hpos : FixedSizesPositive inp)
    (hdisj : BoxRouteIdsDisjoint inp)
    (h : Elegant.Layered.layoutFamilyRN exactIds sets inp o = .ok res) :
    HardConstraints res.scene.layoutDump :=
  layoutFamilyRN_valid_of_seams (regionNotesSeams_of_core C) hgraph hids hfix hpos hdisj h

end PipelineImpl

end Layered
end Elegant

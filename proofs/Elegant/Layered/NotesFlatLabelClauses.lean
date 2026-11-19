import Elegant.Layered.NotesFoundation
import Elegant.Layered.ComposeNotesC8a
import Elegant.Layered.RouteTransport
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Remaining note-stage clauses: C6, C7, C8a, C8b.

`layoutNotes` (`AttachPipeline.lean:256-280`) composes the contracted scene with
placed bundle fragments. The box clauses (`NotesFlatBoxClauses`: C1/C2/C3) and the
route-end clauses (`NotesFlatRouteClauses`: C4/C5) live in sibling modules. This
module states and proves the remaining clauses over the same `NotesExecution`
record from `NotesFoundation`:

* `notes_c8b`: group frames stay clear of labels (or strictly contain them);
* `notes_c8a`: group frames stay clear of foreign boxes;
* `notes_c6`: routes stay clear of unrelated exclusive boxes;
* `notes_c7`: labels stay clear of unrelated exclusive boxes.

Each clause takes the matching contracted-scene and fragment-scene facts (the
tower induction hypotheses) plus one named geometric residual about fragments,
the contracted scene, and the input. No premise mentions `res` validity.
-/

/-! ### Private shift helpers (prefixed copies; siblings stay private) -/

/-- Shifting preserves open-interior overlap (prefixed copy). -/
private theorem nlc_meetsInterior_shift (a b : Rect) (dx dy : Int) :
    (shiftRect dx dy a).meetsInterior (shiftRect dx dy b) ↔ a.meetsInterior b := by
  simp only [Rect.meetsInterior, shiftRect]
  constructor <;> intro h <;> omega

/-- Shifting preserves strict containment (prefixed copy). -/
private theorem nlc_strictInside_shift (o i : Rect) (dx dy : Int) :
    (shiftRect dx dy o).StrictInside (shiftRect dx dy i) ↔ o.StrictInside i := by
  simp only [Rect.StrictInside, shiftRect]
  constructor <;> intro h <;> omega

/-- Equal images under `·.id` of two members of an id-duplicate-free model-box
list force the members to be equal (prefixed copy). -/
private theorem nlc_nodup_id_inj :
    ∀ (l : List ModelBox), (l.map (·.id)).Nodup →
      ∀ {a b : ModelBox}, a ∈ l → b ∈ l → a.id = b.id → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | _ :: _, h, _, _, ha, hb, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with hax | ha'
    · rcases List.mem_cons.mp hb with hbx | hb'

      · exact hax.trans hbx.symm
      · exfalso
        apply h.1
        rw [← hax, e]
        exact List.mem_map_of_mem hb'
    · rcases List.mem_cons.mp hb with hbx | hb'
      · exfalso
        apply h.1
        rw [← hbx, ← e]
        exact List.mem_map_of_mem ha'
      · exact nlc_nodup_id_inj _ h.2 ha' hb' e
/-! ### Clause C8b: group frames against labels -/

/-- First-fragment-wins for every fragment box id (prefixed copy of the sibling
residual: the composed lookup resolves to the placed scene holding the box). -/
def NotesC8bFirst {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ p ∈ e.fragments, ∀ sb ∈ p.scene.boxes,
    e.fragments.findSome? (fun q => q.rect sb.id) =
      some (shiftRect p.dx p.dy sb.rect)

/-- Every placed fragment box mirrors an input box by id, keeping its role. This
transports fragment C8b (which quantifies over fragment group roles) to input roles. -/
def NotesC8bFragRole {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l, ∀ sb ∈ p.scene.boxes,
    ∃ ib ∈ inp.boxes, sb.id = ib.id ∧ sb.role = ib.role.id

/-- An unclaimed contracted box mirrors its input box's role. With first-match,
an unclaimed id cannot be a bundle top (those resolve to fragments), so the
contracted role is the input role. -/
def NotesC8bContractRole {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ cb ∈ e.contracted.scene.boxes, ∀ ib ∈ inp.boxes,
    cb.id = ib.id →
    (∀ p ∈ e.fragments, ∀ r : Rect, p.rect ib.id ≠ some r) →
    cb.role = ib.role.id

/-- Shifted fragment group boxes clear contracted labels. -/
def NotesC8bMixedGL {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    ∀ sg ∈ p.scene.boxes, sg.role = "group" →
      ∀ cl ∈ e.contracted.scene.labels,
        Disjoint (shiftRect p.dx p.dy sg.rect) cl.rect

/-- Contracted group boxes clear shifted fragment labels. -/
def NotesC8bMixedLG {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    ∀ fl ∈ p.scene.labels, ∀ cg ∈ e.contracted.scene.boxes, cg.role = "group" →
      Disjoint cg.rect (shiftRect p.dx p.dy fl.rect)

/-- Group boxes and labels of distinct placed fragments are pairwise disjoint. -/
def NotesC8bCross {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ p ∈ e.fragments, ∀ q ∈ e.fragments, p ≠ q →
    ∀ sg ∈ p.scene.boxes, sg.role = "group" →
      ∀ fl ∈ q.scene.labels,
        Disjoint (shiftRect p.dx p.dy sg.rect) (shiftRect q.dx q.dy fl.rect)

/-- The geometric context for C8b: first-match, both role mirrors, and the
mixed/cross separations. Each conjunct is fragment/contracted/input geometry,
never a claim about `res`. -/
def NotesC8bGeom {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  NotesC8bFirst e ∧ NotesC8bFragRole e ∧ NotesC8bContractRole e ∧
    NotesC8bMixedGL e ∧ NotesC8bMixedLG e ∧ NotesC8bCross e


/-- Parent-projection rects agree: a scene label viewed as a dump label keeps its rect. -/
private theorem nlc_toLabel_rect (sl : SceneLabel) : sl.toLabel.rect = sl.rect := rfl

/-- C8b for the note stage: group frames stay clear of labels. Same-source pairs
transport the fragment or contracted C8b through the shift; mixed and cross pairs
are the residual separations. -/
theorem notes_c8b {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hBase : Validator.C8b e.contracted.scene.layoutDump)
    (hFrag : ∀ p ∈ e.fragments, Validator.C8b p.scene.layoutDump)
    (hGeom : NotesC8bGeom e) :
    Validator.C8b res.scene.layoutDump := by
  obtain ⟨_, hFragRole, hContractRole, hMixedGL, hMixedLG, hCross⟩ := hGeom
  have hnd : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  intro g hg hgr l hl
  obtain ⟨sl, hslmem, hslid⟩ := List.mem_map.mp hl
  obtain ⟨bi, hbim, _, hroleb, _, _, hrect⟩ := e.boxes_mem g hg
  obtain ⟨m, _, _, hlab⟩ := e.labels_mem sl hslmem
  have hgrbi : bi.role.id = "group" := by rw [← hroleb]; exact hgr
  have hlid : sl.toLabel = l := hslid
  rcases classifyRect hrect with ⟨p, hpf, hpR⟩ | ⟨hno, cg, hcgmem, hcgid, hcgr⟩
  · obtain ⟨sg, hsgmem, hsgid, hshift⟩ := Placed.rect_scene_box hpR
    have hgrect : g.rect = shiftRect p.dx p.dy sg.rect := hshift.symm
    have hpfF : p ∈ e.fragments := by rw [e.fragments_eq]; exact hpf
    obtain ⟨li, hlim, hpim⟩ := placedFlatten_mem e.placed_eq hpf
    obtain ⟨fib, hfibmem, hfibid, hfibrole⟩ := hFragRole li hlim p hpim sg hsgmem
    have hfibeq : fib = bi := nlc_nodup_id_inj inp.boxes hnd hfibmem hbim (hfibid.symm.trans hsgid)
    have hsgrole : sg.role = "group" := by rw [hfibrole, hfibeq]; exact hgrbi
    rcases hlab with ⟨q, hqf, fl, hflmem, _, hshiftl⟩ | hcl
    · have hlrect : l.rect = shiftRect q.dx q.dy fl.rect := by rw [← hlid, hshiftl]
      rcases Classical.em (p = q) with rfl | hne
      · have hflmem' : fl.toLabel ∈ p.scene.layoutDump.labels :=
          List.mem_map.mpr ⟨fl, hflmem, rfl⟩
        rcases hFrag p hpfF sg hsgmem hsgrole fl.toLabel hflmem' with hd | hs
        · exact Or.inl (by rw [hgrect, hlrect]; exact (notesShiftRect_disjoint _ _ _ _).mpr hd)
        · exact Or.inr (by rw [hgrect, hlrect]; exact (nlc_strictInside_shift _ _ _ _).mpr hs)
      · have hdisj := hCross p hpfF q hqf hne sg hsgmem hsgrole fl hflmem
        exact Or.inl (by rw [hgrect, hlrect]; exact hdisj)
    · have hdisj := hMixedGL li hlim p hpim sg hsgmem hsgrole sl hcl
      exact Or.inl (by rw [hgrect, ← hlid]; exact hdisj)
  · have hnoF : ∀ p ∈ e.fragments, ∀ r : Rect, p.rect bi.id ≠ some r := by
      intro p hpm r
      exact hno p (by rw [← e.fragments_eq]; exact hpm) r
    have hcbrole : cg.role = "group" := by
      have h := hContractRole cg hcgmem bi hbim hcgid hnoF
      rw [h]; exact hgrbi
    rcases hlab with ⟨q, hqf, fl, hflmem, _, hshiftl⟩ | hcl
    · obtain ⟨lj, hljm, hqjm⟩ :=
        placedFlatten_mem e.placed_eq (by rw [← e.fragments_eq]; exact hqf)
      have hlrect : l.rect = shiftRect q.dx q.dy fl.rect := by rw [← hlid, hshiftl]
      have hdisj := hMixedLG lj hljm q hqjm fl hflmem cg hcgmem hcbrole
      exact Or.inl (by rw [← hcgr, hlrect]; exact hdisj)
    · have hclmem' : sl.toLabel ∈ e.contracted.scene.layoutDump.labels :=
        List.mem_map.mpr ⟨sl, hcl, rfl⟩
      rcases hBase cg hcgmem hcbrole sl.toLabel hclmem' with hd | hs
      · exact Or.inl (by rw [← hcgr, ← hlid]; exact hd)
      · exact Or.inr (by rw [← hcgr, ← hlid]; exact hs)

/-! ### Clause C8a: group frames against boxes -/

/-- Bundle tops are unique. `bundlesOf` appends a target only once. -/
def NotesC8aTopNodup {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  (e.layouts.map (·.top.id)).Nodup

/-- Input parents transfer through the contracted-input fold. -/
def NotesC8aFold {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  IdParentTransferM inp.boxes
    ((e.layouts.foldl contractOne inp).boxes.map
      (fun b => Box.mk b.id b.role.id ⟨0, 0, 0, 0⟩ b.parent b.exclusive))

/-- The contracted scene is no longer than the input. -/
def NotesC8aLen {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  e.contracted.scene.boxes.length ≤ inp.boxes.length

/-- Contracted boxes mirror the contracted-input parents. -/
def NotesC8aContractScene {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  IdParentTransferM ((e.layouts.foldl contractOne inp).boxes) e.contracted.scene.boxes

/-- Every contracted box has an input box with its id and role. -/
def NotesC8aContractRole {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ cg ∈ e.contracted.scene.boxes,
    ∃ ib, inp.boxes.find? (fun b => b.id == cg.id) = some ib ∧ ib.role.id = cg.role

/-- Every placed fragment box has an input box with its id and role. -/
def NotesC8aFragRole {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    ∀ sb ∈ p.scene.boxes, ∃ ib ∈ inp.boxes, ib.id = sb.id ∧ ib.role.id = sb.role

/-- Every bundle id is found in its layout's placed scenes. -/
def NotesC8aFragFound {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ id : String, fragmentIdOf inp l id = true →
    (placedOf' e.margin e.contracted.scene l).any
      (fun p => p.scene.boxes.any (fun b => b.id == id)) = true

/-- Shifted fragment boxes clear contracted boxes no bundle owns. -/
def NotesC8aClear {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    ∀ sb ∈ p.scene.boxes, ∀ cb ∈ e.contracted.scene.boxes,
      fragmentIdOf inp l cb.id = false →
      Disjoint (shiftRect p.dx p.dy sb.rect) cb.rect

/-- Shifted boxes of distinct placed scenes of one bundle are pairwise disjoint. -/
def NotesC8aFragDisj {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    ∀ p' ∈ placedOf' e.margin e.contracted.scene l, ∀ sg ∈ p.scene.boxes, ∀ sb ∈ p'.scene.boxes,
      p ≠ p' → sg.id ≠ sb.id →
      Disjoint (shiftRect p.dx p.dy sg.rect) (shiftRect p'.dx p'.dy sb.rect)

/-- Fragment ancestors are input ancestors. -/
def NotesC8aSceneAnc {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l, ∀ s x : String,
    x ∈ p.scene.layoutDump.ancestors s → x ∈ (inpDumpOf inp).ancestors s

/-- Every shifted fragment box lies in its bundle envelope. -/
def NotesC8aEnv {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    ∀ sb ∈ p.scene.boxes, (envRect e.contracted.scene l).Contained (shiftRect p.dx p.dy sb.rect)

/-- Envelopes of distinct bundles are pairwise disjoint. -/
def NotesC8aEnvDisj {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ a ∈ e.layouts, ∀ b ∈ e.layouts, a.top.id ≠ b.top.id →
    Disjoint (envRect e.contracted.scene a) (envRect e.contracted.scene b)

/-- The geometric context for C8a: exactly the `composeNotes_c8a` side
conditions, bundled as one named fact. Each conjunct is fragment/contracted/input
geometry, never a claim about `res`. -/
def NotesC8aGeom {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  NotesC8aTopNodup e ∧ NotesC8aFold e ∧ NotesC8aLen e ∧ NotesC8aContractScene e ∧
    NotesC8aContractRole e ∧ NotesC8aFragRole e ∧ NotesC8aFragFound e ∧
    NotesC8aClear e ∧ NotesC8aFragDisj e ∧ NotesC8aSceneAnc e ∧
    NotesC8aEnv e ∧ NotesC8aEnvDisj e

/-- C8a for the note stage: group frames stay clear of foreign boxes. This is
the `composeNotes_c8a` composition theorem instantiated on the executed bundle
phases; the geometric side conditions are the single `NotesC8aGeom` residual. -/
theorem notes_c8a {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hBase : Validator.C8a e.contracted.scene.layoutDump)
    (hFragP : ∀ l ∈ e.layouts, Validator.C8a l.part.scene.layoutDump)
    (hFragN : ∀ l ∈ e.layouts, ∀ q ∈ l.notes, Validator.C8a q.2.scene.layoutDump)
    (hGeom : NotesC8aGeom e) :
    Validator.C8a res.scene.layoutDump := by
  obtain ⟨htop, hfold, hlen, hcs, hcr, hfr, hff, hclr, hfd, hsa, henv, henvd⟩ := hGeom
  exact composeNotes_c8a e.scene_eq (Model.boxIds_nodup hwf) htop hBase hfold hlen hcs
    hcr hfr hff hclr hfd hsa hFragP hFragN henv henvd

/-! ### Clause C6: routes clear of unrelated boxes -/

/-- Route classification for the note stage (prefixed copies of the sibling
machinery: this module does not import the sibling file). -/

private theorem nlc_bind_ok {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β}
    {b : β} (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem nlc_mapM_mem {α β : Type} (f : α → Except LayoutError β) :
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
    obtain ⟨b, hfb, h⟩ := nlc_bind_ok h
    obtain ⟨bs, hbs, h⟩ := nlc_bind_ok h
    have hys : b :: bs = ys := Except.ok.inj h
    subst hys
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨a, List.mem_cons_self, hfb⟩
    · obtain ⟨x, hx, hfx⟩ := ih bs hbs y hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

private theorem nlc_findSome?_exists {α β : Type} (f : α → Option β) :
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

private theorem nlc_getD_flatten_mem {α : Type} (l : List (List α)) (a : Nat) {x : α}
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

/-- The bundle owning `id`: the first layout whose top or inside-set claims it. -/
abbrev nlcBundleOf (inp : Input) (layouts : List BundleLayout) (id : String) : Option Nat :=
  layouts.findIdx? fun l => l.top.id == id || Compound.inside inp.boxes l.top.id id

/-- Class (a): neither route end is in a bundle. -/
def nlcKept (inp : Input) (layouts : List BundleLayout) (r : ModelRoute) : Prop :=
  nlcBundleOf inp layouts r.fromId = none ∧ nlcBundleOf inp layouts r.toId = none

/-- Class (b): both route ends are in the same bundle `a`. -/
def nlcSameBundleAt (inp : Input) (layouts : List BundleLayout) (a : Nat)
    (r : ModelRoute) : Prop :=
  nlcBundleOf inp layouts r.fromId = some a ∧ nlcBundleOf inp layouts r.toId = some a

/-- Class (c): every other bundle shape (cross-bundle). -/
def nlcCross (inp : Input) (layouts : List BundleLayout) (r : ModelRoute) : Prop :=
  ¬ nlcKept inp layouts r ∧ ∀ a : Nat, ¬ nlcSameBundleAt inp layouts a r

/-- The `height` local of `composeNotes`. -/
def nlcFrameHeight (contracted : FamilyResult) (o : Options) (margin : Int) : Int :=
  match o.direction with
  | .TB | .BT => contracted.scene.canvas.h - 2 * margin
  | .LR | .RL => contracted.scene.canvas.w - 2 * margin

/-- The `frame` local of `composeNotes`. -/
def nlcFrameOf (contracted : FamilyResult) (o : Options) (margin : Int) : Frame :=
  ⟨o.direction, nlcFrameHeight contracted o margin, margin⟩

/-- The `rects` local of `composeNotes`, stated on the composed boxes. -/
def nlcRectsOf (boxes : List Box) : List (String × Rect) :=
  boxes.map fun b => (b.id, b.rect)

/-- The `labels` local of `composeNotes`, stated on placed fragments. -/
def nlcLabelsOf (fragments : List Placed) (contracted : FamilyResult)
    (inp : Input) : List SceneLabel :=
  inp.labels.filterMap fun l =>
    match fragments.findSome? (·.label l.id) with
    | some label => some label
    | none => contracted.scene.labels.find? (·.id == l.id)

/-- The `titles` local of `composeNotes`. -/
def nlcTitlesOf (fragments : List Placed) (contracted : FamilyResult) :
    List (String × Rect) :=
  fragments.flatMap (·.titles) ++ groupTitles contracted.scene.items

/-- Every composed route falls in class (a), (b), or (c), with the matching
points equation. Kept points equal the contracted route's points; fragment
points equal the shifted fragment route's points; cross points are the
`routeAround` output. (Prefixed copy of the sibling classification.) -/
private theorem nlc_route_cases
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    {rt : Route} (hrt : rt ∈ res.scene.routes) :
    ∃ r ∈ inp.routes, rt.id = r.id ∧ rt.fromId = r.fromId ∧ rt.toId = r.toId ∧
      rt.orthogonal = r.orthogonal ∧
      ((nlcKept inp e.layouts r ∧
        ∃ cr ∈ e.contracted.scene.routes, cr.id = r.id ∧ rt.points = cr.points) ∨
       (∃ a : Nat, nlcSameBundleAt inp e.layouts a r ∧
        ∃ p ∈ e.fragments, ∃ fr ∈ p.scene.routes,
          fr.id = r.id ∧ rt.points = fr.points.map (shiftPoint p.dx p.dy)) ∨
       (nlcCross inp e.layouts r ∧
        ∃ pts : List Point, rt.points = pts ∧
          routeAround inp e.atts (nlcFrameOf e.contracted o e.margin)
            (nlcRectsOf res.scene.boxes)
            (nlcLabelsOf e.fragments e.contracted inp)
            (nlcTitlesOf e.fragments e.contracted) r = .ok pts)) := by
  have h := e.scene_eq
  unfold composeNotes at h
  obtain ⟨placed', hplaced, h⟩ := nlc_bind_ok h
  obtain ⟨boxes', hboxes, h⟩ := nlc_bind_ok h
  obtain ⟨routes', hroutes, h⟩ := nlc_bind_ok h
  have hscene := Except.ok.inj h
  have hrr : res.scene.routes = routes' := (congrArg Scene.routes hscene).symm
  have hpeq : e.placed = placed' := e.placed_is hplaced
  rw [hrr] at hrt
  obtain ⟨x, hx, hstep⟩ := nlc_mapM_mem _ _ _ hroutes rt hrt
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
        obtain ⟨pts, hptsok, hj⟩ := nlc_bind_ok hstep
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
      obtain ⟨pts, hroute, hj⟩ := nlc_bind_ok hroute_raw
      have hmk : Route.mk x.id x.fromId x.toId x.orthogonal pts = rt :=
        Except.ok.inj hj
      have hptseq : rt.points = pts := (congrArg Route.points hmk).symm
      have hroute : routeAround inp e.atts (nlcFrameOf e.contracted o e.margin)
          (nlcRectsOf res.scene.boxes)
          (nlcLabelsOf e.fragments e.contracted inp)
          (nlcTitlesOf e.fragments e.contracted) x = .ok pts := hroute
      have hnkept : ¬ nlcKept inp e.layouts x := by
        intro hcon
        obtain ⟨_, k2⟩ := hcon
        simp only [nlcBundleOf] at k2
        rw [k2] at h2
        simp at h2
      have hnsame : ∀ a : Nat, ¬ nlcSameBundleAt inp e.layouts a x := by
        intro a hcon
        obtain ⟨s1, _⟩ := hcon
        simp only [nlcBundleOf] at s1
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
      obtain ⟨pts, hroute, hj⟩ := nlc_bind_ok hroute_raw
      have hmk : Route.mk x.id x.fromId x.toId x.orthogonal pts = rt :=
        Except.ok.inj hj
      have hptseq : rt.points = pts := (congrArg Route.points hmk).symm
      have hroute : routeAround inp e.atts (nlcFrameOf e.contracted o e.margin)
          (nlcRectsOf res.scene.boxes)
          (nlcLabelsOf e.fragments e.contracted inp)
          (nlcTitlesOf e.fragments e.contracted) x = .ok pts := hroute
      have hnkept : ¬ nlcKept inp e.layouts x := by
        intro hcon
        obtain ⟨k1, _⟩ := hcon
        simp only [nlcBundleOf] at k1
        rw [k1] at h1
        simp at h1
      have hnsame : ∀ a : Nat, ¬ nlcSameBundleAt inp e.layouts a x := by
        intro a' hcon
        obtain ⟨_, s2⟩ := hcon
        simp only [nlcBundleOf] at s2
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
          obtain ⟨a0, ha0, hj⟩ := nlc_bind_ok hstep
          have haa : pts = a0 := Except.ok.inj ha0
          have hmk : Route.mk x.id x.fromId x.toId x.orthogonal a0 = rt :=
            Except.ok.inj hj
          have hba : a = b := beq_iff_eq.mp hab
          have h1a : nlcBundleOf inp e.layouts x.fromId = some a := h1
          have h2a : nlcBundleOf inp e.layouts x.toId = some a := by
            rw [← hba] at h2
            exact h2
          obtain ⟨frag, hfragmem, hfrageq⟩ := nlc_findSome?_exists _ _ _ hf
          have hpfrag : frag ∈ e.fragments := by
            have hflat := nlc_getD_flatten_mem e.placed a hfragmem
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
        obtain ⟨pts, hroute, hj⟩ := nlc_bind_ok hroute_raw
        have hmk : Route.mk x.id x.fromId x.toId x.orthogonal pts = rt :=
          Except.ok.inj hj
        have hptseq : rt.points = pts := (congrArg Route.points hmk).symm
        have hroute : routeAround inp e.atts (nlcFrameOf e.contracted o e.margin)
            (nlcRectsOf res.scene.boxes)
            (nlcLabelsOf e.fragments e.contracted inp)
          (nlcTitlesOf e.fragments e.contracted) x = .ok pts := hroute
        have hnkept : ¬ nlcKept inp e.layouts x := by
          intro hcon
          obtain ⟨k1, _⟩ := hcon
          simp only [nlcBundleOf] at k1
          rw [k1] at h1
          simp at h1
        have hnsame : ∀ a' : Nat, ¬ nlcSameBundleAt inp e.layouts a' x := by
          intro a' hcon
          obtain ⟨s1, s2⟩ := hcon
          simp only [nlcBundleOf] at s1 s2
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

/-- Input-level route scope: the composed scope rewritten through
`composeNotes_ancestors_eq`, so residuals never mention `res`. -/
def nlcScopeOut (inp : Input) (r : ModelRoute) (ib : ModelBox) : Prop :=
  ib.id ∉ ([r.fromId, r.toId] ++ (inpDumpOf inp).ancestors r.fromId ++
    (inpDumpOf inp).ancestors r.toId)

/-- Contracted ancestors are input ancestors. -/
def NotesC6AncC {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ s x : String, x ∈ e.contracted.scene.layoutDump.ancestors s →
    x ∈ (inpDumpOf inp).ancestors s

/-- Fragment ancestors are input ancestors. -/
def NotesC6AncF {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ p ∈ e.fragments, ∀ s x : String, x ∈ p.scene.layoutDump.ancestors s →
    x ∈ (inpDumpOf inp).ancestors s

/-- Flag bridge (kept): the contracted scene keeps id and endpoints of each
kept input route. -/
def NotesC6FlagsKept {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ r : ModelRoute, nlcKept inp e.layouts r →
    ∀ cr ∈ e.contracted.scene.routes, cr.id = r.id →
      cr.orthogonal = r.orthogonal ∧ cr.fromId = r.fromId ∧ cr.toId = r.toId

/-- Flag bridge (fragment): each fragment scene keeps id and endpoints of each
same-bundle input route. -/
def NotesC6FlagsFrag {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ r : ModelRoute, ∀ a : Nat, nlcSameBundleAt inp e.layouts a r →
    ∀ p ∈ e.fragments, ∀ fr ∈ p.scene.routes, fr.id = r.id →
      fr.orthogonal = r.orthogonal ∧ fr.fromId = r.fromId ∧ fr.toId = r.toId

/-- Unclaimed contracted boxes mirror input exclusivity. -/
def NotesC6BoxExclC {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ cb ∈ e.contracted.scene.boxes, ∀ ib ∈ inp.boxes,
    cb.id = ib.id →
    (∀ p ∈ e.placed.flatten, ∀ r : Rect, p.rect ib.id ≠ some r) →
    cb.exclusive = ib.exclusive

/-- Placed fragment boxes mirror input exclusivity. -/
def NotesC6BoxExclF {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l, ∀ sb ∈ p.scene.boxes,
    ∀ ib ∈ inp.boxes, sb.id = ib.id → sb.exclusive = ib.exclusive

/-- Kept routes miss shifted fragment boxes outside the input scope. -/
def NotesC6KeptFrag {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ r ∈ inp.routes, nlcKept inp e.layouts r →
    ∀ cr ∈ e.contracted.scene.routes, cr.id = r.id →
      ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
        ∀ sb ∈ p.scene.boxes, ∀ ib ∈ inp.boxes, sb.id = ib.id →
          ib.exclusive = true → nlcScopeOut inp r ib →
          ¬ Polyline.hitsRect cr.points (shiftRect p.dx p.dy sb.rect)

/-- Fragment routes miss unclaimed contracted boxes outside the input scope. -/
def NotesC6FragContracted {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ (a : Nat) (r : ModelRoute), r ∈ inp.routes → nlcSameBundleAt inp e.layouts a r →
    ∀ p ∈ e.fragments, ∀ fr ∈ p.scene.routes, fr.id = r.id →
      ∀ cb ∈ e.contracted.scene.boxes, ∀ ib ∈ inp.boxes, cb.id = ib.id →
        (∀ q ∈ e.fragments, ∀ t : Rect, q.rect ib.id ≠ some t) →
        ib.exclusive = true → nlcScopeOut inp r ib →
        ¬ Polyline.hitsRect (fr.points.map (shiftPoint p.dx p.dy)) cb.rect

/-- Fragment routes miss shifted boxes of other placed fragments outside the
input scope. -/
def NotesC6FragOther {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ (a : Nat) (r : ModelRoute), r ∈ inp.routes → nlcSameBundleAt inp e.layouts a r →
    ∀ p ∈ e.fragments, ∀ fr ∈ p.scene.routes, fr.id = r.id →
      ∀ q ∈ e.fragments, q ≠ p → ∀ sb ∈ q.scene.boxes, ∀ ib ∈ inp.boxes,
        sb.id = ib.id → ib.exclusive = true → nlcScopeOut inp r ib →
        ¬ Polyline.hitsRect (fr.points.map (shiftPoint p.dx p.dy))
          (shiftRect q.dx q.dy sb.rect)

/-- Router output misses every composed box outside the input scope. -/
def NotesC6RouterClear {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ r ∈ inp.routes, nlcCross inp e.layouts r →
    ∀ pts : List Point,
      routeAround inp e.atts (nlcFrameOf e.contracted o e.margin)
        (nlcRectsOf res.scene.boxes)
        (nlcLabelsOf e.fragments e.contracted inp)
        (nlcTitlesOf e.fragments e.contracted) r = .ok pts →
      ∀ ib ∈ inp.boxes, ib.exclusive = true → nlcScopeOut inp r ib →
        ∀ b ∈ res.scene.boxes, b.id = ib.id →
          ¬ Polyline.hitsRect pts b.rect

/-- The geometric context for C6: ancestor subsumption, flag and exclusivity
mirrors, and the mixed/router clearances. Each conjunct is
fragment/contracted/input geometry (the router clause reads the executed
`res` boxes only as obstacle data), never a claim about `res` validity. -/
def NotesC6Geom {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  NotesC6AncC e ∧ NotesC6AncF e ∧ NotesC6FlagsKept e ∧ NotesC6FlagsFrag e ∧
    NotesC6BoxExclC e ∧ NotesC6BoxExclF e ∧ NotesC6KeptFrag e ∧
    NotesC6FragContracted e ∧ NotesC6FragOther e ∧ NotesC6RouterClear e

/-- Composed route scope is input scope: ancestor walks agree by
`composeNotes_ancestors_eq` and the end boxes agree by id. -/
private theorem nlc_scope_of_res {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    {r : ModelRoute} {ib : ModelBox} {rt : Route} {b : Box}
    (hfrom : rt.fromId = r.fromId) (hto : rt.toId = r.toId) (hidb : b.id = ib.id)
    (hscope : b.id ∉ res.scene.layoutDump.routeScope rt) :
    nlcScopeOut inp r ib := by
  have hanc1 : res.scene.layoutDump.ancestors rt.fromId =
      (inpDumpOf inp).ancestors r.fromId := by
    rw [hfrom]; exact composeNotes_ancestors_eq e.scene_eq r.fromId
  have hanc2 : res.scene.layoutDump.ancestors rt.toId =
      (inpDumpOf inp).ancestors r.toId := by
    rw [hto]; exact composeNotes_ancestors_eq e.scene_eq r.toId
  have hroute : res.scene.layoutDump.routeScope rt =
      ([rt.fromId, rt.toId] ++ res.scene.layoutDump.ancestors rt.fromId ++
        res.scene.layoutDump.ancestors rt.toId) := rfl
  have h := hscope
  rw [hidb, hroute, hanc1, hanc2, hfrom, hto] at h
  exact h

/-- Input scope implies the scope of any dump whose ancestors are input
ancestors and whose route ends agree. -/
private theorem nlc_scope_of_sub {inp : Input} {d : LayoutDump} {fr : Route} {sb : Box}
    {r : ModelRoute} {ib : ModelBox}
    (hsbid : sb.id = ib.id) (hffrom : fr.fromId = r.fromId) (hffto : fr.toId = r.toId)
    (hsub : ∀ s x : String, x ∈ d.ancestors s → x ∈ (inpDumpOf inp).ancestors s)
    (hscope : nlcScopeOut inp r ib) :
    sb.id ∉ d.routeScope fr := by
  have hroute : d.routeScope fr =
      ([fr.fromId, fr.toId] ++ d.ancestors fr.fromId ++ d.ancestors fr.toId) := rfl
  rw [hroute, hsbid, hffrom, hffto]
  simp only [nlcScopeOut] at hscope
  intro hm
  exact hscope (by
    rcases List.mem_append.mp hm with h1 | h3
    · rcases List.mem_append.mp h1 with h11 | h12
      · exact List.mem_append_left _ (List.mem_append_left _ h11)
      · exact List.mem_append_left _
          (List.mem_append_right _ (hsub r.fromId ib.id h12))
    · exact List.mem_append_right _ (hsub r.toId ib.id h3))

/-- Kept routes clear every composed box: fragment boxes by the mixed residual,
contracted boxes by the contracted C6 fact transported through the flag,
exclusivity, and ancestor bridges. -/
private theorem nlc_c6_kept {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : Validator.C6 e.contracted.scene.layoutDump)
    (hFlags : NotesC6FlagsKept e) (hExclC : NotesC6BoxExclC e)
    (hKeptFrag : NotesC6KeptFrag e) (hAncC : NotesC6AncC e)
    {r : ModelRoute} (hr : r ∈ inp.routes) (hkept : nlcKept inp e.layouts r)
    {cr : Route} (hcr : cr ∈ e.contracted.scene.routes) (hcrid : cr.id = r.id)
    {rt : Route} (hpts : rt.points = cr.points) {b : Box} {ib : ModelBox}
    (hib : ib ∈ inp.boxes)
    (hexcb : b.exclusive = ib.exclusive)
    (hrect : outRect e.placed e.contracted.scene ib.id = some b.rect)
    (hexc : b.exclusive = true) (hscopeIn : nlcScopeOut inp r ib) :
    ¬ Polyline.hitsRect rt.points b.rect := by
  have hexcib : ib.exclusive = true := by rw [← hexcb]; exact hexc
  obtain ⟨_, hcrfrom, hcrto⟩ := hFlags r hkept cr hcr hcrid
  rcases classifyRect hrect with ⟨q, hqf, hqR⟩ | ⟨hno, cb, hcbmem, hcbid, hcbr⟩
  · obtain ⟨sq, hsqmem, hsqid, hshift⟩ := Placed.rect_scene_box hqR
    have hbrect : b.rect = shiftRect q.dx q.dy sq.rect := hshift.symm
    obtain ⟨li, hlim, hqim⟩ := placedFlatten_mem e.placed_eq hqf
    have h := hKeptFrag r hr hkept cr hcr hcrid li hlim q hqim sq hsqmem ib hib hsqid
      hexcib hscopeIn
    rw [hpts, hbrect]; exact h
  · have hnoF : ∀ p ∈ e.fragments, ∀ t : Rect, p.rect ib.id ≠ some t := by
      intro p hpm t
      exact hno p (by rw [← e.fragments_eq]; exact hpm) t
    have hexcCb : cb.exclusive = true := by
      have h := hExclC cb hcbmem ib hib hcbid hno
      rw [h, ← hexcb]; exact hexc
    have hscopeC := nlc_scope_of_sub hcbid hcrfrom hcrto hAncC hscopeIn
    have h := hBase cr hcr cb hcbmem hexcCb hscopeC
    rw [hpts, ← hcbr]; exact h

/-- Fragment routes clear every composed box: same-scene boxes by the fragment
C6 fact shifted to the composed scene, other-fragment boxes by the cross
residual, and contracted boxes by the mixed residual. -/
private theorem nlc_c6_frag {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hFrag : ∀ p ∈ e.fragments, Validator.C6 p.scene.layoutDump)
    (hFlags : NotesC6FlagsFrag e) (hExclF : NotesC6BoxExclF e)
    (hFragC : NotesC6FragContracted e) (hFragO : NotesC6FragOther e)
    (hAncF : NotesC6AncF e)
    (a : Nat) {r : ModelRoute} (hr : r ∈ inp.routes)
    (hsame : nlcSameBundleAt inp e.layouts a r)
    {p : Placed} (hpf : p ∈ e.fragments)
    {fr : Route} (hfrmem : fr ∈ p.scene.routes) (hfrid : fr.id = r.id)
    {rt : Route} (hpts : rt.points = fr.points.map (shiftPoint p.dx p.dy))
    {b : Box} {ib : ModelBox} (hib : ib ∈ inp.boxes)
    (hexcb : b.exclusive = ib.exclusive)
    (hrect : outRect e.placed e.contracted.scene ib.id = some b.rect)
    (hexc : b.exclusive = true) (hscopeIn : nlcScopeOut inp r ib) :
    ¬ Polyline.hitsRect rt.points b.rect := by
  have hexcib : ib.exclusive = true := by rw [← hexcb]; exact hexc
  obtain ⟨_, hffrom, hffto⟩ := hFlags r a hsame p hpf fr hfrmem hfrid
  rcases classifyRect hrect with ⟨q, hqf, hqR⟩ | ⟨hno, cb, hcbmem, hcbid, hcbr⟩
  · obtain ⟨sq, hsqmem, hsqid, hshift⟩ := Placed.rect_scene_box hqR
    have hbrect : b.rect = shiftRect q.dx q.dy sq.rect := hshift.symm
    have hqfF : q ∈ e.fragments := by rw [e.fragments_eq]; exact hqf
    rcases Classical.em (p = q) with rfl | hne
    · obtain ⟨li, hlim, hpim⟩ := placedFlatten_mem e.placed_eq hqf
      have hexcSq : sq.exclusive = true := by
        have h := hExclF li hlim p hpim sq hsqmem ib hib hsqid
        rw [h, ← hexcb]; exact hexc
      have hscopeF := nlc_scope_of_sub hsqid hffrom hffto (hAncF p hqfF) hscopeIn
      have h := hFrag p hqfF fr hfrmem sq hsqmem hexcSq hscopeF
      rw [hpts, hbrect]
      exact mt (hitsRect_shift _ _ _ _).mp h
    · have h := hFragO a r hr hsame p hpf fr hfrmem hfrid q hqfF (Ne.symm hne) sq hsqmem
        ib hib hsqid hexcib hscopeIn
      rw [hpts, hbrect]; exact h
  · have hnoF : ∀ q ∈ e.fragments, ∀ t : Rect, q.rect ib.id ≠ some t := by
      intro q hqm t
      exact hno q (by rw [← e.fragments_eq]; exact hqm) t
    have h := hFragC a r hr hsame p hpf fr hfrmem hfrid cb hcbmem ib hib hcbid hnoF
      hexcib hscopeIn
    rw [hpts, ← hcbr]; exact h

/-- Cross routes clear every composed box by the router residual. -/
private theorem nlc_c6_cross {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hRouter : NotesC6RouterClear e)
    {r : ModelRoute} (hr : r ∈ inp.routes) (hcross : nlcCross inp e.layouts r)
    {pts : List Point} (hroute : routeAround inp e.atts (nlcFrameOf e.contracted o e.margin)
      (nlcRectsOf res.scene.boxes) (nlcLabelsOf e.fragments e.contracted inp)
      (nlcTitlesOf e.fragments e.contracted) r = .ok pts)
    {rt : Route} (hpts : rt.points = pts)
    {b : Box} (hb : b ∈ res.scene.boxes) {ib : ModelBox} (hib : ib ∈ inp.boxes)
    (hidb : b.id = ib.id) (hexcib : ib.exclusive = true)
    (hscopeIn : nlcScopeOut inp r ib) :
    ¬ Polyline.hitsRect rt.points b.rect := by
  have h := hRouter r hr hcross pts hroute ib hib hexcib hscopeIn b hb hidb
  rw [hpts]; exact h

/-- C6 for the note stage: routes clear unrelated exclusive boxes. Kept routes
use the contracted fact or the kept/fragment residual, fragment routes use the
fragment fact or the mixed/cross residuals, and cross routes use the router
residual; scopes travel through the input-ancestor bridges. -/
theorem notes_c6 {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : Validator.C6 e.contracted.scene.layoutDump)
    (hFrag : ∀ p ∈ e.fragments, Validator.C6 p.scene.layoutDump)
    (hGeom : NotesC6Geom e) :
    Validator.C6 res.scene.layoutDump := by
  obtain ⟨hAncC, hAncF, hFlagsK, hFlagsF, hExclC, hExclF, hKeptF, hFragC, hFragO,
    hRouter⟩ := hGeom
  intro rt hrt b hb hexc hscope
  obtain ⟨r, hr, _, hfrom, hto, _, hcases⟩ := nlc_route_cases e hrt
  obtain ⟨ib, hib, hidb, _, _, hexcb, hrect⟩ := e.boxes_mem b hb
  have hexcib : ib.exclusive = true := by rw [← hexcb]; exact hexc
  have hscopeIn : nlcScopeOut inp r ib := nlc_scope_of_res e hfrom hto hidb hscope
  rcases hcases with ⟨hkept, cr, hcr, hcrid, hpts⟩ | ⟨a, hsame, p, hpf, fr, hfrmem, hfrid, hpts⟩ |
    ⟨hcross, pts, hpts, hroute⟩
  · exact nlc_c6_kept e hBase hFlagsK hExclC hKeptF hAncC hr hkept hcr hcrid hpts hib hexcb hrect hexc hscopeIn
  · exact nlc_c6_frag e hFrag hFlagsF hExclF hFragC hFragO hAncF a hr hsame hpf hfrmem hfrid hpts hib hexcb hrect hexc hscopeIn
  · exact nlc_c6_cross e hRouter hr hcross hroute hpts hb hib hidb hexcib hscopeIn

/-! ### Clause C7: labels clear of unrelated boxes -/

/-- A composed label that matches a fragment label by id and shifted rect keeps
its owner. The shift only moves the rect. -/
def NotesC7OwnF {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ p ∈ e.fragments, ∀ fl ∈ p.scene.labels, ∀ sl ∈ res.scene.labels,
    sl.id = fl.id → sl.rect = shiftRect p.dx p.dy fl.rect → sl.owner = fl.owner

/-- Same-fragment label scope bridge: outside the composed owner scope implies
outside the fragment owner scope, for id- and owner-matched pairs. -/
def NotesC7BridgeF {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ p ∈ e.fragments, ∀ fl ∈ p.scene.labels, ∀ sb ∈ p.scene.boxes,
    ∀ sl ∈ res.scene.labels, ∀ b ∈ res.scene.boxes,
      sl.id = fl.id → sl.owner = fl.owner → b.id = sb.id →
      b.id ∉ res.scene.layoutDump.labelOwnerAnc sl.toLabel →
      sb.id ∉ p.scene.layoutDump.labelOwnerAnc fl.toLabel

/-- Contracted label scope bridge: outside the composed owner scope implies
outside the contracted owner scope, for the same label and rect-matched boxes. -/
def NotesC7BridgeC {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ cb ∈ e.contracted.scene.boxes, ∀ cl ∈ e.contracted.scene.labels,
    ∀ sl ∈ res.scene.labels, ∀ b ∈ res.scene.boxes,
      sl = cl → b.id = cb.id → b.rect = cb.rect →
      b.id ∉ res.scene.layoutDump.labelOwnerAnc sl.toLabel →
      cb.id ∉ e.contracted.scene.layoutDump.labelOwnerAnc cl.toLabel

/-- Shifted fragment labels clear exclusive contracted boxes. -/
def NotesC7MixedFL {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    ∀ fl ∈ p.scene.labels, ∀ cb ∈ e.contracted.scene.boxes,
      cb.exclusive = true →
      Disjoint (shiftRect p.dx p.dy fl.rect) cb.rect

/-- Contracted labels clear shifted fragment boxes. -/
def NotesC7MixedLF {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    ∀ sb ∈ p.scene.boxes, ∀ cl ∈ e.contracted.scene.labels,
      Disjoint cl.rect (shiftRect p.dx p.dy sb.rect)

/-- Labels and boxes of distinct placed fragments are pairwise disjoint. -/
def NotesC7Cross {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ p ∈ e.fragments, ∀ q ∈ e.fragments, p ≠ q →
    ∀ fl ∈ p.scene.labels, ∀ sb ∈ q.scene.boxes,
      Disjoint (shiftRect p.dx p.dy fl.rect) (shiftRect q.dx q.dy sb.rect)

/-- The geometric context for C7: the exclusivity mirrors (shared with C6),
owner and scope bridges, and the mixed/cross separations. Each conjunct is
fragment/contracted/input/execution geometry, never a claim about `res`. -/
def NotesC7Geom {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  NotesC6BoxExclC e ∧ NotesC6BoxExclF e ∧ NotesC7OwnF e ∧ NotesC7BridgeF e ∧
    NotesC7BridgeC e ∧ NotesC7MixedFL e ∧ NotesC7MixedLF e ∧ NotesC7Cross e

/-- C7 for the note stage: labels stay clear of unrelated exclusive boxes.
Same-source pairs transport the fragment or contracted C7 fact through the
owner/scope bridges; mixed and cross pairs are the residual separations. -/
theorem notes_c7 {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : Validator.C7 e.contracted.scene.layoutDump)
    (hFrag : ∀ p ∈ e.fragments, Validator.C7 p.scene.layoutDump)
    (hGeom : NotesC7Geom e) :
    Validator.C7 res.scene.layoutDump := by
  obtain ⟨hExclC, hExclF, hOwnF, hBridgeF, hBridgeC, hMixedFL, hMixedLF, hCross⟩ := hGeom
  intro l hl b hb hexc hscope
  obtain ⟨sl, hslmem, hslid⟩ := List.mem_map.mp hl
  obtain ⟨ib, hib, hidb, _, _, hexcb, hrect⟩ := e.boxes_mem b hb
  obtain ⟨m, _, hidm, hlab⟩ := e.labels_mem sl hslmem
  have htl : sl.toLabel.rect = sl.rect := nlc_toLabel_rect sl
  have hlid : sl.toLabel = l := hslid
  have hexcib : ib.exclusive = true := by rw [← hexcb]; exact hexc
  have hscopeSl : b.id ∉ res.scene.layoutDump.labelOwnerAnc sl.toLabel := by
    rw [hlid]; exact hscope
  rcases hlab with ⟨p, hpf, fl, hflmem, hflid, hshiftl⟩ | hcl
  · have hown : sl.owner = fl.owner :=
      hOwnF p hpf fl hflmem sl hslmem (hidm.trans hflid.symm) hshiftl
    have hlrect : l.rect = shiftRect p.dx p.dy fl.rect := by rw [← hlid, htl, hshiftl]
    rcases classifyRect hrect with ⟨q, hqf, hqR⟩ | ⟨hno, cb, hcbmem, hcbid, hcbr⟩
    · obtain ⟨sq, hsqmem, hsqid, hshift⟩ := Placed.rect_scene_box hqR
      have hbrect : b.rect = shiftRect q.dx q.dy sq.rect := hshift.symm
      have hqfF : q ∈ e.fragments := by rw [e.fragments_eq]; exact hqf
      rcases Classical.em (p = q) with rfl | hne
      · obtain ⟨li, hlim, hpim⟩ := placedFlatten_mem e.placed_eq hqf
        have hexcSq : sq.exclusive = true := by
          have h := hExclF li hlim p hpim sq hsqmem ib hib hsqid
          rw [h, ← hexcb]; exact hexc
        have hscopeF := hBridgeF p hpf fl hflmem sq hsqmem sl hslmem b hb
          (hidm.trans hflid.symm) hown (hidb.trans hsqid.symm) hscopeSl
        have hflmem' : fl.toLabel ∈ p.scene.layoutDump.labels :=
          List.mem_map.mpr ⟨fl, hflmem, rfl⟩
        have h := hFrag p hpf fl.toLabel hflmem' sq hsqmem hexcSq hscopeF
        rw [hlrect, hbrect]
        exact mt (nlc_meetsInterior_shift _ _ _ _).mp h
      · have h := hCross p hpf q hqfF hne fl hflmem sq hsqmem
        rw [hlrect, hbrect]; exact h
    · have hexcCb : cb.exclusive = true := by
        have h := hExclC cb hcbmem ib hib hcbid hno
        rw [h, ← hexcb]; exact hexc
      obtain ⟨li, hlim, hqim⟩ :=
        placedFlatten_mem e.placed_eq (by rw [← e.fragments_eq]; exact hpf)
      have h := hMixedFL li hlim p hqim fl hflmem cb hcbmem hexcCb
      rw [hlrect, ← hcbr]; exact h
  · rcases classifyRect hrect with ⟨q, hqf, hqR⟩ | ⟨hno, cb, hcbmem, hcbid, hcbr⟩
    · obtain ⟨sq, hsqmem, hsqid, hshift⟩ := Placed.rect_scene_box hqR
      have hbrect : b.rect = shiftRect q.dx q.dy sq.rect := hshift.symm
      obtain ⟨li, hlim, hqim⟩ := placedFlatten_mem e.placed_eq hqf
      have h := hMixedLF li hlim q hqim sq hsqmem sl hcl
      rw [← hlid, htl, hbrect]; exact h
    · have hexcCb : cb.exclusive = true := by
        have h := hExclC cb hcbmem ib hib hcbid hno
        rw [h, ← hexcb]; exact hexc
      have hbids : b.id = cb.id := hidb.trans hcbid.symm
      have hscopeC := hBridgeC cb hcbmem sl hcl sl hslmem b hb rfl hbids hcbr.symm hscopeSl
      have hclmem' : sl.toLabel ∈ e.contracted.scene.layoutDump.labels :=
        List.mem_map.mpr ⟨sl, hcl, rfl⟩
      have h := hBase sl.toLabel hclmem' cb hcbmem hexcCb hscopeC
      rw [← hlid, htl, ← hcbr]; exact h

end PipelineImpl
end Layered
end Elegant

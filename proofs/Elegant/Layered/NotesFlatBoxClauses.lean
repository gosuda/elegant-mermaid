import Elegant.Layered.NotesFoundation
import Elegant.Layered.ComposeNotesC8a
import Elegant.Layered.SceneBounds
import Elegant.Layered.InsetFit
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Box-level clauses for the note stage.

`layoutNotes` lays out each note bundle as a fragment (`bundleLayout`), contracts
each bundle to one footprint box in the base input (`contractOne`), lays out the
contracted input with the base, and translates each fragment into its footprint
box (`composeNotes`). This module states and proves clause C1 (boxes inside the
canvas), clause C2 (exclusive boxes pairwise disjoint), clause C3 (a box lies
inside its parent), and the inset fact for a successful note execution, from the
matching clauses of the base result on the contracted input and of each fragment
result. Those premises are the tower induction hypotheses: each fragment result
comes from `layoutNotes` at lower fuel or from the base, and the contracted
result comes from the base.

The only non-clause premises are the placement/mirror residuals below. Each is a
single `Prop` about fragment, contracted, and input geometry (never about `res`),
and each body was checked by `#eval` on a note on a state, a note on a composite
state, two notes on one state, a note with empty text, and a no-bundle control
(`proofs/wip/Probe/NotesFlatBoxT_probe.lean`).
-/

/-! ### Private list plumbing (prefixed copies: other modules' privates do not resolve) -/

private theorem nbx_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- Membership in a successful `mapM` gives a successful per-element run. -/
private theorem nbx_mapM_ok_of_mem {α β : Type} {f : α → Except LayoutError β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ {a : α}, a ∈ xs →
      ∃ b, f a = .ok b
  | [], _, _, _, ha => by simp at ha
  | _ :: _, _, h, _, ha => by
    simp only [List.mem_cons] at ha
    simp only [List.mapM_cons, bind, Except.bind] at h
    obtain ⟨b, hfb, h⟩ := nbx_bind_ok h
    obtain ⟨bs, hbs, _⟩ := nbx_bind_ok h
    rcases ha with rfl | ha'
    · exact ⟨b, hfb⟩
    · exact nbx_mapM_ok_of_mem hbs ha'

/-- Witness extraction from a successful `findSome?`. -/
private theorem nbx_findSome?_exists {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : β), l.findSome? f = some r → ∃ x, x ∈ l ∧ f x = some r
  | [], _, h => by simp at h
  | a :: rest, _, h => by
    simp only [List.findSome?_cons] at h
    cases hfa : f a with
    | some b =>
      rw [hfa] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨a, List.mem_cons_self, hfa⟩
    | none =>
      rw [hfa] at h
      obtain ⟨x, hx, hfx⟩ := nbx_findSome?_exists f rest _ h
      exact ⟨x, List.mem_cons_of_mem a hx, hfx⟩

/-- Equal images under `·.id` of two members of an id-duplicate-free model-box
list force the members to be equal (specialization of the `ComposeNotesC8a`
argument to the note inputs). -/
private theorem nbx_nodup_id_inj :
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
      · exact nbx_nodup_id_inj _ h.2 ha' hb' e

/-- Every bundle layout has its footprint envelope box in the contracted scene:
`placedFragments` succeeded, so the top lookup succeeded. -/
private theorem nbx_envelope_mem {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) {l : BundleLayout} (hl : l ∈ e.layouts) :
    ∃ eb ∈ e.contracted.scene.boxes,
      eb.id = l.top.id ∧ eb.rect = envRect e.contracted.scene l := by
  obtain ⟨ps, hps⟩ := nbx_mapM_ok_of_mem e.placed_eq hl
  cases hfind : e.contracted.scene.boxes.find? (fun b => b.id == l.top.id) with
  | none =>
    unfold placedFragments at hps
    rw [hfind] at hps
    simp at hps
  | some eb =>
    refine ⟨eb, List.mem_of_find?_eq_some hfind, ?_, ?_⟩
    · have hbe := List.find?_some hfind
      simpa only [beq_iff_eq] using hbe
    · simp only [envRect, hfind]

/-! ### Residuals: one narrow placement/mirror fact per clause family -/

/-- The shifted fragment canvases fit the contracted canvas. With fragment C1
this gives C1 and the inset fact for fragment boxes; the contracted boxes use
the base clause directly. -/
def NotesC1Fit {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ p ∈ e.fragments,
    (Validator.canvasRect e.contracted.scene.layoutDump).Contained
      ⟨p.dx, p.dy, p.scene.canvas.w, p.scene.canvas.h⟩

/-- First-fragment-wins for every fragment box id: the composed lookup resolves
to the placed scene containing the box. This discharges the `resBox_of_fragment`
side conditions. -/
def NotesFirstMatch {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ p ∈ e.fragments, ∀ sb ∈ p.scene.boxes,
    e.fragments.findSome? (fun q => q.rect sb.id) =
      some (shiftRect p.dx p.dy sb.rect)

/-- The contracted scene mirrors the input boxes by id, with parent and
exclusivity kept. This transports base C2/C3 (which quantify over contracted
parents) to input parents. -/
def NotesContractMirror {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ cb ∈ e.contracted.scene.boxes, ∃ ib ∈ inp.boxes,
    cb.id = ib.id ∧ cb.parent = ib.parent ∧ cb.exclusive = ib.exclusive

/-- Each placed fragment scene mirrors input boxes by id, with parent and
exclusivity kept; every fragment box is its layout's top, inside that top, or
one of its notes. This transports fragment C2/C3 to input parents. -/
def NotesFragMirror {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l, ∀ sb ∈ p.scene.boxes,
    ∃ ib ∈ inp.boxes,
      sb.id = ib.id ∧ sb.parent = ib.parent ∧ sb.exclusive = ib.exclusive ∧
        (sb.id = l.top.id ∨ Compound.inside inp.boxes l.top.id sb.id = true ∨
          ∃ q ∈ l.notes, sb.id = q.1.id)

/-- Shifted boxes of distinct placed fragment scenes are pairwise disjoint.
Together with fragment C2 (same placed scene) and the base clause (contracted
boxes), this covers every C2 pair. -/
def NotesPlacedDisjoint {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ pa ∈ e.fragments, ∀ pb ∈ e.fragments, pa ≠ pb →
    ∀ sa ∈ pa.scene.boxes, ∀ sb ∈ pb.scene.boxes,
      Disjoint (shiftRect pa.dx pa.dy sa.rect) (shiftRect pb.dx pb.dy sb.rect)

/-- Shifted fragment boxes clear the contracted boxes no fragment owns. This
covers the mixed C2 pairs (fragment against foreign contracted box). -/
def NotesForeignClear {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l, ∀ sb ∈ p.scene.boxes,
    ∀ cb ∈ e.contracted.scene.boxes,
      (∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r) →
      Disjoint (shiftRect p.dx p.dy sb.rect) cb.rect

/-- The geometric context for C2: first-match, both mirrors, cross-fragment
separation, and foreign clearance. Each conjunct is fragment/contracted/input
geometry, never a claim about `res`. -/
def NotesC2Geom {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  NotesFirstMatch e ∧ NotesContractMirror e ∧ NotesFragMirror e ∧
    NotesPlacedDisjoint e ∧ NotesForeignClear e

/-- Every shifted fragment box lies in its bundle envelope. This chains
fragment boxes to contracted boxes for the mixed C3 case. -/
def NotesEnvFit {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l, ∀ sb ∈ p.scene.boxes,
    (envRect e.contracted.scene l).Contained (shiftRect p.dx p.dy sb.rect)

/-- Parent alignment through the bundle top: each layout has its top input box;
notes are input boxes sharing that top's parent, and every contracted box for
the top id shares it too. This links envelope parents to fragment parents. -/
def NotesParentAlign {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∃ mt ∈ inp.boxes, mt.id = l.top.id ∧
    (∀ q ∈ l.notes, q.1 ∈ inp.boxes ∧ q.1.parent = mt.parent) ∧
    (∀ eb ∈ e.contracted.scene.boxes, eb.id = l.top.id → eb.parent = mt.parent)

/-- Parent locality inside one placed scene: a fragment box is rootless, has a
same-scene parent witness, or its parent lives in no fragment and the box is
its layout's note or top (the mixed case handled through the envelope). -/
def NotesParentLocal {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l, ∀ sb ∈ p.scene.boxes,
    sb.parent = "" ∨ (∃ sp ∈ p.scene.boxes, sp.id = sb.parent) ∨
      ((∀ q ∈ e.fragments, ∀ r : Rect, q.rect sb.parent ≠ some r) ∧
        ((∃ q ∈ l.notes, sb.id = q.1.id) ∨ sb.id = l.top.id))

/-- Non-fragment contracted boxes have rootless or non-fragment parents: no
kept box is parented under a bundle box. This rules out the kept-child of a
fragment-parent C3 configuration. -/
def NotesKeptClosed {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ cb ∈ e.contracted.scene.boxes,
    (∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r) →
      cb.parent = "" ∨
        ∃ cpb ∈ e.contracted.scene.boxes,
          cpb.id = cb.parent ∧
            (∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.parent ≠ some r)

/-- Contracted parent lookup succeeds for the named box. Together with base C3
this yields envelope and kept-box containment. -/
def NotesContractBoxEq {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ eb ∈ e.contracted.scene.boxes, ∀ pb ∈ e.contracted.scene.boxes,
    pb.id = eb.parent → eb.parent ≠ "" →
      e.contracted.scene.layoutDump.box? eb.parent = some pb

/-- Fragment parent lookup succeeds for the named box. Together with fragment
C3 this yields same-scene containment for transport. -/
def NotesFragBoxEq {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    ∀ sb ∈ p.scene.boxes, ∀ sp ∈ p.scene.boxes,
      sp.id = sb.parent → sb.parent ≠ "" →
        p.scene.layoutDump.box? sb.parent = some sp

/-- The geometric context for C3: first-match, both mirrors, envelope fit,
parent alignment and locality, kept closure, and both parent-lookup equations.
Each conjunct is fragment/contracted/input geometry, never a claim about `res`. -/
def NotesC3Geom {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  NotesFirstMatch e ∧ NotesContractMirror e ∧ NotesFragMirror e ∧ NotesEnvFit e ∧
    NotesParentAlign e ∧ NotesParentLocal e ∧ NotesKeptClosed e ∧
    NotesContractBoxEq e ∧ NotesFragBoxEq e

/-! ### The id-disjointness fact -/

/-- Composed box ids are duplicate-free: `contractOne` keeps the input id order
(`boxes_ids`), and well-formedness makes the input ids duplicate-free. -/
theorem notes_boxes_nodup {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o)) :
    (res.scene.boxes.map (·.id)).Nodup := by
  rw [e.boxes_ids]
  exact Model.boxIds_nodup hwf

/-! ### Clause C1 -/

/-- C1 for the note stage: every composed box lies in the contracted canvas,
which is the composed canvas. Fragment boxes travel through their fragment C1
and the canvas fit; contracted boxes use the base C1 directly. -/
theorem notes_c1 {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : Validator.C1 e.contracted.scene.layoutDump)
    (hFrag : ∀ l ∈ e.layouts,
      Validator.C1 l.part.scene.layoutDump ∧
        ∀ q ∈ l.notes, Validator.C1 q.2.scene.layoutDump)
    (hFit : NotesC1Fit e) :
    Validator.C1 res.scene.layoutDump := by
  have hcc : Validator.canvasRect res.scene.layoutDump =
      Validator.canvasRect e.contracted.scene.layoutDump := by
    simp only [Validator.canvasRect, Scene.layoutDump, e.canvas_eq]
  intro b hb
  obtain ⟨_, _, _, _, _, _, hrect⟩ := e.boxes_mem b hb
  rcases classifyRect hrect with hfa | ⟨_, cg, hcgmem, _, hcgr⟩
  · obtain ⟨p, hpf, hpaR⟩ := hfa
    obtain ⟨sb, hsbm, _, hshift⟩ := Placed.rect_scene_box hpaR
    obtain ⟨l, hlm, hpm⟩ := placedFlatten_mem e.placed_eq hpf
    have hpfF : p ∈ e.fragments := by rw [e.fragments_eq]; exact hpf
    have hfit := hFit p hpfF
    have hW : (Validator.canvasRect p.scene.layoutDump).Contained sb.rect := by
      rcases placedOf_scene hpm with hps | ⟨q, hqm, hqs⟩
      · have hsbm' : sb ∈ l.part.scene.boxes := by rw [← hps]; exact hsbm
        have h1 := (hFrag l hlm).1 _ hsbm'
        rwa [← hps] at h1
      · have hsbm' : sb ∈ q.2.scene.boxes := by rw [← hqs]; exact hsbm
        have h1 := ((hFrag l hlm).2 q hqm) _ hsbm'
        rwa [← hqs] at h1
    have hsh := (notesShiftRect_contained _ _ p.dx p.dy).mpr hW
    rw [← hshift, hcc] at *
    simp only [Validator.canvasRect, Scene.layoutDump, shiftRect,
      Rect.Contained] at hsh hfit ⊢
    omega
  · rw [← hcgr, hcc]
    exact hBase _ hcgmem

/-! ### Clause C2 -/

/-- C2 for the note stage. Same placed scene pairs use fragment C2 transported
by `resC2_of_fragment`; contracted pairs use base C2 transported through the
contracted mirror; distinct placed scenes use the separation residual; mixed
pairs use the foreign-clearance residual. -/
theorem notes_c2 {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : Validator.C2 e.contracted.scene.layoutDump)
    (hFrag : ∀ l ∈ e.layouts,
      Validator.C2 l.part.scene.layoutDump ∧
        ∀ q ∈ l.notes, Validator.C2 q.2.scene.layoutDump)
    (hnd : (inp.boxes.map (fun b => b.id)).Nodup)
    (hG : NotesC2Geom e) :
    Validator.C2 res.scene.layoutDump := by
  obtain ⟨hfm, hcm, hfrm, hpd, hfc⟩ := hG
  intro ra hra rb hrb hne hexA hexB hpar
  obtain ⟨ma, hma, hida, _, hpara, hexa, hrcta⟩ := e.boxes_mem ra hra
  obtain ⟨mb, hmb, hidb, _, hparb, hexb, hrctb⟩ := e.boxes_mem rb hrb
  have hmaex : ma.exclusive = true := by rw [← hexa]; exact hexA
  have hmbex : mb.exclusive = true := by rw [← hexb]; exact hexB
  have hmpar : ma.parent = mb.parent := by rw [← hpara, ← hparb]; exact hpar
  have hsaR : ra.id = ma.id := hida
  have hsbR : rb.id = mb.id := hidb
  rcases classifyRect hrcta with hfa | ⟨hnA, ca, hcam, hcaid, hcar⟩ <;>
    rcases classifyRect hrctb with hfb | ⟨hnB, cb, hcbm, hcbid, hcbr⟩
  · obtain ⟨pa, hpfa, hpaR⟩ := hfa
    obtain ⟨sa, hsam, hsaid, hsha⟩ := Placed.rect_scene_box hpaR
    obtain ⟨pb, hpfb, hpbR⟩ := hfb
    obtain ⟨sb, hsbm, hsbid, hshb⟩ := Placed.rect_scene_box hpbR
    have hneS : sa.id ≠ sb.id := by
      have hsaI : sa.id = ra.id := hsaid.trans hsaR.symm
      have hsbI : sb.id = rb.id := hsbid.trans hsbR.symm
      rw [hsaI, hsbI]; exact hne
    have hpfaF : pa ∈ e.fragments := by rw [e.fragments_eq]; exact hpfa
    have hpfbF : pb ∈ e.fragments := by rw [e.fragments_eq]; exact hpfb
    have hfa' := hfm pa hpfaF sa hsam
    have hfb' := hfm pb hpfbF sb hsbm
    by_cases hpp : pa = pb
    · subst hpp
      obtain ⟨l, hlm, hpm⟩ := placedFlatten_mem e.placed_eq hpfa
      obtain ⟨ima, himam, himaid, himapar, himaex, _⟩ := hfrm l hlm pa hpm sa hsam
      obtain ⟨imb, hmbm, hmbid, hmbpar, himbex, _⟩ := hfrm l hlm pa hpm sb hsbm
      have hima : ima = ma := nbx_nodup_id_inj _ hnd himam hma (himaid.symm.trans hsaid)
      have himb : imb = mb := nbx_nodup_id_inj _ hnd hmbm hmb (hmbid.symm.trans hsbid)
      have hexS1 : sa.exclusive = true := by rw [hima] at himaex; rw [himaex]; exact hmaex
      have hexS2 : sb.exclusive = true := by rw [himb] at himbex; rw [himbex]; exact hmbex
      have hparS : sa.parent = sb.parent := by
        have e1 : sa.parent = ma.parent := by rw [hima] at himapar; exact himapar
        have e2 : sb.parent = mb.parent := by rw [himb] at hmbpar; exact hmbpar
        rw [e1, e2]; exact hmpar
      have hdisjS : Disjoint sa.rect sb.rect := by
        rcases placedOf_scene hpm with hps | ⟨q, hqm, hqs⟩
        · have hsa' : sa ∈ l.part.scene.boxes := by rw [← hps]; exact hsam
          have hsb' : sb ∈ l.part.scene.boxes := by rw [← hps]; exact hsbm
          exact (hFrag l hlm).1 _ hsa' _ hsb' hneS hexS1 hexS2 hparS
        · have hsa' : sa ∈ q.2.scene.boxes := by rw [← hqs]; exact hsam
          have hsb' : sb ∈ q.2.scene.boxes := by rw [← hqs]; exact hsbm
          exact ((hFrag l hlm).2 q hqm) _ hsa' _ hsb' hneS hexS1 hexS2 hparS
      have hsaR' : ra.id = sa.id := hsaR.trans hsaid.symm
      have hsbR' : rb.id = sb.id := hsbR.trans hsbid.symm
      exact e.resC2_of_fragment hpfaF hsam hsbm hdisjS hra hsaR' hrb hsbR' hfa' hfb'
    · have hsep := hpd pa hpfaF pb hpfbF hpp sa hsam sb hsbm
      rw [hsha, hshb] at hsep
      exact hsep
  · obtain ⟨pa, hpfa, hpaR⟩ := hfa
    obtain ⟨sa, hsam, _, hsha⟩ := Placed.rect_scene_box hpaR
    obtain ⟨l, hlm, hpm⟩ := placedFlatten_mem e.placed_eq hpfa
    have hnB' : ∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r := by
      rw [e.fragments_eq, hcbid]; exact hnB
    have hclear := hfc l hlm pa hpm sa hsam cb hcbm hnB'
    rw [hsha, hcbr] at hclear
    exact hclear
  · obtain ⟨pb, hpfb, hpbR⟩ := hfb
    obtain ⟨sb, hsbm, _, hshb⟩ := Placed.rect_scene_box hpbR
    obtain ⟨l, hlm, hpm⟩ := placedFlatten_mem e.placed_eq hpfb
    have hnA' : ∀ q ∈ e.fragments, ∀ r : Rect, q.rect ca.id ≠ some r := by
      rw [e.fragments_eq, hcaid]; exact hnA
    have hclear := hfc l hlm pb hpm sb hsbm ca hcam hnA'
    rw [hcar, hshb] at hclear
    exact (Disjoint.comm _ _).mp hclear
  · have hcaR : ca.id = ra.id := hcaid.trans hsaR.symm
    have hcbR : cb.id = rb.id := hcbid.trans hsbR.symm
    have hneC : ca.id ≠ cb.id := by rw [hcaR, hcbR]; exact hne
    obtain ⟨ica, hicam, hicaid, hicapar, hicaex⟩ := hcm ca hcam
    obtain ⟨icb, hicbm, hicbid, hicbpar, hicbex⟩ := hcm cb hcbm
    have hica : ica = ma := nbx_nodup_id_inj _ hnd hicam hma (hicaid.symm.trans hcaid)
    have hicb : icb = mb := nbx_nodup_id_inj _ hnd hicbm hmb (hicbid.symm.trans hcbid)
    have hexC1 : ca.exclusive = true := by rw [hica] at hicaex; rw [hicaex]; exact hmaex
    have hexC2 : cb.exclusive = true := by rw [hicb] at hicbex; rw [hicbex]; exact hmbex
    have hparC : ca.parent = cb.parent := by
      have e1 : ca.parent = ma.parent := by rw [hica] at hicapar; exact hicapar
      have e2 : cb.parent = mb.parent := by rw [hicb] at hicbpar; exact hicbpar
      rw [e1, e2]; exact hmpar
    have hdisjC := hBase _ hcam _ hcbm hneC hexC1 hexC2 hparC
    rw [hcar, hcbr] at hdisjC
    exact hdisjC

/-! ### Clause C3 -/

/-- C3 for the note stage. The given parent box is classified together with the
child: both in one placed scene use fragment C3 transported by
`resC3_of_fragment`; a same-scene parent witness from the locality residual
reduces cross-scene pairs the same way; a parent outside every fragment chains
through the bundle envelope and base C3; kept-contracted pairs use base C3
with the contracted lookup equation. The kept-closure residual rules out the
kept-child of a fragment-parent configuration. -/
theorem notes_c3 {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : Validator.C3 e.contracted.scene.layoutDump)
    (hFrag : ∀ l ∈ e.layouts,
      Validator.C3 l.part.scene.layoutDump ∧
        ∀ q ∈ l.notes, Validator.C3 q.2.scene.layoutDump)
    (hnd : (inp.boxes.map (fun b => b.id)).Nodup)
    (hG : NotesC3Geom e) :
    Validator.C3 res.scene.layoutDump := by
  obtain ⟨hfm, hcm, hfrm, hef, hpa, hpl, hkc, hcbe, hfbe⟩ := hG
  intro rb hrb hne p hp
  have hpId : p.id = rb.parent := by
    have hpt := List.find?_some hp
    simpa only [beq_iff_eq] using hpt
  have hpmem : p ∈ res.scene.boxes := List.mem_of_find?_eq_some hp
  obtain ⟨mb, hmb, hidb, _, hparb, _, hrctb⟩ := e.boxes_mem rb hrb
  obtain ⟨mp, hmp, hidp, _, _, _, hrctp⟩ := e.boxes_mem p hpmem
  have hparI : mb.parent = mp.id := by rw [← hparb, ← hidp]; exact hpId.symm
  have hmbpar : rb.parent = mb.parent := hparb
  rcases classifyRect hrctb with hfb | ⟨hnB, cb, hcbm, hcbid, hcbr⟩ <;>
    rcases classifyRect hrctp with hfp | ⟨_, cp, hcpm, hcpid, hcpr⟩
  · obtain ⟨pa, hpfa, hpaR⟩ := hfb
    obtain ⟨sa, hsam, hsaid, _⟩ := Placed.rect_scene_box hpaR
    obtain ⟨pap, hpfp, hppR⟩ := hfp
    obtain ⟨spa, hspam, hspaid, _⟩ := Placed.rect_scene_box hppR
    have hpfaF : pa ∈ e.fragments := by rw [e.fragments_eq]; exact hpfa
    have hfa' := hfm pa hpfaF sa hsam
    have hidc : rb.id = sa.id := hidb.trans hsaid.symm
    have hidpar : p.id = spa.id := hidp.trans hspaid.symm
    by_cases hpp : pa = pap
    · subst hpp
      obtain ⟨l, hlm, hpm⟩ := placedFlatten_mem e.placed_eq hpfa
      obtain ⟨ima, himam, himaid, himapar, _, _⟩ := hfrm l hlm pa hpm sa hsam
      have hima : ima = mb := nbx_nodup_id_inj _ hnd himam hmb (himaid.symm.trans hsaid)
      have hsaPar : sa.parent = mb.parent := by rw [hima] at himapar; exact himapar
      have hsaNe : sa.parent ≠ "" := by rw [hsaPar, ← hmbpar]; exact hne
      have hsid : spa.id = sa.parent := hspaid.trans (hparI.symm.trans hsaPar.symm)
      have hbox0 : pa.scene.layoutDump.box? sa.parent = some spa :=
        hfbe l hlm pa hpm sa hsam spa hspam hsid hsaNe
      have hcont : spa.rect.Contained sa.rect := by
        rcases placedOf_scene hpm with hps | ⟨q, hqm, hqs⟩
        · have hsa' : sa ∈ l.part.scene.boxes := by rw [← hps]; exact hsam
          have hsp' : spa ∈ l.part.scene.boxes := by rw [← hps]; exact hspam
          have hbox : l.part.scene.layoutDump.box? sa.parent = some spa := by
            have h1 := hbox0
            rwa [hps] at h1
          exact (hFrag l hlm).1 _ hsa' hsaNe _ hbox
        · have hsa' : sa ∈ q.2.scene.boxes := by rw [← hqs]; exact hsam
          have hsp' : spa ∈ q.2.scene.boxes := by rw [← hqs]; exact hspam
          have hbox : q.2.scene.layoutDump.box? sa.parent = some spa := by
            have h1 := hbox0
            rwa [hqs] at h1
          exact ((hFrag l hlm).2 q hqm) _ hsa' hsaNe _ hbox
      have hfp' := hfm pa hpfaF spa hspam
      exact e.resC3_of_fragment hpfaF hsam hspam hcont hrb hidc hpmem hidpar hfa' hfp'
    · obtain ⟨l, hlm, hpm⟩ := placedFlatten_mem e.placed_eq hpfa
      obtain ⟨ima, himam, himaid, himapar, _, _⟩ := hfrm l hlm pa hpm sa hsam
      have hima : ima = mb := nbx_nodup_id_inj _ hnd himam hmb (himaid.symm.trans hsaid)
      have hsaPar : sa.parent = mb.parent := by rw [hima] at himapar; exact himapar
      have hsaNe : sa.parent ≠ "" := by rw [hsaPar, ← hmbpar]; exact hne
      rcases hpl l hlm pa hpm sa hsam with hzero | ⟨sp, hspm, hspid⟩ | ⟨hnone, _⟩
      · rw [hsaPar] at hzero
        exact absurd (hmbpar.trans hzero) hne
      · have hspI : sp.id = mb.parent := hspid.trans hsaPar
        have hbox0 : pa.scene.layoutDump.box? sa.parent = some sp :=
          hfbe l hlm pa hpm sa hsam sp hspm (by rw [hspI, hsaPar]) hsaNe
        have hcont : sp.rect.Contained sa.rect := by
          rcases placedOf_scene hpm with hps | ⟨q, hqm, hqs⟩
          · have hsa' : sa ∈ l.part.scene.boxes := by rw [← hps]; exact hsam
            have hsp' : sp ∈ l.part.scene.boxes := by rw [← hps]; exact hspm
            have hbox : l.part.scene.layoutDump.box? sa.parent = some sp := by
              have h1 := hbox0
              rwa [hps] at h1
            exact (hFrag l hlm).1 _ hsa' hsaNe _ hbox
          · have hsa' : sa ∈ q.2.scene.boxes := by rw [← hqs]; exact hsam
            have hsp' : sp ∈ q.2.scene.boxes := by rw [← hqs]; exact hspm
            have hbox : q.2.scene.layoutDump.box? sa.parent = some sp := by
              have h1 := hbox0
              rwa [hqs] at h1
            exact ((hFrag l hlm).2 q hqm) _ hsa' hsaNe _ hbox
        have hfp2 := hfm pa hpfaF sp hspm
        have hidpar2 : p.id = sp.id := hpId.trans (hmbpar.trans hspI.symm)
        exact e.resC3_of_fragment hpfaF hsam hspm hcont hrb hidc hpmem hidpar2 hfa' hfp2
      · have hsid2 : sa.parent = p.id := by
          rw [hsaPar, ← hmbpar]; exact hpId.symm
        rw [hsid2] at hnone
        have hpfpF : pap ∈ e.fragments := by rw [e.fragments_eq]; exact hpfp
        have hppR' : pap.rect p.id = some p.rect := by rw [← hidp] at hppR; exact hppR
        exact False.elim (hnone pap hpfpF _ hppR')
  · obtain ⟨pa, hpfa, hpaR⟩ := hfb
    obtain ⟨sa, hsam, hsaid, hsha⟩ := Placed.rect_scene_box hpaR
    obtain ⟨l, hlm, hpm⟩ := placedFlatten_mem e.placed_eq hpfa
    obtain ⟨ima, himam, himaid, himapar, _, _⟩ := hfrm l hlm pa hpm sa hsam
    have hima : ima = mb := nbx_nodup_id_inj _ hnd himam hmb (himaid.symm.trans hsaid)
    have hsaPar : sa.parent = mb.parent := by rw [hima] at himapar; exact himapar
    have hsaNe : sa.parent ≠ "" := by rw [hsaPar, ← hmbpar]; exact hne
    have hidc : rb.id = sa.id := hidb.trans hsaid.symm
    have hpfaF : pa ∈ e.fragments := by rw [e.fragments_eq]; exact hpfa
    have hfa' := hfm pa hpfaF sa hsam
    rcases hpl l hlm pa hpm sa hsam with hzero | ⟨sp, hspm, hspid⟩ | ⟨hnone, hex⟩
    · rw [hsaPar] at hzero
      exact absurd (hmbpar.trans hzero) hne
    · have hspI : sp.id = mb.parent := hspid.trans hsaPar
      have hbox0 : pa.scene.layoutDump.box? sa.parent = some sp :=
        hfbe l hlm pa hpm sa hsam sp hspm (by rw [hspI, hsaPar]) hsaNe
      have hcont : sp.rect.Contained sa.rect := by
        rcases placedOf_scene hpm with hps | ⟨q, hqm, hqs⟩
        · have hsa' : sa ∈ l.part.scene.boxes := by rw [← hps]; exact hsam
          have hsp' : sp ∈ l.part.scene.boxes := by rw [← hps]; exact hspm
          have hbox : l.part.scene.layoutDump.box? sa.parent = some sp := by
            have h1 := hbox0
            rwa [hps] at h1
          exact (hFrag l hlm).1 _ hsa' hsaNe _ hbox
        · have hsa' : sa ∈ q.2.scene.boxes := by rw [← hqs]; exact hsam
          have hsp' : sp ∈ q.2.scene.boxes := by rw [← hqs]; exact hspm
          have hbox : q.2.scene.layoutDump.box? sa.parent = some sp := by
            have h1 := hbox0
            rwa [hqs] at h1
          exact ((hFrag l hlm).2 q hqm) _ hsa' hsaNe _ hbox
      have hfp2 := hfm pa hpfaF sp hspm
      have hspI2 : sp.id = mp.id := hspI.trans hparI
      have hidpar2 : p.id = sp.id := hidp.trans hspI2.symm
      exact e.resC3_of_fragment hpfaF hsam hspm hcont hrb hidc hpmem hidpar2 hfa' hfp2
    · obtain ⟨eb, hebm, hebid, hebev⟩ := nbx_envelope_mem e hlm
      have henv := hef l hlm pa hpm sa hsam
      rw [← hebev] at henv
      obtain ⟨mt, hmtm, hmtid, hnotepar, henvpar⟩ := hpa l hlm
      have hmtpar : mt.parent = mb.parent := by
        rcases hex with ⟨q, hqm, hqid⟩ | htop
        · have hqmem : q.1 ∈ inp.boxes := (hnotepar q hqm).1
          have hqeq : q.1 = mb := nbx_nodup_id_inj _ hnd hqmem hmb (by rw [← hqid]; exact hsaid)
          have hqp : q.1.parent = mt.parent := (hnotepar q hqm).2
          have hmbq : mb.parent = q.1.parent := by rw [← hqeq]
          exact hqp.symm.trans hmbq.symm
        · have hmbmt : mb = mt :=
            nbx_nodup_id_inj _ hnd hmb hmtm (hsaid.symm.trans (htop.trans hmtid.symm))
          rw [hmbmt]
      have hebpar : eb.parent = mb.parent := by
        have h1 : eb.parent = mt.parent := henvpar eb hebm hebid
        rw [h1]; exact hmtpar
      have hebNe : eb.parent ≠ "" := by rw [hebpar, ← hmbpar]; exact hne
      have hcpid' : cp.id = eb.parent :=
        hcpid.trans (hidp.symm.trans (hpId.trans (hmbpar.trans hebpar.symm)))
      have hboxc : e.contracted.scene.layoutDump.box? eb.parent = some cp :=
        hcbe eb hebm cp hcpm hcpid' hebNe
      have hcontB := hBase _ hebm hebNe _ hboxc
      have hgoal : cp.rect.Contained rb.rect := Rect.Contained.trans hcontB (by rw [← hsha]; exact henv)
      rwa [hcpr] at hgoal
  · obtain ⟨pap, hpfp, hppR⟩ := hfp
    obtain ⟨spa, hspam, hspaid, _⟩ := Placed.rect_scene_box hppR
    have hnB' : ∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r := by
      rw [e.fragments_eq, hcbid]; exact hnB
    have hkcD := hkc cb hcbm hnB'
    have hcbPar : cb.parent = mb.parent := by
      obtain ⟨ica, hicam, hicaid, hicapar, _⟩ := hcm cb hcbm
      have hica : ica = mb :=
        nbx_nodup_id_inj _ hnd hicam hmb (hicaid.symm.trans hcbid)
      rw [hica] at hicapar
      exact hicapar
    have hspaI : spa.id = mb.parent := hspaid.trans (hidp.symm.trans (hpId.trans hmbpar))
    rcases hkcD with hzero | ⟨_, _, _, hnone2⟩
    · rw [hcbPar] at hzero
      exact absurd (hmbpar.trans hzero) hne
    · have hpid : cb.parent = spa.id := hcbPar.trans hspaI.symm
      rw [hpid] at hnone2
      have hpfpF : pap ∈ e.fragments := by rw [e.fragments_eq]; exact hpfp
      have hfmS := hfm pap hpfpF spa hspam
      obtain ⟨q, hq, hqR⟩ := nbx_findSome?_exists _ _ _ hfmS
      exact absurd hqR (hnone2 q hq _)
  · have hcpC : cp.rect.Contained cb.rect := by
      have hcbPar : cb.parent = mb.parent := by
        obtain ⟨icb, hicbm, hicbid, hicbpar, _⟩ := hcm cb hcbm
        have hicb : icb = mb :=
          nbx_nodup_id_inj _ hnd hicbm hmb (hicbid.symm.trans hcbid)
        rw [hicb] at hicbpar
        exact hicbpar
      have hcpI : cp.id = mb.parent := hcpid.trans (hidp.symm.trans (hpId.trans hmbpar))
      have hcbNe : cb.parent ≠ "" := by rw [hcbPar, ← hmbpar]; exact hne
      have hboxc : e.contracted.scene.layoutDump.box? cb.parent = some cp := by
        have hcpI' : cp.id = cb.parent := by rw [hcpI, hcbPar]
        exact hcbe cb hcbm cp hcpm hcpI' hcbNe
      exact hBase _ hcbm hcbNe _ hboxc
    rw [hcpr, hcbr] at hcpC
    exact hcpC

/-! ### The inset fact -/

/-- The inset fact for the note stage: with the executed margin, every composed
box lies in the margin inset of the canvas. This is the `FlatInsetB` conclusion
at the note base. -/
theorem notes_inset {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : InsetC1 e.contracted.scene e.margin)
    (hFrag : ∀ l ∈ e.layouts,
      InsetC1 l.part.scene e.margin ∧ ∀ q ∈ l.notes, InsetC1 q.2.scene e.margin)
    (hFit : NotesC1Fit e) :
    ∃ P : Params, checkedParams o.profile inp.kind = .ok P ∧
      0 ≤ P.canvasMargin ∧ InsetC1 res.scene P.canvasMargin := by
  have hinset : InsetC1 res.scene e.margin := by
    intro b hb
    obtain ⟨_, _, _, _, _, _, hrect⟩ := e.boxes_mem b hb
    rcases classifyRect hrect with hfa | ⟨_, cg, hcgmem, _, hcgr⟩
    · obtain ⟨p, hpf, hpaR⟩ := hfa
      obtain ⟨sb, hsbm, _, hshift⟩ := Placed.rect_scene_box hpaR
      obtain ⟨l, hlm, hpm⟩ := placedFlatten_mem e.placed_eq hpf
      have hpfF : p ∈ e.fragments := by rw [e.fragments_eq]; exact hpf
      have hW : (insetRect p.scene.canvas e.margin).Contained sb.rect := by
        rcases placedOf_scene hpm with hps | ⟨q, hqm, hqs⟩
        · have hsbm' : sb ∈ l.part.scene.boxes := by rw [← hps]; exact hsbm
          have h1 := (hFrag l hlm).1 _ hsbm'
          rwa [← hps] at h1
        · have hsbm' : sb ∈ q.2.scene.boxes := by rw [← hqs]; exact hsbm
          have h1 := ((hFrag l hlm).2 q hqm) _ hsbm'
          rwa [← hqs] at h1
      have hfit := hFit p hpfF
      rw [← hshift]
      simp only [insetRect, Scene.layoutDump, shiftRect,
        Validator.canvasRect, Rect.Contained, e.canvas_eq] at hW hfit ⊢
      omega
    · rw [← hcgr, e.canvas_eq]
      exact hBase _ hcgmem
  refine ⟨e.params, e.checked, ?_, ?_⟩
  · have h1 := checkedParams_canvasMargin_ge_one e.checked
    omega
  · rw [← e.margin_eq]
    exact hinset

end PipelineImpl
end Layered
end Elegant

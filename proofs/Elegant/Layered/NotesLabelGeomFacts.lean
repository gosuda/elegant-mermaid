import Elegant.Layered.NotesFlatLabelClauses
import Elegant.Layered.NotesPlacementFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Geometry residuals for the note-stage label clauses (C8b, C7) and box
clause (C8a), closed over `NotesExecution`.

TRUTH FIRST (all from `proofs/wip/Probe/NotesGeomFactsT_probe.lean`,
`layoutNotes layoutX [] 1`, vector profile):
left note, right note, note on a group, two notes, long-text note, note
with self-loop, note on an empty group, duplicate-id (non-wellformed),
label-carrying, and note-on-grouped-member-without-routes inputs all
execute and satisfy every conjunct of all four geoms (`first`, role
mirrors, mixed/cross separations, C8a fold/len/scene/role/found/clear/
disjoint/env pieces, C6 ancestor/flag/exclusivity/router pieces, C7
owner/bridge/mixed pieces: all `true`).
Two non-executions bound the claims, not the theorems: a note on a
grouped member WITH routes errors with `LayoutError.domain` (no
execution, nothing to probe), and the duplicate-id input executes but
gives `first=false`, so `NotesC8bFirst` keeps an explicit id-duplicate-free
premise. Every executed scene carries zero labels, so the label-side
separations hold vacuously on the probes; the proofs below stay general
over whatever labels occur.

### Residuals left open (not restated under new names)

* `NotesC8bGeom`: fully proved (`ngfC8bGeom_holds`).
* `NotesC7Geom`: fully proved (`ngfC7Geom_holds`).
* `NotesC8aGeom`: `Env`, `FragRole`, `ContractRole`, `FragDisj`, `Clear`
  (modulo its id bridge), and `EnvDisj` proved above as separate conjunct
  theorems. Still open: `TopNodup` (bundle-top nodup from `bundlesOf`),
  `Fold` and `ContractScene` (`IdParentTransfer` through the `contractOne`
  fold), `Len` (base id-list preservation, `NotesBaseContract` shape),
  `FragFound` (per-bundle id presence in `placedFragments`), `SceneAnc`
  (fragment ancestor subsumption), and the `Clear` id bridge
  (`fragmentIdOf`-false implies unclaimed by every fragment).
* `NotesC6Geom`: `BoxExclC`/`BoxExclF` proved above (shared with C7).
  Still open: `AncC`/`AncF` (contracted/fragment ancestor preservation
  over the base layouts), `FlagsKept`/`FlagsFrag` (route endpoint
  preservation), `KeptFrag`/`FragContracted`/`FragOther` (contracted and
  fragment C6 no-hit transport through envelopes), and `RouterClear`
  (`routeAround` obstacle properties over the visibility grid).
-/

/-! ### Private plumbing (prefixed copies; siblings stay private) -/

private theorem ngf_meets_contained {i o x : Rect} (hc : o.Contained i)
    (h : i.meetsInterior x) : o.meetsInterior x := by
  unfold Rect.Contained Rect.meetsInterior at *
  omega

/-- Disjointness transports through containment on both sides. -/
private theorem ngf_disjoint_of_subset {a' b' a b : Rect} (h : Disjoint a' b')
    (ha : a'.Contained a) (hb : b'.Contained b) : Disjoint a b := by
  unfold Disjoint at h ⊢
  intro hm
  exact h (ngf_meets_contained ha ((Rect.meetsInterior_comm b' a).mp
    (ngf_meets_contained hb ((Rect.meetsInterior_comm a b).mp hm))))

/-- Equal images under `·.id` of two members of an id-duplicate-free model-box
list force the members to be equal (prefixed copy). -/
private theorem ngf_nodup_id_inj :
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
      · exact ngf_nodup_id_inj _ h.2 ha' hb' e

/-! ### C8b: first-match and envelope (reuse of placement facts) -/

/-- First-fragment-wins for every fragment box id: the placement lookup fact
restated for `NotesC8bGeom`. Needs the holding fragment's own lookup
(`hSelf`) and no other fragment resolving the id (`hCross`); the
duplicate-id probe falsifies the conclusion without them. -/
theorem ngfC8bFirst_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hSelf : ∀ p ∈ e.fragments, ∀ sb ∈ p.scene.boxes,
      p.rect sb.id = some (shiftRect p.dx p.dy sb.rect))
    (hCross : ∀ p ∈ e.fragments, ∀ q ∈ e.fragments, p ≠ q →
      ∀ sb ∈ p.scene.boxes, q.rect sb.id = none) :
    NotesC8bFirst e :=
  notesFirstMatch_holds e hSelf hCross

/-- Every shifted fragment box lies in its bundle envelope: the placement
envelope fact restated for `NotesC8aGeom`. -/
theorem ngfC8aEnv_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hPlace : ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      (envRect e.contracted.scene l).Contained ⟨p.dx, p.dy, p.scene.canvas.w, p.scene.canvas.h⟩)
    (hFrag : ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      Validator.C1 p.scene.layoutDump) :
    NotesC8aEnv e :=
  notesEnvFit_holds e hPlace hFrag

/-! ### C8b roles and C6/C7 exclusivity from the box mirrors -/

/-- Every placed fragment box mirrors an input box role: existence from
`NotesFragMirror`, the role equation from the narrow role premise (`frole`
is `true` on every executed probe). -/
theorem ngfC8bFragRole_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hMirror : NotesFragMirror e)
    (hRole : ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      ∀ sb ∈ p.scene.boxes, ∀ ib ∈ inp.boxes, sb.id = ib.id → sb.role = ib.role.id) :
    NotesC8bFragRole e := by
  intro l hl p hpl sb hsb
  obtain ⟨ib, hib, hid, _, _, _⟩ := hMirror l hl p hpl sb hsb
  exact ⟨ib, hib, hid, hRole l hl p hpl sb hsb ib hib hid⟩

/-- An unclaimed contracted box mirrors its input box role: the unclaimed
side condition is irrelevant to roles, so the narrow role premise
(`crole` is `true` on every executed probe) suffices. -/
theorem ngfC8bContractRole_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hRole : ∀ cb ∈ e.contracted.scene.boxes, ∀ ib ∈ inp.boxes,
      cb.id = ib.id → cb.role = ib.role.id) :
    NotesC8bContractRole e := by
  intro cb hcb ib hib hid _
  exact hRole cb hcb ib hib hid

/-- Unclaimed contracted boxes mirror input exclusivity: the mirror gives a
box with the same id, input id-uniqueness identifies it (`first=false` on
the duplicate-id probe shows the premise is load-bearing). -/
theorem ngfC6BoxExclC_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hMirror : NotesContractMirror e)
    (hnd : (inp.boxes.map (·.id)).Nodup) :
    NotesC6BoxExclC e := by
  intro cb hcb ib hib hid hno
  obtain ⟨jb, hjb, hidj, _, hexc⟩ := hMirror cb hcb
  have hjb2 : jb.id = ib.id := hidj.symm.trans hid
  have heq : jb = ib := ngf_nodup_id_inj inp.boxes hnd hjb hib hjb2
  rw [heq] at hexc
  exact hexc

/-- Placed fragment boxes mirror input exclusivity, by the same
uniqueness argument through `NotesFragMirror`. -/
theorem ngfC6BoxExclF_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hMirror : NotesFragMirror e)
    (hnd : (inp.boxes.map (·.id)).Nodup) :
    NotesC6BoxExclF e := by
  intro l hl p hpl sb hsb ib hib hid
  obtain ⟨jb, hjb, hidj, _, hexc, _⟩ := hMirror l hl p hpl sb hsb
  have hjb2 : jb.id = ib.id := hidj.symm.trans hid
  have heq : jb = ib := ngf_nodup_id_inj inp.boxes hnd hjb hib hjb2
  rw [heq] at hexc
  exact hexc
private theorem ngf_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem ngf_mapM_ok_of_mem {α β : Type} {f : α → Except LayoutError β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ {a : α}, a ∈ xs →
      ∃ b, f a = .ok b
  | [], _, _, _, ha => by simp at ha
  | _ :: _, _, h, _, ha => by
    simp only [List.mem_cons] at ha
    simp only [List.mapM_cons, bind, Except.bind] at h
    obtain ⟨b, hfb, h⟩ := ngf_bind_ok h
    obtain ⟨bs, hbs, _⟩ := ngf_bind_ok h
    rcases ha with rfl | ha'
    · exact ⟨b, hfb⟩
    · exact ngf_mapM_ok_of_mem hbs ha'

/-- Every bundle layout has its footprint envelope box in the contracted scene. -/
private theorem ngf_envelope_mem {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) {l : BundleLayout} (hl : l ∈ e.layouts) :
    ∃ eb ∈ e.contracted.scene.boxes,
      eb.id = l.top.id ∧ eb.rect = envRect e.contracted.scene l := by
  obtain ⟨ps, hps⟩ := ngf_mapM_ok_of_mem e.placed_eq hl
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

/-- Shifted fragment group boxes clear contracted labels: the shifted box
lies in its bundle envelope, the label in its owner box, and the envelope
is disjoint from that owner box by the contracted C2 clause. The
applicability premise (`hAppl`) and both containments hold vacuously on
every executed probe (no scene labels occur); the envelope/C2 part is the
same transport the placement facts use. -/
theorem ngfC8bMixedGL_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hEnvFit : NotesEnvFit e)
    (hLabC : ∀ cl ∈ e.contracted.scene.labels, ∃ cb ∈ e.contracted.scene.boxes,
      cb.id = cl.owner ∧ cb.rect.Contained cl.rect)
    (hBaseC2 : Validator.C2 e.contracted.scene.layoutDump)
    (hAppl : ∀ l ∈ e.layouts, ∀ eb ∈ e.contracted.scene.boxes, eb.id = l.top.id →
      ∀ cl ∈ e.contracted.scene.labels, ∀ cb ∈ e.contracted.scene.boxes,
        cb.id = cl.owner →
        eb.id ≠ cb.id ∧ eb.exclusive = true ∧ cb.exclusive = true ∧ eb.parent = cb.parent) :
    NotesC8bMixedGL e := by
  intro l hl p hpl sg hsg hgroup cl hcl
  obtain ⟨eb, heb, hideb, hrectb⟩ := ngf_envelope_mem e hl
  obtain ⟨cb, hcb, hidcb, hcont⟩ := hLabC cl hcl
  obtain ⟨hne, hexE, hexC, hpar⟩ := hAppl l hl eb heb hideb cl hcl cb hcb hidcb
  have hC2 := hBaseC2 eb heb cb hcb hne hexE hexC hpar
  rw [hrectb] at hC2
  have hfit := hEnvFit l hl p hpl sg hsg
  exact ngf_disjoint_of_subset hC2 hfit hcont

/-- Contracted group boxes clear shifted fragment labels: the label lies in
its owner fragment box, which lies in its bundle envelope, and the group
box is disjoint from that envelope by the contracted C2 clause. -/
theorem ngfC8bMixedLG_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hLabF : ∀ p ∈ e.fragments, ∀ fl ∈ p.scene.labels, ∃ fb ∈ p.scene.boxes,
      fb.id = fl.owner ∧ fb.rect.Contained fl.rect)
    (hEnvFit : NotesEnvFit e)
    (hBaseC2 : Validator.C2 e.contracted.scene.layoutDump)
    (hAppl : ∀ l ∈ e.layouts, ∀ eb ∈ e.contracted.scene.boxes, eb.id = l.top.id →
      ∀ cg ∈ e.contracted.scene.boxes, cg.role = "group" →
        cg.id ≠ eb.id ∧ cg.exclusive = true ∧ eb.exclusive = true ∧ cg.parent = eb.parent) :
    NotesC8bMixedLG e := by
  intro l hl p hpl fl hflmem cg hcgmem hgroup
  have hpf : p ∈ e.fragments := by
    rw [e.fragments_eq]
    exact placedOf_mem_flatten e.placed_eq hl hpl
  obtain ⟨fb, hfbmem, _, hcont⟩ := hLabF p hpf fl hflmem
  have hfit := hEnvFit l hl p hpl fb hfbmem
  obtain ⟨eb, heb, hideb, hrectb⟩ := ngf_envelope_mem e hl
  obtain ⟨hne, hexC, hexE, hpar⟩ := hAppl l hl eb heb hideb cg hcgmem hgroup
  have hC2 := hBaseC2 cg hcgmem eb heb hne hexC hexE hpar
  rw [hrectb] at hC2
  have hshift := (notesShiftRect_contained fb.rect fl.rect p.dx p.dy).mpr hcont
  have hsub := Rect.Contained.trans hfit hshift
  exact ngf_disjoint_of_subset hC2 (Rect.Contained.refl _) hsub

/-- Group boxes and labels of distinct placed fragments are pairwise
disjoint: the label lies in its owner box of its own fragment, and distinct
fragments are box-disjoint by the placed-separation fact. -/
theorem ngfC8bCross_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hLabF : ∀ p ∈ e.fragments, ∀ fl ∈ p.scene.labels, ∃ fb ∈ p.scene.boxes,
      fb.id = fl.owner ∧ fb.rect.Contained fl.rect)
    (hPlacedDisj : NotesPlacedDisjoint e) :
    NotesC8bCross e := by
  intro p hpf q hqf hne sg hsg hgroup fl hflmem
  obtain ⟨fb, hfbmem, _, hcont⟩ := hLabF q hqf fl hflmem
  have hdisj := hPlacedDisj p hpf q hqf hne sg hsg fb hfbmem
  have hsub := (notesShiftRect_contained fb.rect fl.rect q.dx q.dy).mpr hcont
  exact ngf_disjoint_of_subset hdisj (Rect.Contained.refl _) hsub

/-- The full C8b geometric context from local premises only: first-match
from the placement lookups, roles from the box mirrors, and the three
separations through envelope containment and contracted C2. -/
theorem ngfC8bGeom_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hSelf : ∀ p ∈ e.fragments, ∀ sb ∈ p.scene.boxes,
      p.rect sb.id = some (shiftRect p.dx p.dy sb.rect))
    (hCross : ∀ p ∈ e.fragments, ∀ q ∈ e.fragments, p ≠ q →
      ∀ sb ∈ p.scene.boxes, q.rect sb.id = none)
    (hFragMirror : NotesFragMirror e)
    (hRoleF : ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      ∀ sb ∈ p.scene.boxes, ∀ ib ∈ inp.boxes, sb.id = ib.id → sb.role = ib.role.id)
    (hRoleC : ∀ cb ∈ e.contracted.scene.boxes, ∀ ib ∈ inp.boxes,
      cb.id = ib.id → cb.role = ib.role.id)
    (hEnvFit : NotesEnvFit e)
    (hLabF : ∀ p ∈ e.fragments, ∀ fl ∈ p.scene.labels, ∃ fb ∈ p.scene.boxes,
      fb.id = fl.owner ∧ fb.rect.Contained fl.rect)
    (hLabC : ∀ cl ∈ e.contracted.scene.labels, ∃ cb ∈ e.contracted.scene.boxes,
      cb.id = cl.owner ∧ cb.rect.Contained cl.rect)
    (hBaseC2 : Validator.C2 e.contracted.scene.layoutDump)
    (hApplGL : ∀ l ∈ e.layouts, ∀ eb ∈ e.contracted.scene.boxes, eb.id = l.top.id →
      ∀ cl ∈ e.contracted.scene.labels, ∀ cb ∈ e.contracted.scene.boxes,
        cb.id = cl.owner →
        eb.id ≠ cb.id ∧ eb.exclusive = true ∧ cb.exclusive = true ∧ eb.parent = cb.parent)
    (hApplLG : ∀ l ∈ e.layouts, ∀ eb ∈ e.contracted.scene.boxes, eb.id = l.top.id →
      ∀ cg ∈ e.contracted.scene.boxes, cg.role = "group" →
        cg.id ≠ eb.id ∧ cg.exclusive = true ∧ eb.exclusive = true ∧ cg.parent = eb.parent)
    (hPlacedDisj : NotesPlacedDisjoint e) :
    NotesC8bGeom e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ngfC8bFirst_holds e hSelf hCross
  · exact ngfC8bFragRole_holds e hFragMirror hRoleF
  · exact ngfC8bContractRole_holds e hRoleC
  · exact ngfC8bMixedGL_holds e hEnvFit hLabC hBaseC2 hApplGL
  · exact ngfC8bMixedLG_holds e hLabF hEnvFit hBaseC2 hApplLG
  · exact ngfC8bCross_holds e hLabF hPlacedDisj

/-- Witness extraction from a successful `findSome?` (prefixed copy). -/
private theorem ngf_findSome?_exists {α β : Type} (f : α → Option β) :
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

/-- A `find?` returning `some` on a member's key (prefixed copy). -/
private theorem ngf_find?_some_of_mem {α : Type} (p : α → Bool) {l : List α} {a : α}
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

/-- A witnessed `findSome?` match forces a `some` result (prefixed copy). -/
private theorem ngf_findSome?_isSome {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (a : α) (v : β), a ∈ l → f a = some v →
      ∃ w, l.findSome? f = some w
  | [], _, _, ha, _ => by simp at ha
  | x :: xs, a, v, ha, hself => by
    simp only [List.mem_cons] at ha
    cases hfx : f x with
    | some w => exact ⟨w, by simp only [List.findSome?_cons, hfx]⟩
    | none =>
      have hxa : x ≠ a := by
        intro h
        subst h
        rw [hself] at hfx
        simp at hfx
      have hmem : a ∈ xs := ha.resolve_left (fun h => hxa h.symm)
      obtain ⟨w, hw⟩ := ngf_findSome?_isSome f xs a v hmem hself
      exact ⟨w, by simp only [List.findSome?_cons, hfx]; exact hw⟩

/-- A composed label matching a fragment label by id keeps its owner: the
composed label is the shifted fragment label (labels come from
`NotesExecution.labels_eq`), identified by fragment label-id uniqueness;
the contracted case is impossible since the fragment already resolves the id.
(`ownF` is `true` on every executed probe.) -/
theorem ngfC7OwnF_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hLabNodup : ∀ p ∈ e.fragments, ∀ q ∈ e.fragments, ∀ fl ∈ p.scene.labels,
      ∀ gl ∈ q.scene.labels, fl.id = gl.id → fl = gl) :
    NotesC7OwnF e := by
  intro p hp fl hfl sl hsl hid _hrect
  rw [e.labels_eq] at hsl
  obtain ⟨m, _hm, hgm⟩ := List.mem_filterMap.mp hsl
  cases hfs : e.fragments.findSome? (·.label m.id) with
  | some v =>
    simp only [hfs] at hgm
    have hvl : v = sl := Option.some.inj hgm
    obtain ⟨q, hq, hqv⟩ := ngf_findSome?_exists _ _ _ hfs
    have hqv2 : (q.scene.labels.find? (·.id == m.id)).map
        (fun g => ({ g with rect := shiftRect q.dx q.dy g.rect } : SceneLabel)) = some v := hqv
    obtain ⟨gl, hgl, hglv⟩ := Option.map_eq_some_iff.mp hqv2
    have hgid := List.find?_some hgl
    simp only [beq_iff_eq] at hgid
    have hlbv : sl = { gl with rect := shiftRect q.dx q.dy gl.rect } := (hglv.trans hvl).symm
    have hidm : sl.id = m.id := by rw [hlbv]; exact hgid
    have h1 : fl.id = gl.id := hid.symm.trans (hidm.trans hgid.symm)
    have h2 : fl = gl :=
      hLabNodup p hp q hq fl hfl gl (List.mem_of_find?_eq_some hgl) h1
    rw [hlbv, h2]
  | none =>
    simp only [hfs] at hgm
    have hsome := List.find?_some hgm
    simp only [beq_iff_eq] at hsome
    have hmem : fl.id == m.id := by
      have h1 : fl.id = m.id := hid.symm.trans hsome
      simp [h1]
    obtain ⟨g, hg⟩ := ngf_find?_some_of_mem (fun l => l.id == m.id) hfl hmem
    have hlab : p.label m.id =
        some ({ g with rect := shiftRect p.dx p.dy g.rect } : SceneLabel) := by
      simp only [Placed.label, hg, Option.map_some]
    obtain ⟨w, hw⟩ := ngf_findSome?_isSome (·.label m.id) e.fragments p _ hp hlab
    rw [hw] at hfs
    simp at hfs

/-- Same-fragment scope bridge: outside the composed owner scope implies
outside the fragment owner scope. Both dumps take the non-route arm
(`hNoRouteF`, `hNoRouteR`: labels are never route-owned on the probes),
fragment ancestors are input ancestors (`hAncF`), and composed ancestors
are input ancestors (`composeNotes_ancestors_eq`). -/
theorem ngfC7BridgeF_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hAncF : NotesC6AncF e)
    (hNoRouteF : ∀ p ∈ e.fragments, ∀ fl ∈ p.scene.labels, ∀ r ∈ p.scene.routes,
      fl.owner ≠ r.id)
    (hNoRouteR : ∀ sl ∈ res.scene.labels, ∀ r ∈ res.scene.routes, sl.owner ≠ r.id) :
    NotesC7BridgeF e := by
  intro p hpf fl hfl sb hsb sl hsl b hb hid hown hidb hscope
  have hnoneF : p.scene.routes.find? (fun r => r.id == (fl.toLabel).owner) = none := by
    rw [List.find?_eq_none]
    intro r hr h
    have heq : r.id = (fl.toLabel).owner := beq_iff_eq.mp h
    exact hNoRouteF p hpf fl hfl r hr heq.symm
  have hnoneR : res.scene.routes.find? (fun r => r.id == (sl.toLabel).owner) = none := by
    rw [List.find?_eq_none]
    intro r hr h
    have heq : r.id = (sl.toLabel).owner := beq_iff_eq.mp h
    exact hNoRouteR sl hsl r hr heq.symm
  have hroutesF : p.scene.layoutDump.routes = p.scene.routes := rfl
  have hnoneF' : p.scene.layoutDump.routes.find? (fun r => r.id == (fl.toLabel).owner) = none := by
    rw [hroutesF]; exact hnoneF
  have hroutesR : res.scene.layoutDump.routes = res.scene.routes := rfl
  have hnoneR' : res.scene.layoutDump.routes.find? (fun r => r.id == (sl.toLabel).owner) = none := by
    rw [hroutesR]; exact hnoneR
  have hF : p.scene.layoutDump.labelOwnerAnc fl.toLabel =
      (fl.toLabel).owner :: p.scene.layoutDump.ancestors (fl.toLabel).owner := by
    unfold LayoutDump.labelOwnerAnc
    rw [hnoneF']
  have hR : res.scene.layoutDump.labelOwnerAnc sl.toLabel =
      (sl.toLabel).owner :: res.scene.layoutDump.ancestors (sl.toLabel).owner := by
    unfold LayoutDump.labelOwnerAnc
    rw [hnoneR']
  rw [hR] at hscope
  rw [hF]
  intro hmem
  rcases List.mem_cons.mp hmem with heq | hmem'
  · exact hscope (List.mem_cons.mpr (Or.inl (hidb.trans (heq.trans hown.symm))))
  · have hsub := hAncF p hpf _ _ hmem'
    have heqA := composeNotes_ancestors_eq e.scene_eq (fl.toLabel).owner
    have hownTO : (sl.toLabel).owner = (fl.toLabel).owner := hown
    have hmemR : b.id ∈ res.scene.layoutDump.ancestors sl.owner := by
      rw [hownTO, heqA, hidb]
      exact hsub
    exact hscope (List.mem_cons.mpr (Or.inr hmemR))

/-- Contracted label scope bridge: the same non-route-arm argument on the
contracted dump, with `hAncC` and `composeNotes_ancestors_eq` carrying the
scope inclusion. -/
theorem ngfC7BridgeC_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hAncC : NotesC6AncC e)
    (hNoRouteC : ∀ cl ∈ e.contracted.scene.labels, ∀ r ∈ e.contracted.scene.routes,
      cl.owner ≠ r.id)
    (hNoRouteR : ∀ sl ∈ res.scene.labels, ∀ r ∈ res.scene.routes, sl.owner ≠ r.id) :
    NotesC7BridgeC e := by
  intro cb hcb cl hcl sl hsl b hb heqsl hidb _hrect hscope
  rw [heqsl] at hsl hscope
  have hnoneC : e.contracted.scene.routes.find? (fun r => r.id == (cl.toLabel).owner) = none := by
    rw [List.find?_eq_none]
    intro r hr h
    have heq : r.id = (cl.toLabel).owner := beq_iff_eq.mp h
    exact hNoRouteC cl hcl r hr heq.symm
  have hnoneR : res.scene.routes.find? (fun r => r.id == (cl.toLabel).owner) = none := by
    rw [List.find?_eq_none]
    intro r hr h
    have heq : r.id = (cl.toLabel).owner := beq_iff_eq.mp h
    exact hNoRouteR cl hsl r hr heq.symm
  have hroutesC : e.contracted.scene.layoutDump.routes = e.contracted.scene.routes := rfl
  have hnoneC' : e.contracted.scene.layoutDump.routes.find?
      (fun r => r.id == (cl.toLabel).owner) = none := by
    rw [hroutesC]; exact hnoneC
  have hroutesR : res.scene.layoutDump.routes = res.scene.routes := rfl
  have hnoneR' : res.scene.layoutDump.routes.find? (fun r => r.id == (cl.toLabel).owner) = none := by
    rw [hroutesR]; exact hnoneR
  have hC : e.contracted.scene.layoutDump.labelOwnerAnc cl.toLabel =
      (cl.toLabel).owner :: e.contracted.scene.layoutDump.ancestors (cl.toLabel).owner := by
    unfold LayoutDump.labelOwnerAnc
    rw [hnoneC']
  have hR : res.scene.layoutDump.labelOwnerAnc cl.toLabel =
      (cl.toLabel).owner :: res.scene.layoutDump.ancestors (cl.toLabel).owner := by
    unfold LayoutDump.labelOwnerAnc
    rw [hnoneR']
  rw [hR] at hscope
  rw [hC]
  intro hmem
  rcases List.mem_cons.mp hmem with heq | hmem'
  · exact hscope (List.mem_cons.mpr (Or.inl (hidb.trans heq)))
  · have hsub := hAncC _ _ hmem'
    have heqA := composeNotes_ancestors_eq e.scene_eq (cl.toLabel).owner
    have hmemR : b.id ∈ res.scene.layoutDump.ancestors (cl.toLabel).owner := by
      rw [heqA, hidb]; exact hsub
    exact hscope (List.mem_cons.mpr (Or.inr hmemR))

/-- Shifted fragment labels clear exclusive contracted boxes: the label lies
in its owner fragment box, which lies in its bundle envelope, disjoint from
the exclusive box by the contracted C2 clause. -/
theorem ngfC7MixedFL_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hLabF : ∀ p ∈ e.fragments, ∀ fl ∈ p.scene.labels, ∃ fb ∈ p.scene.boxes,
      fb.id = fl.owner ∧ fb.rect.Contained fl.rect)
    (hEnvFit : NotesEnvFit e)
    (hBaseC2 : Validator.C2 e.contracted.scene.layoutDump)
    (hAppl : ∀ l ∈ e.layouts, ∀ eb ∈ e.contracted.scene.boxes, eb.id = l.top.id →
      ∀ cb ∈ e.contracted.scene.boxes, cb.exclusive = true →
        eb.id ≠ cb.id ∧ eb.exclusive = true ∧ eb.parent = cb.parent) :
    NotesC7MixedFL e := by
  intro l hl p hpl fl hflmem cb hcbmem hexc
  have hpf : p ∈ e.fragments := by
    rw [e.fragments_eq]
    exact placedOf_mem_flatten e.placed_eq hl hpl
  obtain ⟨fb, hfbmem, _, hcont⟩ := hLabF p hpf fl hflmem
  have hfit := hEnvFit l hl p hpl fb hfbmem
  obtain ⟨eb, heb, hideb, hrectb⟩ := ngf_envelope_mem e hl
  obtain ⟨hne, hexE, hpar⟩ := hAppl l hl eb heb hideb cb hcbmem hexc
  have hC2 := hBaseC2 eb heb cb hcbmem hne hexE hexc hpar
  rw [hrectb] at hC2
  have hshift := (notesShiftRect_contained fb.rect fl.rect p.dx p.dy).mpr hcont
  have hsub := Rect.Contained.trans hfit hshift
  exact ngf_disjoint_of_subset hC2 hsub (Rect.Contained.refl _)

/-- Contracted labels clear shifted fragment boxes: the same envelope
transport with the disjointness stated label-first. -/
theorem ngfC7MixedLF_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hEnvFit : NotesEnvFit e)
    (hLabC : ∀ cl ∈ e.contracted.scene.labels, ∃ cb ∈ e.contracted.scene.boxes,
      cb.id = cl.owner ∧ cb.rect.Contained cl.rect)
    (hBaseC2 : Validator.C2 e.contracted.scene.layoutDump)
    (hAppl : ∀ l ∈ e.layouts, ∀ eb ∈ e.contracted.scene.boxes, eb.id = l.top.id →
      ∀ cl ∈ e.contracted.scene.labels, ∀ cb ∈ e.contracted.scene.boxes,
        cb.id = cl.owner →
        eb.id ≠ cb.id ∧ eb.exclusive = true ∧ cb.exclusive = true ∧ eb.parent = cb.parent) :
    NotesC7MixedLF e := by
  intro l hl p hpl sb hsb cl hcl
  obtain ⟨eb, heb, hideb, hrectb⟩ := ngf_envelope_mem e hl
  obtain ⟨cb, hcb, hidcb, hcont⟩ := hLabC cl hcl
  obtain ⟨hne, hexE, hexC, hpar⟩ := hAppl l hl eb heb hideb cl hcl cb hcb hidcb
  have hC2 := hBaseC2 eb heb cb hcb hne hexE hexC hpar
  rw [hrectb] at hC2
  have hfit := hEnvFit l hl p hpl sb hsb
  exact (Disjoint.comm _ _).mp (ngf_disjoint_of_subset hC2 hfit hcont)

/-- Labels and boxes of distinct placed fragments are pairwise disjoint:
the label lies in its owner box of its own fragment. -/
theorem ngfC7Cross_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hLabF : ∀ p ∈ e.fragments, ∀ fl ∈ p.scene.labels, ∃ fb ∈ p.scene.boxes,
      fb.id = fl.owner ∧ fb.rect.Contained fl.rect)
    (hPlacedDisj : NotesPlacedDisjoint e) :
    NotesC7Cross e := by
  intro p hpf q hqf hne fl hflmem sb hsbmem
  obtain ⟨fb, hfbmem, _, hcont⟩ := hLabF p hpf fl hflmem
  have hdisj := hPlacedDisj p hpf q hqf hne fb hfbmem sb hsbmem
  have hsub := (notesShiftRect_contained fb.rect fl.rect p.dx p.dy).mpr hcont
  exact ngf_disjoint_of_subset hdisj hsub (Rect.Contained.refl _)

/-- The full C7 geometric context from local premises only: exclusivity
from the box mirrors, owner preservation from label identity, scopes from
the ancestor bridges, and the three separations through envelope
containment and contracted C2. -/
theorem ngfC7Geom_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hMirrorC : NotesContractMirror e)
    (hMirrorF : NotesFragMirror e)
    (hnd : (inp.boxes.map (·.id)).Nodup)
    (hLabNodup : ∀ p ∈ e.fragments, ∀ q ∈ e.fragments, ∀ fl ∈ p.scene.labels,
      ∀ gl ∈ q.scene.labels, fl.id = gl.id → fl = gl)
    (hAncF : NotesC6AncF e)
    (hNoRouteF : ∀ p ∈ e.fragments, ∀ fl ∈ p.scene.labels, ∀ r ∈ p.scene.routes,
      fl.owner ≠ r.id)
    (hNoRouteR : ∀ sl ∈ res.scene.labels, ∀ r ∈ res.scene.routes, sl.owner ≠ r.id)
    (hAncC : NotesC6AncC e)
    (hNoRouteC : ∀ cl ∈ e.contracted.scene.labels, ∀ r ∈ e.contracted.scene.routes,
      cl.owner ≠ r.id)
    (hLabF : ∀ p ∈ e.fragments, ∀ fl ∈ p.scene.labels, ∃ fb ∈ p.scene.boxes,
      fb.id = fl.owner ∧ fb.rect.Contained fl.rect)
    (hLabC : ∀ cl ∈ e.contracted.scene.labels, ∃ cb ∈ e.contracted.scene.boxes,
      cb.id = cl.owner ∧ cb.rect.Contained cl.rect)
    (hEnvFit : NotesEnvFit e)
    (hBaseC2 : Validator.C2 e.contracted.scene.layoutDump)
    (hApplFL : ∀ l ∈ e.layouts, ∀ eb ∈ e.contracted.scene.boxes, eb.id = l.top.id →
      ∀ cb ∈ e.contracted.scene.boxes, cb.exclusive = true →
        eb.id ≠ cb.id ∧ eb.exclusive = true ∧ eb.parent = cb.parent)
    (hApplLF : ∀ l ∈ e.layouts, ∀ eb ∈ e.contracted.scene.boxes, eb.id = l.top.id →
      ∀ cl ∈ e.contracted.scene.labels, ∀ cb ∈ e.contracted.scene.boxes,
        cb.id = cl.owner →
        eb.id ≠ cb.id ∧ eb.exclusive = true ∧ cb.exclusive = true ∧ eb.parent = cb.parent)
    (hPlacedDisj : NotesPlacedDisjoint e) :
    NotesC7Geom e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ngfC6BoxExclC_holds e hMirrorC hnd
  · exact ngfC6BoxExclF_holds e hMirrorF hnd
  · exact ngfC7OwnF_holds e hLabNodup
  · exact ngfC7BridgeF_holds e hAncF hNoRouteF hNoRouteR
  · exact ngfC7BridgeC_holds e hAncC hNoRouteC hNoRouteR
  · exact ngfC7MixedFL_holds e hLabF hEnvFit hBaseC2 hApplFL
  · exact ngfC7MixedLF_holds e hEnvFit hLabC hBaseC2 hApplLF
  · exact ngfC7Cross_holds e hLabF hPlacedDisj

/-! ### C8a: the conjuncts that close from the same facts -/

/-- Every placed fragment box has an input box with its id and role
(C8a shape): existence from `NotesFragMirror`, roles from the narrow
premise. -/
theorem ngfC8aFragRole_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hMirror : NotesFragMirror e)
    (hRole : ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      ∀ sb ∈ p.scene.boxes, ∀ ib ∈ inp.boxes, sb.id = ib.id → sb.role = ib.role.id) :
    NotesC8aFragRole e := by
  intro l hl p hpl sb hsb
  obtain ⟨ib, hib, hid, _, _, _⟩ := hMirror l hl p hpl sb hsb
  exact ⟨ib, hib, hid.symm, (hRole l hl p hpl sb hsb ib hib hid).symm⟩

/-- Every contracted box has an input box with its id and role (C8a
find-shape): existence from `NotesContractMirror`, roles from the narrow
premise, identity from the find equation. -/
theorem ngfC8aContractRole_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hMirror : NotesContractMirror e)
    (hRole : ∀ cb ∈ e.contracted.scene.boxes, ∀ ib ∈ inp.boxes,
      cb.id = ib.id → cb.role = ib.role.id) :
    NotesC8aContractRole e := by
  intro cg hcg
  obtain ⟨ib, hib, hid, _, _⟩ := hMirror cg hcg
  have hpred : (fun b : ModelBox => b.id == cg.id) ib = true := by simp [← hid]
  obtain ⟨jb, hfound⟩ := ngf_find?_some_of_mem (fun b : ModelBox => b.id == cg.id) hib hpred
  have hjb := List.mem_of_find?_eq_some hfound
  have hidj := List.find?_some hfound
  simp only [beq_iff_eq] at hidj
  exact ⟨jb, hfound, (hRole cg hcg jb hjb hidj.symm).symm⟩

/-- Shifted boxes of distinct placed scenes of one bundle are pairwise
disjoint: the global placed-separation fact restricted through
flatten membership. -/
theorem ngfC8aFragDisj_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hPlacedDisj : NotesPlacedDisjoint e) :
    NotesC8aFragDisj e := by
  intro l hl p hpl p' hpl' sg hsg sb hsb hne hneid
  have hpf : p ∈ e.fragments := by
    rw [e.fragments_eq]
    exact placedOf_mem_flatten e.placed_eq hl hpl
  have hpf' : p' ∈ e.fragments := by
    rw [e.fragments_eq]
    exact placedOf_mem_flatten e.placed_eq hl hpl'
  exact hPlacedDisj p hpf p' hpf' hne sg hsg sb hsb

/-- Shifted fragment boxes clear contracted boxes no bundle owns: the
foreign-clearance fact via the id bridge (a `fragmentIdOf`-false box is
claimed by no fragment). -/
theorem ngfC8aClear_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hForeign : NotesForeignClear e)
    (hBridge : ∀ l ∈ e.layouts, ∀ cb ∈ e.contracted.scene.boxes,
      fragmentIdOf inp l cb.id = false →
      ∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r) :
    NotesC8aClear e := by
  intro l hl p hpl sb hsb cb hcb hfrag
  exact hForeign l hl p hpl sb hsb cb hcb (hBridge l hl cb hcb hfrag)

/-- Envelopes of distinct bundles are pairwise disjoint: the two footprint
boxes in the contracted scene, separated by the contracted C2 clause (the
same transport as the cross-layout placed case). -/
theorem ngfC8aEnvDisj_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBaseC2 : Validator.C2 e.contracted.scene.layoutDump)
    (hAppl : ∀ a ∈ e.layouts, ∀ b ∈ e.layouts, a.top.id ≠ b.top.id →
      ∀ ea ∈ e.contracted.scene.boxes, ea.id = a.top.id →
      ∀ eb ∈ e.contracted.scene.boxes, eb.id = b.top.id →
        ea.id ≠ eb.id ∧ ea.exclusive = true ∧ eb.exclusive = true ∧ ea.parent = eb.parent) :
    NotesC8aEnvDisj e := by
  intro a ha b hb hne
  obtain ⟨ea, hea, hidea, hrecta⟩ := ngf_envelope_mem e ha
  obtain ⟨eb, heb, hideb, hrectb⟩ := ngf_envelope_mem e hb
  obtain ⟨hne', hexA, hexB, hpar⟩ := hAppl a ha b hb hne ea hea hidea eb heb hideb
  have hC2 := hBaseC2 ea hea eb heb hne' hexA hexB hpar
  rw [hrecta, hrectb] at hC2
  exact hC2

end PipelineImpl
end Layered
end Elegant


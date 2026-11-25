import Elegant.Layered.NotesFlatBoxClauses
import Elegant.Layered.RecursiveFit
import Elegant.Layered.SelectFacts
import Elegant.Layered.NotesFlatLabelClauses

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Id and parent bookkeeping for the note stage.

Over `e : NotesExecution base exactIds fuel inp o res` this module discharges
the seven residual defs of `NotesFlatBoxClauses.lean` as theorems named
`<defName>_holds` (lower-case first letter):
`NotesContractMirror`, `NotesFragMirror`, `NotesParentAlign`, `NotesParentLocal`,
`NotesKeptClosed`, `NotesContractBoxEq`, `NotesFragBoxEq`.

Truth evidence (TRUTH FIRST): every def and every premise below was evaluated
with `#eval` in `proofs/wip/Probe/NotesMirrorFactsT_probe.lean` on six inputs:
a note on a state, a note on a composite state, two notes on one state, a note
with empty text, a note target nested under a group (`nmxNested`), and a note
box parented under a group while its target is rootless (`nmxNested` is the
nested-target input; `nmxNoteParent` the parented-note input). All seven defs
and all five premises below are `true` on the four author inputs. `nmxNested`
fails with `LayoutError.domain`, so it yields no execution. `nmxNoteParent`
succeeds and falsifies exactly the two shapes that need narrowing premises
plus those premises: `fragMirror = false`, `parentAlign = false`,
`fragRoots = false`, `notePar = false`, everything else `true`
(`contractMirror`, `parentLocal`, `keptClosed`, both `boxEq`, `baseContract`,
`baseFrag`, `keptPar`). The id lists of `baseContract`/`baseFrag` were checked
directly; their triple (id/parent/exclusive) halves replay the author's probe
(`nbxMirror` parent checks on part and note scenes, `nbxResid` `exclF`/`exclC`),
all `true` on the four author inputs.

Falsifiers recorded (narrowing premises are load-bearing, not stylistic):
* `NotesFragMirror` without `NotesFragRoots`: `nmxNoteParent` executes; the
  note box `S1.note` has parent `"G"` in the input, while `subInput` clears the
  note parent, so the executed note scene box has parent `""`.
* `NotesParentAlign` without `NotesBundleNoteParent`: same execution; the note
  parent `"G"` differs from the top parent `""`.
* `NotesKeptClosed` without `NotesKeptParent`: no succeeding execution in the
  probe falsifies it, and it is unprovable from base preservation alone: a kept
  box with a dangling (or fragment-owned) parent is absent from no execution
  hypothesis, and `inside` is state-relative, so the fold-removal argument does
  not transport across `contractOne` steps. The premise states parent closure
  on the contracted input, which is strictly narrower than res validity.
-/

/-- Base id/parent/flag preservation on the contracted input, in the style of
`XB_layout_ids` (`ExactStepFacts.lean`): the executed contracted scene carries
exactly the contracted-input ids, and every contracted box mirrors a
contracted-input box in id, parent, and exclusivity. -/
def NotesBaseContract {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  e.contracted.scene.boxes.map (·.id) = e.contractedInput.boxes.map (·.id) ∧
    ∀ cb ∈ e.contracted.scene.boxes, ∃ mb ∈ e.contractedInput.boxes,
      cb.id = mb.id ∧ cb.parent = mb.parent ∧ cb.exclusive = mb.exclusive

/-- Executed-scene id/parent/flag preservation on every fragment input, in the
style of `XB_layout_ids` (`ExactStepFacts.lean`): each executed part scene
carries exactly its fragment-input ids with mirrored id, parent, and
exclusivity (the part run is the recursive `layoutNotes` call, the note runs
are `base`), and likewise for every executed per-note scene. -/
def NotesBaseFrag {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts,
    ((l.part.scene.boxes.map (·.id) =
        (subInput inp (fun x => x.id == l.top.id ||
          Compound.inside inp.boxes l.top.id x.id) l.top.id).boxes.map (·.id)) ∧
      ∀ sb ∈ l.part.scene.boxes,
        ∃ mb ∈ (subInput inp (fun x => x.id == l.top.id ||
          Compound.inside inp.boxes l.top.id x.id) l.top.id).boxes,
          sb.id = mb.id ∧ sb.parent = mb.parent ∧ sb.exclusive = mb.exclusive) ∧
    ∀ q ∈ l.notes,
      ((q.2.scene.boxes.map (·.id) =
        (subInput inp (fun x => x.id == q.1.id) q.1.id).boxes.map (·.id)) ∧
        ∀ sb ∈ q.2.scene.boxes,
          ∃ mb ∈ (subInput inp (fun x => x.id == q.1.id) q.1.id).boxes,
            sb.id = mb.id ∧ sb.parent = mb.parent ∧ sb.exclusive = mb.exclusive)

/-- The placed part selects the bundle top and its descendants; a placed note
selects only its own input box. Both contain their selected root, whose parent
is cleared in the fragment. All other part boxes retain their input parent. -/
def NotesFragMirrorT {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    (p.scene = l.part.scene ∧ l.top ∈ inp.boxes ∧
      (∃ root ∈ p.scene.boxes, root.id = l.top.id) ∧
      ∀ sb ∈ p.scene.boxes, ∃ ib ∈ inp.boxes,
        sb.id = ib.id ∧ sb.exclusive = ib.exclusive ∧
        (sb.id = l.top.id ∨ Compound.inside inp.boxes l.top.id sb.id = true) ∧
        sb.parent = (if sb.id = l.top.id then "" else ib.parent)) ∨
    ∃ q ∈ l.notes, p.scene = q.2.scene ∧ q.1 ∈ inp.boxes ∧
      (∃ root ∈ p.scene.boxes, root.id = q.1.id) ∧
      ∀ sb ∈ p.scene.boxes, sb.id = q.1.id ∧ sb.exclusive = q.1.exclusive ∧ sb.parent = ""

/-- Parent-independent input provenance for placed fragment boxes. -/
def NotesFragIdExcl {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    ∀ sb ∈ p.scene.boxes, ∃ ib ∈ inp.boxes, sb.id = ib.id ∧ sb.exclusive = ib.exclusive

/-- Fragment roots: every bundle top and every bundle note box is rootless in
the input. `subInput` clears the top/note parent, so the executed fragment
scenes carry `""` there; without this the scene/input parents disagree. -/
def NotesFragRoots {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts,
    (∀ b ∈ inp.boxes, b.id = l.top.id → b.parent = "") ∧
      ∀ q ∈ l.notes, q.1.parent = ""

/-- Bundle note alignment: every bundle note shares its top's parent. The
layout reads both boxes from the input without constraining their parents. -/
def NotesBundleNoteParent {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ q ∈ l.notes, q.1.parent = l.top.parent

/-- Contracted-input parent closure outside fragments: every contracted-input
box is rootless or has a contracted-input parent witness whose id sits in no
fragment. The scene-level `NotesKeptClosed` follows by id rewriting. -/
def NotesKeptParent {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ kb ∈ e.contractedInput.boxes,
    kb.parent = "" ∨
      ∃ kpb ∈ e.contractedInput.boxes,
        kpb.id = kb.parent ∧
          (∀ q ∈ e.fragments, ∀ r : Rect, q.rect kb.parent ≠ some r)

/-! ### Private list plumbing (prefixed copies: other modules' privates do not resolve) -/

private theorem nmf_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- Membership in a successful `mapM` gives a successful per-element run. -/
private theorem nmf_mapM_ok_of_mem {α β : Type} {f : α → Except LayoutError β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ {a : α}, a ∈ xs →
      ∃ b, f a = .ok b
  | [], _, _, _, ha => by simp at ha
  | _ :: _, _, h, _, ha => by
    simp only [List.mem_cons] at ha
    simp only [List.mapM_cons, bind, Except.bind] at h
    obtain ⟨b, hfb, h⟩ := nmf_bind_ok h
    obtain ⟨bs, hbs, _⟩ := nmf_bind_ok h
    rcases ha with rfl | ha'
    · exact ⟨b, hfb⟩
    · exact nmf_mapM_ok_of_mem hbs ha'

/-- Membership in a successful `mapM` gives a successful per-element run with
the value. -/
private theorem nmf_mapM_mem {α β : Type} {f : α → Except LayoutError β} :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h, _, hy => by
    have h2 : ([] : List β) = ys := by simpa [List.mapM_nil, pure, Except.pure] using h
    subst h2
    cases hy
  | _ :: _, ys, h, y, hy => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    obtain ⟨b, hfb, h⟩ := nmf_bind_ok h
    obtain ⟨bs, hbs, h⟩ := nmf_bind_ok h
    have hys : b :: bs = ys := Except.ok.inj h
    subst hys
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨_, List.mem_cons_self, hfb⟩
    · obtain ⟨x, hx, hfx⟩ := nmf_mapM_mem _ bs hbs y hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- Witness extraction from a successful `findSome?`. -/
private theorem nmf_findSome?_exists {α β : Type} (f : α → Option β) :
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
      obtain ⟨x, hx, hfx⟩ := nmf_findSome?_exists f rest _ h
      exact ⟨x, List.mem_cons_of_mem a hx, hfx⟩

/-- Equal images under `·.id` of two members of an id-duplicate-free model-box
list force the members to be equal. -/
private theorem nmf_nodup_id_inj :
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
      · exact nmf_nodup_id_inj _ h.2 ha' hb' e

/-- Equal images under `·.id` of two members of an id-duplicate-free dump-box
list force the members to be equal. -/
private theorem nmf_box_nodup_id_inj :
    ∀ (l : List Box), (l.map (·.id)).Nodup →
      ∀ {a b : Box}, a ∈ l → b ∈ l → a.id = b.id → a = b
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
      · exact nmf_box_nodup_id_inj _ h.2 ha' hb' e

/-- A `find?` hit on an id-unique list names the member with that id. -/
private theorem nmf_find?_unique {α : Type} (f : α → String) :
    ∀ (l : List α), (l.map f).Nodup → ∀ (x : α), x ∈ l → ∀ v, f x = v →
      l.find? (fun a => f a == v) = some x := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons c cs ih =>
    intro hnd x hx v hv
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    cases hx with
    | head =>
      simp [hv]
    | tail _ hx' =>
      have hfx : f x ∈ cs.map f := List.mem_map.mpr ⟨x, hx', rfl⟩
      by_cases hcv : (f c == v) = true
      · exact absurd (by
          have hce : f c = v := beq_iff_eq.mp hcv
          rw [show f c = f x from hce.trans hv.symm]
          exact hfx) hnot
      · simp only [List.find?_cons, hcv]
        exact ih hnd' x hx' v hv

/-- A `findIdx?` hit exposes the index and the predicate witness. -/
private theorem nmf_findIdx_lookup {α : Type} {p : α → Bool}
    {l : List α} {n : Nat} (h : l.findIdx? p = some n) :
    n < l.length ∧ ∃ a, l[n]? = some a ∧ p a = true := by
  induction l generalizing n with
  | nil =>
    rw [List.findIdx?_nil] at h
    exact absurd h (by simp)
  | cons a as ih =>
    rw [List.findIdx?_cons] at h
    by_cases hp : p a = true
    · rw [ite_eq_left hp] at h
      have hn : n = 0 := (Option.some.inj h).symm
      subst hn
      exact ⟨Nat.zero_lt_succ _, a, rfl, hp⟩
    · rw [ite_eq_right hp] at h
      obtain ⟨m, hmfind, hmn⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hmlen, x, hxget, hpx⟩ := ih hmfind
      rw [← hmn]
      exact ⟨Nat.succ_lt_succ hmlen, x, (List.getElem?_cons_succ).trans hxget, hpx⟩

/-! ### `subInput` / `contractOne` membership and id uniqueness -/

/-- Membership in a `subInput` box list: the member comes from an input box
satisfying `keep`, with id and exclusivity kept and the parent kept except for
the cleared root. -/
private theorem nmf_subInput_mem {inp : Input} {keep : ModelBox → Bool} {root : String}
    {x : ModelBox} (hx : x ∈ (subInput inp keep root).boxes) :
    ∃ ib ∈ inp.boxes, keep ib = true ∧ ib.id = x.id ∧ x.exclusive = ib.exclusive ∧
      ((x.id = root ∧ x.parent = "") ∨ (x.id ≠ root ∧ x.parent = ib.parent)) := by
  have hsub : (subInput inp keep root).boxes =
      ((selectInput inp keep).boxes.map fun b =>
        if b.id == root then { b with parent := "" } else b) := rfl
  rw [hsub, List.mem_map] at hx
  obtain ⟨y, hym, hxy⟩ := hx
  have hsel : (selectInput inp keep).boxes =
      ((inp.boxes.zipIdx.filter fun q => keep q.1).map fun q =>
        if q.1.parent == "" then { q.1 with parent := "" } else q.1) := rfl
  rw [hsel, List.mem_map] at hym
  obtain ⟨q, hqf, hyq⟩ := hym
  have hqz : q ∈ inp.boxes.zipIdx := (List.mem_filter.mp hqf).1
  have hmem : q.1 ∈ inp.boxes := List.fst_mem_of_mem_zipIdx hqz
  have hk : keep q.1 = true := List.mem_filter.mp hqf |>.2
  have hyid : y.id = q.1.id := by
    rw [← hyq]
    by_cases h : (q.1.parent == "") = true
    · have hp : q.1.parent = "" := beq_iff_eq.mp h
      simp [hp]
    · simp [h]
  have hypar : y.parent = q.1.parent := by
    rw [← hyq]
    by_cases h : (q.1.parent == "") = true
    · have hp : q.1.parent = "" := beq_iff_eq.mp h
      simp [hp]
    · simp [h]
  have hyexc : y.exclusive = q.1.exclusive := by
    rw [← hyq]
    by_cases h : (q.1.parent == "") = true
    · have hp : q.1.parent = "" := beq_iff_eq.mp h
      simp [hp]
    · simp [h]
  have hxid : x.id = y.id := by
    rw [← hxy]
    by_cases h : (y.id == root) = true
    · have hr : y.id = root := beq_iff_eq.mp h
      simp [hr]
    · simp [h]
  have hxexc : x.exclusive = y.exclusive := by
    rw [← hxy]
    by_cases h : (y.id == root) = true
    · have hr : y.id = root := beq_iff_eq.mp h
      simp [hr]
    · simp [h]
  refine ⟨q.1, hmem, hk, hyid.symm.trans hxid.symm, hxexc.trans hyexc, ?_⟩
  by_cases h : (y.id == root) = true
  · left
    have hr : y.id = root := beq_iff_eq.mp h
    have hxp : x.parent = "" := by rw [← hxy]; simp [hr]
    exact ⟨hxid.trans hr, hxp⟩
  · right
    have hxp : x.parent = y.parent := by rw [← hxy]; simp [h]
    have hne : x.id ≠ root := fun he => h (beq_iff_eq.mpr (hxid.symm.trans he))
    exact ⟨hne, hxp.trans hypar⟩

/-- Membership in a `contractOne` box list: the member mirrors an input box in
id, parent, and exclusivity (the step only shrinks the target's role). -/
private theorem nmf_contractOne_mem3 (inp : Input) (l : BundleLayout)
    {x : ModelBox} (hx : x ∈ (contractOne inp l).boxes) :
    ∃ ib ∈ inp.boxes, ib.id = x.id ∧ ib.parent = x.parent ∧ ib.exclusive = x.exclusive := by
  simp only [contractOne, List.mem_map, List.mem_filter] at hx
  obtain ⟨q, hq, hxq⟩ := hx
  obtain ⟨hz, _⟩ := hq
  obtain ⟨_, hlt, hxeq⟩ := List.mem_zipIdx hz
  have hqmem : q.1 ∈ inp.boxes := by
    have hidx : q.2 - 0 < inp.boxes.length := by omega
    rw [hxeq]
    exact List.getElem_mem hidx
  subst hxq
  split
  · exact ⟨q.1, hqmem, rfl, rfl, rfl⟩
  · exact ⟨q.1, hqmem, rfl, rfl, rfl⟩

/-- Membership in a folded `contractOne` box list: every surviving box mirrors
an input box in id, parent, and exclusivity. -/
private theorem nmf_contractFold_mem3 (inp : Input) (layouts : List BundleLayout)
    {x : ModelBox} (hx : x ∈ (layouts.foldl contractOne inp).boxes) :
    ∃ ib ∈ inp.boxes, ib.id = x.id ∧ ib.parent = x.parent ∧ ib.exclusive = x.exclusive := by
  induction layouts generalizing inp with
  | nil =>
    simp only [List.foldl_nil] at hx
    exact ⟨x, hx, rfl, rfl, rfl⟩
  | cons l rest ih =>
    rw [List.foldl_cons] at hx
    obtain ⟨y, hym, hid, hpar, hexc⟩ := ih _ hx
    obtain ⟨ib, hib, hid2, hpar2, hexc2⟩ := nmf_contractOne_mem3 _ _ hym
    exact ⟨ib, hib, hid2.trans hid, hpar2.trans hpar, hexc2.trans hexc⟩

/-- Every input box satisfying `keep` has its cleared image in the `subInput`
box list. -/
private theorem nmf_subInput_image {inp : Input} {keep : ModelBox → Bool} {root : String}
    (hnd : (inp.boxes.map (·.id)).Nodup)
    {ib : ModelBox} (hib : ib ∈ inp.boxes) (hk : keep ib = true) :
    ∃ x ∈ (subInput inp keep root).boxes, x.id = ib.id ∧
      x.parent = (if ib.id == root then "" else ib.parent) ∧ x.exclusive = ib.exclusive := by
  have hsel : ib.id ∈ (selectInput inp keep).boxes.map (·.id) := by
    rw [selectInput_box_ids]
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hib, hk⟩)
  obtain ⟨y, hym, hyid⟩ := List.mem_map.mp hsel
  have hsel2 : (selectInput inp keep).boxes =
      ((inp.boxes.zipIdx.filter fun q => keep q.1).map fun q =>
        if q.1.parent == "" then { q.1 with parent := "" } else q.1) := rfl
  have hym0 : y ∈ (selectInput inp keep).boxes := hym
  rw [hsel2, List.mem_map] at hym
  obtain ⟨q, hqf, hyq⟩ := hym
  have hqmem : q.1 ∈ inp.boxes :=
    List.fst_mem_of_mem_zipIdx (List.mem_filter.mp hqf |>.1)
  have hdemid : (if q.1.parent == "" then { q.1 with parent := "" } else q.1).id = q.1.id := by
    by_cases h : (q.1.parent == "") = true
    · have hp : q.1.parent = "" := beq_iff_eq.mp h
      simp [hp]
    · simp [h]
  have hqid : q.1.id = ib.id := by
    have h1 : y.id = q.1.id := by rw [← hyq]; exact hdemid
    exact h1.symm.trans hyid
  have hqib : q.1 = ib := nmf_nodup_id_inj _ hnd hqmem hib hqid
  have hyib : y = (if ib.parent == "" then { ib with parent := "" } else ib) := by
    rw [← hqib]
    exact hyq.symm
  have hypar : y.parent = ib.parent := by
    rw [hyib]
    by_cases h : (ib.parent == "") = true
    · have hp : ib.parent = "" := beq_iff_eq.mp h
      simp [hp]
    · simp [h]
  have hyexc : y.exclusive = ib.exclusive := by
    rw [hyib]
    by_cases h : (ib.parent == "") = true
    · have hp : ib.parent = "" := beq_iff_eq.mp h
      simp [hp]
    · simp [h]
  refine ⟨(if y.id == root then { y with parent := "" } else y), ?_, ?_, ?_, ?_⟩
  · have hsub : (subInput inp keep root).boxes =
        ((selectInput inp keep).boxes.map fun b =>
          if b.id == root then { b with parent := "" } else b) := rfl
    rw [hsub]
    exact List.mem_map.mpr ⟨y, hym0, rfl⟩
  · rw [show (y.id == root) = (ib.id == root) from by rw [hyid]]
    by_cases h : (ib.id == root) = true
    · simp [h, hyid]
    · simp [h, hyid]
  · rw [show (y.id == root) = (ib.id == root) from by rw [hyid]]
    by_cases h : (ib.id == root) = true
    · simp [h]
    · simp [h, hypar]
  · rw [show (y.id == root) = (ib.id == root) from by rw [hyid]]
    by_cases h : (ib.id == root) = true
    · simp [h, hyexc]
    · simp [h, hyexc]

/-! ### Id uniqueness through the note stage -/

/-- Filtered id lists stay duplicate-free. -/
private theorem nmf_filter_ids_nodup (boxes : List ModelBox) (keep : ModelBox → Bool)
    (hnd : (boxes.map (·.id)).Nodup) : ((boxes.filter keep).map (·.id)).Nodup :=
  List.Nodup.sublist ((List.filter_sublist).map _) hnd

/-- The kept-pair id list is the filtered input id list. -/
private theorem nmf_zipIdx_ids (inp : Input) (keep : ModelBox → Bool) :
    ((inp.boxes.zipIdx.filter fun q => keep q.1).map fun q => q.1.id) =
      (inp.boxes.filter keep).map (·.id) :=
  zipIdx_filter_map_fst keep (·.id) inp.boxes 0

/-- `contractOne` keeps duplicate-free ids. -/
private theorem nmf_contractOne_nodup (inp : Input) (l : BundleLayout)
    (hnd : (inp.boxes.map (·.id)).Nodup) :
    ((contractOne inp l).boxes.map (·.id)).Nodup := by
  have hid : ∀ q : ModelBox × Nat,
      ((if q.1.id == l.top.id then { q.1 with role := .node, direction := "" } else q.1).id) =
        q.1.id := by
    intro q
    by_cases h : (q.1.id == l.top.id) = true
    · have ht : q.1.id = l.top.id := beq_iff_eq.mp h
      simp [ht]
    · simp [h]
  have hcongr : ((contractOne inp l).boxes.map (·.id)) =
      ((inp.boxes.zipIdx.filter fun q =>
        !(Compound.inside inp.boxes l.top.id q.1.id ||
          (l.notes.map (·.1.id)).contains q.1.id)).map fun q => q.1.id) := by
    unfold contractOne
    simp only [List.map_map]
    apply List.map_congr_left
    intro q _
    exact hid q
  rw [hcongr]
  have hzip : (((inp.boxes.zipIdx.filter fun q =>
      !(Compound.inside inp.boxes l.top.id q.1.id ||
        (l.notes.map (·.1.id)).contains q.1.id)).map fun q => q.1.id)) =
      (((inp.boxes.filter fun b =>
        !(Compound.inside inp.boxes l.top.id b.id ||
          (l.notes.map (·.1.id)).contains b.id)).map (·.id))) :=
    zipIdx_filter_map_fst (fun b => !(Compound.inside inp.boxes l.top.id b.id ||
      (l.notes.map (·.1.id)).contains b.id)) (fun b => b.id) inp.boxes 0
  rw [hzip]
  exact nmf_filter_ids_nodup _ _ hnd

/-- Folded `contractOne` keeps duplicate-free ids. -/
private theorem nmf_contractFold_nodup (inp : Input) (layouts : List BundleLayout)
    (hnd : (inp.boxes.map (·.id)).Nodup) :
    (((layouts.foldl contractOne inp).boxes.map (·.id))).Nodup := by
  induction layouts generalizing inp with
  | nil =>
    simp only [List.foldl_nil]
    exact hnd
  | cons l rest ih =>
    rw [List.foldl_cons]
    exact ih _ (nmf_contractOne_nodup _ _ hnd)

/-- `subInput` keeps duplicate-free ids. -/
private theorem nmf_subInput_nodup (inp : Input) (keep : ModelBox → Bool) (root : String)
    (hnd : (inp.boxes.map (·.id)).Nodup) :
    (((subInput inp keep root).boxes.map (·.id))).Nodup := by
  have hid : ∀ b : ModelBox,
      ((if b.id == root then { b with parent := "" } else b).id) = b.id := by
    intro b
    by_cases h : (b.id == root) = true
    · have ht : b.id = root := beq_iff_eq.mp h
      simp [ht]
    · simp [h]
  have hcongr : (((subInput inp keep root).boxes.map (·.id))) =
      ((selectInput inp keep).boxes.map (·.id)) := by
    unfold subInput
    simp only [List.map_map]
    apply List.map_congr_left
    intro b _
    exact hid b
  rw [hcongr, selectInput_box_ids]
  exact nmf_filter_ids_nodup _ _ hnd

/-! ### Bundle-layout inversion: tops and notes come from the input -/

/-- Inverting one executed `bundleLayout`: the top and every note box come
from the input boxes. -/
private theorem nmf_bundleLayout_mem {recur base : Input → Options → Except LayoutError FamilyResult}
    {inp : Input} {o : Options} {margin gap : Int} {b : Bundle} {l : BundleLayout}
    (h : bundleLayout recur base inp o margin gap b = .ok l) :
    l.top ∈ inp.boxes ∧ ∀ q ∈ l.notes, q.1 ∈ inp.boxes := by
  unfold bundleLayout at h
  cases hb : inp.boxes[b.target]? with
  | none =>
    rw [hb] at h
    simp at h
  | some top =>
    rw [hb] at h
    simp only [bind, Except.bind] at h
    obtain ⟨part, hpart, h⟩ := nmf_bind_ok h
    obtain ⟨notes, hnotes, h⟩ := nmf_bind_ok h
    have hl : l = ⟨top, b, part, notes, _⟩ := (Except.ok.inj h).symm
    have htop : l.top = top := by rw [hl]
    have hnotes' : l.notes = notes := by rw [hl]
    have htopmem : top ∈ inp.boxes := by
      obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp hb
      rw [← heq]
      exact List.getElem_mem hi
    refine ⟨by rw [htop]; exact htopmem, ?_⟩
    intro q hq
    rw [hnotes'] at hq
    obtain ⟨a, ham, haq⟩ := nmf_mapM_mem _ _ hnotes q hq
    cases hbox : inp.boxes[a.note]? with
    | none =>
      rw [hbox] at haq
      simp at haq
    | some box =>
      rw [hbox] at haq
      obtain ⟨r, hr, hqr⟩ := nmf_bind_ok haq
      have hq1 : q.1 = box := by
        have hqq := Except.ok.inj hqr
        exact (congrArg Prod.fst hqq).symm
      rw [hq1]
      obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp hbox
      rw [← heq]
      exact List.getElem_mem hi

/-- Every executed layout's top and note boxes come from the input boxes. -/
private theorem nmf_layout_mem {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) {l : BundleLayout} (hl : l ∈ e.layouts) :
    l.top ∈ inp.boxes ∧ ∀ q ∈ l.notes, q.1 ∈ inp.boxes := by
  obtain ⟨b, hbm, hbl⟩ := nmf_mapM_mem _ _ e.layouts_eq l hl
  exact nmf_bundleLayout_mem hbl
def NotesBoxMirror (inp : Input) (res : FamilyResult) : Prop :=
  res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
    ∀ sb ∈ res.scene.boxes, ∃ mb ∈ inp.boxes,
      sb.id = mb.id ∧ sb.parent = mb.parent ∧ sb.exclusive = mb.exclusive ∧ sb.role = mb.role.id

theorem layoutNotes_boxes_mirror
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (hbase : ∀ ids inp o res, base ids inp o = .ok res → NotesBoxMirror inp res)
    (fuel : Nat) {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutNotes base exactIds fuel inp o = .ok res) : NotesBoxMirror inp res := by
  cases fuel with
  | zero => exact hbase exactIds inp o res h
  | succ fuel =>
    rcases layoutNotes_success_phases h with ⟨_, hleaf⟩ | hexecution
    · exact hbase exactIds inp o res hleaf
    · obtain ⟨execution⟩ := hexecution
      constructor
      · exact execution.boxes_ids
      · intro sb hsb
        obtain ⟨mb, hmb, hid, hrole, hparent, hexcl, _⟩ := execution.boxes_mem sb hsb
        exact ⟨mb, hmb, hid, hparent, hexcl, hrole⟩

private theorem notesFragment_mirror
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {Mirror : Input → FamilyResult → Prop}
    (hbase : ∀ ids inp o res, base ids inp o = .ok res → Mirror inp res)
    (hpreserve : ∀ fuel {ids inp o res}, layoutNotes base ids fuel inp o = .ok res → Mirror inp res)
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) :
    ∀ l ∈ e.layouts,
      Mirror (subInput inp (fun x => x.id == l.top.id ||
        Compound.inside inp.boxes l.top.id x.id) l.top.id) l.part ∧
      ∀ q ∈ l.notes, Mirror (subInput inp (fun x => x.id == q.1.id) q.1.id) q.2 := by
  intro l hl
  obtain ⟨b, _, hb⟩ := nmf_mapM_mem _ _ e.layouts_eq l hl
  unfold bundleLayout at hb
  cases ht : inp.boxes[b.target]? with
  | none => simp [ht] at hb
  | some top =>
    rw [ht] at hb
    simp only [bind, Except.bind] at hb
    obtain ⟨part, hpart, hb⟩ := bind_ok' hb
    obtain ⟨notes, hnotes, hb⟩ := bind_ok' hb
    have heq : l = ⟨top, b, part, notes, _⟩ := (Except.ok.inj hb).symm
    rw [heq]
    constructor
    · exact hpreserve fuel hpart
    · intro q hq
      obtain ⟨att, _, hq⟩ := nmf_mapM_mem _ _ hnotes q hq
      cases hbox : inp.boxes[att.note]? with
      | none => simp [hbox] at hq
      | some box =>
        rw [hbox] at hq
        dsimp only at hq
        obtain ⟨r, hr, hq⟩ := bind_ok' hq
        have hqe : q = (box, r) := (Except.ok.inj hq).symm
        rw [hqe]
        exact hbase exactIds _ o _ hr

theorem notesBaseFrag_of_box_mirror
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (hbase : ∀ ids inp o res, base ids inp o = .ok res → NotesBoxMirror inp res)
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : NotesBaseFrag e := by
  intro l hl
  obtain ⟨hp, hq⟩ := notesFragment_mirror hbase (layoutNotes_boxes_mirror hbase) e l hl
  constructor
  · refine ⟨hp.1, ?_⟩
    intro sb hsb
    obtain ⟨mb, hmb, hid, hpar, hexc, _⟩ := hp.2 sb hsb
    exact ⟨mb, hmb, hid, hpar, hexc⟩
  · intro q hqm
    have h := hq q hqm
    refine ⟨h.1, ?_⟩
    intro sb hsb
    obtain ⟨mb, hmb, hid, hpar, hexc, _⟩ := h.2 sb hsb
    exact ⟨mb, hmb, hid, hpar, hexc⟩

private theorem notesSubInput_source_role {inp : Input} {keep : ModelBox → Bool} {root : String}
    {b : ModelBox} (hb : b ∈ (subInput inp keep root).boxes) :
    ∃ ib ∈ inp.boxes, b.id = ib.id ∧ b.role = ib.role := by
  unfold subInput at hb
  simp only [List.mem_map] at hb
  obtain ⟨sb, hsb, heq⟩ := hb
  unfold selectInput at hsb
  simp only [List.mem_map, List.mem_filter] at hsb
  obtain ⟨entry, ⟨hentry, _⟩, hsource⟩ := hsb
  have hsid : sb.id = entry.1.id := by rw [← hsource]; split <;> rfl
  have hsrole : sb.role = entry.1.role := by rw [← hsource]; split <;> rfl
  have hbid : b.id = sb.id := by rw [← heq]; split <;> rfl
  have hbrole : b.role = sb.role := by rw [← heq]; split <;> rfl
  exact ⟨entry.1, List.fst_mem_of_mem_zipIdx hentry, hbid.trans hsid, hbrole.trans hsrole⟩

theorem notesC8aFragRole_of_box_mirror
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (hbase : ∀ ids inp o res, base ids inp o = .ok res → NotesBoxMirror inp res)
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : NotesC8aFragRole e := by
  intro l hl p hp sb hsb
  obtain ⟨hpart, hnotes⟩ := notesFragment_mirror hbase (layoutNotes_boxes_mirror hbase) e l hl
  rcases placedOf_scene hp with hs | ⟨q, hq, hs⟩
  · rw [hs] at hsb
    obtain ⟨mb, hmb, hid, _, _, hrole⟩ := hpart.2 sb hsb
    obtain ⟨ib, hib, hid', hrole'⟩ := notesSubInput_source_role hmb
    exact ⟨ib, hib, hid'.symm.trans hid.symm, by rw [hrole, hrole']⟩
  · rw [hs] at hsb
    obtain ⟨mb, hmb, hid, _, _, hrole⟩ := (hnotes q hq).2 sb hsb
    obtain ⟨ib, hib, hid', hrole'⟩ := notesSubInput_source_role hmb
    exact ⟨ib, hib, hid'.symm.trans hid.symm, by rw [hrole, hrole']⟩

private theorem notesLayout_footprint_note_count {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) {l : BundleLayout} (hl : l ∈ e.layouts) :
    l.footprint.notes.length = l.notes.length := by
  obtain ⟨b, _, hb⟩ := nmf_mapM_mem _ _ e.layouts_eq l hl
  unfold bundleLayout at hb
  cases ht : inp.boxes[b.target]? with
  | none => simp [ht] at hb
  | some top =>
    rw [ht] at hb
    simp only [bind, Except.bind] at hb
    obtain ⟨part, hpart, hb⟩ := bind_ok' hb
    obtain ⟨notes, hnotes, hb⟩ := bind_ok' hb
    have heq : l = ⟨top, b, part, notes, _⟩ := (Except.ok.inj hb).symm
    have hlen := (mapM_getElem? _ _ _ hnotes).1
    rw [heq]
    simp only [footprint_notes, List.length_mapIdx, List.length_map, List.length_zip]
    omega

private theorem notesSubInput_id_mem {inp : Input} {keep : ModelBox → Bool} {root : String}
    {b : ModelBox} (hb : b ∈ inp.boxes) (hk : keep b = true) :
    b.id ∈ (subInput inp keep root).boxes.map (·.id) := by
  have hids : (subInput inp keep root).boxes.map (·.id) =
      (inp.boxes.filter keep).map (·.id) := by
    unfold subInput
    dsimp only
    rw [List.map_map]
    simp only [Function.comp_def]
    have heq : ((selectInput inp keep).boxes.map
        (fun x => (if x.id == root then { x with parent := "" } else x).id)) =
        (selectInput inp keep).boxes.map (·.id) := by
      apply List.map_congr_left
      intro x _
      split <;> rfl
    rw [heq, selectInput_box_ids]
  rw [hids]
  exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hb, hk⟩)

private theorem notesLayout_placed_scenes
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) {l : BundleLayout} (hl : l ∈ e.layouts) :
    (∃ p ∈ placedOf' e.margin e.contracted.scene l, p.scene = l.part.scene) ∧
      ∀ q ∈ l.notes, ∃ p ∈ placedOf' e.margin e.contracted.scene l, p.scene = q.2.scene := by
  obtain ⟨ps, hps⟩ := nmf_mapM_ok_of_mem e.placed_eq hl
  cases hf : e.contracted.scene.boxes.find? (fun b => b.id == l.top.id) with
  | none =>
    simp [placedFragments, hf] at hps
  | some box =>
    let place := fun (r : Rect) (s : Scene) =>
      (⟨s, box.rect.x + r.x - e.margin, box.rect.y + r.y - e.margin⟩ : Placed)
    have hplaced : placedOf' e.margin e.contracted.scene l =
        place l.footprint.target l.part.scene ::
          (l.notes.zip l.footprint.notes).map (fun q => place q.2 q.1.2.scene) := by
      simp [placedOf', placedFragments, hf, place, pure, Except.pure]
    constructor
    · rw [hplaced]
      exact ⟨_, List.mem_cons_self, rfl⟩
    · intro q hq
      have hlen : l.notes.length ≤ l.footprint.notes.length := by
        rw [notesLayout_footprint_note_count e hl]
        exact Nat.le_refl _
      have hqmap : q ∈ (l.notes.zip l.footprint.notes).map Prod.fst := by
        rw [List.map_fst_zip hlen]
        exact hq
      obtain ⟨pair, hp, heq⟩ := List.mem_map.mp hqmap
      obtain ⟨note, rect⟩ := pair
      dsimp only at heq
      subst note
      rw [hplaced]
      refine ⟨place rect q.2.scene, ?_, rfl⟩
      apply List.mem_cons_of_mem
      exact List.mem_map_of_mem hp

theorem notesC8aFragFound_of_base
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) (hbase : NotesBaseFrag e) :
    NotesC8aFragFound e := by
  intro l hl id hfrag
  have hplaces := notesLayout_placed_scenes e hl
  have hinput := nmf_layout_mem e hl
  have finish : ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      id ∈ p.scene.boxes.map (·.id) →
      (placedOf' e.margin e.contracted.scene l).any
        (fun p => p.scene.boxes.any (fun b => b.id == id)) = true := by
    intro p hp hm
    obtain ⟨sb, hsb, hid⟩ := List.mem_map.mp hm
    apply List.any_eq_true.mpr
    refine ⟨p, hp, List.any_eq_true.mpr ⟨sb, hsb, ?_⟩⟩
    exact beq_iff_eq.mpr hid
  have htop : (id == l.top.id || Compound.inside inp.boxes l.top.id id) = true ∨
      (l.notes.map (·.1.id)).contains id = true := by
    simpa only [fragmentIdOf, Bool.or_eq_true] using hfrag
  rcases htop with htop | hnote
  · have hex : ∃ b ∈ inp.boxes, b.id = id ∧
        (b.id == l.top.id || Compound.inside inp.boxes l.top.id b.id) = true := by
      cases hself : id == l.top.id with
      | true =>
        have heq : id = l.top.id := beq_iff_eq.mp hself
        refine ⟨l.top, hinput.1, heq.symm, ?_⟩
        simp
      | false =>
        have hins : Compound.inside inp.boxes l.top.id id = true := by simpa [hself] using htop
        have hins' := hins
        unfold Compound.inside at hins'
        cases hfind : inp.boxes.find? (fun b => b.id == id) with
        | none => simp [hfind] at hins'
        | some b =>
          have hid : b.id = id := by
            simpa only [beq_iff_eq] using List.find?_some hfind
          refine ⟨b, List.mem_of_find?_eq_some hfind, hid, ?_⟩
          rw [hid]
          simp [hins]
    obtain ⟨b, hb, hid, hkeep⟩ := hex
    have hsub := notesSubInput_id_mem
      (keep := fun x => x.id == l.top.id || Compound.inside inp.boxes l.top.id x.id)
      (root := l.top.id) hb hkeep
    have hscene : id ∈ l.part.scene.boxes.map (·.id) := by
      rw [(hbase l hl).1.1, ← hid]
      exact hsub
    obtain ⟨p, hp, hpEq⟩ := hplaces.1
    apply finish p hp
    rw [hpEq]
    exact hscene
  · have hnoteMem : id ∈ (l.notes.map (·.1.id)) := by
      simpa only [List.contains_eq_mem, decide_eq_true_eq] using hnote
    obtain ⟨q, hq, hqid⟩ := List.mem_map.mp hnoteMem
    have hqmem := hinput.2 q hq
    have hkeep : (q.1.id == q.1.id) = true := by simp
    have hsub := notesSubInput_id_mem (keep := fun x => x.id == q.1.id)
      (root := q.1.id) hqmem hkeep
    have hscene : id ∈ q.2.scene.boxes.map (·.id) := by
      rw [((hbase l hl).2 q hq).1, ← hqid]
      exact hsub
    obtain ⟨p, hp, hpEq⟩ := hplaces.2 q hq
    apply finish p hp
    rw [hpEq]
    exact hscene



/-- The ancestor walk is empty when the id is absent from the boxes. -/
private theorem nmf_ancestors_findIdx_none {boxes : List ModelBox} {fuel : Nat} {id : String}
    (h : boxes.findIdx? (fun box => box.id == id) = none) :
    Compound.ancestors boxes fuel id = [] := by
  induction fuel generalizing id with
  | zero => exact Compound.ancestors.eq_1 _ _
  | succ n ih =>
    by_cases hid : id = ""
    · subst hid
      exact Compound.ancestors.eq_2 _ _
    · rw [Compound.ancestors.eq_3 _ _ _ hid, h]

/-- A box kept beside its bundle top resolves its parent inside the same
fragment input: the parent is the top or strictly inside the top. -/
private theorem nmf_inside_parent {inp : Input} (hnd : (inp.boxes.map (·.id)).Nodup)
    {ib : ModelBox} (hib : ib ∈ inp.boxes) {top : String}
    (hin : Compound.inside inp.boxes top ib.id = true) {P : String} (hpar : ib.parent = P) :
    P = top ∨ Compound.inside inp.boxes top P = true := by
  unfold Compound.inside Compound.path at hin
  cases h1 : inp.boxes.find? (fun box => box.id == ib.id) with
  | none => simp [h1] at hin
  | some fb =>
    cases h2 : inp.boxes.findIdx? (fun box => box.id == top) with
    | none => simp [h1, h2] at hin
    | some tidx =>
      simp only [h1, h2] at hin
      have hfbid : fb.id = ib.id := by
        simpa only [beq_iff_eq] using List.find?_some h1
      have hfb : fb = ib :=
        nmf_nodup_id_inj _ hnd (List.mem_of_find?_eq_some h1) hib hfbid
      subst hfb
      rw [hpar] at hin
      cases hlen : inp.boxes.length with
      | zero =>
        rw [hlen, Compound.ancestors.eq_1] at hin
        simp at hin
      | succ n =>
        rw [hlen] at hin
        have hmem : tidx ∈ Compound.ancestors inp.boxes (Nat.succ n) P := by
          have hdec : decide (tidx ∈ Compound.ancestors inp.boxes (Nat.succ n) P) = true := by
            rw [← List.contains_eq_mem]
            exact hin
          exact of_decide_eq_true hdec
        by_cases hP0 : P = ""
        · subst hP0
          rw [Compound.ancestors.eq_2] at hmem
          simp at hmem
        · cases h3 : inp.boxes.findIdx? (fun box => box.id == P) with
          | none =>
            rw [nmf_ancestors_findIdx_none h3] at hmem
            simp at hmem
          | some pidx =>
            obtain ⟨hlen', Pbox, hget, hpred⟩ := nmf_findIdx_lookup h3
            have hPboxid : Pbox.id = P := beq_iff_eq.mp hpred
            have hPmem : Pbox ∈ inp.boxes := List.mem_of_getElem? hget
            simp only [Compound.ancestors.eq_3 _ _ _ hP0, h3, hget] at hmem
            rcases List.mem_append.mp hmem with htail | hhead
            · right
              have hfindP : inp.boxes.find? (fun box => box.id == P) = some Pbox :=
                nmf_find?_unique _ _ hnd _ hPmem _ hPboxid
              unfold Compound.inside Compound.path
              simp only [hfindP, h2]
              rw [hlen, List.contains_eq_mem, decide_eq_true_eq]
              exact CompoundHelpers.ancestors_mem_mono _ htail
            · left
              have htp : tidx = pidx := List.mem_singleton.mp hhead
              obtain ⟨_, Tbox, hTget, hTpred⟩ := nmf_findIdx_lookup h2
              have hTboxid : Tbox.id = top := beq_iff_eq.mp hTpred
              subst htp
              have hTP : Tbox = Pbox := Option.some.inj (hTget.symm.trans hget)
              rw [← hPboxid, ← hTboxid, hTP]

/-- A same-scene witness from a fragment-input image: if the input box behind
`mb.parent` survives in the fragment input, its scene box witnesses the
parent. -/
private theorem nmf_part_wit {inp : Input} {l : BundleLayout} {p : Placed}
    (hps : p.scene = l.part.scene)
    (hideq : (l.part.scene.boxes.map (·.id)) =
      ((subInput inp (fun x => x.id == l.top.id ||
        Compound.inside inp.boxes l.top.id x.id) l.top.id).boxes.map (·.id)))
    {sb : Box} {mb : ModelBox} (hpar : sb.parent = mb.parent)
    {x : ModelBox} (hxmem : x ∈ (subInput inp (fun x => x.id == l.top.id ||
      Compound.inside inp.boxes l.top.id x.id) l.top.id).boxes)
    (hxid : x.id = mb.parent) :
    ∃ sp ∈ p.scene.boxes, sp.id = sb.parent := by
  have hxidm : x.id ∈ l.part.scene.boxes.map (·.id) := by
    rw [hideq]
    exact List.mem_map_of_mem hxmem
  obtain ⟨sp, hspm, hspid⟩ := List.mem_map.mp hxidm
  refine ⟨sp, by rw [hps]; exact hspm, ?_⟩
  rw [hspid, hxid, ← hpar]

/-! ### The seven residual facts -/

/-- The contracted scene mirrors the input boxes in id, parent, and
exclusivity: base preservation on the contracted input chained with the
`contractOne` fold. -/
theorem notesContractMirror_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : NotesBaseContract e) : NotesContractMirror e := by
  intro cb hcb
  obtain ⟨mb, hmb, hid, hpar, hexc⟩ := hBase.2 cb hcb
  rw [e.contractedInput_eq] at hmb
  obtain ⟨ib, hib, hid2, hpar2, hexc2⟩ := nmf_contractFold_mem3 _ _ hmb
  exact ⟨ib, hib, hid.trans hid2.symm, hpar.trans hpar2.symm, hexc.trans hexc2.symm⟩

private theorem parentTransfer_of_boxMirror {src : List ModelBox} {dst : List Box}
    (hnd : (src.map (·.id)).Nodup)
    (hmirror : ∀ b ∈ dst, ∃ m ∈ src, b.id = m.id ∧ b.parent = m.parent) :
    IdParentTransferM src dst := by
  intro id b hb
  obtain ⟨m, hm, hid, hparent⟩ := hmirror b (List.mem_of_find?_eq_some hb)
  have htest := List.find?_some hb
  have hbid : b.id = id := beq_iff_eq.mp htest
  let mapped := Box.mk m.id m.role.id ⟨0, 0, 0, 0⟩ m.parent m.exclusive
  refine ⟨mapped, ?_, hid.symm, hparent.symm⟩
  exact nmf_find?_unique (·.id) (modelBoxesToDump src)
    (by simpa only [modelBoxesToDump, List.map_map, Function.comp_def] using hnd)
    mapped (List.mem_map.mpr ⟨m, hm, rfl⟩) id (hid.symm.trans hbid)

theorem contractFold_parentTransfer (inp : Input) (layouts : List BundleLayout)
    (hnd : (inp.boxes.map (·.id)).Nodup) :
    IdParentTransferM inp.boxes (modelBoxesToDump (layouts.foldl contractOne inp).boxes) := by
  apply parentTransfer_of_boxMirror hnd
  intro b hb
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hb
  obtain ⟨original, horiginal, hid, hparent, _⟩ := nmf_contractFold_mem3 inp layouts hm
  exact ⟨original, horiginal, hid.symm, hparent.symm⟩

theorem notesContractedScene_parentTransfer
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hnd : (inp.boxes.map (·.id)).Nodup) (hBase : NotesBaseContract e) :
    IdParentTransferM e.contractedInput.boxes e.contracted.scene.boxes := by
  apply parentTransfer_of_boxMirror
  · rw [e.contractedInput_eq]
    exact nmf_contractFold_nodup inp e.layouts hnd
  · intro b hb
    obtain ⟨m, hm, hid, hparent, _⟩ := hBase.2 b hb
    exact ⟨m, hm, hid, hparent⟩

/-- Parent alignment through the bundle top: the top and its notes come from
the input, notes share the top's parent by hypothesis, and the contracted top
box shares it by base preservation. -/
theorem notesParentAlign_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : NotesBaseContract e) (hNotePar : NotesBundleNoteParent e)
    (hnd : (inp.boxes.map (·.id)).Nodup) : NotesParentAlign e := by
  intro l hl
  obtain ⟨hltop, hlnote⟩ := nmf_layout_mem e hl
  refine ⟨l.top, hltop, rfl, ?_, ?_⟩
  · intro q hq
    exact ⟨hlnote q hq, hNotePar l hl q hq⟩
  · intro eb heb heid
    obtain ⟨kb, hkb, hid, hpar, hexc⟩ := hBase.2 eb heb
    rw [e.contractedInput_eq] at hkb
    obtain ⟨ib, hib, hid2, hpar2, hexc2⟩ := nmf_contractFold_mem3 _ _ hkb
    have hibtop : ib = l.top :=
      nmf_nodup_id_inj _ hnd hib hltop (hid2.trans (hid.symm.trans heid))
    have hpar' : eb.parent = ib.parent := hpar.trans hpar2.symm
    rw [hpar', hibtop]

/-- Each placed fragment scene mirrors the input boxes: the executed part and
note scenes mirror their fragment inputs, the fragment inputs sit in the input
with parents kept except for the cleared top/note roots, and roots are
rootless in the input by hypothesis. -/
theorem notesFragMirror_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hFrag : NotesBaseFrag e) (hRoots : NotesFragRoots e)
    (hnd : (inp.boxes.map (·.id)).Nodup) : NotesFragMirror e := by
  intro l hl p hpm sb hsb
  rcases placedOf_scene hpm with hps | ⟨q, hqm, hqs⟩
  · obtain ⟨hideq, htriple⟩ := (hFrag l hl).1
    rw [hps] at hsb
    obtain ⟨mb, hmb, hid, hpar, hexc⟩ := htriple sb hsb
    obtain ⟨ib, hib, hkeep, hid2, hexc2, hparcase⟩ := nmf_subInput_mem hmb
    have hpc := hparcase
    rcases hpc with ⟨hidtop, hparz⟩ | ⟨hnetop, hparp⟩
    · refine ⟨ib, hib, hid.trans hid2.symm, ?_, hexc.trans hexc2, ?_⟩
      · rw [hpar, hparz]
        have hibtop : ib.id = l.top.id := hid2.trans hidtop
        have hr : ib.parent = "" := (hRoots l hl).1 ib hib hibtop
        exact hr.symm
      · exact Or.inl (hid.trans hidtop)
    · refine ⟨ib, hib, hid.trans hid2.symm, hpar.trans hparp, hexc.trans hexc2, ?_⟩
      by_cases hb : ib.id == l.top.id
      · exact Or.inl (hid.trans (hid2.symm.trans (beq_iff_eq.mp hb)))
      · have hins : Compound.inside inp.boxes l.top.id ib.id = true := by
          simpa [hb] using hkeep
        exact Or.inr (Or.inl (by rw [hid, hid2.symm]; exact hins))
  · obtain ⟨hideq, htriple⟩ := (hFrag l hl).2 q hqm
    rw [hqs] at hsb
    obtain ⟨mb, hmb, hid, hpar, hexc⟩ := htriple sb hsb
    obtain ⟨ib, hib, hkeep, hid2, hexc2, hparcase⟩ := nmf_subInput_mem hmb
    have hqmem : q.1 ∈ inp.boxes := (nmf_layout_mem e hl).2 q hqm
    have hpc := hparcase
    have hmbq : mb.id = q.1.id := by
      rcases hpc with ⟨h, _⟩ | ⟨hne, _⟩
      · exact h
      · exfalso
        have hibq : ib.id = q.1.id := beq_iff_eq.mp hkeep
        exact hne (hid2.symm.trans hibq)
    refine ⟨ib, hib, hid.trans hid2.symm, ?_, hexc.trans hexc2, ?_⟩
    · rw [hpar]
      rcases hparcase with ⟨_, hparz⟩ | ⟨_, hparp⟩
      · have hibq : ib.id = q.1.id := hid2.trans hmbq
        have heq : ib = q.1 := nmf_nodup_id_inj _ hnd hib hqmem hibq
        have hr : q.1.parent = "" := (hRoots l hl).2 q hqm
        rw [hparz, heq]
        exact hr.symm
      · exact hparp
    · exact Or.inr (Or.inr ⟨q, hqm, hid.trans hmbq⟩)

/-- Trace a placed scene to its executed part or note run and transport its box
fields through the corresponding `subInput` selection. -/
theorem notesFragMirrorT_holds
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hFrag : NotesBaseFrag e) (hnd : (inp.boxes.map (·.id)).Nodup) : NotesFragMirrorT e := by
  intro l hl p hp
  obtain ⟨htop, hnotes⟩ := nmf_layout_mem e hl
  rcases placedOf_scene hp with hps | ⟨q, hq, hps⟩
  · obtain ⟨hids, hboxes⟩ := (hFrag l hl).1
    have hroot := notesSubInput_id_mem
      (keep := fun x => x.id == l.top.id || Compound.inside inp.boxes l.top.id x.id)
      (root := l.top.id) htop (by simp)
    rw [← hids, ← hps] at hroot
    refine Or.inl ⟨hps, htop, List.mem_map.mp hroot, ?_⟩
    intro sb hsb
    rw [hps] at hsb
    obtain ⟨mb, hmb, hid, hpar, hexc⟩ := hboxes sb hsb
    obtain ⟨ib, hib, hkeep, hmbId, hmbExcl, hmbParent⟩ := nmf_subInput_mem hmb
    have hsbId := hid.trans hmbId.symm
    refine ⟨ib, hib, hsbId, hexc.trans hmbExcl, ?_, ?_⟩
    · rw [hsbId]
      simpa only [Bool.or_eq_true, beq_iff_eq] using hkeep
    · rcases hmbParent with ⟨hrootId, hrootParent⟩ | ⟨hnotRoot, hkeptParent⟩
      · have heq := hid.trans hrootId
        simpa only [ite_eq_left heq] using hpar.trans hrootParent
      · have hne : sb.id ≠ l.top.id := fun heq => hnotRoot (hid.symm.trans heq)
        simpa only [ite_eq_right hne] using hpar.trans hkeptParent
  · obtain ⟨hids, hboxes⟩ := (hFrag l hl).2 q hq
    have hqInput := hnotes q hq
    have hroot := notesSubInput_id_mem (keep := fun x => x.id == q.1.id)
      (root := q.1.id) hqInput (by simp)
    rw [← hids, ← hps] at hroot
    refine Or.inr ⟨q, hq, hps, hqInput, List.mem_map.mp hroot, ?_⟩
    intro sb hsb
    rw [hps] at hsb
    obtain ⟨mb, hmb, hid, hpar, hexc⟩ := hboxes sb hsb
    obtain ⟨ib, hib, hkeep, hmbId, hmbExcl, hmbParent⟩ := nmf_subInput_mem hmb
    have hibId : ib.id = q.1.id := beq_iff_eq.mp hkeep
    have hmbRoot := hmbId.symm.trans hibId
    have hibNote : ib = q.1 := nmf_nodup_id_inj _ hnd hib hqInput hibId
    rw [hibNote] at hmbExcl
    refine ⟨hid.trans hmbRoot, hexc.trans hmbExcl, ?_⟩
    rcases hmbParent with ⟨_, hrootParent⟩ | ⟨hnotRoot, _⟩
    · exact hpar.trans hrootParent
    · exact (hnotRoot hmbRoot).elim

theorem notesFragIdExcl_holds
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hFrag : NotesBaseFrag e) (hnd : (inp.boxes.map (·.id)).Nodup) : NotesFragIdExcl e := by
  intro l hl p hp sb hsb
  rcases notesFragMirrorT_holds e hFrag hnd l hl p hp with
    ⟨_, _, _, hpart⟩ | ⟨q, _, _, hqInput, _, hnote⟩
  · obtain ⟨ib, hib, hid, hexc, _, _⟩ := hpart sb hsb
    exact ⟨ib, hib, hid, hexc⟩
  · obtain ⟨hid, hexc, _⟩ := hnote sb hsb
    exact ⟨q.1, hqInput, hid, hexc⟩

/-- The role witness is the same input box as any id-matching provenance
witness. Role preservation comes from the base box mirror, not `NotesBaseFrag`. -/
theorem notesFragRole_eq_of_id
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hRole : NotesC8aFragRole e) (hnd : (inp.boxes.map (·.id)).Nodup) :
    ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
      ∀ sb ∈ p.scene.boxes, ∀ ib ∈ inp.boxes, sb.id = ib.id → sb.role = ib.role.id := by
  intro l hl p hp sb hsb ib hib hid
  obtain ⟨rb, hrb, hrid, hrole⟩ := hRole l hl p hp sb hsb
  have heq : rb = ib := nmf_nodup_id_inj _ hnd hrb hib (hrid.trans hid)
  rw [← heq]
  exact hrole.symm

/-- Parent locality inside one placed scene: a fragment box is rootless, has a
same-scene parent witness, or its parent lives in no fragment and the box is
its layout's note or top. -/
theorem notesParentLocal_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hFrag : NotesBaseFrag e) (hnd : (inp.boxes.map (·.id)).Nodup) : NotesParentLocal e := by
  intro l hl p hpm sb hsb
  rcases placedOf_scene hpm with hps | ⟨q, hqm, hqs⟩
  · obtain ⟨hideq, htriple⟩ := (hFrag l hl).1
    rw [hps] at hsb
    obtain ⟨mb, hmb, hid, hpar, hexc⟩ := htriple sb hsb
    obtain ⟨ib, hib, hkeep, hid2, hexc2, hparcase⟩ := nmf_subInput_mem hmb
    by_cases hzero : sb.parent = ""
    · exact Or.inl hzero
    · right; left
      have hmbne : mb.parent ≠ "" := fun he => hzero (hpar.trans he)
      have hR : mb.id ≠ l.top.id ∧ mb.parent = ib.parent := by
        rcases hparcase with ⟨_, hpr⟩ | ⟨hne, hpr⟩
        · exfalso; exact hmbne hpr
        · exact ⟨hne, hpr⟩
      obtain ⟨hne, hpmem⟩ := hR
      have hne2 : ib.id ≠ l.top.id := fun he => hne (hid2.symm.trans he)
      have hinside : Compound.inside inp.boxes l.top.id ib.id = true := by
        by_cases hb : ib.id == l.top.id
        · exfalso; exact hne2 (beq_iff_eq.mp hb)
        · simpa [hb] using hkeep
      rcases nmf_inside_parent hnd hib hinside hpmem.symm with hPtop | hPin
      · -- parent is the top: image the top box into the fragment input
        have hltop : l.top ∈ inp.boxes := (nmf_layout_mem e hl).1
        have hkeeptop : ((fun x => x.id == l.top.id ||
            Compound.inside inp.boxes l.top.id x.id) l.top) = true := by
          show ((l.top.id == l.top.id) ||
            Compound.inside inp.boxes l.top.id l.top.id) = true
          simp
        obtain ⟨x, hxmem, hxid, _, _⟩ :=
          nmf_subInput_image (keep := fun x => x.id == l.top.id ||
            Compound.inside inp.boxes l.top.id x.id) hnd hltop hkeeptop
        exact nmf_part_wit hps hideq hpar hxmem (hxid.trans hPtop.symm)
      · unfold Compound.inside at hPin
        cases hP1 : inp.boxes.find? (fun box => box.id == mb.parent) with
        | none => simp [hP1] at hPin
        | some Pbox =>
          have hPboxid : Pbox.id = mb.parent := by
            simpa only [beq_iff_eq] using List.find?_some hP1
          have hPmem : Pbox ∈ inp.boxes := List.mem_of_find?_eq_some hP1
          have hkeepP : ((fun x => x.id == l.top.id ||
              Compound.inside inp.boxes l.top.id x.id) Pbox) = true := by
            by_cases hPt : (Pbox.id == l.top.id) = true
            · simp [hPt]
            · have hins : (Compound.inside inp.boxes l.top.id Pbox.id) = true := by
                rw [hPboxid]; exact hPin
              simp [hPt, hins]
          obtain ⟨x, hxmem, hxid, _, _⟩ :=
            nmf_subInput_image (keep := fun x => x.id == l.top.id ||
              Compound.inside inp.boxes l.top.id x.id) hnd hPmem hkeepP
          exact nmf_part_wit hps hideq hpar hxmem (hxid.trans hPboxid)
  · rw [hqs] at hsb
    obtain ⟨hideq, htriple⟩ := (hFrag l hl).2 q hqm
    obtain ⟨mb, hmb, hid, hpar, hexc⟩ := htriple sb hsb
    obtain ⟨ib, hib, hkeep, hid2, hexc2, hparcase⟩ := nmf_subInput_mem hmb
    have hmbpar : mb.parent = "" := by
      rcases hparcase with ⟨_, h⟩ | ⟨hne, _⟩
      · exact h
      · exfalso
        have hibq : ib.id = q.1.id := beq_iff_eq.mp hkeep
        exact hne (hid2.symm.trans hibq)
    exact Or.inl (hpar.trans hmbpar)

/-- Non-fragment contracted boxes have rootless or non-fragment parents:
contracted-input parent closure transported through the base mirror. -/
theorem notesKeptClosed_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : NotesBaseContract e) (hKept : NotesKeptParent e) : NotesKeptClosed e := by
  intro cb hcb hnonfrag
  obtain ⟨kb, hkb, hid, hpar, hexc⟩ := hBase.2 cb hcb
  rcases hKept kb hkb with hroot | ⟨kpb, hkpbm, hkid, hknon⟩
  · exact Or.inl (hpar.trans hroot)
  · have hmem : kpb.id ∈ e.contracted.scene.boxes.map (·.id) := by
      rw [hBase.1]
      exact List.mem_map_of_mem hkpbm
    obtain ⟨cpb, hcpm, hcpid⟩ := List.mem_map.mp hmem
    refine Or.inr ⟨cpb, hcpm, ?_, ?_⟩
    · rw [hcpid, hkid, ← hpar]
    · intro q hq r hr
      rw [hpar] at hr
      exact hknon q hq r hr

/-- Contracted parent lookup succeeds: the named parent box is the unique
scene box with that id. -/
theorem notesContractBoxEq_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : NotesBaseContract e) (hnd : (inp.boxes.map (·.id)).Nodup) :
    NotesContractBoxEq e := by
  intro eb heb pb hpb hpid hne
  have hscenenodup : (e.contracted.scene.boxes.map (·.id)).Nodup := by
    rw [hBase.1, e.contractedInput_eq]
    exact nmf_contractFold_nodup _ _ hnd
  show e.contracted.scene.boxes.find? (fun b => b.id == eb.parent) = some pb
  exact nmf_find?_unique _ _ hscenenodup _ hpb _ hpid

/-- Fragment parent lookup succeeds: the named parent box is the unique
same-scene box with that id. -/
theorem notesFragBoxEq_holds {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hFrag : NotesBaseFrag e) (hnd : (inp.boxes.map (·.id)).Nodup) : NotesFragBoxEq e := by
  intro l hl p hpm sb hsb sp hspm hspid hsne
  rcases placedOf_scene hpm with hps | ⟨q, hqm, hqs⟩
  · obtain ⟨hideq, htriple⟩ := (hFrag l hl).1
    rw [hps] at hsb
    have hnodup : (p.scene.boxes.map (·.id)).Nodup := by
      rw [hps, hideq]
      exact nmf_subInput_nodup _ _ _ hnd
    show p.scene.boxes.find? (fun b => b.id == sb.parent) = some sp
    exact nmf_find?_unique _ _ hnodup _ hspm _ hspid
  · obtain ⟨hideq, htriple⟩ := (hFrag l hl).2 q hqm
    rw [hqs] at hsb
    have hnodup : (p.scene.boxes.map (·.id)).Nodup := by
      rw [hqs, hideq]
      exact nmf_subInput_nodup _ _ _ hnd
    show p.scene.boxes.find? (fun b => b.id == sb.parent) = some sp
    exact nmf_find?_unique _ _ hnodup _ hspm _ hspid

private def ParentTruncation (src dst : List Box) : Prop :=
  ∀ id b, dst.find? (fun b => b.id == id) = some b →
    ∃ a, src.find? (fun b => b.id == id) = some a ∧ (b.parent = "" ∨ b.parent = a.parent)

private theorem parentTruncation_ancestors {src dst : LayoutDump}
    (htransfer : ParentTruncation src.boxes dst.boxes) :
    ∀ (k k' : Nat), k ≤ k' → ∀ (id x : String),
      x ∈ LayoutDump.ancestors.go dst k id → x ∈ LayoutDump.ancestors.go src k' id := by
  intro k
  induction k with
  | zero => intro k' _ _ _ hx; cases hx
  | succ k ih =>
    intro k' hk id x hx
    cases k' with
    | zero => omega
    | succ k' =>
      have hkk : k ≤ k' := Nat.le_of_succ_le_succ hk
      simp only [LayoutDump.ancestors.go, LayoutDump.box?] at hx ⊢
      cases hd : dst.boxes.find? (fun b => b.id == id) with
      | none => rw [hd] at hx; cases hx
      | some db =>
        rw [hd] at hx
        obtain ⟨sb, hsb, hpar⟩ := htransfer id db hd
        rw [hsb]
        dsimp only at hx ⊢
        rcases hpar with hzero | hpar
        · simp [hzero] at hx
        · rw [hpar] at hx
          by_cases hp : sb.parent = ""
          · simp [hp] at hx
          · simp only [hp, ↓reduceIte] at hx ⊢
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ih k' hkk sb.parent x hx')

private theorem notesSubInput_length_le (inp : Input) (keep : ModelBox → Bool) (root : String) :
    (subInput inp keep root).boxes.length ≤ inp.boxes.length := by
  simp only [subInput, selectInput, List.length_map]
  simpa only [List.length_zipIdx] using List.length_filter_le (fun q => keep q.1) inp.boxes.zipIdx

private theorem notesSubInput_ancestors
    {inp : Input} {keep : ModelBox → Bool} {root : String} {scene : Scene}
    (hnd : (inp.boxes.map (·.id)).Nodup)
    (hids : scene.boxes.map (·.id) = (subInput inp keep root).boxes.map (·.id))
    (hboxes : ∀ sb ∈ scene.boxes, ∃ mb ∈ (subInput inp keep root).boxes,
      sb.id = mb.id ∧ sb.parent = mb.parent ∧ sb.exclusive = mb.exclusive) :
    ∀ id x, x ∈ scene.layoutDump.ancestors id → x ∈ (inpDumpOf inp).ancestors id := by
  have htransfer : ParentTruncation (inpDumpOf inp).boxes scene.layoutDump.boxes := by
    intro id sb hsb
    obtain ⟨mb, hmb, hid, hpar, _⟩ := hboxes sb (List.mem_of_find?_eq_some hsb)
    obtain ⟨ib, hib, _, hid', _, hp⟩ := nmf_subInput_mem hmb
    have htest := List.find?_some hsb
    have hsbid : sb.id = id := beq_iff_eq.mp htest
    let mapped := Box.mk ib.id ib.role.id ⟨0, 0, 0, 0⟩ ib.parent ib.exclusive
    refine ⟨mapped, ?_, ?_⟩
    · exact nmf_find?_unique (·.id) (modelBoxesToDump inp.boxes)
        (by simpa only [modelBoxesToDump, List.map_map, Function.comp_def] using hnd)
        mapped (List.mem_map.mpr ⟨ib, hib, rfl⟩) id (hid'.trans (hid.symm.trans hsbid))
    · rcases hp with ⟨_, hz⟩ | ⟨_, hp⟩
      · exact Or.inl (hpar.trans hz)
      · exact Or.inr (hpar.trans hp)
  have hlen := congrArg List.length hids
  simp only [List.length_map] at hlen
  have hbound : scene.layoutDump.boxes.length ≤ (inpDumpOf inp).boxes.length := by
    change scene.boxes.length ≤ (modelBoxesToDump inp.boxes).length
    rw [hlen]
    simpa only [modelBoxesToDump, List.length_map] using notesSubInput_length_le inp keep root
  intro id x hx
  unfold LayoutDump.ancestors at hx ⊢
  exact parentTruncation_ancestors htransfer _ _ hbound id x hx

theorem notesC8aSceneAnc_of_base
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hnd : (inp.boxes.map (·.id)).Nodup) (hbase : NotesBaseFrag e) :
    NotesC8aSceneAnc e := by
  intro l hl p hp id x hx
  rcases placedOf_scene hp with hs | ⟨q, hq, hs⟩
  · rw [hs] at hx
    exact notesSubInput_ancestors hnd (hbase l hl).1.1 (hbase l hl).1.2 id x hx
  · rw [hs] at hx
    exact notesSubInput_ancestors hnd ((hbase l hl).2 q hq).1
      ((hbase l hl).2 q hq).2 id x hx

theorem notesC6AncF_of_sceneAnc
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) (h : NotesC8aSceneAnc e) :
    NotesC6AncF e := by
  intro p hp id x hx
  rw [e.fragments_eq] at hp
  obtain ⟨l, hl, hp⟩ := placedFlatten_mem e.placed_eq hp
  exact h l hl p hp id x hx

theorem notesC6AncC_of_base
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hnd : (inp.boxes.map (·.id)).Nodup) (hbase : NotesBaseContract e) :
    NotesC6AncC e := by
  have hcontract := notesContractedScene_parentTransfer e hnd hbase
  rw [e.contractedInput_eq] at hcontract
  have htransfer := (contractFold_parentTransfer inp e.layouts hnd).trans hcontract
  have htrunc : ParentTruncation (inpDumpOf inp).boxes e.contracted.scene.layoutDump.boxes := by
    intro id b hb
    obtain ⟨a, ha, _, hp⟩ := htransfer id b hb
    exact ⟨a, ha, Or.inr hp.symm⟩
  have hlen := congrArg List.length hbase.1
  simp only [List.length_map] at hlen
  have hbound : e.contracted.scene.layoutDump.boxes.length ≤ (inpDumpOf inp).boxes.length := by
    change e.contracted.scene.boxes.length ≤ (modelBoxesToDump inp.boxes).length
    rw [hlen, e.contractedInput_eq]
    simpa only [modelBoxesToDump, List.length_map] using fold_length_le inp e.layouts
  intro id x hx
  unfold LayoutDump.ancestors at hx ⊢
  exact parentTruncation_ancestors htrunc _ _ hbound id x hx

def NotesRouteMirror (inp : Input) (res : FamilyResult) : Prop :=
  ∀ rt ∈ res.scene.routes, ∃ r ∈ inp.routes,
    rt.id = r.id ∧ rt.fromId = r.fromId ∧ rt.toId = r.toId ∧ rt.orthogonal = r.orthogonal

theorem layoutNotes_routes_mirror
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (hbase : ∀ ids inp o res, base ids inp o = .ok res → NotesRouteMirror inp res)
    (fuel : Nat) {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutNotes base exactIds fuel inp o = .ok res) : NotesRouteMirror inp res := by
  cases fuel with
  | zero => exact hbase exactIds inp o res h
  | succ fuel =>
    rcases layoutNotes_success_phases h with ⟨_, hleaf⟩ | hexecution
    · exact hbase exactIds inp o res hleaf
    · obtain ⟨execution⟩ := hexecution
      exact execution.routes_mem

theorem notesFlagsFragment_of_route_mirror
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (hbase : ∀ ids inp o res, base ids inp o = .ok res → NotesRouteMirror inp res)
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hnd : (inp.routes.map (·.id)).Nodup) :
    notesFlagsFragment inp e.layouts e.fragments := by
  intro r hr a hsame p hp fr hfr hid
  rw [e.fragments_eq] at hp
  obtain ⟨l, hl, hp⟩ := placedFlatten_mem e.placed_eq hp
  obtain ⟨hpart, hnotes⟩ := notesFragment_mirror hbase (layoutNotes_routes_mirror hbase) e l hl
  have finish : ∀ {keep : ModelBox → Bool} {root : String} {s : FamilyResult},
      NotesRouteMirror (subInput inp keep root) s → fr ∈ s.scene.routes →
      fr.orthogonal = r.orthogonal ∧ fr.fromId = r.fromId ∧ fr.toId = r.toId := by
    intro keep root s hmir hmem
    obtain ⟨source, hs, hsid, hfrom, hto, hort⟩ := hmir fr hmem
    have hinput : source ∈ inp.routes := by
      change source ∈ (selectInput inp keep "").routes at hs
      exact ((selectInput_route_mem inp keep "" source).mp hs).1
    have hsource := nmf_find?_unique (fun x : ModelRoute => x.id) inp.routes hnd
      source hinput r.id (hsid.symm.trans hid)
    have hroute := nmf_find?_unique (fun x : ModelRoute => x.id) inp.routes hnd r hr r.id rfl
    have heq : source = r := Option.some.inj (hsource.symm.trans hroute)
    subst source
    exact ⟨hort, hfrom, hto⟩
  rcases placedOf_scene hp with hps | ⟨q, hq, hqs⟩
  · rw [hps] at hfr
    exact finish hpart hfr
  · rw [hqs] at hfr
    exact finish (hnotes q hq) hfr

end PipelineImpl
end Layered
end Elegant
import Elegant.Layered.NotesPlacementFacts
import Elegant.Layered.NotesMirrorFacts
import Elegant.Layered.SelectFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Whole-record assembly of the note-stage C2 and C3 geometric contexts.

`NotesC2Geom` (`NotesFlatBoxClauses.lean`) is the conjunction `NotesFirstMatch`,
`NotesContractMirror`, `NotesFragMirror`, `NotesPlacedDisjoint`,
`NotesForeignClear`; `NotesC3Geom` adds `NotesEnvFit`, `NotesParentAlign`,
`NotesParentLocal`, `NotesKeptClosed`, `NotesContractBoxEq`, `NotesFragBoxEq`.
Each conjunct has a closer theorem (`notesFirstMatch_holds`,
`notesContractMirror_holds`, `notesFragMirror_holds`, `notesEnvFit_holds`,
`notesPlacedDisjoint_holds`, `notesForeignClear_holds`,
`notesParentAlign_holds`, `notesParentLocal_holds`, `notesKeptClosed_holds`,
`notesContractBoxEq_holds`, `notesFragBoxEq_holds`); this module assembles
them into the whole records.

Premises are only the executed run `e : NotesExecution`, local well-formedness
(for input-id nodup), and narrow defs for the still-open conjunct halves:
`NotesBaseContract`, `NotesBaseFrag`, `NotesFragRoots`, `NotesBundleNoteParent`,
`NotesKeptParent` (from `NotesMirrorFacts`), the contracted `Validator.C2` base
clause, and the six `Ngb*` defs below. The holding-rect half of
`NotesFirstMatch` is not a premise: it follows from the executed placement
equation, `NotesBaseFrag`, and input-id nodup (`nga_placed_rect_self`), so
this assembly is strictly weaker than the `Ngc2BridgeW`/`Ngc3BridgeW` bridges,
which carry that half explicitly.
-/

/-- Cross-fragment lookup absence: a box id held by one placed fragment is
resolved by no other fragment. Serves `NotesFirstMatch` alone. -/
def NgbFirstCross {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ p ∈ e.fragments, ∀ q ∈ e.fragments, p ≠ q →
    ∀ sb ∈ p.scene.boxes, q.rect sb.id = none

/-- Fragment canvases sit inside their bundle envelopes. Serves `NotesEnvFit`
alone (and through it the two envelope-chained C2 conjuncts). -/
def NgbEnvPlace {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    (envRect e.contracted.scene l).Contained ⟨p.dx, p.dy, p.scene.canvas.w, p.scene.canvas.h⟩

/-- Fragment C1: every placed fragment scene satisfies the C1 canvas clause.
Serves `NotesEnvFit` alone. -/
def NgbFragC1 {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    Validator.C1 p.scene.layoutDump

/-- Distinct bundle tops are exclusive boxes sharing their parent in the
contracted scene. Serves `NotesPlacedDisjoint` alone. -/
def NgbTopPairsExclusive {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ la ∈ e.layouts, ∀ lb ∈ e.layouts, la ≠ lb →
    ∀ ea ∈ e.contracted.scene.boxes, ea.id = la.top.id →
    ∀ eb ∈ e.contracted.scene.boxes, eb.id = lb.top.id →
      ea.id ≠ eb.id ∧ ea.exclusive = true ∧ eb.exclusive = true ∧ ea.parent = eb.parent

/-- Boxes of two distinct placed fragments of one layout are disjoint after
shifting. Serves `NotesPlacedDisjoint` alone. -/
def NgbSamePlaceDisjoint {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ pa ∈ placedOf' e.margin e.contracted.scene l,
    ∀ pb ∈ placedOf' e.margin e.contracted.scene l, pa ≠ pb →
    ∀ sa ∈ pa.scene.boxes, ∀ sb ∈ pb.scene.boxes,
      Disjoint (shiftRect pa.dx pa.dy sa.rect) (shiftRect pb.dx pb.dy sb.rect)

/-- A contracted box that no fragment holds is exclusive and shares the
bundle top's parent domain in the contracted scene. Serves
`NotesForeignClear` alone. -/
def NgbForeignExclusive {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ eb ∈ e.contracted.scene.boxes, eb.id = l.top.id →
    ∀ cb ∈ e.contracted.scene.boxes,
      (∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r) →
        cb.id ≠ eb.id ∧ cb.exclusive = true ∧ eb.exclusive = true ∧ cb.parent = eb.parent

/-! ### Private plumbing (prefixed copies: other modules' privates do not resolve) -/

/-- Equal images under `·.id` of two members of an id-duplicate-free scene-box
list force the members to be equal. -/
private theorem nga_box_nodup_id_inj :
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
      · exact nga_box_nodup_id_inj _ h.2 ha' hb' e

private theorem nga_subInput_id (b : ModelBox) (root : String) :
    ((if b.id == root then { b with parent := "" } else b : ModelBox).id) = b.id := by
  by_cases h : (b.id == root) = true
  · have ht : b.id = root := beq_iff_eq.mp h
    simp [ht]
  · simp [h]

/-- `subInput` preserves the id image of the selected boxes: clearing the
root parent does not change ids. -/
private theorem nga_subInput_ids_eq {inp : Input} {keep : ModelBox → Bool} {root : String} :
    ((subInput inp keep root).boxes.map (·.id)) =
      ((selectInput inp keep root).boxes.map (·.id)) := by
  unfold subInput
  rw [List.map_map, Function.comp_def, selectInput_box_ids inp keep root,
    ← selectInput_box_ids inp keep ""]
  exact List.map_congr_left (fun b _ => nga_subInput_id b root)

/-- `subInput` keeps duplicate-free ids. -/
private theorem nga_subInput_ids_nodup {inp : Input} {keep : ModelBox → Bool} {root : String}
    (hnd : (inp.boxes.map (·.id)).Nodup) :
    (((subInput inp keep root).boxes.map (·.id))).Nodup := by
  rw [nga_subInput_ids_eq, selectInput_box_ids]
  exact List.Nodup.sublist
    (List.Sublist.map (fun box : ModelBox => box.id) List.filter_sublist) hnd

/-- Every placed fragment scene of an executed layout carries duplicate-free
ids: the executed part and note scenes mirror `subInput` images of the
duplicate-free input. -/
private theorem nga_frag_scene_nodup
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBaseF : NotesBaseFrag e) (hnd : (inp.boxes.map (·.id)).Nodup)
    {l : BundleLayout} (hl : l ∈ e.layouts) {p : Placed}
    (hpm : p ∈ placedOf' e.margin e.contracted.scene l) :
    ((p.scene.boxes.map (·.id))).Nodup := by
  rcases placedOf_scene hpm with hps | ⟨q, hqm, hqs⟩
  · obtain ⟨hideq, _⟩ := (hBaseF l hl).1
    rw [hps, hideq]
    exact nga_subInput_ids_nodup hnd
  · obtain ⟨hideq, _⟩ := (hBaseF l hl).2 q hqm
    rw [hqs, hideq]
    exact nga_subInput_ids_nodup hnd

/-- A box of a fragment scene with duplicate-free ids resolves in that
fragment to its own shifted rect: the holding-rect half of
`NotesFirstMatch`, discharged from the executed placement. -/
private theorem nga_placed_rect_self {p : Placed} {sb : Box}
    (hn : ((p.scene.boxes.map (·.id))).Nodup) (hsb : sb ∈ p.scene.boxes) :
    p.rect sb.id = some (shiftRect p.dx p.dy sb.rect) := by
  unfold Placed.rect
  cases hf : p.scene.boxes.find? (fun b => b.id == sb.id) with
  | none =>
    exact False.elim (List.find?_eq_none.mp hf sb hsb (beq_self_eq_true sb.id))
  | some b =>
    have hbmem : b ∈ p.scene.boxes := List.mem_of_find?_eq_some hf
    have hbid : b.id = sb.id := by
      simpa only [beq_iff_eq] using List.find?_some hf
    have heq : b = sb := nga_box_nodup_id_inj p.scene.boxes hn hbmem hsb hbid
    subst heq
    rfl

/-- The first fragment that knows a box id is the fragment holding it: the
holding-rect half comes from the executed placement plus `NotesBaseFrag`,
the cross-fragment absence from `NgbFirstCross`. -/
private theorem nga_firstMatch_of_cross
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBaseF : NotesBaseFrag e) (hnd : (inp.boxes.map (·.id)).Nodup)
    (hCross : NgbFirstCross e) : NotesFirstMatch e := by
  refine notesFirstMatch_holds e ?_ hCross
  intro p hp sb hsb
  rw [e.fragments_eq] at hp
  obtain ⟨l, hl, hpl⟩ := placedFlatten_mem e.placed_eq hp
  exact nga_placed_rect_self (nga_frag_scene_nodup e hBaseF hnd hl hpl) hsb

/-! ### The two whole-record assemblies -/

/-- The whole C2 geometric context of the note stage from the executed run,
local well-formedness, the contracted C2 base clause, and one narrow def per
still-open conjunct half. -/
theorem notesC2Geom_holds
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hBase : Validator.C2 e.contracted.scene.layoutDump)
    (hBaseC : NotesBaseContract e) (hBaseF : NotesBaseFrag e)
    (hRoots : NotesFragRoots e) (hCross : NgbFirstCross e)
    (hPlace : NgbEnvPlace e) (hFragC1 : NgbFragC1 e)
    (hApplTops : NgbTopPairsExclusive e) (hSameEnv : NgbSamePlaceDisjoint e)
    (hApplForeign : NgbForeignExclusive e) :
    NotesC2Geom e := by
  have hnd : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hEnv : NotesEnvFit e := notesEnvFit_holds e hPlace hFragC1
  exact ⟨nga_firstMatch_of_cross e hBaseF hnd hCross,
    notesContractMirror_holds e hBaseC,
    notesFragMirror_holds e hBaseF hRoots hnd,
    notesPlacedDisjoint_holds e hBase hApplTops hEnv hSameEnv,
    notesForeignClear_holds e hBase hApplForeign hEnv⟩

/-- The whole C3 geometric context of the note stage from the executed run,
local well-formedness, and one narrow def per still-open conjunct half. No
contracted-scene clause is needed: C3 has no contracted-C2 consumer. -/
theorem notesC3Geom_holds
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hBaseC : NotesBaseContract e) (hBaseF : NotesBaseFrag e)
    (hRoots : NotesFragRoots e) (hNotePar : NotesBundleNoteParent e)
    (hKeptPar : NotesKeptParent e) (hCross : NgbFirstCross e)
    (hPlace : NgbEnvPlace e) (hFragC1 : NgbFragC1 e) :
    NotesC3Geom e := by
  have hnd : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  exact ⟨nga_firstMatch_of_cross e hBaseF hnd hCross,
    notesContractMirror_holds e hBaseC,
    notesFragMirror_holds e hBaseF hRoots hnd,
    notesEnvFit_holds e hPlace hFragC1,
    notesParentAlign_holds e hBaseC hNotePar hnd,
    notesParentLocal_holds e hBaseF hnd,
    notesKeptClosed_holds e hBaseC hKeptPar,
    notesContractBoxEq_holds e hBaseC hnd,
    notesFragBoxEq_holds e hBaseF hnd⟩

end PipelineImpl
end Layered
end Elegant

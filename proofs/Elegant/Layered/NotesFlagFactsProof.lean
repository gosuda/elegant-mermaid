import Elegant.Layered.NotesRouterInvariantProof
import Elegant.Layered.ComposeNotesC8a

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Note-stage flag bridges: narrowed reductions for the three flag/side facts.

Proved (narrowed, over the executed `NotesExecution` run `e`):
* `notesFlagsKept_of_keptBase`: kept input routes keep id, flags, and endpoints in the
  executed contracted scene, from `nffKeptBase` (contracted-input survival plus
  executed-base preservation).
* `notesFlagsFragment_of_fragBase`: same-bundle input routes keep id, flags, and
  endpoints in every executed fragment scene, from `nffFragBase` (per-layout
  source-scene preservation).
* `notesKeptBox_of_keptOutside`: kept input routes resolve to the contracted scene
  (no fragment claims their ends), from `nffKeptOutside` (ends absent from every
  executed source scene).

Each conclusion is strictly narrower than its tracked W form (`nriFlagsKeptW`,
`nriFlagsFragmentW`, `nriKeptBoxW` in `NotesRouterInvariantProof.lean`): it covers
input routes only (`r ∈ inp.routes`), and each residual is a lemma on the way
(contracted-input, base-result, and source-scene vocabulary the target never mentions),
never a restatement. The three W forms stay open: the unguarded statements are false,
and the residuals name the exact guard each future proof must discharge
(`contractOne` and fuel induction for survival, executed-`base` preservation, and
note-id avoidance).

Witnesses (unguarded forms are false):
* flags: `r = { x with orthogonal := !x.orthogonal }` for a real bundle route `x`
  (`r ∉ inp.routes`, same id and ends, flipped flag): same-bundle holds while the
  fragment route keeps the flags of `x`.
* kept-box: route `t.note → o` with the note fragment claiming `t.note`:
  bundle-external by `bundleOf`, but claimed.

Probe evidence (`proofs/wip/Probe/NotesFlagFactsProof_probe.lean`): all six Bool
images (the three residuals plus the three narrowed conclusions) evaluate to `true`
on state, group, two-note, empty-text, and zero-size-fixed executed inputs; the note
self-loop and the nested-group inputs are rejected with `LayoutError.domain`, so the
executed-run statements hold vacuously there.
-/

/-! ## Kept-route flags via the contracted input. -/

/-- Base-side kept premise over the executed run: every kept input route survives the
`contractOne` fold with id, flags, and endpoints intact, and the executed `base` run
keeps the survivor's id, flags, and endpoints. Strictly narrower than `nriFlagsKeptW`
(executed contracted input plus base behavior, input routes only). -/
def nffKeptBase {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ r ∈ inp.routes, notesKept inp e.layouts r →
    ∃ rc ∈ e.contractedInput.routes, rc.id = r.id ∧ rc.orthogonal = r.orthogonal ∧
      rc.fromId = r.fromId ∧ rc.toId = r.toId ∧
      ∀ cr ∈ e.contracted.scene.routes, cr.id = rc.id →
        cr.orthogonal = rc.orthogonal ∧ cr.fromId = rc.fromId ∧ cr.toId = rc.toId

/-- Narrowed `notesFlagsKept` (input routes only) from the kept premise. -/
theorem notesFlagsKept_of_keptBase
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    {e : NotesExecution base exactIds fuel inp o res}
    (hbase : nffKeptBase e)
    {r : ModelRoute} (hmem : r ∈ inp.routes) (hkept : notesKept inp e.layouts r)
    {cr : Route} (hcr : cr ∈ e.contracted.scene.routes) (hid : cr.id = r.id) :
    cr.orthogonal = r.orthogonal ∧ cr.fromId = r.fromId ∧ cr.toId = r.toId := by
  obtain ⟨rc, _, hidrc, horc, hfromc, htoc, hkeep⟩ := hbase r hmem hkept
  obtain ⟨ho, hf, ht⟩ := hkeep cr hcr (hid.trans hidrc.symm)
  exact ⟨ho.trans horc, hf.trans hfromc, ht.trans htoc⟩

/-! ## Fragment flags via the per-layout source scenes. -/

/-- Fragment-side kept premise over the executed run: every same-bundle input route
keeps id, flags, and endpoints in each executed source scene (the part scene and every
note scene of every layout). Strictly narrower than `nriFlagsFragmentW` (source scenes
rather than placed fragments, input routes only). -/
def nffFragBase {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ r ∈ inp.routes, ∀ a : Nat, notesSameBundleAt inp e.layouts a r →
    ∀ l ∈ e.layouts, ∀ s ∈ (l.part :: l.notes.map (·.2)),
      ∀ fr ∈ s.scene.routes, fr.id = r.id →
        fr.orthogonal = r.orthogonal ∧ fr.fromId = r.fromId ∧ fr.toId = r.toId

/-- Narrowed `notesFlagsFragment` (input routes only) from the fragment premise. -/
theorem notesFlagsFragment_of_fragBase
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    {e : NotesExecution base exactIds fuel inp o res}
    (hfrag : nffFragBase e)
    {r : ModelRoute} (hmem : r ∈ inp.routes) {a : Nat}
    (hsame : notesSameBundleAt inp e.layouts a r)
    {p : Placed} (hpmem : p ∈ e.fragments)
    {fr : Route} (hfr : fr ∈ p.scene.routes) (hid : fr.id = r.id) :
    fr.orthogonal = r.orthogonal ∧ fr.fromId = r.fromId ∧ fr.toId = r.toId := by
  have hmem' : p ∈ e.placed.flatten := by rw [← e.fragments_eq]; exact hpmem
  obtain ⟨l, hl, hpl⟩ := placedFlatten_mem e.placed_eq hmem'
  rcases placedOf_scene hpl with hps | ⟨qn, hqn, hscene⟩
  · have hfrs : fr ∈ l.part.scene.routes := by rw [← hps]; exact hfr
    exact hfrag r hmem a hsame l hl l.part
      (List.mem_cons.mpr (Or.inl rfl)) fr hfrs hid
  · have hfrs : fr ∈ qn.2.scene.routes := by rw [← hscene]; exact hfr
    have hsmem : qn.2 ∈ l.part :: l.notes.map (·.2) :=
      List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨qn, hqn, rfl⟩))
    exact hfrag r hmem a hsame l hl qn.2 hsmem fr hfrs hid

/-! ## Kept-box resolution via source-scene absence. -/

/-- Kept-outside premise over the executed run: no executed source scene (part scene
or note scene of any layout) holds a box with a kept input route's end id. Strictly
narrower than `nriKeptBoxW` (source-scene boxes rather than placed rect lookups,
input routes only). -/
def nffKeptOutside {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ r ∈ inp.routes, notesKept inp e.layouts r →
    ∀ l ∈ e.layouts, ∀ s ∈ (l.part :: l.notes.map (·.2)),
      (∀ b ∈ s.scene.boxes, b.id ≠ r.fromId) ∧ (∀ b ∈ s.scene.boxes, b.id ≠ r.toId)

/-- A placed rect lookup misses when no scene box carries the id. -/
private theorem nff_rect_none_of_nobox {p : Placed} {id : String}
    (h : ∀ b ∈ p.scene.boxes, b.id ≠ id) : p.rect id = none := by
  have hnone : (p.scene.boxes.find? (·.id == id)) = none := by
    rw [List.find?_eq_none]
    intro b hb heq
    exact h b hb (beq_iff_eq.mp heq)
  unfold Placed.rect
  rw [hnone]
  rfl
/-- A placed fragment of the executed run claims neither end of a kept input route. -/
private theorem nff_placed_rect_none_of_outside
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    {e : NotesExecution base exactIds fuel inp o res}
    (hout : nffKeptOutside e)
    {r : ModelRoute} (hmem : r ∈ inp.routes) (hkept : notesKept inp e.layouts r)
    {p : Placed} (hpmem : p ∈ e.placed.flatten)
    {id : String} (hid : id = r.fromId ∨ id = r.toId) : p.rect id = none := by
  obtain ⟨l, hl, hpl⟩ := placedFlatten_mem e.placed_eq hpmem
  have hpair := hout r hmem hkept l hl
  rcases placedOf_scene hpl with hps | ⟨qn, hqn, hscene⟩
  · have hs := hpair l.part (List.mem_cons.mpr (Or.inl rfl))
    rcases hid with rfl | rfl
    · exact nff_rect_none_of_nobox (by rw [hps]; exact hs.1)
    · exact nff_rect_none_of_nobox (by rw [hps]; exact hs.2)
  · have hsmem : qn.2 ∈ l.part :: l.notes.map (·.2) :=
      List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨qn, hqn, rfl⟩))
    have hs := hpair qn.2 hsmem
    rcases hid with rfl | rfl
    · exact nff_rect_none_of_nobox (by rw [hscene]; exact hs.1)
    · exact nff_rect_none_of_nobox (by rw [hscene]; exact hs.2)

/-- Narrowed `notesKeptBoxContracted` (input routes only) from the outside premise. -/
theorem notesKeptBox_of_keptOutside
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    {e : NotesExecution base exactIds fuel inp o res}
    (hout : nffKeptOutside e)
    {r : ModelRoute} (hmem : r ∈ inp.routes) (hkept : notesKept inp e.layouts r) :
    notesKeptBoxContracted e.placed r := by
  constructor
  · intro p hpmem q hq
    have hrect :=
      nff_placed_rect_none_of_outside hout hmem hkept hpmem (Or.inl (rfl : r.fromId = r.fromId))
    rw [hrect] at hq
    exact absurd hq (by simp)
  · intro p hpmem q hq
    have hrect :=
      nff_placed_rect_none_of_outside hout hmem hkept hpmem (Or.inr (rfl : r.toId = r.toId))
    rw [hrect] at hq
    exact absurd hq (by simp)

end PipelineImpl
end Layered
end Elegant

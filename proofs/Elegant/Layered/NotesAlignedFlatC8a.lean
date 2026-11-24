import Elegant.Layered.RecursiveC8aInputInvariant
import Elegant.Layered.NotesDimensionsInduction
import Elegant.Layered.NotesFlatAssembly

set_option autoImplicit false
set_option warningAsError true

namespace Elegant.Layered.PipelineImpl

private theorem notesPartRun
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {ids : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base ids fuel inp o res) {l : BundleLayout} (hl : l ∈ e.layouts) :
    layoutNotes base ids fuel (subInput inp
      (fun b => b.id == l.top.id || Compound.inside inp.boxes l.top.id b.id) l.top.id) o = .ok l.part := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  obtain ⟨hlen, hget⟩ := mapM_getElem? _ _ _ e.layouts_eq
  have hlt : i < e.bundles.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨out, hrun, hout⟩ := hget i e.bundles[i] (List.getElem?_eq_getElem hlt)
  have heq : out = l := Option.some.inj (hout.symm.trans hi)
  subst out
  exact (bundleLayout_part_note_runs hrun).1

/-- The same part certificate feeds the inner induction and callers holding an
execution record rather than the whole wrapper's success equation. -/
theorem NotesExecution.partsC8a_of_flatAligned
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {ids : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base ids fuel inp o res)
    (hFlat : FlatC8aBAligned (layoutNotes base ids fuel))
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (haligned : attachedNoteParents inp = true) :
    ∀ l ∈ e.layouts, Validator.C8a l.part.scene.layoutDump := by
  intro l hl
  exact hFlat _ o l.part (notePartSubInput_wellFormed l.top.id hwf)
    (notePartSubInput_framedParents l.top.id hwf hfp)
    (attachedNoteParents_notePartSubInput hwf haligned l.top.id) (notesPartRun e hl)

/-- The guarded flat C8a lift proves recursive part scenes by fuel induction.
It consumes the contracted clause only at the current checked note input. -/
theorem notes_flatC8aB_aligned
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (ids : List String)
    (hGeom : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base ids fuel inp o res), WellFormed (inputModel inp o) →
      framedParents inp = true → attachedNoteParents inp = true → NotesC8aGeomT e)
    (hFlat : FlatC8aBAligned (base ids))
    (hContract : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base ids fuel inp o res), WellFormed (inputModel inp o) →
      framedParents inp = true → attachedNoteParents inp = true →
      Validator.C8a e.contracted.scene.layoutDump)
    (hNote : ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
      (e : NotesExecution base ids fuel inp o res), ∀ l ∈ e.layouts,
      ∀ q ∈ l.notes, Validator.C8a q.2.scene.layoutDump) :
    ∀ fuel : Nat, FlatC8aBAligned (layoutNotes base ids fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res hwf hfp haligned hok
    exact hFlat inp o res hwf hfp haligned hok
  | succ fuel ih =>
    intro inp o res hwf hfp haligned hok
    obtain hempty | hExecution := layoutNotes_success_phases hok
    · exact hFlat inp o res hwf hfp haligned hempty.2
    · obtain ⟨e⟩ := hExecution
      exact notes_c8a' e hwf (hContract fuel e hwf hfp haligned)
        (e.partsC8a_of_flatAligned ih hwf hfp haligned) (hNote fuel e)
        (hGeom fuel e hwf hfp haligned)

end Elegant.Layered.PipelineImpl

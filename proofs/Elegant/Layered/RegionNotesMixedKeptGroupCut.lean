import Elegant.Layered.RegionNotesDistinctParentEnvelopes

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- The mixed residual is closed on locally parent-aligned note executions. This is the
existing attachment-parent check, not a restriction on the role of a note. -/
theorem regionNotes_mixedKeptGroupClear_of_attachedNoteParents
    {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opt => layoutRIds ids (reindexRegionSets idSets sub) sub opt)
      exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o)) (hparents : attachedNoteParents inp = true)
    (hcontract : Validator.C8a e.contracted.scene.layoutDump) :
    NotesC8aClearKeptGroupOutsidePart e := by
  intro l hl p hp sb hsb cb hcb hfree _ _ hforeign hgroup hnote
  exact mixedNotesC8aClear_note_keptGroup e hwf hparents
    (fun _ _ _ _ h => layoutRIds_boxes_mirror h) (regionNotes_envelope_contains (idSets := idSets) e)
    hcontract hl hp hnote hsb hcb hfree hforeign hgroup

/-- Every mixed pair is covered on a locally parent-aligned region-note execution. -/
theorem regionNotes_c8aGeomT_of_attachedNoteParents
    {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opt => layoutRIds ids (reindexRegionSets idSets sub) sub opt)
      exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o)) (hparents : attachedNoteParents inp = true)
    (hcontract : Validator.C8a e.contracted.scene.layoutDump) : NotesC8aGeomT e :=
  regionNotes_c8aGeomT_of_mixedResidual (idSets := idSets) e hwf
    (regionNotes_mixedKeptGroupClear_of_attachedNoteParents (idSets := idSets) e hwf hparents hcontract)
    hcontract

end Elegant.Layered.PipelineImpl

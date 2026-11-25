import Elegant.Layered.ExactSubInputStepC2
import Elegant.Layered.NotesAlignedFlatC8a
import Elegant.Layered.NotesIndividualC8a
import Elegant.Layered.RegionC8aGroupPlainCutover
import Elegant.Layered.RegionNotesMixedKeptGroupCut
import Elegant.Layered.RegionFrameStepClosure
import Elegant.Layered.RegionNotesSameBundleC8a
import Elegant.Layered.RegionNotesContractedC8a

set_option autoImplicit false
set_option warningAsError true

namespace Elegant.Layered.PipelineImpl

private abbrev alignedRegionBase (idSets : List (String × List String)) :=
  fun (ids : List String) (inp : Input) (o : Options) =>
    layoutRIds ids (reindexRegionSets idSets inp) inp o

/-- Flat note-stage C8a for parent-aligned inputs, using contracted and
raw-region C8a. -/
theorem regionNotes_flatC8aAligned {exactIds : List String}
    {idSets : List (String × List String)} :
    ∀ fuel : Nat, FlatC8aBAligned (layoutNotes (alignedRegionBase idSets) exactIds fuel) :=
  notes_flatC8aB_aligned (base := alignedRegionBase idSets) exactIds
    (by
      intro fuel inp o res e hwf hfp hparents
      have hcontract := regionNotes_contractedC8aAligned (idSets := idSets) fuel e hwf hfp hparents
      exact regionNotes_c8aGeomT_of_attachedNoteParents (idSets := idSets) e hwf hparents hcontract)
    (fun inp o res hwf hfp _ hok => flatC8aB_layoutRIds_reindex_closed exactIds idSets
      inp o res hwf hfp hok)
    (regionNotes_contractedC8aAligned (exactIds := exactIds) (idSets := idSets)) (by
      intro fuel inp o res e
      exact regionNotes_individualC8a (idSets := idSets) e)

/-- The recursive note base preserves the box mirror and fixed reservations.
    The wrapped flat inset composes with the existing execution's frame fit. -/
theorem stepC8a_regionNotes (exactIds : List String)
    (idSets : List (String × List String)) (outerFuel : Nat) :
    RecursiveStepFactsB (layoutNotes (alignedRegionBase idSets) exactIds outerFuel)
      ExpandChildC8aStep := by
  refine stepC8aB_of_boxMirror (layoutNotes (alignedRegionBase idSets) exactIds outerFuel)
    ?_ (flatInsetB_regionNotes idSets exactIds outerFuel)
  intro sub opt res h
  exact ⟨layoutNotes_boxes_mirror (fun _ _ _ _ hRegion => layoutRIds_boxes_mirror hRegion)
      outerFuel h, layoutRegionNotes_fixedBoxDimensions idSets h⟩

/-- Successful region-note family runs satisfy C8a under the alignment
checked by family admission. -/
theorem layoutFamilyRN_c8a {exactIds : List String}
    {sets : List ModelRegionSet} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (hgraph : RegionImpl.graphRegions inp sets = .ok idSets)
    (h : layoutFamilyRN exactIds sets inp o = .ok res) : Validator.C8a res.scene.layoutDump := by
  have hB : layoutFamilyB (layoutNotes (alignedRegionBase idSets) exactIds (inp.boxes.length + 1))
      inp o = .ok res := by
    simpa only [layoutFamilyRN, hgraph] using h
  obtain ⟨hwf, hrec⟩ := layoutFamilyB_success hB
  exact layoutRecursiveB_c8a_aligned _
    (regionNotes_flatC8aAligned (exactIds := exactIds) (idSets := idSets) (inp.boxes.length + 1))
    (subInputWellFormedB_of _)
    (stepC8a_regionNotes exactIds idSets (inp.boxes.length + 1))
    (inp.boxes.length + 1) inp o res hwf (layoutFamilyB_framed_parents hB)
    (layoutFamilyB_attached_note_parents hB) hrec

end Elegant.Layered.PipelineImpl

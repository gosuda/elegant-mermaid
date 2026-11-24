import Elegant.Layered.NotesDimensionsInduction
import Elegant.Layered.RegionSceneDimensions

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem region_fragments_boxes_nonneg
    {idSets : List (String × List String)} {exactIds : List String} {fuel : Nat}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opts => layoutRIds ids (reindexRegionSets idSets sub) sub opts)
      exactIds fuel inp o res) :
    ∀ p ∈ e.fragments, ∀ b ∈ p.scene.boxes, 0 ≤ b.rect.w ∧ 0 ≤ b.rect.h := by
  intro p hp
  rw [e.fragments_eq] at hp
  obtain ⟨l, hl, hPlaced⟩ := placedFlatten_mem e.placed_eq hp
  obtain ⟨hLength, hRuns⟩ := mapM_getElem? _ e.bundles e.layouts e.layouts_eq
  obtain ⟨i, hIndex⟩ := List.mem_iff_getElem?.mp hl
  have hi : i < e.bundles.length := hLength ▸ (List.getElem?_eq_some_iff.mp hIndex).1
  have hBundle : e.bundles[i]? = some e.bundles[i] := List.getElem?_eq_getElem hi
  obtain ⟨actual, hLayout, hActual⟩ := hRuns i e.bundles[i] hBundle
  have hSame : actual = l := Option.some.inj (hActual.symm.trans hIndex)
  subst actual
  obtain ⟨hPart, hNotes⟩ := bundleLayout_part_note_runs hLayout
  rcases placedOf_scene hPlaced with hScene | ⟨q, hq, hScene⟩
  · rw [hScene]
    exact layoutNotes_boxes_nonneg
      (base := fun ids sub opts => layoutRIds ids (reindexRegionSets idSets sub) sub opts)
      (fun _ _ _ _ h => layoutRIds_boxes_dims_nonneg h) hPart
  · rw [hScene]
    exact layoutRIds_boxes_dims_nonneg (hNotes q hq)

theorem NotesExecution.region_boxes_nonneg
    {idSets : List (String × List String)} {exactIds : List String} {fuel : Nat}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opts => layoutRIds ids (reindexRegionSets idSets sub) sub opts)
      exactIds fuel inp o res) :
    ∀ b ∈ res.scene.boxes, 0 ≤ b.rect.w ∧ 0 ≤ b.rect.h :=
  e.boxes_nonneg (layoutRIds_boxes_dims_nonneg e.contracted_eq)
    (region_fragments_boxes_nonneg e)

theorem NotesExecution.region_rects_lookup_nonneg
    {idSets : List (String × List String)} {exactIds : List String} {fuel : Nat}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opts => layoutRIds ids (reindexRegionSets idSets sub) sub opts)
      exactIds fuel inp o res)
    {id : String} {rect : Rect}
    (hLookup : (notesRectsOf res.scene.boxes).lookup id = some rect) :
    0 ≤ rect.w ∧ 0 ≤ rect.h :=
  e.rects_lookup_nonneg (layoutRIds_boxes_dims_nonneg e.contracted_eq)
    (region_fragments_boxes_nonneg e) hLookup

end Elegant.Layered.PipelineImpl

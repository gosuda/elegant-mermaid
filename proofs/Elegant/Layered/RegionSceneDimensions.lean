import Elegant.Layered.RegionBaseExecutedValidity

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem partRects_dims_nonneg {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) {part : List Nat × Part}
    (hpart : part ∈ execution.componentsAcc.parts) {rect : Rect} (hrect : rect ∈ part.2.rects) :
    0 ≤ rect.w ∧ 0 ≤ rect.h := by
  obtain ⟨_, hall⟩ := actual_components_parts_geometryR (by rfl) execution.components_eq
  obtain ⟨_, _, cg, run, loops, _, _, _, _, _, _, hrun, _, heq⟩ := hall part hpart
  have hdims := (R_partSizingR_chosenFacts execution hrun).1
  have hcovered := componentRunR_original_nodes_covered hrun
  rw [heq] at hrect
  change rect ∈ (placeComponentExact execution.params cg run 0 execution.measured loops).rects
    at hrect
  unfold placeComponentExact at hrect
  dsimp only at hrect
  obtain ⟨unshifted, hunshifted, rfl⟩ := List.mem_map.mp hrect
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hunshifted
  dsimp only [shiftRect]
  exact frameRect_dims_nonneg execution.params cg run i hdims (hcovered i (List.mem_range.mp hi))

private theorem packedRect_dims_nonneg {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) {index : Nat}
    (hi : index < inp.boxes.length) :
    0 ≤ (execution.packedAcc.rects.getD index default).w ∧
      0 ≤ (execution.packedAcc.rects.getD index default).h := by
  obtain ⟨part, hpart, ⟨key, rect⟩, hentry, hkey⟩ := sceneExecutionR_parts_entryR execution hi
  change key = index at hkey
  subst key
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hpart
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hentry
  have hp := execution.packed_eq
  unfold packAcc at hp
  obtain ⟨packed, hpack, _⟩ := bind_ok hp
  have hkLen : k < packed.boxes.length := by
    rw [Pack.pack_count hpack, List.length_map]
    exact (List.getElem?_eq_some_iff.mp hk).1
  let shelf := packed.boxes[k]
  have hshelf : packed.boxes[k]? = some shelf := List.getElem?_eq_getElem hkLen
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[k]? = some (part, shelf) :=
    List.getElem?_zip_eq_some.mpr ⟨hk, hshelf⟩
  have hsize : index < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_sizeR]
    exact hi
  rw [actual_components_packed_rect_valueR (by rfl) execution.components_eq
    execution.packed_eq packed hpack hselected hj hsize default]
  dsimp only [shiftRect]
  exact partRects_dims_nonneg execution hpart (List.of_mem_zip hentry).2

/-- The selected component run checks the sizes after fixed-size substitution and
region placement. Frame construction, packing, and output orientation preserve
nonnegative dimensions without any additional input admission premise. -/
theorem layoutRIds_boxes_dims_nonneg {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRIds exactIds idSets inp o = .ok res) :
    ∀ b ∈ res.scene.boxes, 0 ≤ b.rect.w ∧ 0 ≤ b.rect.h := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  intro box hbox
  rw [execution.boxes_eq_mapR] at hbox
  obtain ⟨⟨source, index⟩, hsource, rfl⟩ := List.mem_map.mp hbox
  have hi := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hsource)).1
  have hdims := packedRect_dims_nonneg execution hi
  change 0 ≤ (orientRect o.direction execution.packedAcc.canvasH
      (execution.packedAcc.rects.getD index default)).w ∧
    0 ≤ (orientRect o.direction execution.packedAcc.canvasH
      (execution.packedAcc.rects.getD index default)).h
  cases o.direction <;> first | exact hdims | exact ⟨hdims.2, hdims.1⟩

end Elegant.Layered.PipelineImpl

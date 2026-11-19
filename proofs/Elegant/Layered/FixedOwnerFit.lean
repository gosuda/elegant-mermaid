import Elegant.Layered.SizingCoverageBridge
import Elegant.Layered.InputFixedFit

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

theorem SceneExecution.fixed_box_dominates
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {i : Nat} {box : Box} {source : ModelBox} {entry : String × Size}
    (hbox : res.scene.boxes[i]? = some box)
    (hsource : inp.boxes[i]? = some source)
    (hfixed : inp.fixedSizes.find? (fun e => e.1 == source.id) = some entry) :
    entry.2.w ≤ box.rect.w ∧ entry.2.h ≤ box.rect.h := by
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    simp only [boxLines] at h
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
        (mapM_getElem? _ _ _ h).1
      _ = inp.boxes.length := List.length_zipIdx
  have hi : i < execution.lines.length :=
    hlinesLen ▸ (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨ls, hline⟩ : ∃ ls, execution.lines[i]? = some ls :=
    ⟨_, List.getElem?_eq_getElem hi⟩
  obtain ⟨rect, hrect⟩ := execution.packed_rect_exists
    (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨node, hnode, _, hborder, hnw, hnh⟩ :=
    measuredGraph_fixed_node_dims execution.graph_eq hline hsource hfixed
  have hfit := execution.packed_rect_minimum_dims_of_coverage
    execution.parts_coverage hnode hborder hrect
  obtain ⟨actual, hactual, hboxeq⟩ := execution.box_index_origin hbox
  rw [hsource] at hactual
  cases Option.some.inj hactual
  have hget : execution.packedAcc.rects.getD i default = rect := by
    obtain ⟨hii, heq⟩ := Array.getElem?_eq_some_iff.mp hrect
    simpa [Array.getD, hii] using heq
  rw [hboxeq, hget]
  dsimp only [shiftRect]
  cases hd : o.direction <;>
    simp only [hd, orientRect] at hnw hnh hfit ⊢ <;> omega

theorem SceneExecution.fixed_owner_fit
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {i : Nat} {box : Box} {source : ModelBox}
    (hfit : InputFixedFit inp o)
    (hbox : res.scene.boxes[i]? = some box)
    (hsource : inp.boxes[i]? = some source)
    (hany : inp.fixedSizes.any (fun e => e.1 == source.id) = true)
    (hex : source.exclusive = false)
    (hown : ∃ l ∈ inp.labels, l.owner = source.id) :
    FixedSizeFit execution.params source.role (execution.lines.getD i [])
      ⟨box.rect.w, box.rect.h⟩ := by
  obtain ⟨entry, hfixed⟩ :
      ∃ entry, inp.fixedSizes.find? (fun e => e.1 == source.id) = some entry := by
    cases hf : inp.fixedSizes.find? (fun e => e.1 == source.id) with
    | none =>
      obtain ⟨e, hmem, hid⟩ := List.any_eq_true.mp hany
      exact absurd (List.find?_eq_none.mp hf e hmem) (by rw [hid]; decide)
    | some entry => exact ⟨entry, rfl⟩
  have hmem : entry ∈ inp.fixedSizes := List.mem_of_find?_eq_some hfixed
  have hid : entry.1 = source.id := by simpa using List.find?_some hfixed
  have hwrap : StyledMeasure.wrap execution.metric
      (Measure.wrapTarget execution.metric.profile execution.params.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD i source.id).toList =
        .ok (execution.lines.getD i []) := by
    have hlines := execution.lines_eq
    simp only [boxLines] at hlines
    obtain ⟨_, hlookup⟩ := mapM_getElem? _ _ _ hlines
    obtain ⟨measured, hmeasured, hindex⟩ := hlookup i (source, i)
      (by simp only [List.getElem?_zipIdx, hsource, Option.map_some, Nat.zero_add])
    dsimp only at hmeasured
    have hget : execution.lines.getD i [] = measured := by
      simp only [List.getD_eq_getElem?_getD, hindex, Option.getD_some]
    rw [hget]
    exact hmeasured
  have hfit' : FixedSizeFit execution.params source.role (execution.lines.getD i [])
      entry.2 :=
    hfit entry hmem i source hsource hid.symm hex hown
      execution.params execution.metric (execution.lines.getD i [])
      execution.checked execution.metric_eq hwrap
  have hdom := execution.fixed_box_dominates hbox hsource hfixed
  exact FixedSizeFit.mono hfit' hdom.1 hdom.2

end PipelineImpl
end Layered
end Elegant

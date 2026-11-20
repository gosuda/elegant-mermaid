import Elegant.Layered.ComponentCoverage
import Elegant.Layered.PlainNodeSizingFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem componentFold_rects_size
    (P : Params) (inp : Input) (o : Options) (g : Graph)
    (measured : List MeasuredLabel) (comps : List (List Nat)) :
    ∀ start out : Acc,
      comps.foldlM (fun acc comp => layoutComponent P inp o g acc comp measured) start =
        .ok out → out.rects.size = start.rects.size := by
  induction comps with
  | nil =>
    intro start out h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
  | cons comp rest ih =>
    intro start out h
    simp only [List.foldlM_cons] at h
    cases hc : layoutComponent P inp o g start comp measured with
    | error e => simp [hc, bind, Except.bind] at h
    | ok next =>
      simp only [hc, bind, Except.bind] at h
      exact (ih next out h).trans (layoutComponent_sizes hc).1.symm

private theorem packFold_rects_size
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons, ih]
    exact (packStep_sizes start pair).1

theorem SceneExecution.components_rects_size
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    execution.componentsAcc.rects.size = inp.boxes.length := by
  have h := componentFold_rects_size execution.params inp o execution.graph
    execution.measured (components execution.graph) _ _ execution.components_eq
  simpa only [Array.size_replicate] using h

theorem SceneExecution.parts_coverage
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    ∀ i rect, execution.componentsAcc.rects[i]? = some rect →
      ∃ part ∈ execution.componentsAcc.parts,
        ∃ entry ∈ part.1.zip part.2.rects, entry.1 = i := by
  intro i rect hrect
  have hi := (Array.getElem?_eq_some_iff.mp hrect).1
  rw [execution.components_rects_size] at hi
  exact sceneExecution_parts_entry execution hi

theorem SceneExecution.packed_rects_size
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    execution.packedAcc.rects.size = inp.boxes.length := by
  have h := execution.packed_eq
  unfold packAcc at h
  obtain ⟨packed, _, h⟩ := bind_ok h
  have hout := Except.ok.inj h
  rw [← hout]
  change ((execution.componentsAcc.parts.zip packed.boxes).foldl packStep
    { execution.componentsAcc with
      canvasW := packed.width
      canvasH := packed.height
      titles := [] }).rects.size = inp.boxes.length
  rw [packFold_rects_size]
  exact execution.components_rects_size

theorem SceneExecution.packed_rect_exists
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {i : Nat} (hi : i < inp.boxes.length) :
    ∃ rect, execution.packedAcc.rects[i]? = some rect := by
  have hsize : i < execution.packedAcc.rects.size := by
    rw [execution.packed_rects_size]
    exact hi
  exact ⟨execution.packedAcc.rects[i],
    Array.getElem?_eq_some_iff.mpr ⟨hsize, rfl⟩⟩

theorem SceneExecution.ordinary_node_packed_fit
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {i : Nat} {ls : List Measure.Line} {box : ModelBox}
    (hline : execution.lines[i]? = some ls)
    (hbox : inp.boxes[i]? = some box) (hrole : box.role = .node)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false) :
    ∃ rect, execution.packedAcc.rects[i]? = some rect ∧
      (ls.foldl (fun w line => max w line.width) 0) ≤
        (orientRect o.direction execution.packedAcc.canvasH rect).w ∧
      ((ls.length : Int) * execution.params.lineH) ≤
        (orientRect o.direction execution.packedAcc.canvasH rect).h := by
  obtain ⟨rect, hrect⟩ := execution.packed_rect_exists
    (List.getElem?_eq_some_iff.mp hbox).1
  obtain ⟨node, hnode, _, _⟩ := measuredGraph_node_border_zero
    execution.checked execution.graph_eq hline hbox hrole hfixed
  exact ⟨rect, hrect, execution.ordinary_node_packed_text_fit
    execution.parts_coverage hline hbox hrole hfixed hnode hrect⟩

theorem SceneExecution.ordinary_box_line_height
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {index : Nat} {box : Box} (hbox : res.scene.boxes[index]? = some box)
    {source : ModelBox} (hsource : inp.boxes[index]? = some source)
    (hrole : source.role = .node)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false)
    {ls : List Measure.Line} (hline : execution.lines[index]? = some ls) :
    (ls.foldl (fun w line => max w line.width) 0) ≤ box.rect.w ∧
      ((ls.length : Int) * execution.params.lineH) ≤ box.rect.h := by
  obtain ⟨rect, hrect⟩ := execution.packed_rect_exists
    (List.getElem?_eq_some_iff.mp hsource).1
  exact execution.ordinary_box_line_height_of_coverage execution.parts_coverage
    hbox hsource hrole hfixed hline hrect

end Elegant.Layered.PipelineImpl

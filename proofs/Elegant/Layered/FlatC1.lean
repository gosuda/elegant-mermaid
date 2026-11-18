import Elegant.Layered.SceneBounds
import Elegant.Layered.CellRectToC1

set_option autoImplicit false

namespace Elegant.Layered

/-- Every box of a successful flat `PipelineImpl.layout` scene lies inside the
canvas: the executed packing bounds give `Size.containsCellRect` on each scene
box, and `containsCellRect_contained` turns that into `Validator.C1`. -/
theorem layout_c1 {inp : Input} {o : Options} {res : FamilyResult}
    (h : PipelineImpl.layout inp o = .ok res) : Validator.C1 res.scene.layoutDump := by
  obtain ⟨_, _, hboxes, _⟩ := PipelineImpl.layout_scene_box_route_bounded_of_success h
  intro b hb
  simp only [Scene.layoutDump] at hb ⊢
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  have hzip : (b, i) ∈ res.scene.boxes.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    exact hi
  have hbnd := hboxes (b, i) hzip
  dsimp only at hbnd
  exact containsCellRect_contained hbnd

end Elegant.Layered

import Elegant.Layered.NotesFlatRouteClauses

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Composition keeps the dimensions of the contracted or placed fragment box it selected. -/
theorem NotesExecution.boxes_nonneg
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : ∀ b ∈ e.contracted.scene.boxes, 0 ≤ b.rect.w ∧ 0 ≤ b.rect.h)
    (hFrag : ∀ p ∈ e.fragments, ∀ b ∈ p.scene.boxes, 0 ≤ b.rect.w ∧ 0 ≤ b.rect.h) :
    ∀ b ∈ res.scene.boxes, 0 ≤ b.rect.w ∧ 0 ≤ b.rect.h := by
  intro b hb
  obtain ⟨_, _, _, _, _, _, hRect⟩ := e.boxes_mem b hb
  rcases classifyRect hRect with ⟨p, hp, hPlaced⟩ | ⟨_, cb, hcb, _, hContracted⟩
  · obtain ⟨sb, hsb, _, hShift⟩ := Placed.rect_scene_box hPlaced
    have hMember : p ∈ e.fragments := by
      rw [e.fragments_eq]
      exact hp
    obtain ⟨hw, hh⟩ := hFrag p hMember sb hsb
    rw [← hShift]
    exact notesShiftRect_nonneg hw hh p.dx p.dy
  · rw [← hContracted]
    exact hBase cb hcb

/-- A successful router rectangle lookup inherits dimensions from the selected scene box. -/
theorem NotesExecution.rects_lookup_nonneg
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : ∀ b ∈ e.contracted.scene.boxes, 0 ≤ b.rect.w ∧ 0 ≤ b.rect.h)
    (hFrag : ∀ p ∈ e.fragments, ∀ b ∈ p.scene.boxes, 0 ≤ b.rect.w ∧ 0 ≤ b.rect.h)
    {id : String} {rect : Rect}
    (hLookup : (notesRectsOf res.scene.boxes).lookup id = some rect) :
    0 ≤ rect.w ∧ 0 ≤ rect.h := by
  obtain ⟨before, after, hSplit, _⟩ := List.lookup_eq_some_iff.mp hLookup
  have hPair : (id, rect) ∈ notesRectsOf res.scene.boxes := by
    rw [hSplit]
    exact List.mem_append_right before List.mem_cons_self
  change (id, rect) ∈ res.scene.boxes.map (fun b => (b.id, b.rect)) at hPair
  obtain ⟨b, hb, heq⟩ := List.mem_map.mp hPair
  have hRect : b.rect = rect := congrArg Prod.snd heq
  rw [← hRect]
  exact e.boxes_nonneg hBase hFrag b hb

end PipelineImpl
end Layered
end Elegant

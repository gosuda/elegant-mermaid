import Elegant.Layered.Pipeline
import Elegant.Layered.ExactPipeline

set_option autoImplicit false

/-! Consequences of the attached-note parent guard: a successful family layout implies every
note box attached through `attachmentsOf` shares its target's parent. -/

namespace Elegant
namespace Layered

theorem attachedNoteParents_eq {inp : Input} (h : attachedNoteParents inp = true) :
    ∀ a ∈ attachedNotes inp.boxes, noteParentOK inp.boxes a = true := by
  unfold attachedNoteParents at h
  exact List.all_eq_true.mp h

theorem layoutFamily_attached_note_parents {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutFamily inp o = .ok res) :
    attachedNoteParents inp = true := by
  by_cases hn : o.limits.maxNodes < inp.boxes.length <;>
    by_cases he : o.limits.maxEdges < inp.routes.length <;>
    by_cases ht : o.limits.maxTextBytes < inputTextBytes inp <;>
    by_cases hw : modelWellFormed (inputModel inp o) <;>
    by_cases hf : framedParents inp <;>
    by_cases ha : attachedNoteParents inp <;>
    simp_all [layoutFamily]

theorem layoutFamilyB_attached_note_parents
    {base : Input → Options → Except LayoutError FamilyResult} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutFamilyB base inp o = .ok res) :
    attachedNoteParents inp = true := by
  by_cases hn : o.limits.maxNodes < inp.boxes.length <;>
    by_cases he : o.limits.maxEdges < inp.routes.length <;>
    by_cases ht : o.limits.maxTextBytes < inputTextBytes inp <;>
    by_cases hw : modelWellFormed (inputModel inp o) <;>
    by_cases hf : framedParents inp <;>
    by_cases ha : attachedNoteParents inp <;>
    simp_all [layoutFamilyB]

end Layered
end Elegant

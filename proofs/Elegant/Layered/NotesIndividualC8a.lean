import Elegant.Layered.NotesGeomC68Proof

set_option autoImplicit false
set_option warningAsError true

namespace Elegant.Layered.PipelineImpl

private theorem noteSubInput_id {inp : Input} {id : String} {b : ModelBox}
    (hb : b ∈ (subInput inp (fun x => x.id == id) id).boxes) : b.id = id := by
  change b ∈ ((selectInput inp (fun x => x.id == id)).boxes.map fun x =>
    if x.id == id then { x with parent := "" } else x) at hb
  obtain ⟨selected, hs, rfl⟩ := List.mem_map.mp hb
  obtain ⟨src, _, hkeep, hid, _⟩ := selectInput_box_spec inp (fun x => x.id == id) "" hs
  have hselected : selected.id = id := hid.trans (beq_iff_eq.mp hkeep)
  by_cases he : (selected.id == id) = true
  · rw [ite_eq_left he]
    exact hselected
  · rw [ite_eq_right he]
    exact hselected

/-- An individually laid-out note has no distinct-id box pair. Its role and
its original parent or children are immaterial to this raw sub-run. -/
theorem notesIndividualC8a_of_box_mirror
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hBase : ∀ ids sub opt result, base ids sub opt = .ok result → NotesBoxMirror sub result) :
    ∀ l ∈ e.layouts, ∀ q ∈ l.notes, Validator.C8a q.2.scene.layoutDump := by
  have hfrag := notesBaseFrag_of_box_mirror hBase e
  intro l hl q hq
  have hId : ∀ b ∈ q.2.scene.boxes, b.id = q.1.id := by
    intro b hb
    obtain ⟨src, hsrc, hid, _, _⟩ := ((hfrag l hl).2 q hq).2 b hb
    exact hid.trans (noteSubInput_id hsrc)
  intro group hg _ b hb hne _ _
  exact (hne ((hId b hb).trans (hId group hg).symm)).elim

theorem regionNotes_individualC8a {idSets : List (String × List String)}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution (fun ids sub opt => layoutRIds ids (reindexRegionSets idSets sub) sub opt)
      exactIds fuel inp o res) :
    ∀ l ∈ e.layouts, ∀ q ∈ l.notes, Validator.C8a q.2.scene.layoutDump :=
  notesIndividualC8a_of_box_mirror e (fun _ _ _ _ h => layoutRIds_boxes_mirror h)

end Elegant.Layered.PipelineImpl

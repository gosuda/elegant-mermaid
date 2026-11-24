import Elegant.Layered.NotesMirrorFacts
import Elegant.Layered.NoteParents

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem attachedNotes_eq_map_attachmentsOf (boxes : List ModelBox) :
    attachedNotes boxes = (attachmentsOf boxes).map (fun a => (a.target, a.note, a.right)) := by
  simp only [attachedNotes, attachmentsOf, List.map_filterMap]
  congr 1
  funext q
  change (if q.1.shape == "note" && (q.1.direction == "left" || q.1.direction == "right") then
    (noteTargetId q.1.id).bind fun target =>
      (boxes.findIdx? (·.id == target)).map fun t => (t, q.2, q.1.direction == "right")
    else none) = _
  by_cases h : (q.1.shape == "note" && (q.1.direction == "left" || q.1.direction == "right")) = true
  · simp only [ite_eq_left h, Option.map_bind, Option.map_map, Function.comp_def]
  · simp only [ite_eq_right h, Option.map_none]

private theorem bundlesOf_note_mem (boxes : List ModelBox) (atts : List Attach) :
    ∀ b ∈ bundlesOf boxes atts, ∀ a ∈ b.notes, a ∈ atts ∧ a.target = b.target := by
  unfold bundlesOf
  refine List.foldlRecOn (motive := fun bs : List Bundle => ∀ b ∈ bs, ∀ a ∈ b.notes,
    a ∈ atts ∧ a.target = b.target) atts _ ?_ ?_
  · simp
  · intro acc ih next _
    by_cases h : (isNested boxes atts next.target || acc.any (·.target == next.target)) = true
    · simpa only [ite_eq_left h] using ih
    · simp only [ite_eq_right h]
      intro b hb a ha
      rcases List.mem_append.mp hb with hb | hb
      · exact ih b hb a ha
      · have heq := List.mem_singleton.mp hb
        subst b
        change a ∈ atts.filter (·.target == next.target) at ha
        obtain ⟨hm, ht⟩ := List.mem_filter.mp ha
        exact ⟨hm, beq_iff_eq.mp ht⟩

private theorem mapM_mem_origin {α β : Type} {f : α → Except LayoutError β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, f x = .ok y := by
  obtain ⟨i, hiy⟩ := List.mem_iff_getElem?.mp hy
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hiy
  obtain ⟨hlen, hget⟩ := mapM_getElem? f xs ys h
  have hi : i < xs.length := by rwa [← hlen]
  obtain ⟨out, hf, hout⟩ := hget i xs[i] (List.getElem?_eq_getElem hi)
  have heq : out = y := Option.some.inj (hout.symm.trans hiy)
  exact ⟨xs[i], List.getElem_mem hi, heq ▸ hf⟩

private theorem bundleLayout_note_origin {recur base : Input → Options → Except LayoutError FamilyResult}
    {inp : Input} {o : Options} {margin gap : Int} {b : Bundle} {l : BundleLayout}
    (h : bundleLayout recur base inp o margin gap b = .ok l)
    {q : ModelBox × FamilyResult} (hq : q ∈ l.notes) :
    inp.boxes[b.target]? = some l.top ∧ ∃ a ∈ b.notes, inp.boxes[a.note]? = some q.1 := by
  unfold bundleLayout at h
  cases htop : inp.boxes[b.target]? with
  | none => simp [htop] at h
  | some top =>
    rw [htop] at h
    simp only [bind, Except.bind] at h
    obtain ⟨part, _, h⟩ := bind_ok' h
    obtain ⟨notes, hnotes, h⟩ := bind_ok' h
    have hl : l = ⟨top, b, part, notes, _⟩ := (Except.ok.inj h).symm
    rw [hl] at hq ⊢
    refine ⟨rfl, ?_⟩
    obtain ⟨a, ha, hrun⟩ := mapM_mem_origin hnotes hq
    cases hbox : inp.boxes[a.note]? with
    | none => simp [hbox] at hrun
    | some box =>
      rw [hbox] at hrun
      dsimp only at hrun
      obtain ⟨r, _, hrun⟩ := bind_ok' hrun
      have hpair : q = (box, r) := (Except.ok.inj hrun).symm
      refine ⟨a, ha, ?_⟩
      rwa [hpair]

/-- Every laid-out note shares its bundle top's input parent by the admission check on their indices. -/
theorem notesBundleNoteParent_holds
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hparents : attachedNoteParents inp = true) : NotesBundleNoteParent e := by
  intro l hl q hq
  obtain ⟨b, hb, hrun⟩ := mapM_mem_origin e.layouts_eq hl
  obtain ⟨htop, a, ha, hbox⟩ := bundleLayout_note_origin hrun hq
  rw [e.bundles_eq, e.atts_eq] at hb
  obtain ⟨hatt, htarget⟩ := bundlesOf_note_mem _ _ b hb a ha
  have htuple : (a.target, a.note, a.right) ∈ attachedNotes inp.boxes := by
    rw [attachedNotes_eq_map_attachmentsOf]
    exact List.mem_map.mpr ⟨a, hatt, rfl⟩
  have htargetBox : inp.boxes[a.target]? = some l.top := by rwa [htarget]
  have hchecked := attachedNoteParents_eq hparents _ htuple
  have heq : (q.1.parent == l.top.parent) = true := by
    simpa only [noteParentOK, htargetBox, hbox] using hchecked
  exact beq_iff_eq.mp heq

end Elegant.Layered.PipelineImpl

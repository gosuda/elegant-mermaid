import Elegant.Layered.NoteParents
import Elegant.Layered.NotesStepGuardProof
import Elegant.Layered.NotesSubInputWellFormedExecuted
import Elegant.Layered.StatePipeline

set_option autoImplicit false
set_option warningAsError true

namespace Elegant.Layered.PipelineImpl

private theorem attachmentRows (boxes : List ModelBox) :
    attachedNotes boxes = boxes.zipIdx.filterMap (fun q =>
      if q.1.shape == "note" && (q.1.direction == "left" || q.1.direction == "right") then
        (noteTargetId q.1.id).bind fun id =>
          (boxes.findIdx? (·.id == id)).map fun i => (i, q.2, q.1.direction == "right")
      else none) := rfl

private theorem alignedPair {inp : Input} (hnt : (inp.boxes.map (·.id)).Nodup)
    (haligned : attachedNoteParents inp = true) {note target : ModelBox}
    (hnote : note ∈ inp.boxes) (htarget : target ∈ inp.boxes)
    (htrigger : (note.shape == "note" && (note.direction == "left" || note.direction == "right")) = true)
    (hname : noteTargetId note.id = some target.id) : note.parent = target.parent := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hnote
  cases hidx : inp.boxes.findIdx? (·.id == target.id) with
  | none =>
    have hnone := List.findIdx?_eq_none_iff.mp hidx target htarget
    simp at hnone
  | some i =>
    obtain ⟨hi, htest, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hidx
    have heq := eq_of_mem_id hnt (List.getElem_mem hi) htarget (beq_iff_eq.mp htest)
    have ht : inp.boxes[i]? = some target := by rw [List.getElem?_eq_getElem hi, heq]
    have hmem : (i, j, note.direction == "right") ∈ attachedNotes inp.boxes := by
      rw [attachmentRows]
      refine List.mem_filterMap.mpr ⟨(note, j), List.mem_zipIdx_iff_getElem?.mpr hj, ?_⟩
      change (if note.shape == "note" && (note.direction == "left" || note.direction == "right") then
        (noteTargetId note.id).bind fun id =>
          (inp.boxes.findIdx? (·.id == id)).map fun k => (k, j, note.direction == "right")
        else none) = some (i, j, note.direction == "right")
      rw [ite_eq_left htrigger, hname, Option.bind_some, hidx, Option.map_some]
    have h := attachedNoteParents_eq haligned _ hmem
    exact beq_iff_eq.mp (by simpa only [noteParentOK, ht, hj] using h)

private theorem attachedNoteParents_of_pairs {out : Input}
    (h : ∀ note ∈ out.boxes, ∀ target ∈ out.boxes,
      (note.shape == "note" && (note.direction == "left" || note.direction == "right")) = true →
      noteTargetId note.id = some target.id → note.parent = target.parent) :
    attachedNoteParents out = true := by
  unfold attachedNoteParents
  rw [List.all_eq_true]
  intro a ha
  rw [attachmentRows] at ha
  obtain ⟨q, hq, hrow⟩ := List.mem_filterMap.mp ha
  by_cases htrigger : (q.1.shape == "note" && (q.1.direction == "left" || q.1.direction == "right")) = true
  · rw [ite_eq_left htrigger] at hrow
    obtain ⟨name, hname, hrow⟩ := Option.bind_eq_some_iff.mp hrow
    obtain ⟨i, hidx, rfl⟩ := Option.map_eq_some_iff.mp hrow
    obtain ⟨hi, htest, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hidx
    have hqget := List.mem_zipIdx_iff_getElem?.mp hq
    have ht := h q.1 (List.mem_of_getElem? hqget) out.boxes[i] (List.getElem_mem hi)
      htrigger (by rw [hname, beq_iff_eq.mp htest])
    simpa only [noteParentOK, List.getElem?_eq_getElem hi, hqget] using
      (beq_iff_eq.mpr ht : (q.1.parent == out.boxes[i].parent) = true)
  · rw [ite_eq_right htrigger] at hrow
    cases hrow

private theorem attachedNoteParents_parentMap {inp out : Input}
    (hnt : (inp.boxes.map (·.id)).Nodup) (haligned : attachedNoteParents inp = true)
    (keep : ModelBox → Bool) (parent : ModelBox → String)
    (hboxes : out.boxes = (inp.boxes.filter keep).map (fun b => { b with parent := parent b }))
    (hpar : ∀ a ∈ inp.boxes, keep a = true → ∀ b ∈ inp.boxes, keep b = true →
      a.parent = b.parent → parent a = parent b) : attachedNoteParents out = true := by
  apply attachedNoteParents_of_pairs
  intro note hn target ht htrigger hname
  rw [hboxes] at hn ht
  obtain ⟨a, ham, rfl⟩ := List.mem_map.mp hn
  obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp ht
  obtain ⟨ha, hka⟩ := List.mem_filter.mp ham
  obtain ⟨hb, hkb⟩ := List.mem_filter.mp hbm
  exact hpar a ha hka b hb hkb (alignedPair hnt haligned ha hb htrigger hname)

private theorem selectInput_parentMap (inp : Input) (keep : ModelBox → Bool) (root : String) :
    (selectInput inp keep root).boxes = (inp.boxes.filter keep).map
      (fun b => { b with parent := if b.parent == root then "" else b.parent }) := by
  unfold selectInput
  dsimp only
  rw [zipIdx_filter_map_fst (β := ModelBox) keep
    (fun (b : ModelBox) => if b.parent == root then { b with parent := "" } else b)
    inp.boxes 0]
  apply List.map_congr_left
  intro b _
  by_cases h : (b.parent == root) = true
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]

theorem attachedNoteParents_selectInput {inp : Input} (hnt : (inp.boxes.map (·.id)).Nodup)
    (haligned : attachedNoteParents inp = true) (keep : ModelBox → Bool) (root : String) :
    attachedNoteParents (selectInput inp keep root) = true := by
  refine attachedNoteParents_parentMap hnt haligned keep _ (selectInput_parentMap inp keep root) ?_
  intro a _ _ b _ _ hpar
  simp only [hpar]

theorem attachedNoteParents_childSubInput {inp : Input} (hnt : (inp.boxes.map (·.id)).Nodup)
    (haligned : attachedNoteParents inp = true) (group : ModelBox) :
    attachedNoteParents (childSubInput inp group) = true :=
  attachedNoteParents_selectInput hnt haligned _ group.id

theorem attachedNoteParents_parentSubInput {inp : Input} (hnt : (inp.boxes.map (·.id)).Nodup)
    (haligned : attachedNoteParents inp = true) (group : ModelBox) (P : Params)
    (lines : List Measure.Line) (child : FamilyResult) :
    attachedNoteParents (parentSubInput inp group P lines child) = true := by
  have hboxes : (parentSubInput inp group P lines child).boxes =
      (selectInput inp (fun b => !Compound.inside inp.boxes group.id b.id) "").boxes := rfl
  unfold attachedNoteParents
  rw [hboxes]
  exact attachedNoteParents_selectInput hnt haligned
    (fun b => !Compound.inside inp.boxes group.id b.id) ""

/-- Alignment and unique ids hold at every child/parent selection that may
reach the note base, including the zero-fuel and no-independent-group calls. -/
theorem notesCallReached_attachmentFacts {top inp : Input}
    (hnt : (top.boxes.map (·.id)).Nodup) (haligned : attachedNoteParents top = true)
    (hreach : NotesCallReached top inp) :
    (inp.boxes.map (·.id)).Nodup ∧ attachedNoteParents inp = true := by
  induction hreach with
  | refl => exact ⟨hnt, haligned⟩
  | child mid group _ ih =>
    exact ⟨selectInput_boxes_nodup
      (fun b => Compound.inside mid.boxes group.id b.id) group.id ih.1,
      attachedNoteParents_childSubInput ih.1 ih.2 group⟩
  | parent mid group P lines child _ ih =>
    exact ⟨selectInput_boxes_nodup
      (fun b => !Compound.inside mid.boxes group.id b.id) "" ih.1,
      attachedNoteParents_parentSubInput ih.1 ih.2 group P lines child⟩

private theorem ancestorBox_chainWalk {boxes : List ModelBox} :
    ∀ (fuel : Nat) (id : String) {i : Nat} {b : ModelBox}, boxes[i]? = some b →
      i ∈ Compound.ancestors boxes fuel id → b ∈ chainWalk boxes fuel id ∧ b.id ≠ "" := by
  intro fuel
  induction fuel with
  | zero =>
    intro id i b _ h
    simp [Compound.ancestors] at h
  | succ fuel ih =>
    intro id i b hget h
    by_cases hid : id = ""
    · simp only [hid, CompoundHelpers.ancestors_empty] at h
      cases h
    rw [Compound.ancestors.eq_3 _ _ _ hid] at h
    rw [chainWalk_succ hid fuel]
    cases hidx : boxes.findIdx? (·.id == id) with
    | none => simp [hidx] at h
    | some j =>
      cases hb : boxes[j]? with
      | none => simp [hidx, hb] at h
      | some c =>
        simp only [hidx, hb] at h ⊢
        rcases List.mem_append.mp h with h | h
        · obtain ⟨hwalk, hnonempty⟩ := ih c.parent hget h
          exact ⟨List.mem_cons_of_mem _ hwalk, hnonempty⟩
        · obtain rfl := List.mem_singleton.mp h
          have heq := Option.some.inj (hget.symm.trans hb)
          subst c
          obtain ⟨_, htest, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hidx
          obtain ⟨_, hval⟩ := List.getElem?_eq_some_iff.mp hget
          have hbid : b.id = id := by rw [← hval]; exact beq_iff_eq.mp htest
          exact ⟨List.mem_cons_self, fun he => hid (hbid.symm.trans he)⟩

private theorem inside_self_impossible {inp : Input} (hf : InputFacts inp) {b : ModelBox}
    (hb : b ∈ inp.boxes) (hs : Compound.inside inp.boxes b.id b.id = true) : False := by
  obtain ⟨src, hsrc, hsId, i, hi, ancestor, hget, haId, hmem⟩ := inside_spec hs
  have hsrcEq := eq_of_mem_id hf.nodup hsrc hb hsId
  have hancEq := eq_of_mem_id hf.nodup (List.mem_of_getElem? hget) hb haId
  rw [hsrcEq] at hmem
  rw [hancEq] at hget
  obtain ⟨hwalkMem, hbId⟩ := ancestorBox_chainWalk _ _ hget hmem
  have hterm := hf.term b hb inp.boxes.length (by omega)
  obtain hroot | ⟨walk, hwalk, hlast⟩ := chainWalk_of_chainTerm _ _ hterm
  · rw [hroot, chainWalk_nil] at hwalkMem
    cases hwalkMem
  · rw [hwalk] at hwalkMem
    cases walk with
    | nil => cases hwalkMem
    | cons c tail =>
      have hfull : chainWalk inp.boxes (inp.boxes.length + 1) b.id = b :: c :: tail := by
        rw [chainWalk_succ hbId, hi]
        simp only [hget, hwalk]
      have hnodup := chainWalk_nodup _ _ _ hfull
        (by simpa only [List.getLast?_cons_cons] using hlast)
      exact (List.nodup_cons.mp hnodup).1 hwalkMem

private theorem inside_of_equal_parent {inp : Input} (hf : InputFacts inp)
    {a b : ModelBox} (ha : a ∈ inp.boxes) (hb : b ∈ inp.boxes) (hpar : a.parent = b.parent)
    {top : String} (hin : Compound.inside inp.boxes top a.id = true) :
    Compound.inside inp.boxes top b.id = true := by
  obtain ⟨src, hsrc, hid, _, hidx, _, _, _, hmem⟩ := inside_spec hin
  have heq := eq_of_mem_id hf.nodup hsrc ha hid
  rw [heq, hpar] at hmem
  exact inside_of_ancestors hf.nodup hb rfl hidx hmem

private theorem subInput_parentMap (inp : Input) (keep : ModelBox → Bool) (top : String) :
    (subInput inp keep top).boxes = (inp.boxes.filter keep).map
      (fun b => { b with parent := if b.id == top then "" else b.parent }) := by
  change ((selectInput inp keep "").boxes.map fun b =>
    if b.id == top then { b with parent := "" } else b) = _
  rw [selectInput_parentMap, List.map_map]
  apply List.map_congr_left
  intro b _
  have hunchanged : ({ b with parent := if b.parent == "" then "" else b.parent } : ModelBox) = b := by
    by_cases hp : b.parent = ""
    · cases b
      simp_all
    · simp [hp]
  simp only [Function.comp_apply, hunchanged]
  split <;> rfl

/-- Cutting the part root's parent cannot split an attachment within that part.
If a kept endpoint is the root and another is not, they cannot have the same
parent: the non-root endpoint is a proper descendant of the root. -/
theorem attachedNoteParents_notePartSubInput {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) (haligned : attachedNoteParents inp = true)
    (top : String) : attachedNoteParents (subInput inp
      (fun b => b.id == top || Compound.inside inp.boxes top b.id) top) = true := by
  have hf := inputFacts_of_wellFormed hwf
  refine attachedNoteParents_parentMap hf.nodup haligned _ _ (subInput_parentMap inp _ top) ?_
  intro a ha hka b hb hkb hpar
  by_cases haTop : a.id = top <;> by_cases hbTop : b.id = top
  · simp [haTop, hbTop]
  · have hbIn : Compound.inside inp.boxes top b.id = true := by simpa [hbTop] using hkb
    have haIn := inside_of_equal_parent hf hb ha hpar.symm hbIn
    rw [← haTop] at haIn
    exact (inside_self_impossible hf ha haIn).elim
  · have haIn : Compound.inside inp.boxes top a.id = true := by simpa [haTop] using hka
    have hbIn := inside_of_equal_parent hf ha hb hpar haIn
    rw [← hbTop] at hbIn
    exact (inside_self_impossible hf hb hbIn).elim
  · simp [haTop, hbTop, hpar]

/-- The one-note call runs the raw base, but its selected box parent is empty
for every kept box, independently of the note's role. -/
theorem attachedNoteParents_noteSubInput {inp : Input} (hnt : (inp.boxes.map (·.id)).Nodup)
    (haligned : attachedNoteParents inp = true) (id : String) :
    attachedNoteParents (subInput inp (fun b => b.id == id) id) = true := by
  refine attachedNoteParents_parentMap hnt haligned _ _ (subInput_parentMap inp _ id) ?_
  intro a _ ha b _ hb _
  rw [ite_eq_left ha, ite_eq_left hb]

end Elegant.Layered.PipelineImpl

namespace Elegant.Layered

/-- The generic region-note entry, before any State-specific decoration,
already applies the attachment-parent check through `layoutFamilyB`. -/
theorem layoutFamilyRN_attachedNoteParents {ids : List String} {sets : List ModelRegionSet}
    {inp : Input} {o : Options} {res : FamilyResult} (h : layoutFamilyRN ids sets inp o = .ok res) :
    attachedNoteParents inp = true := by
  cases hgraph : RegionImpl.graphRegions inp sets with
  | error err => simp [layoutFamilyRN, hgraph] at h
  | ok idSets =>
    have hB : layoutFamilyB (PipelineImpl.layoutNotes
        (fun ids' sub opt => PipelineImpl.layoutRIds ids'
          (PipelineImpl.reindexRegionSets idSets sub) sub opt) ids (inp.boxes.length + 1)) inp o = .ok res := by
      simpa only [layoutFamilyRN, hgraph] using h
    exact layoutFamilyB_attached_note_parents hB

end Elegant.Layered

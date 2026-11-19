import Elegant.SequenceValid1

set_option autoImplicit false

/-! The boxes and labels at the end of a checked sequence layout: every box is an exclusive actor
header or a participant frame in the header zone, or a settled box of the walk below it, and every
label is a header label or a settled label of the walk (`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

theorem participant_not_note {b : ModelBox} (h : isParticipantBox b = true) : isNoteBox b = false := by
  unfold isParticipantBox at h
  unfold isNoteBox
  cases hr : b.role <;> simp_all

theorem participant_not_fragment {b : ModelBox} (h : isParticipantBox b = true) :
    isFragmentBox b = false := by
  unfold isParticipantBox at h
  unfold isFragmentBox
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [h.2]
  simp [isFragmentShape, fragmentKinds]

theorem boxFinalOk_title {pl : Plan} {ck : CheckState} {b : ModelBox} {i : Nat}
    (h : boxFinalOk pl ck b i = true) (hp : isParticipantBox b = true) :
    titlePos pl.m i = labelPosById pl.m (b.id ++ ".label") := by
  unfold boxFinalOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, h⟩ := h
  have ha : isActorBox b = false := isParticipantBox_not_actor hp
  have hn : isNoteBox b = false := participant_not_note hp
  simp only [ha, hn, Bool.false_eq_true, ↓reduceIte, hp, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem participant_not_placed {pl : Plan} {placed : List Nat} (hc : PlacedCls pl placed) {i : Nat}
    {b : ModelBox} (hb : pl.m.boxes[i]? = some b) (hp : isParticipantBox b = true) : i ∉ placed := by
  intro hi
  obtain ⟨b', hb', h⟩ := hc i hi
  rw [hb] at hb'
  cases hb'
  rcases h with h | h | h
  · rw [isParticipantBox_not_actor hp] at h; cases h
  · rw [participant_not_note hp] at h; cases h
  · rw [participant_not_fragment hp] at h; cases h

/-- The three kinds of box at the end of a checked layout. -/
inductive BoxCls (pl : Plan) (cs : List Int) (w : Walk) (placed : List Nat) (E : List Ent)
    (i : Nat) (b : ModelBox) : Prop
  | actorEx (o : Nat) (ho : o < pl.actorBoxes.length) (hao : pl.actorBoxes[o]? = some i)
      (hnp : i ∉ placed) (hact : isActorBox b = true) (hex : b.exclusive = true)
      (hr : rr w i = actorRect pl cs o) (hpar : b.parent = "" ∨ isParticipantId pl.m b.parent = true)
  | part (hnp : i ∉ placed) (hp : isParticipantBox b = true) (hex : b.exclusive = false)
      (hpar : b.parent = "") (hr : rr w i = participantRect pl (actorRects pl cs) b i)
  | placed (hip : i ∈ placed) (hex : b.exclusive = false) (e : Ent) (he : e ∈ E)
      (hs : e.self = some i) (hr : e.r = rr w i) (hh : e.host = boxParent pl.m i)

theorem box_cls {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) {i : Nat} {b : ModelBox}
    (hb : pl.m.boxes[i]? = some b) : BoxCls pl cs w ck.placed E i b := by
  have hc := boxFinalOk_cls (finalOk_box F.fin i b hb)
  have placedCase : i ∈ ck.placed → b.exclusive = false → BoxCls pl cs w ck.placed E i b := by
    intro hip hex
    obtain ⟨e, he, hs, hr, hh⟩ := F.inv.link_box i hip (by simp)
    exact BoxCls.placed hip hex e he hs hr hh
  obtain ⟨-, h⟩ := hc
  rcases h with ⟨hact, hex, hnp, hpar⟩ | ⟨hact, hex, hip⟩ | ⟨hn, hex, hip⟩ | ⟨hp, hex, hpar⟩ |
      ⟨hf, hex, hip⟩
  · have hm : i ∈ pl.actorBoxes := F.pf.ab_complete i b hb hact
    obtain ⟨o, ho, hoe⟩ := List.mem_iff_getElem.mp hm
    refine BoxCls.actorEx o ho (by simp [List.getElem?_eq_getElem ho, hoe]) hnp hact hex ?_ hpar
    have e1 : pl.actorBoxes.getD o 0 = i := by simp [List.getD_eq_getElem?_getD, ho, hoe]
    have h1 := F.inv.unplaced i hnp
    have h2 := hdr_actor cs F.pf o ho
    rw [e1] at h2
    show w.boxRects.getD i rectZero = _
    rw [h1]
    exact h2
  · exact placedCase hip hex
  · exact placedCase hip hex
  · have hnp := participant_not_placed F.plcls hb hp
    refine BoxCls.part hnp hp hex hpar ?_
    show w.boxRects.getD i rectZero = _
    rw [F.inv.unplaced i hnp, hdr_part cs hb hp]
  · exact placedCase hip hex

end Sequence
end Elegant

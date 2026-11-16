import Elegant.SequenceValid2

set_option autoImplicit false

/-! The zones of the boxes and labels, and the ancestors of the dump (`spec/layout/sequence.md`,
sequence-54). -/

namespace Elegant
namespace Sequence

/-- A rectangle in the header zone: above the first row. -/
def TopZ (pl : Plan) (r : Rect) : Prop :=
  0 ≤ r.y ∧ r.y + r.h ≤ pl.bandTop + pl.bandHeight + pl.c.boxMargin ∧ 0 ≤ r.w ∧ 0 ≤ r.h

/-- A rectangle in the row zone: from the first row down. -/
def BotZ (pl : Plan) (r : Rect) : Prop := B0 pl ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h

/-- A label rectangle in the header zone. -/
def TopLab (pl : Plan) (r : Rect) : Prop := r.y + r.h ≤ pl.bandTop ∧ 0 ≤ r.w ∧ 0 ≤ r.h

theorem top_bot_disjoint {pl : Plan} (hpl : pl.Wf) {a b : Rect} (ha : TopZ pl a) (hb : BotZ pl b) :
    Disjoint a b := by
  unfold TopZ at ha
  unfold BotZ B0 at hb
  have := hpl.pos.boxMargin
  unfold Disjoint Rect.meetsInterior
  intro h
  omega

theorem bot_top_disjoint {pl : Plan} (hpl : pl.Wf) {a b : Rect} (ha : BotZ pl a) (hb : TopZ pl b) :
    Disjoint a b :=
  disjoint_comm' (top_bot_disjoint hpl hb ha)

theorem toplab_bot_disjoint {pl : Plan} (hpl : pl.Wf) (hpf : PlanFacts pl) {a b : Rect}
    (ha : TopLab pl a) (hb : BotZ pl b) : Disjoint a b := by
  unfold TopLab at ha
  unfold BotZ B0 at hb
  have := hpl.pos.boxMargin
  have := hpf.bandH0
  unfold Disjoint Rect.meetsInterior
  intro h
  omega

theorem box_zone {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) {i : Nat} {b : ModelBox}
    (hb : pl.m.boxes[i]? = some b) :
    (i ∉ ck.placed ∧ TopZ pl (rr w i)) ∨ (i ∈ ck.placed ∧ BotZ pl (rr w i)) := by
  have hbm := F.wf.pos.boxMargin
  have hlh := F.wf.pos.lineHeight
  have hwp := F.wf.pos.wrapPadding
  have hbh := F.pf.bandH0
  have hbt := F.pf.bandT0
  rcases box_cls F hb with ⟨o, ho, hao, hnp, hact, hex, hr, hpar⟩ | ⟨hnp, hp, hex, hpar, hr⟩ |
      ⟨hip, hex, e, he, hs, hr, hh⟩
  · left
    refine ⟨hnp, ?_⟩
    have h1 := F.pf.bandH o
    have h2 := F.wf.widths o
    have h3 := F.wf.heights o
    rw [hr]
    unfold TopZ actorRect
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega
  · left
    refine ⟨hnp, ?_⟩
    have hfr := participantRect_ok pl (actorRects pl cs) b i
    have h1 := F.pf.bandT i b hb hp
    have h2 := widest_nonneg (pl.titleLines i)
    have h3 : 0 ≤ ((pl.titleLines i).length : Int) * pl.c.lineHeight :=
      Int.mul_nonneg (Int.natCast_nonneg _) hlh
    rw [hr]
    unfold TopZ
    have hy := hfr.y
    have hh := hfr.h
    have hw := hfr.w
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · right
    refine ⟨hip, ?_⟩
    have h := F.inv.ent_ok e he
    rw [hr] at h
    exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- The header label rectangles are zero or lie in the header zone inside a participant frame; the
others are settled by the walk. -/
inductive LabCls (pl : Plan) (cs : List Int) (w : Walk) (E : List Ent) (p : Nat) : Prop
  | hdr (hl0 : Lab0Cls pl (headerRects pl cs) (w.labelRects.getD p rectZero))
      (heq : w.labelRects.getD p rectZero = (headerLabels pl (headerRects pl cs)).getD p rectZero)
  | settled (e : Ent) (he : e ∈ E) (hs : e.self = none) (hr : e.r = w.labelRects.getD p rectZero)

theorem label_cls {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) (p : Nat) : LabCls pl cs w E p := by
  have hfr : ∀ i b, pl.m.boxes[i]? = some b → isParticipantBox b = true →
      FrameOk pl i ((headerRects pl cs).getD i rectZero) := by
    intro i b hb hp
    rw [hdr_part cs hb hp]
    exact participantRect_ok _ _ _ _
  have htitle : ∀ i b, pl.m.boxes[i]? = some b → isParticipantBox b = true →
      titlePos pl.m i = labelPosById pl.m (b.id ++ ".label") := by
    intro i b hb hp
    exact boxFinalOk_title (finalOk_box F.fin i b hb) hp
  have hcls := headerLabels_cls F.wf F.pf (headerRects pl cs) hfr htitle p
  rcases F.inv.link_lab p with h | ⟨e, he, hs, hr⟩
  · exact LabCls.hdr (by rw [h]; exact hcls) h
  · exact LabCls.settled e he hs hr

theorem label_zone {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) (p : Nat) :
    TopLab pl (w.labelRects.getD p rectZero) ∨ BotZ pl (w.labelRects.getD p rectZero) := by
  rcases label_cls F p with ⟨hl0, -⟩ | ⟨e, he, hs, hr⟩
  · left
    rcases hl0 with h | ⟨i, b, hb, hp, hst, hy, hw, hh⟩
    · rw [h]
      have := F.pf.bandT0
      unfold TopLab rectZero
      refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
    · exact ⟨hy, hw, hh⟩
  · right
    have h := F.inv.ent_ok e he
    rw [hr] at h
    exact ⟨h.1, h.2.1, h.2.2.1⟩

end Sequence
end Elegant

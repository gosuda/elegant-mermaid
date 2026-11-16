import Elegant.SequenceValid6

set_option autoImplicit false

/-! Clauses 1, 2, 3, and 7 of the validator (`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

theorem rr_mem {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) {j : Nat} (hj : j < pl.m.boxes.length) :
    rr w j ∈ w.boxRects := by
  have hl := F.inv.lenR
  unfold rr
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

theorem dump_c1 {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) : Validator.C1 (dumpOf pl cs w) := by
  intro b hb
  obtain ⟨j, bm, hbm, rfl⟩ := mem_dump_boxes.mp hb
  have hj : j < pl.m.boxes.length := (List.getElem?_eq_some_iff.mp hbm).1
  have hq := extentOf_boxRect w (rr w j) (rr_mem F hj)
  have hz := box_zone F hbm
  have hmx := F.wf.pos.diagramMarginX
  have hmy := F.wf.pos.diagramMarginY
  have hbm0 := F.wf.pos.boxMargin
  have hbh := F.pf.bandH0
  have hbt := F.pf.bandT0
  have hy0 : 0 ≤ (rr w j).y ∧ 0 ≤ (rr w j).w ∧ 0 ≤ (rr w j).h := by
    rcases hz with ⟨-, h⟩ | ⟨-, h⟩
    · exact ⟨h.1, h.2.2.1, h.2.2.2⟩
    · unfold BotZ B0 at h
      exact ⟨by omega, h.2.1, h.2.2⟩
  unfold Qb at hq
  unfold Validator.canvasRect
  rw [dump_canvas]
  show Rect.Contained _ (shiftR (sxOf pl w) pl.c.diagramMarginY (rr w j))
  unfold Rect.Contained shiftR sxOf
  dsimp only
  omega

theorem actor_hdr_disjoint {pl : Plan} {cs : List Int} {steps : List Step} (hwf : pl.Wf)
    (hcs : cs = columns pl steps) {o o' : Nat} (hne : o ≠ o') (ho : o < pl.widths.length)
    (ho' : o' < pl.widths.length) : Disjoint (actorRect pl cs o) (actorRect pl cs o') := by
  subst hcs
  unfold Disjoint Rect.meetsInterior actorRect
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := actor_headers_disjoint pl hwf steps o o' hlt ho'
    intro h
    dsimp only at h
    omega
  · have := actor_headers_disjoint pl hwf steps o' o hgt ho
    intro h
    dsimp only at h
    omega

theorem dump_c2 {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) : Validator.C2 (dumpOf pl cs w) := by
  intro b hb c hc hne hbex hcex _
  obtain ⟨i, bm, hbm, rfl⟩ := mem_dump_boxes.mp hb
  obtain ⟨j, cm, hcm, rfl⟩ := mem_dump_boxes.mp hc
  have hbe : bm.exclusive = true := hbex
  have hce : cm.exclusive = true := hcex
  rcases box_cls F hbm with ⟨o, ho, hao, -, -, -, hr, -⟩ | ⟨-, -, hex, -, -⟩ | ⟨-, hex, -⟩
  · rcases box_cls F hcm with ⟨o', ho', hao', -, -, -, hr', -⟩ | ⟨-, -, hex, -, -⟩ | ⟨-, hex, -⟩
    · have hoo : o ≠ o' := by
        intro h
        subst h
        rw [hao] at hao'
        have := Option.some.inj hao'
        subst this
        rw [hbm] at hcm
        have := Option.some.inj hcm
        subst this
        exact hne rfl
      have hlo : o < pl.widths.length := by rw [F.pf.lenW]; exact ho
      have hlo' : o' < pl.widths.length := by rw [F.pf.lenW]; exact ho'
      have hd := actor_hdr_disjoint F.wf F.hcs hoo hlo hlo'
      show Disjoint (shiftR (sxOf pl w) pl.c.diagramMarginY (rr w i))
        (shiftR (sxOf pl w) pl.c.diagramMarginY (rr w j))
      rw [disjoint_shift, hr, hr']
      exact hd
    · rw [hce] at hex; cases hex
    · rw [hce] at hex; cases hex
  · rw [hbe] at hex; cases hex
  · rw [hbe] at hex; cases hex

theorem dump_c3 {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) : Validator.C3 (dumpOf pl cs w) := by
  intro b hb hne p hp
  obtain ⟨j, bm, hbm, rfl⟩ := mem_dump_boxes.mp hb
  have hne' : bm.parent ≠ "" := hne
  have hjl : j < pl.m.boxes.length := (List.getElem?_eq_some_iff.mp hbm).1
  rcases box_cls F hbm with ⟨o, ho, hao, hnp, hact, hex, hr, hpar⟩ | ⟨-, -, -, hpar, -⟩ |
      ⟨hip, hex, e, he, hs, hr, hh⟩
  · have hpid : isParticipantId pl.m bm.parent = true := hpar.resolve_left hne'
    unfold isParticipantId at hpid
    rw [List.any_eq_true] at hpid
    obtain ⟨pb, hpb, hpb2⟩ := hpid
    simp only [Bool.and_eq_true, beq_iff_eq] at hpb2
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hpb
    have hbox := box?_dbox (cs := cs) (w := w) F.fm hk
    rw [hpb2.2] at hbox
    have hp' : p = dbox pl w pb k := by
      have : (dumpOf pl cs w).box? bm.parent = some (dbox pl w pb k) := hbox
      have h2 : (dumpOf pl cs w).box? (dbox pl w bm j).parent = some p := hp
      have h3 : (dbox pl w bm j).parent = bm.parent := rfl
      rw [h3] at h2
      rw [this] at h2
      exact (Option.some.inj h2).symm
    subst hp'
    have hkj : j ≠ k := by
      intro h
      subst h
      rw [hbm] at hk
      have := Option.some.inj hk
      subst this
      have := isParticipantBox_not_actor hpb2.1
      rw [hact] at this
      cases this
    have hspec := headersOk_spec F.hdr hk hbm hpb2.1 hkj
    have hcont := hspec.1 hpb2.2.symm
    have hnpk := participant_not_placed F.plcls hk hpb2.1
    have e1 := F.inv.unplaced k hnpk
    have e2 := F.inv.unplaced j hnp
    show Rect.Contained (shiftR (sxOf pl w) pl.c.diagramMarginY (rr w k))
      (shiftR (sxOf pl w) pl.c.diagramMarginY (rr w j))
    rw [contained_shift]
    show Rect.Contained (w.boxRects.getD k rectZero) (w.boxRects.getD j rectZero)
    rw [e1, e2]
    exact hcont
  · exact absurd hpar hne'
  · have hne2 : boxParent pl.m j ≠ "" := by rw [boxParent_of_getElem pl.m j bm hbm]; exact hne'
    obtain ⟨t, ht, htl, hid, hst⟩ := parent_placed F hip hne2
    obtain ⟨tm, htm, hbox⟩ := box?_of_actor F htl
    have hp' : p = dbox pl w tm t := by
      have h2 : (dumpOf pl cs w).box? (dbox pl w bm j).parent = some p := hp
      have h3 : (dbox pl w bm j).parent = boxId pl.m t := by
        show bm.parent = _
        rw [hid, boxParent_of_getElem pl.m j bm hbm]
      rw [h3, hbox] at h2
      exact (Option.some.inj h2).symm
    subst hp'
    show Rect.Contained (shiftR (sxOf pl w) pl.c.diagramMarginY (rr w t))
      (shiftR (sxOf pl w) pl.c.diagramMarginY (rr w j))
    rw [contained_shift]
    exact contained_of_strictInside hst

theorem dump_c7 {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) : Validator.C7 (dumpOf pl cs w) := by
  intro l hl b hb hex _
  obtain ⟨p, lm, hlm, rfl⟩ := mem_dump_labels.mp hl
  obtain ⟨j, bm, hbm, rfl⟩ := mem_dump_boxes.mp hb
  have hbe : bm.exclusive = true := hex
  rcases box_cls F hbm with ⟨o, ho, hao, hnp, hact, hex', hr, hpar⟩ | ⟨-, -, hex', -, -⟩ |
      ⟨-, hex', -⟩
  · have hbm0 := F.wf.pos.boxMargin
    have hbh := F.pf.bandH0
    have hh1 := F.pf.bandH o
    show Disjoint (shiftR (sxOf pl w) pl.c.diagramMarginY (w.labelRects.getD p rectZero))
      (shiftR (sxOf pl w) pl.c.diagramMarginY (rr w j))
    rw [disjoint_shift, hr]
    rcases label_zone F p with hz | hz
    · apply disjoint_of_le
      unfold TopLab at hz
      unfold actorRect
      dsimp only
      omega
    · apply disjoint_of_le'
      unfold BotZ B0 at hz
      unfold actorRect
      dsimp only
      omega
  · rw [hbe] at hex'; cases hex'
  · rw [hbe] at hex'; cases hex'

end Sequence
end Elegant

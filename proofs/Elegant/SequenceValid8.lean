import Elegant.SequenceValid7

set_option autoImplicit false

/-! Clause 8 of the validator: no group frame overlaps a foreign box or label
(`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

theorem ancGo_ne_empty (m : Model) : ∀ (k : Nat) (s : String), "" ∉ ancGo m k s := by
  intro k
  induction k with
  | zero => intro s h; simp [ancGo] at h
  | succ k ih =>
    intro s h
    unfold ancGo at h
    cases hf : m.boxes.find? (fun b => b.id == s) with
    | none => simp [hf] at h
    | some b =>
      simp only [hf] at h
      by_cases hp : b.parent = ""
      · simp [hp] at h
      · simp only [hp, ↓reduceIte, List.mem_cons] at h
        rcases h with h | h
        · exact hp h.symm
        · exact ih _ h

theorem not_chainS_empty (m : Model) (h : String) : ¬ ChainS m h "" := by
  rintro ⟨hne, hc⟩
  rcases hc with hc | hc
  · exact hne hc.symm
  · exact ancGo_ne_empty m _ _ hc

theorem role_group_of {pl : Plan} {w : Walk} {bm : ModelBox} {j : Nat}
    (h : (dbox pl w bm j).role = "group") : bm.role = BoxRole.group := by
  unfold dbox at h
  dsimp only at h
  cases hr : bm.role with
  | group => rfl
  | node => rw [hr] at h; simp [BoxRole.id] at h

theorem isActorBox_role {b : ModelBox} (h : isActorBox b = true) : b.role = BoxRole.node := by
  unfold isActorBox at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem parent_mem_anc {pl : Plan} (hfm : ModelFacts pl.m) {i : Nat} {bm : ModelBox}
    (hb : pl.m.boxes[i]? = some bm) (hne : bm.parent ≠ "") :
    bm.parent ∈ ancGo pl.m pl.m.boxes.length (boxId pl.m i) := by
  have hi : i < pl.m.boxes.length := (List.getElem?_eq_some_iff.mp hb).1
  have hp := boxParent_of_getElem pl.m i bm hb
  exact anc_of_chainS pl.m hfm.nodup i hi bm.parent ⟨by rw [hp]; exact hne, Or.inl (by rw [hp])⟩

theorem top_pair {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) {gi bi : Nat} {gm bm : ModelBox}
    (hgm : pl.m.boxes[gi]? = some gm) (hbm : pl.m.boxes[bi]? = some bm)
    (hgp : isParticipantBox gm = true) (hbc : isParticipantBox bm = true ∨ isActorBox bm = true)
    (hne : bi ≠ gi) (hpar : bm.parent ≠ gm.id) (hnpg : gi ∉ ck.placed) (hnpb : bi ∉ ck.placed) :
    Disjoint (rr w gi) (rr w bi) := by
  have hspec := headersOk_spec F.hdr hgm hbm hgp hne
  have hd := hspec.2 hpar hbc
  show Disjoint (w.boxRects.getD gi rectZero) (w.boxRects.getD bi rectZero)
  rw [F.inv.unplaced gi hnpg, F.inv.unplaced bi hnpb]
  exact hd

theorem dump_c8a {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) : Validator.C8a (dumpOf pl cs w) := by
  intro g hg hrole b hb hne hn1 hn2
  obtain ⟨gi, gm, hgm, rfl⟩ := mem_dump_boxes.mp hg
  obtain ⟨bi, bm, hbm, rfl⟩ := mem_dump_boxes.mp hb
  have hgrole : gm.role = BoxRole.group := role_group_of hrole
  have hgl : gi < pl.m.boxes.length := (List.getElem?_eq_some_iff.mp hgm).1
  have hbl : bi < pl.m.boxes.length := (List.getElem?_eq_some_iff.mp hbm).1
  have hidg : boxId pl.m gi = gm.id := boxId_of_getElem pl.m gi gm hgm
  have hidb : boxId pl.m bi = bm.id := boxId_of_getElem pl.m bi bm hbm
  have hgne : gm.id ≠ "" := by rw [← hidg]; exact F.fm.nonempty gi hgl
  have hne' : bi ≠ gi := by
    intro h
    subst h
    rw [hgm] at hbm
    have := Option.some.inj hbm
    subst this
    exact hne rfl
  rw [ancestors_eq F.fm] at hn1 hn2
  change gm.id ∉ ancGo pl.m pl.m.boxes.length bm.id at hn1
  change bm.id ∉ ancGo pl.m pl.m.boxes.length gm.id at hn2
  rw [← hidb] at hn1
  rw [← hidg] at hn2
  show Disjoint (shiftR (sxOf pl w) pl.c.diagramMarginY (rr w gi))
    (shiftR (sxOf pl w) pl.c.diagramMarginY (rr w bi))
  rw [disjoint_shift]
  rcases box_cls F hgm with ⟨-, -, -, -, hact, -⟩ | ⟨hnpg, hgp, -, -, hrg⟩ |
      ⟨hipg, -, eg, heg, hsg, hrg, hhg⟩
  · have := isActorBox_role hact
    rw [hgrole] at this
    cases this
  · rcases box_cls F hbm with ⟨o, ho, hao, hnpb, hact, -, hrb, -⟩ | ⟨hnpb, hbp, -, hparb, hrb⟩ |
        ⟨hipb, hexb, eb, heb, hsb, hrb, hhb⟩
    · by_cases hpar : bm.parent = gm.id
      · exfalso
        apply hn1
        have hne2 : bm.parent ≠ "" := by rw [hpar]; exact hgne
        have := parent_mem_anc F.fm hbm hne2
        rw [hpar] at this
        exact this
      · exact top_pair F hgm hbm hgp (Or.inr hact) hne' hpar hnpg hnpb
    · have hpar : bm.parent ≠ gm.id := by rw [hparb]; exact fun h => hgne h.symm
      exact top_pair F hgm hbm hgp (Or.inl hbp) hne' hpar hnpg hnpb
    · have hz1 := box_zone F hgm
      have hz2 := box_zone F hbm
      rcases hz1 with ⟨-, h1⟩ | ⟨h1, -⟩
      · rcases hz2 with ⟨h2, -⟩ | ⟨-, h2⟩
        · exact absurd hipb h2
        · exact top_bot_disjoint F.wf h1 h2
      · exact absurd h1 hnpg
  · rcases box_cls F hbm with ⟨o, ho, hao, hnpb, hact, -, hrb, -⟩ | ⟨hnpb, hbp, -, hparb, hrb⟩ |
        ⟨hipb, hexb, eb, heb, hsb, hrb, hhb⟩
    · have hz1 := box_zone F hgm
      have hz2 := box_zone F hbm
      rcases hz1 with ⟨h1, -⟩ | ⟨-, h1⟩
      · exact absurd hipg h1
      · rcases hz2 with ⟨-, h2⟩ | ⟨h2, -⟩
        · exact bot_top_disjoint F.wf h1 h2
        · exact absurd h2 hnpb
    · have hz1 := box_zone F hgm
      have hz2 := box_zone F hbm
      rcases hz1 with ⟨h1, -⟩ | ⟨-, h1⟩
      · exact absurd hipg h1
      · rcases hz2 with ⟨-, h2⟩ | ⟨h2, -⟩
        · exact bot_top_disjoint F.wf h1 h2
        · exact absurd h2 hnpb
    · have hne_e : eg ≠ eb := by
        intro h
        rw [h, hsb] at hsg
        have := Option.some.inj hsg
        exact hne' this
      have hsep := F.inv.ent_sep eg heg eb heb ⟨gi, hsg, ⟨gm, hgm, hgrole⟩⟩ hne_e
      rcases hsep with hd | hc | hc
      · rw [← hrg, ← hrb]
        exact hd
      · exfalso
        apply hn1
        have hc' : ChainS pl.m (boxParent pl.m bi) gm.id := by
          rw [← hhb, ← hidg]
          simpa [entId, hsg] using hc
        exact anc_of_chainS pl.m F.fm.nodup bi hbl _ hc'
      · exfalso
        apply hn2
        have hc' : ChainS pl.m (boxParent pl.m gi) bm.id := by
          rw [← hhg, ← hidb]
          simpa [entId, hsb] using hc
        exact anc_of_chainS pl.m F.fm.nodup gi hgl _ hc'

theorem lab0_toplab {pl : Plan} (hpf : PlanFacts pl) {rects : List Rect} {l : Rect}
    (h : Lab0Cls pl rects l) : TopLab pl l := by
  rcases h with h | ⟨i, b, hb, hp, hst, hy, hw, hh⟩
  · rw [h]
    have := hpf.bandT0
    unfold TopLab rectZero
    refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
  · exact ⟨hy, hw, hh⟩

theorem dump_c8b {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) : Validator.C8b (dumpOf pl cs w) := by
  intro g hg hrole l hl
  obtain ⟨gi, gm, hgm, rfl⟩ := mem_dump_boxes.mp hg
  obtain ⟨p, lm, hlm, rfl⟩ := mem_dump_labels.mp hl
  have hgrole : gm.role = BoxRole.group := role_group_of hrole
  have hgl : gi < pl.m.boxes.length := (List.getElem?_eq_some_iff.mp hgm).1
  have hidg : boxId pl.m gi = gm.id := boxId_of_getElem pl.m gi gm hgm
  have hgne : gm.id ≠ "" := by rw [← hidg]; exact F.fm.nonempty gi hgl
  show Disjoint (shiftR (sxOf pl w) pl.c.diagramMarginY (rr w gi))
      (shiftR (sxOf pl w) pl.c.diagramMarginY (w.labelRects.getD p rectZero)) ∨
    Rect.StrictInside (shiftR (sxOf pl w) pl.c.diagramMarginY (rr w gi))
      (shiftR (sxOf pl w) pl.c.diagramMarginY (w.labelRects.getD p rectZero))
  rw [disjoint_shift, strictInside_shift]
  rcases box_cls F hgm with ⟨-, -, -, -, hact, -⟩ | ⟨hnpg, hgp, -, hparg, hrg⟩ |
      ⟨hipg, -, eg, heg, hsg, hrg, hhg⟩
  · have := isActorBox_role hact
    rw [hgrole] at this
    cases this
  · rcases label_cls F p with ⟨hl0, heq⟩ | ⟨e, he, hs, hr⟩
    · rcases hl0 with h0 | ⟨k, kb, hk, hkp, hst, hy, hw, hh⟩
      · left
        rw [h0]
        apply disjoint_comm'
        apply disjoint_of_zero
        left
        unfold rectZero
        exact Int.le_refl _
      · by_cases hkg : k = gi
        · subst hkg
          right
          have e1 : (headerRects pl cs).getD k rectZero = rr w k := by
            show _ = w.boxRects.getD k rectZero
            rw [F.inv.unplaced k hnpg]
          rw [← e1]
          exact hst
        · left
          have hkpar : kb.parent = "" := by
            rcases box_cls F hk with ⟨-, -, -, -, hact', -⟩ | ⟨-, -, -, hpark, -⟩ | ⟨hipk, -⟩
            · rw [isParticipantBox_not_actor hkp] at hact'; cases hact'
            · exact hpark
            · exact absurd hipk (participant_not_placed F.plcls hk hkp)
          have hne2 : kb.parent ≠ gm.id := by
            rw [hkpar]; exact fun h => hgne h.symm
          have hspec := headersOk_spec F.hdr hgm hk hgp hkg
          have hd := hspec.2 hne2 (Or.inl hkp)
          have e1 : (headerRects pl cs).getD gi rectZero = rr w gi := by
            show _ = w.boxRects.getD gi rectZero
            rw [F.inv.unplaced gi hnpg]
          rw [← e1]
          exact disjoint_of_strictInside hst hd
    · left
      have hz := box_zone F hgm
      have hok := F.inv.ent_ok e he
      rw [hr] at hok
      rcases hz with ⟨-, h1⟩ | ⟨h1, -⟩
      · exact top_bot_disjoint F.wf h1 ⟨hok.1, hok.2.1, hok.2.2.1⟩
      · exact absurd h1 hnpg
  · rcases label_cls F p with ⟨hl0, heq⟩ | ⟨e, he, hs, hr⟩
    · left
      have hz := box_zone F hgm
      have hlt := lab0_toplab F.pf hl0
      rcases hz with ⟨h1, -⟩ | ⟨-, h1⟩
      · exact absurd hipg h1
      · exact disjoint_comm' (toplab_bot_disjoint F.wf F.pf hlt h1)
    · have hne_e : eg ≠ e := by
        intro h
        rw [h, hs] at hsg
        cases hsg
      have hsep := F.inv.ent_sep eg heg e he ⟨gi, hsg, ⟨gm, hgm, hgrole⟩⟩ hne_e
      rcases hsep with hd | hc | hc
      · left
        rw [← hrg, ← hr]
        exact hd
      · right
        obtain ⟨hne0, hcase⟩ := hc
        have hcase' : boxId pl.m gi = e.host ∨
            boxId pl.m gi ∈ ancGo pl.m (pl.m.boxes.length - 1) e.host := by
          simpa [entId, hsg] using hcase
        rcases F.inv.ent_host e he with h0 | ⟨t, ht, h0⟩
        · exact absurd h0 hne0
        · have htl := F.inv.placed_lt t ht
          have hst := F.inv.ent_strict e he t ht (by simp) h0
          rw [hr] at hst
          rcases hcase' with hc1 | hc1
          · have : gi = t := boxId_inj F.fm hgl htl (by rw [hc1, h0])
            subst this
            exact hst
          · rw [h0] at hc1
            exact strictInside_trans (strict_chain F _ t gi ht hgl hc1) hst
      · exfalso
        have : ChainS pl.m eg.host "" := by simpa [entId, hs] using hc
        exact not_chainS_empty pl.m _ this

theorem dump_c8 {pl : Plan} {cs : List Int} {steps : List Step} {w : Walk} {ck : CheckState}
    {E : List Ent} (F : FinFacts pl cs steps w ck E) : Validator.C8 (dumpOf pl cs w) :=
  ⟨dump_c8a F, dump_c8b F⟩

end Sequence
end Elegant

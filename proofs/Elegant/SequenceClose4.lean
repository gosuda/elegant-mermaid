import Elegant.SequenceClose3

set_option autoImplicit false

namespace Elegant
namespace Sequence

theorem pairwise_fragsAdd {pl : Plan} {fs : List FragRun} (r : Rect)
    (h : fs.Pairwise fun g f => f.top + adv pl f ≤ g.top ∧ ∀ d ∈ f.dividers, d.row + hgt pl d ≤ g.top) :
    (fragsAdd fs r).Pairwise fun g f => f.top + adv pl f ≤ g.top ∧ ∀ d ∈ f.dividers, d.row + hgt pl d ≤ g.top := by
  cases fs with
  | nil => exact List.Pairwise.nil
  | cons g0 r0 =>
    obtain ⟨a, b⟩ := List.pairwise_cons.mp h
    exact List.pairwise_cons.mpr ⟨a, b⟩

theorem inv_close {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w w' : Walk}
    {E : List Ent} (hpl : pl.Wf) (hfm : ModelFacts pl.m) (hI : Inv pl hdr lab0 stack placed w E)
    {f : FragRun} {rest : List FragRun} (hfs : w.fragments = f :: rest)
    (h : closeFragment pl { w with fragments := rest } f = .ok w') :
    ∃ E', Inv pl hdr lab0 stack.tail placed w' E' := by
  obtain ⟨width, hge, hcov, rfl⟩ := closeFragment_spec pl _ f w' h
  have hst : stack = f.box :: rest.map (·.box) := by
    have := hI.stack_eq
    rw [hfs] at this
    exact this.symm
  subst hst
  have hbm := hpl.pos.boxMargin
  have hbt := hpl.pos.boxTextMargin
  have hfmem : f ∈ w.fragments := by rw [hfs]; exact List.mem_cons_self
  have hfa := hI.frag_adv f hfmem
  have hftop := hI.frag_top f hfmem
  have hadv : 0 < adv pl f := fragmentAdvance_pos pl hpl f.kind f.box
  have hmemb := hI.frag_members f hfmem
  have hfrag := hI.frag
  rw [hfs] at hfrag
  have hfragMem := hfrag.2.2 f List.mem_cons_self
  have hnest := hI.frag_nested
  rw [hfs] at hnest
  have hfboxlt : f.box < pl.m.boxes.length := hI.stack_lt f.box List.mem_cons_self
  have hfboxplaced : f.box ∈ placed := hI.stack_placed f.box List.mem_cons_self
  have hrestlt : ∀ s ∈ rest.map (·.box), s < pl.m.boxes.length :=
    fun s hs => hI.stack_lt s (List.mem_cons_of_mem _ hs)
  have hrestlen : (rest.map (·.box)).length ≤ pl.m.boxes.length := by
    have := hI.stack_len
    simp only [List.length_cons] at this
    omega
  have hnd := hI.stack_nodup
  have hfnot : f.box ∉ rest.map (·.box) := (List.nodup_cons.mp hnd).1
  have hspan := rectSpan_ordered f.members (fun r hr => (hfragMem r hr).2.1)
  have hcur_ge : f.top + adv pl f ≤ w.cursor := hfa.1
  let w1 : Walk := { w with fragments := rest }
  have hFx : (frameRect pl w1 f width).x = (rectSpan f.members).1 - pl.c.boxMargin -
      half (width - ((rectSpan f.members).2 - (rectSpan f.members).1 + 2 * pl.c.boxMargin)) := rfl
  have hFy : (frameRect pl w1 f width).y = f.top := rfl
  have hFw : (frameRect pl w1 f width).w = width := rfl
  have hFh : (frameRect pl w1 f width).h = w.cursor + pl.c.boxMargin - f.top := rfl
  have hCur : (closeWith pl w1 f width).cursor = w.cursor + pl.c.boxMargin :=
    closeWith_cursor pl w1 f width
  have hFr : (closeWith pl w1 f width).fragments = fragsAdd rest (frameRect pl w1 f width) :=
    closeWith_fragments pl w1 f width
  have hBox : (closeWith pl w1 f width).boxRects = w.boxRects.set f.box (frameRect pl w1 f width) :=
    closeWith_boxRects pl w1 f width
  have hLab := closeWith_labelRects pl w1 f width
  generalize frameRect pl w1 f width = F at hFx hFy hFw hFh hFr hBox hLab
  have hFh' : F.y + F.h = w.cursor + pl.c.boxMargin := by omega
  have hFw0 : 0 ≤ F.w := by omega
  have hFh0 : 0 ≤ F.h := by omega
  have hp : boxParent pl.m f.box = topId pl.m (rest.map (·.box)) := hI.chain.1
  let eF : Ent := ⟨F, boxParent pl.m f.box, some f.box⟩
  let labEnts : List Ent := if f.kind == fragmentKindRect then []
    else (labelEntRects pl f F).map fun r => ⟨r, boxId pl.m f.box, none⟩
  have hmemE : ∀ e, e ∈ E ++ [eF] ++ labEnts ↔ e ∈ E ∨ e = eF ∨
      ((f.kind == fragmentKindRect) = false ∧ ∃ r, NewLab pl f F r ∧ e = ⟨r, boxId pl.m f.box, none⟩) := by
    intro e
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ((he | he) | he)
      · exact Or.inl he
      · exact Or.inr (Or.inl he)
      · right; right
        cases hk : (f.kind == fragmentKindRect)
        · simp only [labEnts, hk, Bool.false_eq_true, ↓reduceIte, List.mem_map] at he
          obtain ⟨r, hr, rfl⟩ := he
          exact ⟨rfl, r, mem_labelEntRects.mp hr, rfl⟩
        · simp [labEnts, hk] at he
    · rintro (he | he | ⟨hk, r, hr, rfl⟩)
      · exact Or.inl (Or.inl he)
      · exact Or.inl (Or.inr he)
      · refine Or.inr ?_
        simp only [labEnts, hk, Bool.false_eq_true, ↓reduceIte, List.mem_map]
        exact ⟨r, mem_labelEntRects.mpr hr, rfl⟩
  have hcases : ∀ e ∈ E ++ [eF] ++ labEnts, e ∈ E ∨ e = eF ∨
      ((f.kind == fragmentKindRect) = false ∧ ∃ r, NewLab pl f F r ∧ e = ⟨r, boxId pl.m f.box, none⟩) :=
    fun e he => (hmemE e).mp he
  have hprops : ∀ r, (f.kind == fragmentKindRect) = false → NewLab pl f F r →
      f.top < r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧ (∃ b ∈ bandsOf pl f, b.1 ≤ r.y ∧ r.y + r.h ≤ b.2) ∧
        r.y + r.h ≤ w.cursor ∧ F.StrictInside r := by
    intro r hk hr
    exact newLab_props hpl hk hFy hFh' (by rw [hFw]; exact hcov hk) hfa hr
  have hjf : ∀ e ∈ E, e.r.y + e.r.h ≤ f.top ∨
      (ChainS pl.m e.host (boxId pl.m f.box) ∧ ∀ b ∈ bandsOf pl f, Avoids e.r b) :=
    fun e he => hI.ent_j1 e he f hfmem
  have hold_F : ∀ e ∈ E, Disjoint e.r F ∨ ChainS pl.m e.host (boxId pl.m f.box) := by
    intro e he
    rcases hjf e he with h1 | ⟨h1, -⟩
    · exact Or.inl (disjoint_of_le (by omega))
    · exact Or.inr h1
  have hold_lab : ∀ e ∈ E, ∀ r, (f.kind == fragmentKindRect) = false → NewLab pl f F r →
      Disjoint e.r r := by
    intro e he r hk hr
    obtain ⟨h1, -, -, ⟨b, hb, hb1, hb2⟩, -⟩ := hprops r hk hr
    rcases hjf e he with h2 | ⟨-, h2⟩
    · exact disjoint_of_le (by omega)
    · rcases h2 b hb with h3 | h3
      · exact disjoint_of_le (by omega)
      · exact disjoint_of_le' (by omega)
  have hnestF : ∀ g0 ∈ rest, g0.top + adv pl g0 ≤ f.top ∧ ∀ d ∈ g0.dividers, d.row + hgt pl d ≤ f.top :=
    fun g0 hg0 => (List.pairwise_cons.mp hnest).1 g0 hg0
  have hbandle : ∀ g0 ∈ rest, ∀ b ∈ bandsOf pl g0, b.2 ≤ f.top := by
    intro g0 hg0 b hb
    have hn := hnestF g0 hg0
    simp only [bandsOf, List.mem_cons, List.mem_map] at hb
    rcases hb with rfl | ⟨d, hd, rfl⟩
    · exact hn.1
    · exact hn.2 d hd
  have hlen_tail : ∀ i, i < pl.m.boxes.length → (w.boxRects.set f.box F).getD i rectZero =
      if f.box = i then F else w.boxRects.getD i rectZero := by
    intro i hi
    rw [getD_set_gen]
    by_cases hc : f.box = i
    · subst hc
      simp [hfboxlt, hI.lenR]
    · simp [hc]
  refine ⟨E ++ [eF] ++ labEnts, ?_⟩
  show Inv pl hdr lab0 (rest.map (·.box)) placed (closeWith pl w1 f width) (E ++ [eF] ++ labEnts)
  refine { stack_eq := ?_, chain := ?_, stack_lt := hrestlt, stack_len := hrestlen,
           stack_nodup := (List.nodup_cons.mp hnd).2, placed_lt := hI.placed_lt, stack_placed := ?_,
           lenR := ?_, lenL := ?_, unplaced := ?_, frag := ?_, cursor := ?_, frag_top := ?_,
           frag_adv := ?_, frag_members := ?_, frag_nested := ?_, ent_ok := ?_, ent_host := ?_,
           ent_j1 := ?_, ent_cover := ?_, ent_sep := ?_, ent_strict := ?_, link_box := ?_,
           link_lab := ?_ }
  · rw [hFr, fragsAdd_map_box]
  · exact hI.chain.2
  · intro s hs
    exact hI.stack_placed s (List.mem_cons_of_mem _ hs)
  · rw [hBox, List.length_set]; exact hI.lenR
  · rw [hLab]
    split
    · exact hI.lenL
    · rw [closeLabels_length]; exact hI.lenL
  · intro i hi
    rw [hBox]
    have hne : f.box ≠ i := fun h => hi (h ▸ hfboxplaced)
    simp only [getD_set_gen, hne, false_and, ↓reduceIte]
    exact hI.unplaced i hi
  · rw [hFr, hCur]
    have hbase : FragInv rest (w.cursor + pl.c.boxMargin) := (FragInv.tail hfrag).mono (by omega)
    refine fragsAdd_inv hbase F ?_ hFw0 hFh0 (by omega)
    intro g hg
    have := (List.pairwise_cons.mp hfrag.2.1).1 g (List.mem_of_mem_head? hg)
    omega
  · rw [hCur]; have := hI.cursor; omega
  · intro g hg
    rw [hFr] at hg
    obtain ⟨g0, hg0, h1, -⟩ := mem_fragsAdd hg
    rw [h1]
    exact hI.frag_top g0 (by rw [hfs]; exact List.mem_cons_of_mem _ hg0)
  · intro g hg
    rw [hFr] at hg
    rw [hCur]
    obtain ⟨g0, hg0, h1, h2, h3, h4, -⟩ := mem_fragsAdd hg
    have hg0' : g0 ∈ w.fragments := by rw [hfs]; exact List.mem_cons_of_mem _ hg0
    have hb := hI.frag_adv g0 hg0'
    have ha : adv pl g = adv pl g0 := by simp [adv, h2, h3]
    rw [ha, h1, h4]
    exact ⟨by omega, fun d hd => ⟨(hb.2 d hd).1, by have := (hb.2 d hd).2; omega⟩⟩
  · intro g hg r hr
    rw [hFr] at hg
    obtain ⟨g0, hg0, h1, h2, h3, h4, h5, -⟩ := mem_fragsAdd hg
    have hg0' : g0 ∈ w.fragments := by rw [hfs]; exact List.mem_cons_of_mem _ hg0
    have ha : adv pl g = adv pl g0 := by simp [adv, h2, h3]
    rw [ha, h1]
    rcases h5 r hr with h | h
    · exact hI.frag_members g0 hg0' r h
    · subst h
      have := (hnestF g0 hg0).1
      omega
  · rw [hFr]
    exact pairwise_fragsAdd F (List.pairwise_cons.mp hnest).2
  · intro e he
    rcases hcases e he with he | rfl | ⟨hk, r, hr, rfl⟩
    · have h := hI.ent_ok e he
      rw [hCur]
      exact ⟨h.1, h.2.1, h.2.2.1, by omega⟩
    · rw [hCur]
      show B0 pl ≤ F.y ∧ 0 ≤ F.w ∧ 0 ≤ F.h ∧ F.y + F.h ≤ w.cursor + pl.c.boxMargin
      omega
    · obtain ⟨h1, h2, h3, -, h4, -⟩ := hprops r hk hr
      rw [hCur]
      show B0 pl ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧ r.y + r.h ≤ w.cursor + pl.c.boxMargin
      omega
  · intro e he
    rcases hcases e he with he | rfl | ⟨hk, r, hr, rfl⟩
    · exact hI.ent_host e he
    · show boxParent pl.m f.box = "" ∨ ∃ t ∈ placed, boxParent pl.m f.box = boxId pl.m t
      rw [hp]
      exact topId_host_of (fun s hs => hI.stack_placed s (List.mem_cons_of_mem _ hs))
    · exact Or.inr ⟨f.box, hfboxplaced, rfl⟩
  · intro e he g hg
    rw [hFr] at hg
    obtain ⟨g0, hg0, h1, h2, h3, h4, -⟩ := mem_fragsAdd hg
    have hg0' : g0 ∈ w.fragments := by rw [hfs]; exact List.mem_cons_of_mem _ hg0
    have hbands : bandsOf pl g = bandsOf pl g0 := bandsOf_congr h1 h2 h3 h4
    rw [hbands, h1, h3]
    have hgmem : g0.box ∈ f.box :: rest.map (·.box) :=
      List.mem_cons_of_mem _ (List.mem_map_of_mem hg0)
    rcases hcases e he with he | rfl | ⟨hk, r, hr, rfl⟩
    · exact hI.ent_j1 e he g0 hg0'
    · right
      refine ⟨?_, fun b hb => Or.inr ?_⟩
      · show ChainS pl.m (boxParent pl.m f.box) (boxId pl.m g0.box)
        rw [hp]
        exact chainS_top_of hfm hI.chain.2 hrestlt hrestlen g0.box (List.mem_map_of_mem hg0)
      · show b.2 ≤ F.y
        have := hbandle g0 hg0 b hb
        omega
    · obtain ⟨h1', -, -, -, -, -⟩ := hprops r hk hr
      right
      refine ⟨chainS_top_of hfm hI.chain hI.stack_lt hI.stack_len g0.box hgmem, fun b hb => Or.inr ?_⟩
      show b.2 ≤ r.y
      have := hbandle g0 hg0 b hb
      omega
  · intro e he g hg hh
    rw [hFr] at hg
    rcases hcases e he with he | rfl | ⟨hk, r, hr, rfl⟩
    · obtain ⟨g0, hg0, h1, h2, h3, h4, h5, h6⟩ := mem_fragsAdd hg
      have hg0' : g0 ∈ w.fragments := by rw [hfs]; exact List.mem_cons_of_mem _ hg0
      obtain ⟨k, hk, hk2⟩ := hI.ent_cover e he g0 hg0' (h3 ▸ hh)
      exact ⟨k, h6 k hk, hk2⟩
    · obtain _ | ⟨g1, rest1⟩ := rest
      · simp [fragsAdd] at hg
      · have hF2 : fragsAdd (g1 :: rest1) F = { g1 with members := g1.members ++ [F] } :: rest1 := rfl
        rw [hF2] at hg
        have hp1 : boxParent pl.m f.box = boxId pl.m g1.box := hp
        rcases List.mem_cons.mp hg with rfl | hgr
        · exact ⟨F, by simp, Rect.Contained.refl F⟩
        · exfalso
          have heq : boxId pl.m g.box = boxId pl.m g1.box := hh.symm.trans hp1
          have hl1 : g.box < pl.m.boxes.length :=
            hI.stack_lt _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hgr)))
          have hl2 : g1.box < pl.m.boxes.length := hrestlt _ List.mem_cons_self
          have hbe := boxId_inj hfm hl1 hl2 heq
          have hnd2 := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
          exact hnd2 (by show g1.box ∈ rest1.map (·.box); rw [← hbe]; exact List.mem_map_of_mem hgr)
    · exfalso
      obtain ⟨g0, hg0, h1, h2, h3, h4, h5, h6⟩ := mem_fragsAdd hg
      have heq : boxId pl.m f.box = boxId pl.m g0.box := by
        have := hh
        rw [h3] at this
        exact this
      have hl0 : g0.box < pl.m.boxes.length := hrestlt _ (List.mem_map_of_mem hg0)
      have hbe := boxId_inj hfm hfboxlt hl0 heq
      exact hfnot (by rw [hbe]; exact List.mem_map_of_mem hg0)
  · intro e he e' he' hself hne
    rcases hcases e he with he | rfl | ⟨hk, r, hr, rfl⟩
    · rcases hcases e' he' with he' | rfl | ⟨hk', r', hr', rfl⟩
      · exact hI.ent_sep e he e' he' hself hne
      · rcases hold_F e he with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · exact Or.inl (hold_lab e he r' hk' hr')
    · rcases hcases e' he' with he' | rfl | ⟨hk', r', hr', rfl⟩
      · rcases hold_F e' he' with h | h
        · exact Or.inl ((Rect.disjoint_comm _ _).mp h)
        · exact Or.inr (Or.inl h)
      · exact absurd rfl hne
      · exact Or.inr (Or.inl ⟨hfm.nonempty f.box hfboxlt, Or.inl rfl⟩)
    · exact absurd hself (by rintro ⟨i, hi, -⟩; simp at hi)
  · intro e he g hg hgs hh
    by_cases hgf : g = f.box
    · subst hgf
      rw [hBox, list_getD_set_self _ _ _ _ (by rw [hI.lenR]; exact hfboxlt)]
      rcases hcases e he with he | rfl | ⟨hk, r, hr, rfl⟩
      · obtain ⟨m, hm, hmc⟩ := hI.ent_cover e he f hfmem hh
        have hms := hmemb m hm
        have hb := hfragMem m hm
        have hsp := rectSpan_mem f.members m hm
        exact strict_of_member hpl hFx hFw rfl hge hFy hFh' hsp.1 hsp.2 (by omega) hb.2.2.2 hmc
      · exfalso
        have h1 : boxId pl.m f.box = topId pl.m (rest.map (·.box)) := by
          have : boxParent pl.m f.box = boxId pl.m f.box := hh
          rw [← this]; exact hp
        exact boxId_ne_topId hfm hrestlt hfboxlt hfnot h1
      · exact (hprops r hk hr).2.2.2.2.2
    · have hgs' : g ∉ f.box :: rest.map (·.box) := fun hm => hgs ((List.mem_cons.mp hm).resolve_left hgf)
      have hgl : g < pl.m.boxes.length := hI.placed_lt g hg
      have hfg : f.box ≠ g := fun h => hgf h.symm
      rw [hBox]
      simp only [getD_set_gen, hfg, false_and, ↓reduceIte]
      rcases hcases e he with he | rfl | ⟨hk, r, hr, rfl⟩
      · exact hI.ent_strict e he g hg hgs' hh
      · exfalso
        have h1 : boxId pl.m g = topId pl.m (rest.map (·.box)) := by
          have : boxParent pl.m f.box = boxId pl.m g := hh
          rw [← this]; exact hp
        exact boxId_ne_topId hfm hrestlt hgl (fun hm => hgs' (List.mem_cons_of_mem _ hm)) h1
      · exfalso
        have hbe := boxId_inj hfm hfboxlt hgl hh
        exact hgf hbe.symm
  · intro i hi his
    by_cases hif : i = f.box
    · subst hif
      refine ⟨eF, (hmemE _).mpr (Or.inr (Or.inl rfl)), rfl, ?_, rfl⟩
      show F = (closeWith pl w1 f width).boxRects.getD f.box rectZero
      rw [hBox, list_getD_set_self _ _ _ _ (by rw [hI.lenR]; exact hfboxlt)]
    · have his' : i ∉ f.box :: rest.map (·.box) := fun hm => his ((List.mem_cons.mp hm).resolve_left hif)
      obtain ⟨e, he, h1, h2, h3⟩ := hI.link_box i hi his'
      refine ⟨e, (hmemE e).mpr (Or.inl he), h1, ?_, h3⟩
      have hfi : f.box ≠ i := fun h => hif h.symm
      rw [hBox]
      simp only [getD_set_gen, hfi, false_and, ↓reduceIte]
      exact h2
  · intro p
    rw [hLab]
    split
    · rcases hI.link_lab p with h' | ⟨e, he, h1, h2⟩
      · exact Or.inl h'
      · exact Or.inr ⟨e, (hmemE e).mpr (Or.inl he), h1, h2⟩
    · rename_i hk
      rcases closeLabels_getD pl w.labelRects f F p with h | h
      · rcases hI.link_lab p with h' | ⟨e, he, h1, h2⟩
        · exact Or.inl (h.trans h')
        · exact Or.inr ⟨e, (hmemE e).mpr (Or.inl he), h1, h2.trans h.symm⟩
      · refine Or.inr ⟨⟨_, boxId pl.m f.box, none⟩, (hmemE _).mpr (Or.inr (Or.inr ⟨?_, _, h, rfl⟩)),
          rfl, rfl⟩
        simpa using hk

end Sequence
end Elegant

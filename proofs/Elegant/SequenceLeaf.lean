import Elegant.SequenceInv

set_option autoImplicit false

/-! The invariant step for a row that places leaves: a message, a note, or both together with a created
actor. The leaves are an optional box and an optional label, and the members that join the innermost
open fragment. -/

namespace Elegant
namespace Sequence

theorem disjoint_of_le {a b : Rect} (h : a.y + a.h ≤ b.y) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  omega

theorem disjoint_of_le' {a b : Rect} (h : b.y + b.h ≤ a.y) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  omega

theorem mem_fragsAddAll {fs : List FragRun} {ms : List Rect} {f' : FragRun}
    (h : f' ∈ fragsAddAll fs ms) :
    ∃ f ∈ fs, f'.top = f.top ∧ f'.kind = f.kind ∧ f'.box = f.box ∧ f'.dividers = f.dividers ∧
      (∀ r ∈ f'.members, r ∈ f.members ∨ r ∈ ms) ∧ (∀ r ∈ f.members, r ∈ f'.members) := by
  cases fs with
  | nil => simp [fragsAddAll] at h
  | cons f0 rest =>
    simp only [fragsAddAll, List.mem_cons] at h
    rcases h with rfl | h
    · refine ⟨f0, List.mem_cons_self, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact Or.inl hr
        · exact Or.inr hr
      · intro r hr
        exact List.mem_append_left _ hr
    · exact ⟨f', List.mem_cons_of_mem _ h, rfl, rfl, rfl, rfl, fun r hr => Or.inl hr, fun r hr => hr⟩

theorem bandsOf_congr {pl : Plan} {f f' : FragRun} (h1 : f'.top = f.top) (h2 : f'.kind = f.kind)
    (h3 : f'.box = f.box) (h4 : f'.dividers = f.dividers) : bandsOf pl f' = bandsOf pl f := by
  simp [bandsOf, adv, h1, h2, h3, h4]

theorem band_hi_le {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w : Walk}
    {E : List Ent} (hI : Inv pl hdr lab0 stack placed w E) {f : FragRun} (hf : f ∈ w.fragments)
    {b : Int × Int} (hb : b ∈ bandsOf pl f) : b.2 ≤ w.cursor := by
  have h := hI.frag_adv f hf
  simp only [bandsOf, List.mem_cons, List.mem_map] at hb
  rcases hb with rfl | ⟨d, hd, rfl⟩
  · exact h.1
  · exact (h.2 d hd).2

theorem tid_unsettled {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w : Walk}
    {E : List Ent} (hfm : ModelFacts pl.m) (hI : Inv pl hdr lab0 stack placed w E) {g : Nat}
    (hg : g < pl.m.boxes.length) (hgs : g ∉ stack) : boxId pl.m g ≠ topId pl.m stack := by
  cases hst : stack with
  | nil => exact hfm.nonempty g hg
  | cons s0 rest =>
    intro h
    have := boxId_inj hfm hg (hI.stack_lt s0 (by rw [hst]; exact List.mem_cons_self)) h
    exact hgs (by rw [hst, this]; exact List.mem_cons_self)

theorem chainS_top {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w : Walk}
    {E : List Ent} (hfm : ModelFacts pl.m) (hI : Inv pl hdr lab0 stack placed w E) {f : Nat}
    (hf : f ∈ stack) : ChainS pl.m (topId pl.m stack) (boxId pl.m f) := by
  cases hst : stack with
  | nil => rw [hst] at hf; simp at hf
  | cons s0 rest =>
    rw [hst] at hf hI
    exact chainS_stack pl.m hfm.nodup hfm.nonempty s0 rest hI.chain hI.stack_lt hI.stack_len f hf

theorem tid_host {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w : Walk}
    {E : List Ent} (hI : Inv pl hdr lab0 stack placed w E) :
    topId pl.m stack = "" ∨ ∃ t ∈ placed, topId pl.m stack = boxId pl.m t := by
  cases hst : stack with
  | nil => exact Or.inl rfl
  | cons s0 rest =>
    refine Or.inr ⟨s0, hI.stack_placed s0 (by rw [hst]; exact List.mem_cons_self), rfl⟩

theorem fragInv_addAll {fs : List FragRun} {c' : Int} (hI : FragInv fs c') :
    ∀ (ms : List Rect), (∀ r ∈ ms, (∀ f ∈ fs.head?, f.top ≤ r.y) ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧ r.y + r.h ≤ c') →
      FragInv (ms.foldl fragsAdd fs) c' := by
  intro ms
  induction ms generalizing fs with
  | nil => intro _; exact hI
  | cons r t ih =>
    intro h
    simp only [List.foldl_cons]
    have hr := h r List.mem_cons_self
    have h1 := fragsAdd_inv hI r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
    refine ih h1 fun r' hr' => ?_
    have hr'' := h r' (List.mem_cons_of_mem _ hr')
    exact ⟨(fragsAdd_head fs r r'.y).mpr hr''.1, hr''.2⟩

theorem mem_optList {β : Type} (o : Option (Nat × β)) (i : Nat) :
    i ∈ (o.map (·.1)).toList ↔ ∃ r, o = some (i, r) := by
  cases o with
  | none => simp
  | some q =>
    obtain ⟨n, r⟩ := q
    simp only [Option.map_some, Option.toList_some, List.mem_singleton]
    constructor
    · intro h; subst h; exact ⟨r, rfl⟩
    · rintro ⟨r', h⟩
      have := (Prod.mk.inj (Option.some.inj h)).1
      exact this.symm

theorem topId_head {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w : Walk}
    {E : List Ent} (hI : Inv pl hdr lab0 stack placed w E) {g : FragRun} {rest : List FragRun}
    (hfs : w.fragments = g :: rest) : topId pl.m stack = boxId pl.m g.box := by
  have hst := hI.stack_eq
  rw [hfs] at hst
  have hst' : stack = g.box :: rest.map (·.box) := hst.symm
  rw [hst']
  rfl

theorem frag_tail_ne {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w : Walk}
    {E : List Ent} (hfm : ModelFacts pl.m) (hI : Inv pl hdr lab0 stack placed w E) {g : FragRun}
    {rest : List FragRun} (hfs : w.fragments = g :: rest) {f : FragRun} (hf : f ∈ rest) :
    boxId pl.m f.box ≠ boxId pl.m g.box := by
  intro h
  have hst := hI.stack_eq
  rw [hfs] at hst
  have hst' : stack = g.box :: rest.map (·.box) := hst.symm
  have hl1 : f.box < pl.m.boxes.length :=
    hI.stack_lt _ (by rw [hst']; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hf))
  have hl2 : g.box < pl.m.boxes.length := hI.stack_lt _ (by rw [hst']; exact List.mem_cons_self)
  have heq := boxId_inj hfm hl1 hl2 h
  have hnd := hI.stack_nodup
  rw [hst'] at hnd
  have hnot := (List.nodup_cons.mp hnd).1
  exact hnot (by rw [← heq]; exact List.mem_map_of_mem hf)

theorem inv_leaf {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w w' : Walk}
    {E : List Ent} (hfm : ModelFacts pl.m) (hI : Inv pl hdr lab0 stack placed w E)
    (NB : Option (Nat × Rect)) (NL : Option (Nat × Rect)) (Ms : List Rect) (c' : Int)
    (hR : w'.boxRects = match NB with | some q => w.boxRects.set q.1 q.2 | none => w.boxRects)
    (hL : w'.labelRects = match NL with | some q => w.labelRects.set q.1 q.2 | none => w.labelRects)
    (hF : w'.fragments = fragsAddAll w.fragments Ms) (hC : w'.cursor = c') (hc : w.cursor ≤ c')
    (hnb : ∀ n r, NB = some (n, r) → n < pl.m.boxes.length ∧ n ∉ placed ∧
      boxParent pl.m n = topId pl.m stack ∧ w.cursor ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧ r.y + r.h ≤ c')
    (hnl : ∀ p r, NL = some (p, r) → w.cursor ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧ r.y + r.h ≤ c')
    (hms : ∀ r ∈ Ms, w.cursor ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧ r.y + r.h ≤ c')
    (hcovB : ∀ n r, NB = some (n, r) → r ∈ Ms)
    (hcovL : ∀ p r, NL = some (p, r) → ∃ k ∈ Ms, k.Contained r)
    (hng : ∀ n r, NB = some (n, r) → ¬ IsGroupAt pl.m n) :
    ∃ E', Inv pl hdr lab0 stack ((NB.map (·.1)).toList ++ placed) w' E' := by
  let tid := topId pl.m stack
  let nbE : List Ent := (NB.map fun q => (⟨q.2, tid, some q.1⟩ : Ent)).toList
  let nlE : List Ent := (NL.map fun q => (⟨q.2, tid, none⟩ : Ent)).toList
  have hmem : ∀ e, e ∈ E ++ nbE ++ nlE ↔ e ∈ E ∨ (∃ n r, NB = some (n, r) ∧ e = ⟨r, tid, some n⟩) ∨
      (∃ p r, NL = some (p, r) ∧ e = ⟨r, tid, none⟩) := by
    intro e
    simp only [List.mem_append, nbE, nlE]
    constructor
    · rintro ((he | he) | he)
      · exact Or.inl he
      · cases hN : NB with
        | none => simp [hN] at he
        | some q =>
          obtain ⟨n, r⟩ := q
          simp only [hN, Option.map_some, Option.toList_some, List.mem_singleton] at he
          exact Or.inr (Or.inl ⟨n, r, rfl, he⟩)
      · cases hN : NL with
        | none => simp [hN] at he
        | some q =>
          obtain ⟨p, r⟩ := q
          simp only [hN, Option.map_some, Option.toList_some, List.mem_singleton] at he
          exact Or.inr (Or.inr ⟨p, r, rfl, he⟩)
    · rintro (he | ⟨n, r, hN, rfl⟩ | ⟨p, r, hN, rfl⟩)
      · exact Or.inl (Or.inl he)
      · refine Or.inl (Or.inr ?_); simp [hN]
      · refine Or.inr ?_; simp [hN]
  refine ⟨E ++ nbE ++ nlE, ?_⟩
  have hok_old := hI.ent_ok
  have hB0 := hI.cursor
  have hnewB : ∀ n r, NB = some (n, r) → B0 pl ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧ r.y + r.h ≤ c' := by
    intro n r h
    have := hnb n r h
    exact ⟨by omega, this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2⟩
  have hnewL : ∀ p r, NL = some (p, r) → B0 pl ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧ r.y + r.h ≤ c' := by
    intro p r h
    have := hnl p r h
    exact ⟨by omega, this.2.1, this.2.2.1, this.2.2.2⟩
  have hS : w'.fragments = fragsAddAll w.fragments Ms := hF
  refine { stack_eq := ?_, chain := hI.chain, stack_lt := hI.stack_lt, stack_len := hI.stack_len,
           stack_nodup := hI.stack_nodup, placed_lt := ?_, stack_placed := ?_, lenR := ?_, lenL := ?_,
           unplaced := ?_, frag := ?_, cursor := ?_, frag_top := ?_, frag_adv := ?_,
           frag_members := ?_, frag_nested := ?_, ent_ok := ?_, ent_host := ?_, ent_j1 := ?_,
           ent_cover := ?_, ent_sep := ?_, ent_strict := ?_, link_box := ?_, link_lab := ?_ }
  · rw [hS, ← hI.stack_eq]; cases w.fragments <;> simp [fragsAddAll]
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨r, h⟩ := (mem_optList NB i).mp hi
      exact (hnb i r h).1
    · exact hI.placed_lt i hi
  · intro s hs
    exact List.mem_append_right _ (hI.stack_placed s hs)
  · rw [hR]; cases NB <;> simp [hI.lenR]
  · rw [hL]; cases NL <;> simp [hI.lenL]
  · intro i hi
    have hi1 : i ∉ placed := fun h => hi (List.mem_append_right _ h)
    rw [hR]
    cases hNB : NB with
    | none => exact hI.unplaced i hi1
    | some q =>
      obtain ⟨n, r⟩ := q
      have hne : n ≠ i := by
        intro h; apply hi; rw [← h]; exact List.mem_append_left _ (by simp [hNB])
      simp only [getD_set_gen, hne, false_and, ↓reduceIte]
      exact hI.unplaced i hi1
  · rw [hS, hC]
    have hbase := hI.frag.mono hc
    rw [← foldl_fragsAdd]
    refine fragInv_addAll hbase Ms fun r hr => ?_
    have h := hms r hr
    exact ⟨fun f hf => Int.le_trans (hI.frag.1 f (List.mem_of_mem_head? hf)) h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  · rw [hC]; omega
  · intro f hf
    rw [hS] at hf
    obtain ⟨f0, hf0, h1, -⟩ := mem_fragsAddAll hf
    rw [h1]; exact hI.frag_top f0 hf0
  · intro f hf
    rw [hS] at hf
    obtain ⟨f0, hf0, h1, h2, h3, h4, -⟩ := mem_fragsAddAll hf
    have ha : adv pl f = adv pl f0 := by simp [adv, h2, h3]
    have hb := hI.frag_adv f0 hf0
    rw [hC, ha, h1, h4]
    exact ⟨by omega, fun d hd => ⟨(hb.2 d hd).1, by have := (hb.2 d hd).2; omega⟩⟩
  · intro f hf r hr
    rw [hS] at hf
    obtain ⟨f0, hf0, h1, h2, h3, h4, h5, -⟩ := mem_fragsAddAll hf
    have ha : adv pl f = adv pl f0 := by simp [adv, h2, h3]
    rw [ha, h1]
    rcases h5 r hr with h | h
    · exact hI.frag_members f0 hf0 r h
    · have := (hI.frag_adv f0 hf0).1
      have := (hms r h).1
      omega
  · rw [hS]
    have h := hI.frag_nested
    cases hfs : w.fragments with
    | nil => exact List.Pairwise.nil
    | cons f0 rest =>
      rw [hfs] at h
      obtain ⟨h1, h2⟩ := List.pairwise_cons.mp h
      exact List.pairwise_cons.mpr ⟨h1, h2⟩
  · intro e he
    rcases (hmem e).mp he with he | ⟨n, r, hN, rfl⟩ | ⟨p, r, hN, rfl⟩
    · have h := hok_old e he
      rw [hC]
      exact ⟨h.1, h.2.1, h.2.2.1, by omega⟩
    · rw [hC]; exact hnewB n r hN
    · rw [hC]; exact hnewL p r hN
  · intro e he
    rcases (hmem e).mp he with he | ⟨n, r, hN, rfl⟩ | ⟨p, r, hN, rfl⟩
    · exact (hI.ent_host e he).imp_right fun ⟨t, ht, h⟩ => ⟨t, List.mem_append_right _ ht, h⟩
    · exact (tid_host hI).imp_right fun ⟨t, ht, h⟩ => ⟨t, List.mem_append_right _ ht, h⟩
    · exact (tid_host hI).imp_right fun ⟨t, ht, h⟩ => ⟨t, List.mem_append_right _ ht, h⟩
  · intro e he f hf
    rw [hS] at hf
    obtain ⟨f0, hf0, h1, h2, h3, h4, -⟩ := mem_fragsAddAll hf
    have hbands : bandsOf pl f = bandsOf pl f0 := bandsOf_congr h1 h2 h3 h4
    have hbox : f0.box ∈ stack := by rw [← hI.stack_eq]; exact List.mem_map_of_mem hf0
    rw [hbands, h1, h3]
    rcases (hmem e).mp he with he | ⟨n, r, hN, rfl⟩ | ⟨p, r, hN, rfl⟩
    · exact hI.ent_j1 e he f0 hf0
    · right
      refine ⟨chainS_top hfm hI hbox, fun b hb => Or.inr ?_⟩
      have h5 := band_hi_le hI hf0 hb
      have h6 := (hnb n r hN).2.2.2.1
      show b.2 ≤ r.y
      omega
    · right
      refine ⟨chainS_top hfm hI hbox, fun b hb => Or.inr ?_⟩
      have h5 := band_hi_le hI hf0 hb
      have h6 := (hnl p r hN).1
      show b.2 ≤ r.y
      omega
  · intro e he f hf hh
    rw [hS] at hf
    cases hfs : w.fragments with
    | nil => rw [hfs] at hf; simp [fragsAddAll] at hf
    | cons g rest =>
      have hF2 : fragsAddAll (g :: rest) Ms = { g with members := g.members ++ Ms } :: rest := rfl
      have htid : tid = boxId pl.m g.box := topId_head hI hfs
      rw [hfs, hF2] at hf
      rcases (hmem e).mp he with he | ⟨n, r, hN, rfl⟩ | ⟨p, r, hN, rfl⟩
      · rcases List.mem_cons.mp hf with rfl | hfr
        · obtain ⟨k, hk, hk2⟩ := hI.ent_cover e he g (by rw [hfs]; exact List.mem_cons_self) hh
          exact ⟨k, List.mem_append_left _ hk, hk2⟩
        · obtain ⟨k, hk, hk2⟩ :=
            hI.ent_cover e he f (by rw [hfs]; exact List.mem_cons_of_mem _ hfr) hh
          exact ⟨k, hk, hk2⟩
      · rcases List.mem_cons.mp hf with rfl | hfr
        · exact ⟨r, List.mem_append_right _ (hcovB n r hN), Rect.Contained.refl r⟩
        · exact (frag_tail_ne hfm hI hfs hfr (hh.symm.trans htid)).elim
      · rcases List.mem_cons.mp hf with rfl | hfr
        · obtain ⟨k, hk, hk2⟩ := hcovL p r hN
          exact ⟨k, List.mem_append_right _ hk, hk2⟩
        · exact (frag_tail_ne hfm hI hfs hfr (hh.symm.trans htid)).elim
  · intro e he e' he' hself hne
    have hold : ∀ x ∈ E, x.r.y + x.r.h ≤ w.cursor := fun x hx => (hok_old x hx).2.2.2
    rcases (hmem e).mp he with he | ⟨n, r, hN, rfl⟩ | ⟨p, r, hN, rfl⟩
    · rcases (hmem e').mp he' with he' | ⟨n', r', hN', rfl⟩ | ⟨p', r', hN', rfl⟩
      · exact hI.ent_sep e he e' he' hself hne
      · exact Or.inl (disjoint_of_le (by have := hold e he; have := (hnb n' r' hN').2.2.2.1; show e.r.y + e.r.h ≤ r'.y; omega))
      · exact Or.inl (disjoint_of_le (by have := hold e he; have := (hnl p' r' hN').1; show e.r.y + e.r.h ≤ r'.y; omega))
    · rcases (hmem e').mp he' with he' | ⟨n', r', hN', rfl⟩ | ⟨p', r', hN', rfl⟩
      · exact Or.inl (disjoint_of_le' (by have := hold e' he'; have := (hnb n r hN).2.2.2.1; show e'.r.y + e'.r.h ≤ r.y; omega))
      · exfalso
        obtain ⟨i, hi, hg⟩ := hself
        exact hng n r hN (by rw [Option.some.inj hi]; exact hg)
      · exfalso
        obtain ⟨i, hi, hg⟩ := hself
        exact hng n r hN (by rw [Option.some.inj hi]; exact hg)
    · exact absurd hself (by rintro ⟨i, hi, -⟩; simp at hi)
  · intro e he g hg hgs hh
    have hgl : g < pl.m.boxes.length := by
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨r, h⟩ := (mem_optList NB g).mp hg
        exact (hnb g r h).1
      · exact hI.placed_lt g hg
    have hbr : ∀ g, g ∈ placed → w'.boxRects.getD g rectZero = w.boxRects.getD g rectZero := by
      intro g hg
      rw [hR]
      cases hNB : NB with
      | none => rfl
      | some q =>
        obtain ⟨n, r⟩ := q
        have hne : n ≠ g := fun h => (hnb n r hNB).2.1 (h ▸ hg)
        simp only [getD_set_gen, hne, false_and, ↓reduceIte]
    rcases (hmem e).mp he with he | ⟨n, r, hN, rfl⟩ | ⟨p, r, hN, rfl⟩
    · rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨r, h⟩ := (mem_optList NB g).mp hg
        exact (host_not_new hfm hI hgl (hnb g r h).2.1 he hh).elim
      · rw [hbr g hg]
        exact hI.ent_strict e he g hg hgs hh
    · exact (tid_unsettled hfm hI hgl hgs hh.symm).elim
    · exact (tid_unsettled hfm hI hgl hgs hh.symm).elim
  · intro i hi his
    have hbr : ∀ g, g ∈ placed → w'.boxRects.getD g rectZero = w.boxRects.getD g rectZero := by
      intro g hg
      rw [hR]
      cases hNB : NB with
      | none => rfl
      | some q =>
        obtain ⟨n, r⟩ := q
        have hne : n ≠ g := fun h => (hnb n r hNB).2.1 (h ▸ hg)
        simp only [getD_set_gen, hne, false_and, ↓reduceIte]
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨r, hN⟩ := (mem_optList NB i).mp hi
      have hlt : i < w.boxRects.length := by rw [hI.lenR]; exact (hnb i r hN).1
      refine ⟨⟨r, tid, some i⟩, (hmem _).mpr (Or.inr (Or.inl ⟨i, r, hN, rfl⟩)), rfl, ?_, ?_⟩
      · rw [hR, hN]
        simp [hlt]
      · exact ((hnb i r hN).2.2.1).symm
    · obtain ⟨e, he, h1, h2, h3⟩ := hI.link_box i hi his
      exact ⟨e, (hmem e).mpr (Or.inl he), h1, by rw [hbr i hi]; exact h2, h3⟩
  · intro p'
    rw [hL]
    cases hNL : NL with
    | none =>
      dsimp only
      rcases hI.link_lab p' with h | ⟨e, he, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, (hmem e).mpr (Or.inl he), h1, h2⟩
    | some q =>
      obtain ⟨p, r⟩ := q
      dsimp only
      simp only [getD_set_gen]
      by_cases hc : p = p' ∧ p < w.labelRects.length
      · simp only [show (p = p' ∧ p < w.labelRects.length) = True from eq_true hc, ↓reduceIte]
        exact Or.inr ⟨⟨r, tid, none⟩, (hmem _).mpr (Or.inr (Or.inr ⟨p, r, hNL, rfl⟩)), rfl, rfl⟩
      · simp only [show (p = p' ∧ p < w.labelRects.length) = False from eq_false hc, ↓reduceIte]
        rcases hI.link_lab p' with h | ⟨e, he, h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨e, (hmem e).mpr (Or.inl he), h1, h2⟩

end Sequence
end Elegant

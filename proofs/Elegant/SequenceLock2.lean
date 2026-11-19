import Elegant.SequenceLock1

set_option autoImplicit false

/-! The lockstep walk: the layout walk and the model check advance together, and the walk invariant
holds after every step (`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

theorem stepNote_routeRuns (pl : Plan) (cs : List Int) (w : Walk) (placement a b box : Nat) :
    (stepNote pl cs w placement a b box).routeRuns = w.routeRuns := by
  unfold stepNote
  simp only [Walk.advance, addMember_routeRuns, placeLabel_routeRuns]

theorem not_mem_of_contains_false {l : List Nat} {a : Nat} (h : l.contains a = false) : a ∉ l := by
  intro hm
  have := List.contains_iff_mem.mpr hm
  rw [h] at this
  cases this

theorem boxParent_of_get {m : Model} {k : Nat} {b : ModelBox} (h : m.boxes[k]? = some b) :
    boxParent m k = b.parent := by
  simp [boxParent, h]

theorem step_lock {pl : Plan} {hdr lab0 : List Rect} {cs : List Int} {steps : List Step}
    (hpl : pl.Wf) (hpf : PlanFacts pl) (hfm : ModelFacts pl.m) (hcs : cs = columns pl steps)
    {w w' : Walk} {ck ck' : CheckState} {E : List Ent} (s : Step) (hs : s ∈ steps)
    (hI : Inv pl hdr lab0 ck.stack ck.placed w E) (hR : RInv pl cs ck w)
    (hw : stepWalk pl cs w s = .ok w') (hck : stepCheck pl ck s = some ck') :
    ∃ E', Inv pl hdr lab0 ck'.stack ck'.placed w' E' ∧ RInv pl cs ck' w' := by
  cases s with
  | message bits src dst route destroyed =>
    have hw' : stepMessage pl cs w bits src dst route destroyed = w' := by
      change Except.ok (stepMessage pl cs w bits src dst route destroyed) = Except.ok w' at hw
      injection hw
    subst hw'
    simp only [stepCheck] at hck
    split at hck
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨⟨⟨hsrc, hdst⟩, hroute⟩, hends⟩ := hc
      have hsrcW : src < pl.widths.length := by rw [hpf.lenW]; exact hsrc
      have hdstW : dst < pl.widths.length := by rw [hpf.lenW]; exact hdst
      split at hck
      · rename_i hb10
        split at hck
        · rename_i bi hcr
          have hck' := Option.some.inj hck
          subst hck'
          obtain ⟨hab, b, hb, hnpl, hpar⟩ := createOk_spec pl ck dst bi hcr
          obtain ⟨r, hr⟩ := createdRect_of pl cs bits dst (msgY pl w route) bi hb10 hab
          have hcreate : ∀ bi' r', createdRect pl cs bits dst (msgY pl w route) = some (bi', r') →
              bi' < pl.m.boxes.length ∧ bi' ∉ ck.placed ∧ boxParent pl.m bi' = topId pl.m ck.stack ∧
                ¬ IsGroupAt pl.m bi' := by
            intro bi' r' h
            rw [hr] at h
            have h1 : bi = bi' := (Prod.mk.inj (Option.some.inj h)).1
            rw [← h1]
            refine ⟨(List.getElem?_eq_some_iff.mp hb).1, not_mem_of_contains_false hnpl, ?_, ?_⟩
            · rw [boxParent_of_get hb]; exact hpar
            · rintro ⟨b2, hb2, hrole⟩
              obtain ⟨b3, hb3, hact⟩ := hpf.ab_actor dst hdst
              have e : pl.actorBoxes[dst] = bi := by
                have := hab
                simp [List.getElem?_eq_getElem hdst] at this
                exact this
              rw [e, hb2] at hb3
              have := Option.some.inj hb3
              subst this
              simp [isActorBox, hrole] at hact
          obtain ⟨E', hI'⟩ := inv_message hpl hfm hI hcs hs hsrcW hdstW hcreate
          rw [hr] at hI'
          exact ⟨E', hI', rinv_message hpl hpf hR hI.cursor hI.lenR hsrc hdst hends hroute rfl rfl⟩
        · cases hck
      · rename_i hb10
        have hb10' : bits.testBit 10 = false := by simpa using hb10
        have hck' := Option.some.inj hck
        subst hck'
        have hcr := createdRect_none_of pl cs bits dst (msgY pl w route) hb10'
        have hcreate : ∀ bi' r', createdRect pl cs bits dst (msgY pl w route) = some (bi', r') →
            bi' < pl.m.boxes.length ∧ bi' ∉ ck.placed ∧ boxParent pl.m bi' = topId pl.m ck.stack ∧
              ¬ IsGroupAt pl.m bi' := by
          intro bi' r' h
          rw [hcr] at h
          cases h
        obtain ⟨E', hI'⟩ := inv_message hpl hfm hI hcs hs hsrcW hdstW hcreate
        rw [hcr] at hI'
        exact ⟨E', hI', rinv_message hpl hpf hR hI.cursor hI.lenR hsrc hdst hends hroute rfl rfl⟩
    · cases hck
  | note placement a b box =>
    have hw' : stepNote pl cs w placement a b box = w' := by
      change Except.ok (stepNote pl cs w placement a b box) = Except.ok w' at hw
      injection hw
    subst hw'
    simp only [stepCheck] at hck
    cases hbx : pl.m.boxes[box]? with
    | none => simp [hbx] at hck
    | some b' =>
      simp only [hbx] at hck
      split at hck
      · rename_i hc
        have hck' := Option.some.inj hck
        subst hck'
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
        obtain ⟨⟨⟨hn, -⟩, hnpl⟩, hpar⟩ := hc
        have hbl : box < pl.m.boxes.length := (List.getElem?_eq_some_iff.mp hbx).1
        have hng : ¬ IsGroupAt pl.m box := by
          rintro ⟨b2, hb2, hrole⟩
          rw [hbx] at hb2
          have := Option.some.inj hb2
          subst this
          simp [isNoteBox, hrole] at hn
        have hpar' : boxParent pl.m box = topId pl.m ck.stack := by
          rw [boxParent_of_get hbx]; exact hpar
        obtain ⟨E', hI'⟩ := inv_note (cs := cs) (placement := placement) (a := a) (b := b) hpl hfm hI hbl
          (not_mem_of_contains_false hnpl) hpar' hng
        refine ⟨E', hI', ?_, ?_, ?_, ?_⟩
        · rw [stepNote_routeRuns]; exact hR.runs_len
        · intro i run hget
          rw [stepNote_routeRuns] at hget
          exact hR.runs_ok i run hget
        · exact actor_form_set hR.actor_form box _ (stepNote_boxRects_eq pl cs w placement a b box)
            (fun o ho => actor_ne_note hpf ho hbx hn)
        · exact hR.stack_group
      · cases hck
  | fragmentStart kind box =>
    have hw' : stepFragmentStart pl w kind box = w' := by
      change Except.ok (stepFragmentStart pl w kind box) = Except.ok w' at hw
      injection hw
    subst hw'
    simp only [stepCheck] at hck
    cases hbx : pl.m.boxes[box]? with
    | none => simp [hbx] at hck
    | some b' =>
      simp only [hbx] at hck
      split at hck
      · rename_i hc
        have hck' := Option.some.inj hck
        subst hck'
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨hfr, hnpl⟩, hpar⟩, hlen⟩ := hc
        have hbl : box < pl.m.boxes.length := (List.getElem?_eq_some_iff.mp hbx).1
        have hpar' : boxParent pl.m box = topId pl.m ck.stack := by
          rw [boxParent_of_get hbx]; exact hpar
        have hg : IsGroupAt pl.m box := by
          refine ⟨b', hbx, ?_⟩
          simp [isFragmentBox] at hfr
          exact hfr.1
        refine ⟨_, inv_push hpl hfm hI kind box hbl (not_mem_of_contains_false hnpl) hpar' hlen, ?_, ?_, ?_, ?_⟩
        · exact hR.runs_len
        · exact hR.runs_ok
        · exact hR.actor_form
        · intro s hs
          rcases List.mem_cons.mp hs with rfl | hs
          · exact hg
          · exact hR.stack_group s hs
      · cases hck
  | fragmentElse box sect =>
    have hw' : stepFragmentElse pl w box sect = w' := by
      change Except.ok (stepFragmentElse pl w box sect) = Except.ok w' at hw
      injection hw
    subst hw'
    simp only [stepCheck] at hck
    cases hst : ck.stack with
    | nil => rw [hst] at hck; cases hck
    | cons top rest =>
      rw [hst] at hck
      dsimp only at hck
      split at hck
      · have hck' := Option.some.inj hck
        subst hck'
        have hne : w.fragments ≠ [] := by
          intro hf
          have := hI.stack_eq
          rw [hf, hst] at this
          cases this
        exact ⟨E, inv_else hpl hI box sect hne,
          hR.runs_len, hR.runs_ok, hR.actor_form, hR.stack_group⟩
      · cases hck
  | fragmentEnd =>
    simp only [stepCheck] at hck
    cases hst : ck.stack with
    | nil => rw [hst] at hck; cases hck
    | cons top rest =>
      rw [hst] at hck
      have hck' := Option.some.inj hck
      subst hck'
      obtain ⟨f, frs, hfs⟩ : ∃ f frs, w.fragments = f :: frs := by
        cases hf : w.fragments with
        | nil =>
          have := hI.stack_eq
          rw [hf, hst] at this
          cases this
        | cons f frs => exact ⟨f, frs, rfl⟩
      simp only [stepWalk, stepFragmentEnd, hfs] at hw
      obtain ⟨E', hI'⟩ := inv_close hpl hfm hI hfs hw
      rw [hst] at hI'
      have hfbox : f.box = top := by
        have := hI.stack_eq
        rw [hfs, hst] at this
        exact (List.cons.inj this).1
      obtain ⟨width, -, -, rfl⟩ := closeFragment_spec pl _ f w' hw
      have hg : IsGroupAt pl.m f.box := by
        rw [hfbox]
        exact hR.stack_group top (by rw [hst]; exact List.mem_cons_self)
      refine ⟨E', hI', ?_, ?_, ?_, ?_⟩
      · rw [closeWith_routeRuns]; exact hR.runs_len
      · intro i run hget
        rw [closeWith_routeRuns] at hget
        exact hR.runs_ok i run hget
      · exact actor_form_set hR.actor_form f.box _ (closeWith_boxRects pl _ f width)
          (fun o ho => actor_ne_group hpf ho hg)
      · intro s hs
        exact hR.stack_group s (by rw [hst]; exact List.mem_cons_of_mem _ hs)
  | activateStart actor =>
    have hw' : stepActivateStart pl cs w actor = w' := by
      change Except.ok (stepActivateStart pl cs w actor) = Except.ok w' at hw
      injection hw
    subst hw'
    simp only [stepCheck] at hck
    have hck' := Option.some.inj hck
    subst hck'
    obtain ⟨h1, h2, h3, h4, h5⟩ := stepActivateStart_fields pl cs w actor
    refine ⟨E, hI.transport h1 h2 h3 h4, ?_, ?_, ?_, ?_⟩
    · rw [h5]; exact hR.runs_len
    · rw [h5]; exact hR.runs_ok
    · rw [h3]; exact hR.actor_form
    · exact hR.stack_group
  | activateEnd actor =>
    have hw' : stepActivateEnd pl w actor = w' := by
      change Except.ok (stepActivateEnd pl w actor) = Except.ok w' at hw
      injection hw
    subst hw'
    simp only [stepCheck] at hck
    have hck' := Option.some.inj hck
    subst hck'
    obtain ⟨h1, h2, h3, h4, h5⟩ := stepActivateEnd_fields pl w actor
    refine ⟨E, hI.transport h1 h2 h3 h4, ?_, ?_, ?_, ?_⟩
    · rw [h5]; exact hR.runs_len
    · rw [h5]; exact hR.runs_ok
    · rw [h3]; exact hR.actor_form
    · exact hR.stack_group

theorem walk_lock {pl : Plan} {hdr lab0 : List Rect} {cs : List Int} {steps : List Step}
    (hpl : pl.Wf) (hpf : PlanFacts pl) (hfm : ModelFacts pl.m) (hcs : cs = columns pl steps) :
    ∀ (l : List Step), (∀ s ∈ l, s ∈ steps) → ∀ (w : Walk) (ck : CheckState) (E : List Ent),
      Inv pl hdr lab0 ck.stack ck.placed w E → RInv pl cs ck w → ∀ (w1 : Walk) (ck1 : CheckState),
        l.foldlM (stepWalk pl cs) w = .ok w1 → l.foldlM (stepCheck pl) ck = some ck1 →
        ∃ E1, Inv pl hdr lab0 ck1.stack ck1.placed w1 E1 ∧ RInv pl cs ck1 w1 := by
  intro l
  induction l with
  | nil =>
    intro _ w ck E hI hR w1 ck1 hw hck
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hw
    simp only [List.foldlM_nil, pure, Option.some.injEq] at hck
    subst hw
    subst hck
    exact ⟨E, hI, hR⟩
  | cons s t ih =>
    intro hl w ck E hI hR w1 ck1 hw hck
    simp only [List.foldlM_cons, bind, Except.bind] at hw
    simp only [List.foldlM_cons, bind, Option.bind] at hck
    cases hs1 : stepWalk pl cs w s with
    | error e => rw [hs1] at hw; cases hw
    | ok w2 =>
      rw [hs1] at hw
      cases hs2 : stepCheck pl ck s with
      | none => rw [hs2] at hck; cases hck
      | some ck2 =>
        rw [hs2] at hck
        obtain ⟨E2, hI2, hR2⟩ := step_lock hpl hpf hfm hcs s (hl s List.mem_cons_self) hI hR hs1 hs2
        exact ih (fun s' hs' => hl s' (List.mem_cons_of_mem _ hs')) w2 ck2 E2 hI2 hR2 w1 ck1 hw hck

end Sequence
end Elegant

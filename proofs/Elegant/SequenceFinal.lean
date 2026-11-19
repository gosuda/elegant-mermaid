import Elegant.SequenceLock2

set_option autoImplicit false

/-! The walk invariant at the end of the walk: the headers, the open fragments closed, and the route
and actor part of the invariant (`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

theorem getD_zipIdx_map {α β : Type} (l : List α) (f : α × Nat → β) (i : Nat) (d : β) (a : α)
    (ha : l[i]? = some a) : (l.zipIdx.map f).getD i d = f (a, i) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, ha]

theorem isParticipantBox_not_actor {b : ModelBox} (h : isParticipantBox b = true) :
    isActorBox b = false := by
  unfold isParticipantBox at h
  unfold isActorBox
  cases hr : b.role <;> simp_all

theorem hdr_actor {pl : Plan} (cs : List Int) (hpf : PlanFacts pl) (o : Nat)
    (ho : o < pl.actorBoxes.length) :
    (headerRects pl cs).getD (pl.actorBoxes.getD o 0) rectZero = actorRect pl cs o := by
  obtain ⟨b, hb, hact⟩ := hpf.ab_actor o ho
  have e : pl.actorBoxes.getD o 0 = pl.actorBoxes[o] := by simp [List.getD_eq_getElem?_getD, ho]
  have hnp : isParticipantBox b = false := by
    cases hp : isParticipantBox b with
    | false => rfl
    | true =>
      have := isParticipantBox_not_actor hp
      rw [hact] at this
      cases this
  rw [e]
  unfold headerRects
  simp only []
  rw [getD_zipIdx_map _ _ _ _ b hb]
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  unfold actorRects
  rw [getD_zipIdx_map _ _ _ _ b hb]
  simp only []
  rw [findIdx_of_nodup _ hpf.ab_nodup o ho]

theorem initRInv {pl : Plan} (cs : List Int) (hpf : PlanFacts pl) :
    RInv pl cs ⟨[], [], 0⟩ (initWalk pl cs) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · intro i run h
    simp [initWalk] at h
  · intro o ho
    refine ⟨pl.bandTop, ?_⟩
    show (headerRects pl cs).getD _ rectZero = _
    rw [hdr_actor cs hpf o ho]
    rfl
  · intro s hs
    simp at hs

theorem rinv_close {pl : Plan} {cs : List Int} (hpf : PlanFacts pl) {stack stack' placed : List Nat}
    {routes : Nat} {w w' : Walk} {f : FragRun} {rest : List FragRun}
    (hR : RInv pl cs ⟨stack, placed, routes⟩ w) (hst : stack = f.box :: stack') {width : Int}
    (hw : closeWith pl { w with fragments := rest } f width = w') :
    RInv pl cs ⟨stack', placed, routes⟩ w' := by
  subst hw
  have hg : IsGroupAt pl.m f.box := hR.stack_group f.box (by rw [hst]; exact List.mem_cons_self)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [closeWith_routeRuns]; exact hR.runs_len
  · intro i run hget
    rw [closeWith_routeRuns] at hget
    exact hR.runs_ok i run hget
  · exact actor_form_set hR.actor_form f.box _ (closeWith_boxRects pl _ f width)
      (fun o ho => actor_ne_group hpf ho hg)
  · intro s hs
    exact hR.stack_group s (by rw [hst]; exact List.mem_cons_of_mem _ hs)

theorem closeAll_lock {pl : Plan} {hdr lab0 : List Rect} {cs : List Int} (hpl : pl.Wf)
    (hpf : PlanFacts pl) (hfm : ModelFacts pl.m) :
    ∀ (n : Nat) (stack placed : List Nat) (routes : Nat) (w w2 : Walk) (E : List Ent),
      Inv pl hdr lab0 stack placed w E → RInv pl cs ⟨stack, placed, routes⟩ w →
      w.fragments.length = n → closeAll pl w n = .ok w2 →
      ∃ E', Inv pl hdr lab0 [] placed w2 E' ∧ RInv pl cs ⟨[], placed, routes⟩ w2 := by
  intro n
  induction n with
  | zero =>
    intro stack placed routes w w2 E hI hR hn hc
    have hf : w.fragments = [] := List.length_eq_zero_iff.mp hn
    have hs : stack = [] := by
      have := hI.stack_eq
      rw [hf] at this
      exact this.symm
    subst hs
    simp only [closeAll, pure, Except.pure, Except.ok.injEq] at hc
    subst hc
    exact ⟨E, hI, hR⟩
  | succ n ih =>
    intro stack placed routes w w2 E hI hR hn hc
    cases hfs : w.fragments with
    | nil => rw [hfs] at hn; simp at hn
    | cons f rest =>
      have hst : stack = f.box :: rest.map (·.box) := by
        have := hI.stack_eq
        rw [hfs] at this
        exact this.symm
      simp only [closeAll, hfs, bind, Except.bind] at hc
      cases hcf : closeFragment pl { w with fragments := rest } f with
      | error e => rw [hcf] at hc; cases hc
      | ok w' =>
        rw [hcf] at hc
        obtain ⟨E', hI'⟩ := inv_close hpl hfm hI hfs hcf
        obtain ⟨width, -, -, hw'⟩ := closeFragment_spec pl _ f w' hcf
        have hR' : RInv pl cs ⟨stack.tail, placed, routes⟩ w' :=
          rinv_close hpf (stack' := stack.tail) hR (by rw [hst]; rfl) hw'.symm
        have hlen : w'.fragments.length = n := by
          have h1 := congrArg List.length hI'.stack_eq
          have h2 := congrArg List.length hI.stack_eq
          simp only [List.length_map, List.length_tail] at h1 h2
          rw [hfs] at hn h2
          simp only [List.length_cons] at hn h2
          omega
        have hc' : closeAll pl w' n = .ok w2 := hc
        exact ih stack.tail placed routes w' w2 E' hI' hR' hlen hc'

theorem walk_final {pl : Plan} {cs : List Int} {steps : List Step} (hpl : pl.Wf) (hpf : PlanFacts pl)
    (hfm : ModelFacts pl.m) (hcs : cs = columns pl steps) {w3 : Walk} {ck : CheckState}
    (hw : walk pl cs steps = .ok w3)
    (hck : steps.foldlM (stepCheck pl) ⟨[], [], 0⟩ = some ck) :
    ∃ E, Inv pl (headerRects pl cs) (headerLabels pl (headerRects pl cs)) [] ck.placed w3 E ∧
      RInv pl cs ⟨[], ck.placed, ck.routes⟩ w3 := by
  unfold walk at hw
  simp only [bind, Except.bind, pure, Except.pure] at hw
  cases h1 : steps.foldlM (stepWalk pl cs) (initWalk pl cs) with
  | error e => simp [h1] at hw
  | ok w1 =>
    simp only [h1] at hw
    cases h2 : closeAll pl w1 w1.fragments.length with
    | error e => simp [h2] at hw
    | ok w2 =>
      simp only [h2, Except.ok.injEq] at hw
      subst hw
      obtain ⟨E1, hI1, hR1⟩ := walk_lock hpl hpf hfm hcs steps (fun s hs => hs) (initWalk pl cs)
        ⟨[], [], 0⟩ [] inv_init (initRInv cs hpf) w1 ck h1 hck
      obtain ⟨E2, hI2, hR2⟩ := closeAll_lock hpl hpf hfm _ ck.stack ck.placed ck.routes w1 w2 E1
        hI1 hR1 rfl h2
      exact ⟨E2, hI2.transport rfl rfl rfl rfl, hR2.runs_len, hR2.runs_ok, hR2.actor_form,
        hR2.stack_group⟩

end Sequence
end Elegant

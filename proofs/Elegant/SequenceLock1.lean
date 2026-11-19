import Elegant.SequencePlan

set_option autoImplicit false

/-! The route and actor part of the walk invariant, and the helper facts about the steps that the
lockstep walk needs (`spec/layout/sequence.md`, sequence-54). -/

namespace Elegant
namespace Sequence

theorem Inv.transport {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w w' : Walk}
    {E : List Ent} (h : Inv pl hdr lab0 stack placed w E) (hf : w'.fragments = w.fragments)
    (hc : w'.cursor = w.cursor) (hb : w'.boxRects = w.boxRects) (hl : w'.labelRects = w.labelRects) :
    Inv pl hdr lab0 stack placed w' E := by
  refine { stack_eq := ?_, chain := h.chain, stack_lt := h.stack_lt, stack_len := h.stack_len,
           stack_nodup := h.stack_nodup, placed_lt := h.placed_lt, stack_placed := h.stack_placed,
           lenR := ?_, lenL := ?_, unplaced := ?_, frag := ?_, cursor := ?_, frag_top := ?_,
           frag_adv := ?_, frag_members := ?_, frag_nested := ?_, ent_ok := ?_,
           ent_host := h.ent_host, ent_j1 := ?_, ent_cover := ?_, ent_sep := h.ent_sep,
           ent_strict := ?_, link_box := ?_, link_lab := ?_ }
  · simpa only [hf] using h.stack_eq
  · simpa only [hb] using h.lenR
  · simpa only [hl] using h.lenL
  · simpa only [hb] using h.unplaced
  · simpa only [hf, hc] using h.frag
  · simpa only [hc] using h.cursor
  · simpa only [hf] using h.frag_top
  · simpa only [hf, hc] using h.frag_adv
  · simpa only [hf] using h.frag_members
  · simpa only [hf] using h.frag_nested
  · simpa only [hc] using h.ent_ok
  · simpa only [hf] using h.ent_j1
  · simpa only [hf] using h.ent_cover
  · simpa only [hb] using h.ent_strict
  · simpa only [hb] using h.link_box
  · simpa only [hb, hl] using h.link_lab

theorem stepActivateStart_fields (pl : Plan) (cs : List Int) (w : Walk) (actor : Nat) :
    (stepActivateStart pl cs w actor).fragments = w.fragments ∧
      (stepActivateStart pl cs w actor).cursor = w.cursor ∧
      (stepActivateStart pl cs w actor).boxRects = w.boxRects ∧
      (stepActivateStart pl cs w actor).labelRects = w.labelRects ∧
      (stepActivateStart pl cs w actor).routeRuns = w.routeRuns :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem stepActivateEnd_fields (pl : Plan) (w : Walk) (actor : Nat) :
    (stepActivateEnd pl w actor).fragments = w.fragments ∧
      (stepActivateEnd pl w actor).cursor = w.cursor ∧
      (stepActivateEnd pl w actor).boxRects = w.boxRects ∧
      (stepActivateEnd pl w actor).labelRects = w.labelRects ∧
      (stepActivateEnd pl w actor).routeRuns = w.routeRuns := by
  unfold stepActivateEnd
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem closeWith_routeRuns (pl : Plan) (w : Walk) (run : FragRun) (width : Int) :
    (closeWith pl w run width).routeRuns = w.routeRuns := by
  unfold closeWith
  rw [addMember_routeRuns]

/-- A route run: the stubs and the row of a message, between two lifelines of the plan. -/
def RunOK (pl : Plan) (cs : List Int) (i : Nat) (run : RouteRun) : Prop :=
  ∃ src dst, src < pl.actorBoxes.length ∧ dst < pl.actorBoxes.length ∧
    routeEndsOk pl i src dst = true ∧ ∃ y : Int, B0 pl ≤ y ∧
      ((src ≠ dst ∧ ∃ a b : Int, run.points =
          [⟨cs.getD src 0, a⟩, ⟨cs.getD src 0, y⟩, ⟨cs.getD dst 0, y⟩, ⟨cs.getD dst 0, b⟩]) ∨
        (src = dst ∧ ∃ a dx : Int, 0 ≤ dx ∧ run.points =
          [⟨cs.getD src 0, a⟩, ⟨cs.getD src 0, y⟩, ⟨cs.getD src 0 + dx, y⟩,
            ⟨cs.getD src 0 + dx, y + pl.c.selfLoopDepth⟩, ⟨cs.getD src 0, y + pl.c.selfLoopDepth⟩,
            ⟨cs.getD src 0, a⟩]))

structure RInv (pl : Plan) (cs : List Int) (ck : CheckState) (w : Walk) : Prop where
  runs_len : w.routeRuns.length = ck.routes
  runs_ok : ∀ i run, w.routeRuns[i]? = some run → RunOK pl cs i run
  actor_form : ∀ o, o < pl.actorBoxes.length → ∃ y : Int,
    w.boxRects.getD (pl.actorBoxes.getD o 0) rectZero =
      ⟨cs.getD o 0 - half (pl.widths.getD o 0), y, pl.widths.getD o 0, pl.heights.getD o 0⟩
  stack_group : ∀ s ∈ ck.stack, IsGroupAt pl.m s

theorem createdRect_none_of (pl : Plan) (cs : List Int) (bits dst : Nat) (y : Int)
    (h : bits.testBit 10 = false) : createdRect pl cs bits dst y = none := by
  unfold createdRect
  simp [h]

theorem createdRect_some_iff (pl : Plan) (cs : List Int) (bits dst : Nat) (y : Int) (b : Nat) (r : Rect)
    (h : createdRect pl cs bits dst y = some (b, r)) :
    bits.testBit 10 = true ∧ pl.actorBoxes[dst]? = some b := by
  unfold createdRect at h
  by_cases hb : bits.testBit 10 = true
  · simp only [hb, ↓reduceIte] at h
    refine ⟨hb, ?_⟩
    cases hab : pl.actorBoxes[dst]? with
    | none => simp [hab] at h
    | some bi =>
      simp only [hab, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1]
  · simp [hb] at h

theorem createdRect_of (pl : Plan) (cs : List Int) (bits dst : Nat) (y : Int) (bi : Nat)
    (h : bits.testBit 10 = true) (hb : pl.actorBoxes[dst]? = some bi) :
    ∃ r, createdRect pl cs bits dst y = some (bi, r) := by
  unfold createdRect
  simp [h, hb]

theorem createOk_spec (pl : Plan) (st : CheckState) (dst bi : Nat) (h : createOk pl st dst = some bi) :
    pl.actorBoxes[dst]? = some bi ∧ ∃ b, pl.m.boxes[bi]? = some b ∧ st.placed.contains bi = false ∧
      b.parent = topId pl.m st.stack := by
  unfold createOk at h
  cases hab : pl.actorBoxes[dst]? with
  | none => simp [hab] at h
  | some bi' =>
    simp only [hab] at h
    cases hb : pl.m.boxes[bi']? with
    | none => simp [hb] at h
    | some b =>
      simp only [hb] at h
      by_cases hc : (!(st.placed.contains bi') && !b.exclusive && b.parent == topId pl.m st.stack) = true
      · simp only [hc, ↓reduceIte, Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
        exact ⟨rfl, b, hb, hc.1.1, hc.2⟩
      · simp only [hc] at h
        cases h

theorem stepMessage_runs {pl : Plan} (hpl : pl.Wf) (cs : List Int) (w : Walk) (bits src dst route : Nat)
    (destroyed : Int) :
    ∃ run, (stepMessage pl cs w bits src dst route destroyed).routeRuns = w.routeRuns ++ [run] ∧
      (src ≠ dst → ∃ a b : Int, run.points =
        [⟨cs.getD src 0, a⟩, ⟨cs.getD src 0, msgY pl w route⟩, ⟨cs.getD dst 0, msgY pl w route⟩,
          ⟨cs.getD dst 0, b⟩]) ∧
      (src = dst → ∃ a dx : Int, 0 ≤ dx ∧ run.points =
        [⟨cs.getD src 0, a⟩, ⟨cs.getD src 0, msgY pl w route⟩, ⟨cs.getD src 0 + dx, msgY pl w route⟩,
          ⟨cs.getD src 0 + dx, msgY pl w route + pl.c.selfLoopDepth⟩,
          ⟨cs.getD src 0, msgY pl w route + pl.c.selfLoopDepth⟩, ⟨cs.getD src 0, a⟩]) := by
  unfold stepMessage
  simp only [Walk.advance, addMember_routeRuns, placeLabel_routeRuns, markDestroyed_routeRuns,
    createdBox_routeRuns]
  refine ⟨_, rfl, fun hne => ?_, fun heq => ?_⟩
  · rw [messageRun_points_cross _ _ _ _ _ _ _ _ _ hne]
    exact ⟨_, _, rfl⟩
  · subst heq
    rw [messageRun_points_self]
    exact ⟨_, msgDx pl src src route, msgDx_nonneg hpl src src route, rfl⟩

theorem actor_form_set {pl : Plan} {cs : List Int} {w w' : Walk}
    (hf : ∀ o, o < pl.actorBoxes.length → ∃ y : Int,
      w.boxRects.getD (pl.actorBoxes.getD o 0) rectZero =
        ⟨cs.getD o 0 - half (pl.widths.getD o 0), y, pl.widths.getD o 0, pl.heights.getD o 0⟩)
    (k : Nat) (r : Rect) (hb : w'.boxRects = w.boxRects.set k r)
    (hk : ∀ o, o < pl.actorBoxes.length → pl.actorBoxes.getD o 0 ≠ k) :
    ∀ o, o < pl.actorBoxes.length → ∃ y : Int,
      w'.boxRects.getD (pl.actorBoxes.getD o 0) rectZero =
        ⟨cs.getD o 0 - half (pl.widths.getD o 0), y, pl.widths.getD o 0, pl.heights.getD o 0⟩ := by
  intro o ho
  obtain ⟨y, hy⟩ := hf o ho
  refine ⟨y, ?_⟩
  rw [hb, getD_set_gen]
  have hne : k ≠ pl.actorBoxes.getD o 0 := fun h => hk o ho h.symm
  simp only [hne, false_and, ↓reduceIte]
  exact hy

theorem actor_ne_group {pl : Plan} (hpf : PlanFacts pl) {o : Nat} (ho : o < pl.actorBoxes.length) {k : Nat}
    (hg : IsGroupAt pl.m k) : pl.actorBoxes.getD o 0 ≠ k := by
  intro h
  obtain ⟨b, hb, hbr⟩ := hg
  obtain ⟨b', hb', hact⟩ := hpf.ab_actor o ho
  have e : pl.actorBoxes.getD o 0 = pl.actorBoxes[o] := by simp [List.getD_eq_getElem?_getD, ho]
  rw [e] at h
  rw [h, hb] at hb'
  have := Option.some.inj hb'
  subst this
  simp [isActorBox, hbr] at hact

theorem actor_ne_note {pl : Plan} (hpf : PlanFacts pl) {o : Nat} (ho : o < pl.actorBoxes.length) {k : Nat}
    {b : ModelBox} (hb : pl.m.boxes[k]? = some b) (hn : isNoteBox b = true) :
    pl.actorBoxes.getD o 0 ≠ k := by
  intro h
  obtain ⟨b', hb', hact⟩ := hpf.ab_actor o ho
  have e : pl.actorBoxes.getD o 0 = pl.actorBoxes[o] := by simp [List.getD_eq_getElem?_getD, ho]
  rw [e] at h
  rw [h, hb] at hb'
  have := Option.some.inj hb'
  subst this
  simp [isActorBox, isNoteBox] at hact hn
  simp [hn.1, hn.2] at hact

theorem nodup_getD_ne {l : List Nat} (hnd : l.Nodup) {a b : Nat} (ha : a < l.length) (hb : b < l.length)
    (hab : a ≠ b) : l.getD a 0 ≠ l.getD b 0 := by
  intro h
  have e1 : l.getD a 0 = l[a] := by simp [List.getD_eq_getElem?_getD, ha]
  have e2 : l.getD b 0 = l[b] := by simp [List.getD_eq_getElem?_getD, hb]
  rw [e1, e2] at h
  exact hab (hnd.eq_of_getElem_eq ha hb h)

theorem rinv_message {pl : Plan} {cs : List Int} {ck ck' : CheckState} {w : Walk} (hpl : pl.Wf)
    (hpf : PlanFacts pl) (hr : RInv pl cs ck w) (hcur : B0 pl ≤ w.cursor)
    (hlenR : w.boxRects.length = pl.m.boxes.length)
    {bits src dst route : Nat} {destroyed : Int} (hsrc : src < pl.actorBoxes.length)
    (hdst : dst < pl.actorBoxes.length) (hends : routeEndsOk pl route src dst = true)
    (hroute : route = ck.routes) (hstack : ck'.stack = ck.stack) (hroutes : ck'.routes = ck.routes + 1) :
    RInv pl cs ck' (stepMessage pl cs w bits src dst route destroyed) := by
  obtain ⟨run, hruns, hcross, hself⟩ := stepMessage_runs hpl cs w bits src dst route destroyed
  have hmt := hpl.pos.messageTop
  have hn : 0 ≤ msgCount pl route * pl.c.lineHeight :=
    Int.mul_nonneg (Int.natCast_nonneg _) hpl.pos.lineHeight
  have hy : B0 pl ≤ msgY pl w route := by unfold msgY; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hruns]; simp [hr.runs_len, hroutes]
  · intro i run' hget
    rw [hruns] at hget
    by_cases hi : i < w.routeRuns.length
    · rw [List.getElem?_append_left hi] at hget
      exact hr.runs_ok i run' hget
    · rw [List.getElem?_append_right (by omega)] at hget
      have h0 : i - w.routeRuns.length = 0 := by
        cases hk : i - w.routeRuns.length with
        | zero => rfl
        | succ k => rw [hk] at hget; simp at hget
      have hrun : run' = run := by
        rw [h0] at hget
        simpa using hget.symm
      have hi' : i = route := by rw [hroute, ← hr.runs_len]; omega
      subst hrun
      subst hi'
      refine ⟨src, dst, hsrc, hdst, hends, msgY pl w i, hy, ?_⟩
      by_cases hsd : src = dst
      · right
        exact ⟨hsd, (hself hsd)⟩
      · left
        exact ⟨hsd, hcross hsd⟩
  · rw [stepMessage_boxRects_eq]
    intro o ho
    obtain ⟨y0, hy0⟩ := hr.actor_form o ho
    cases hc : createdRect pl cs bits dst (msgY pl w route) with
    | none => exact ⟨y0, hy0⟩
    | some q =>
      obtain ⟨bi, r⟩ := q
      obtain ⟨-, hab⟩ := createdRect_some_iff _ _ _ _ _ _ _ hc
      have hr0 := createdRect_spec _ _ _ _ _ _ _ hc
      have hbi : pl.actorBoxes.getD dst 0 = bi := by simp [List.getD_eq_getElem?_getD, hab]
      have hbi_lt : bi < pl.m.boxes.length := by
        have := hpf.ab_actor dst hdst
        obtain ⟨b, hb, -⟩ := this
        have e : pl.actorBoxes[dst] = bi := by
          have := hab
          simp [List.getElem?_eq_getElem hdst] at this
          exact this
        rw [e] at hb
        exact (List.getElem?_eq_some_iff.mp hb).1
      by_cases hod : o = dst
      · subst hod
        refine ⟨msgY pl w route, ?_⟩
        simp only []
        rw [getD_set_gen, hbi]
        simp [hbi_lt, hlenR, hr0]
      · have hne := nodup_getD_ne hpf.ab_nodup ho hdst hod
        refine ⟨y0, ?_⟩
        simp only []
        rw [getD_set_gen]
        have : bi ≠ pl.actorBoxes.getD o 0 := fun h => hne (by rw [hbi, h])
        simp only [this, false_and, ↓reduceIte]
        exact hy0
  · rw [hstack]; exact hr.stack_group

end Sequence
end Elegant

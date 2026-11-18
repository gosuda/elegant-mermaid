import Elegant.Kinds.Timeline
import Elegant.LanesFacts
import Elegant.LanesConsts

set_option autoImplicit false

/-! Timeline validity: every successful `Timeline.layout` satisfies the validator's hard
constraints. The adapter, decoder facts, plan geometry and route facts live in
`Elegant.Kinds.Timeline`; this module assembles the remaining clauses. Captions stay
opaque: the proofs never evaluate wrapped text, they only use that every measured caption
has non-negative width and positive height. -/

namespace Elegant.Kinds.Timeline

open Lanes Lanes.Timeline

/-! ### Loop preservation -/

private theorem loop_preserves {α β : Type} (inputs : List α)
    (step : α → β → Except LayoutError (ForInStep β)) (P : β → Prop)
    (initial final : β) (hi : P initial)
    (hstep : ∀ item ∈ inputs, ∀ state next, P state →
      step item state = .ok next → P next.value)
    (h : forIn inputs initial step = .ok final) : P final := by
  induction inputs generalizing initial with
  | nil =>
    have he : initial = final := by
      simpa only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] using h
    simpa only [← he] using hi
  | cons item rest ih =>
    rw [List.forIn_cons] at h
    cases hs : step item initial with
    | error err => simp [hs, Bind.bind, Except.bind] at h
    | ok next =>
      have hn := hstep item (List.mem_cons_self ..) initial next hi hs
      cases next with
      | done state =>
        dsimp only [ForInStep.value] at hn
        have he : state = final := by
          simpa [hs, Bind.bind, Except.bind, pure, Except.pure] using h
        simpa only [← he] using hn
      | yield state =>
        have htail : forIn rest state step = .ok final := by
          simpa [hs, Bind.bind, Except.bind, pure, Except.pure] using h
        exact ih state hn
          (fun item hm state next hp hnext =>
            hstep item (List.mem_cons_of_mem _ hm) state next hp hnext) htail

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ### Measured captions -/

theorem caption_width_nonneg {profile : Profile} {role : TextRole} {target : Int}
    {text : String} {caption : Lanes.Caption}
    (h : measureCaption profile role target text = .ok caption) : 0 ≤ caption.w := by
  have fold : ∀ (lines : List Measure.Line) (w : Int),
      w ≤ lines.foldl (fun w l => max w l.width) w := by
    intro lines
    induction lines with
    | nil => intro w; exact Int.le_refl _
    | cons l rest ih =>
      intro w
      show rest.foldl (fun w l => max w l.width) (max w l.width) ≥ _
      exact Int.le_trans (Int.le_max_left w l.width) (ih _)
  unfold measureCaption at h
  dsimp only at h
  cases profile <;> dsimp only at h
  all_goals
    obtain ⟨metric, _, h⟩ := bind_ok h
    cases hw : StyledMeasure.wrap metric target text.toList with
    | error err =>
      simp only [hw, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
      cases h
    | ok lines =>
      simp only [hw, pure, Except.pure, Bind.bind, Except.bind, Except.ok.injEq] at h
      subst caption
      exact fold lines 0

/-- Every caption of a successfully decoded model has positive height and non-negative
width. -/
structure DecodedSizes (g : Family) : Prop where
  title : ∀ card, g.title = some card → 0 < card.caption.h ∧ 0 ≤ card.caption.w
  sections : ∀ card ∈ g.sections, 0 < card.caption.h ∧ 0 ≤ card.caption.w
  periods : ∀ period ∈ g.periods, 0 < period.caption.h ∧ 0 ≤ period.caption.w ∧
    ∀ e ∈ period.events, 0 < e.caption.h ∧ 0 ≤ e.caption.w

private theorem caption_ok {profile : Profile} {role : TextRole} {target : Int}
    {text : String} {caption : Lanes.Caption}
    (h : measureCaption profile role target text = .ok caption) :
    0 < caption.h ∧ 0 ≤ caption.w :=
  ⟨measureCaption_height_positive h, caption_width_nonneg h⟩

theorem decode_facts {m : Model} {g : Family} (h : decode m = .ok g) :
    DecodedSizes g ∧ (∀ period ∈ g.periods, period.sectionIndex = -1 ∨
      0 ≤ period.sectionIndex) := by
  have hp := decode_parentsRooted h
  unfold decode at h
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨final, hloop, hret⟩ := bind_ok h
  have hfinal : final = g := by
    simpa only [pure, Except.pure, Except.ok.injEq] using hret
  subst g
  refine loop_preserves _ _
    (fun state => DecodedSizes state ∧
      (∀ period ∈ state.periods, period.sectionIndex = -1 ∨ 0 ≤ period.sectionIndex))
    _ _ ⟨⟨(fun _ hc => by cases hc), (fun _ hc => by cases hc),
      (fun _ hp => by cases hp)⟩, (fun _ hm => by cases hm)⟩ ?_ hloop
  intro box _hbox state next hs hstep
  split at hstep
  · obtain ⟨caption, hc, hstep⟩ := bind_ok hstep
    have he : ForInStep.yield
        ({ state with title := some { id := box.id, caption } } : Family) = next := by
      simpa only [hc, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] using hstep
    subst next
    refine ⟨⟨?_, hs.1.sections, hs.1.periods⟩, hs.2⟩
    intro card hc'
    have he : ({ id := box.id, caption } : Lanes.Timeline.Card) = card :=
      Option.some.inj hc'
    subst card
    exact caption_ok hc
  · obtain ⟨caption, hc, hstep⟩ := bind_ok hstep
    have he : ForInStep.yield
        ({ state with sections := state.sections ++ [{ id := box.id, caption }] } :
          Family) = next := by
      simpa only [hc, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] using hstep
    subst next
    refine ⟨⟨hs.1.title, ?_, hs.1.periods⟩, hs.2⟩
    intro card hc'
    rcases List.mem_append.mp hc' with hold | hnew
    · exact hs.1.sections card hold
    · have he : card = ({ id := box.id, caption } : Lanes.Timeline.Card) :=
        List.mem_singleton.mp hnew
      subst card
      exact caption_ok hc
  · obtain ⟨sectionIndex, hsection, hstep⟩ := bind_ok hstep
    have hsectionBounds : sectionIndex = -1 ∨ 0 ≤ sectionIndex := by
      unfold sectionOf at hsection
      simp only [pure, Except.pure] at hsection
      split at hsection
      · exact Or.inl (Except.ok.inj hsection).symm
      · rename_i head _tail
        split at hsection
        · rename_i n
          split at hsection
          · rename_i hle
            have he := Except.ok.inj hsection
            exact Or.inr (by omega)
          · change (Except.error LayoutError.domain : Except LayoutError Int) =
              Except.ok sectionIndex at hsection
            cases hsection
        · change (Except.error LayoutError.domain : Except LayoutError Int) =
            Except.ok sectionIndex at hsection
          cases hsection
    split at hstep
    · change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
        .ok next at hstep
      cases hstep
    · obtain ⟨caption, hc, hstep⟩ := bind_ok hstep
      have he : ForInStep.yield
          ({ state with periods := state.periods ++
            [{ id := box.id, caption, sectionIndex, events := [] }] } : Family) = next := by
        simpa only [hc, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] using hstep
      subst next
      refine ⟨⟨hs.1.title, hs.1.sections, ?_⟩, ?_⟩
      · intro period hm
        rcases List.mem_append.mp hm with hold | hnew
        · exact hs.1.periods period hold
        · have he : period =
            { id := box.id, caption, sectionIndex, events := [] } :=
            List.mem_singleton.mp hnew
          subst period
          exact ⟨(caption_ok hc).1, (caption_ok hc).2, fun e he' => by cases he'⟩
      · intro period hm
        rcases List.mem_append.mp hm with hold | hnew
        · exact hs.2 period hold
        · have he : period =
            { id := box.id, caption, sectionIndex, events := [] } :=
            List.mem_singleton.mp hnew
          subst period
          exact hsectionBounds
  · cases hprevious : state.periods.getLast? with
    | none =>
      simp only [hprevious] at hstep
      change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
        .ok next at hstep
      cases hstep
    | some previous =>
      simp only [hprevious] at hstep
      cases hroute : m.routes.find? (·.toId == box.id) with
      | none =>
        simp only [hroute] at hstep
        change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
          .ok next at hstep
        cases hstep
      | some route =>
        simp only [hroute] at hstep
        by_cases hbad : (route.fromId != (if m.options.direction == .LR then
            ((previous.events.getLast?).map (·.id)).getD previous.id else previous.id)) = true
        · simp only [hbad, ↓reduceIte] at hstep
          change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
            .ok next at hstep
          cases hstep
        · simp only [hbad] at hstep
          obtain ⟨caption, hc, hstep⟩ := bind_ok hstep
          let event : Lanes.Timeline.Event := { id := box.id, caption, link := route.id }
          let updated := { previous with events := previous.events ++ [event] }
          have he : ForInStep.yield
              ({ state with periods :=
                  state.periods.set (state.periods.length - 1) updated } : Family) = next := by
            simpa only [hc, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] using hstep
          subst next
          refine ⟨⟨hs.1.title, hs.1.sections, ?_⟩, ?_⟩
          · intro period hm
            rcases List.mem_or_eq_of_mem_set hm with hold | hnew
            · exact hs.1.periods period hold
            · subst period
              have hprev := hs.1.periods previous (List.mem_of_getLast? hprevious)
              refine ⟨hprev.1, hprev.2.1, ?_⟩
              intro e he'
              rcases List.mem_append.mp he' with hold | hnew
              · exact hprev.2.2 e hold
              · have he2 : e = event := List.mem_singleton.mp hnew
                subst e
                exact caption_ok hc
          · intro period hm
            rcases List.mem_or_eq_of_mem_set hm with hold | hnew
            · exact hs.2 period hold
            · subst period
              have hprevMem := List.mem_of_getLast? hprevious
              exact hs.2 previous hprevMem
  · change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
      .ok next at hstep
    cases hstep

/-- The sizes a successful native timeline layout works with: positive card width,
non-negative period, section and event heights, and the constant gaps. -/
theorem native_sizes {g : Family} {profile : Profile} {r : Lanes.Timeline.Result}
    (_h : Lanes.Timeline.layout g profile = .ok r) (hs : DecodedSizes g) :
    let c := Lanes.TimelineConsts.load profile
    0 < Lanes.Timeline.cardWidth g c ∧
    0 ≤ Lanes.Timeline.periodHeight g c ∧
    0 ≤ Lanes.Timeline.sectionHeight g c ∧
    (∀ period ∈ g.periods, ∀ e ∈ period.events, 0 ≤ Lanes.Timeline.eventHeight c e) ∧
    0 ≤ c.sectionGap ∧ 0 ≤ c.eventGap ∧ 0 ≤ c.columnGap := by
  intro c
  have signs := Lanes.timeline_constants_positive profile
  have hpad : 0 ≤ c.cardPadding := signs.2.2.2.2.1
  refine ⟨Int.lt_of_lt_of_le signs.1 (Lanes.Timeline.cardWidth_lower g c), ?_, ?_, ?_,
    Int.le_of_lt signs.2.2.2.1, Int.le_of_lt signs.2.2.1, Int.le_of_lt signs.2.1⟩
  · have key : ∀ (l : List Lanes.Timeline.Period) (w : Int), 0 ≤ w →
        (∀ p ∈ l, 0 ≤ p.caption.h + 2 * c.cardPadding) →
        0 ≤ l.foldl (fun w p => max w (p.caption.h + 2 * c.cardPadding)) w := by
      intro l
      induction l with
      | nil => intro w hw _; exact hw
      | cons p rest ih =>
        intro w hw hnn
        rw [List.foldl_cons]
        have hhead : 0 ≤ p.caption.h + 2 * c.cardPadding :=
          hnn p (List.mem_cons_self ..)
        have hmax : 0 ≤ max w (p.caption.h + 2 * c.cardPadding) := by
          rw [Int.max_def]
          split
          · exact hhead
          · exact hw
        exact ih (max w (p.caption.h + 2 * c.cardPadding)) hmax
          (fun x hx => hnn x (List.mem_cons_of_mem _ hx))
    exact key g.periods 0 (Int.le_refl 0) (fun p hmem => by
      obtain ⟨hph, _⟩ := hs.periods p hmem
      omega)
  · have key : ∀ (l : List Lanes.Timeline.Card) (w : Int), 0 ≤ w →
        (∀ s ∈ l, 0 ≤ s.caption.h + 2 * c.cardPadding) →
        0 ≤ l.foldl (fun w s => max w (s.caption.h + 2 * c.cardPadding)) w := by
      intro l
      induction l with
      | nil => intro w hw _; exact hw
      | cons s rest ih =>
        intro w hw hnn
        rw [List.foldl_cons]
        have hhead : 0 ≤ s.caption.h + 2 * c.cardPadding :=
          hnn s (List.mem_cons_self ..)
        have hmax : 0 ≤ max w (s.caption.h + 2 * c.cardPadding) := by
          rw [Int.max_def]
          split
          · exact hhead
          · exact hw
        exact ih (max w (s.caption.h + 2 * c.cardPadding)) hmax
          (fun x hx => hnn x (List.mem_cons_of_mem _ hx))
    exact key g.sections 0 (Int.le_refl 0) (fun s hmem => by
      obtain ⟨hsh, _⟩ := hs.sections s hmem
      omega)
  · intro period hmem e hev
    have he := (hs.periods period hmem).2.2 e hev
    unfold Lanes.Timeline.eventHeight
    omega

/-! ### Slot order -/

theorem members_bound {g : Family} {s : Int} {k : Nat} (h : k ∈ members g s) :
    k < g.periods.length := by
  unfold members at h
  obtain ⟨pair, hpair, he⟩ := List.mem_filterMap.mp h
  obtain ⟨p, j⟩ := pair
  simp only at he
  split at he
  · have hjk : j = k := Option.some.inj he
    exact hjk ▸ (List.mem_zipIdx' hpair).1
  · exact absurd he (by simp)

private theorem mem_members_of_getElem? {g : Family} {s : Int} {i : Nat}
    {p : Lanes.Timeline.Period}
    (hi : g.periods[i]? = some p) (hs : p.sectionIndex = s) : i ∈ members g s := by
  unfold members
  refine List.mem_filterMap.mpr ⟨(p, i), List.mk_mem_zipIdx_iff_getElem?.mpr hi, ?_⟩
  simp [hs]

theorem members_nodup (g : Family) (s : Int) : (members g s).Nodup := by
  have main : ∀ (ps : List Lanes.Timeline.Period) (start : Nat),
      ((ps.zipIdx start).filterMap
        (fun pair : Lanes.Timeline.Period × Nat =>
          if pair.1.sectionIndex == s then some pair.2 else none)).Nodup := by
    intro ps
    induction ps with
    | nil => intro _start; simp [List.zipIdx_nil]
    | cons p rest ih =>
      intro start
      rw [List.zipIdx_cons, List.filterMap_cons]
      by_cases hp : (p.sectionIndex == s) = true
      · simp only [hp, ↓reduceIte]
        refine List.nodup_cons.mpr ⟨?_, ih (start + 1)⟩
        intro hxmem
        obtain ⟨pair, hpair, he⟩ := List.mem_filterMap.mp hxmem
        obtain ⟨q, j⟩ := pair
        simp only at he
        split at he
        · have hbound := List.mem_zipIdx hpair
          have hj : j = start := Option.some.inj he
          omega
        · exact absurd he (by simp)
      · simpa only [hp, Bool.false_eq_true, ↓reduceIte] using ih (start + 1)
  exact main g.periods 0

private theorem idxOf_eq_of_getElem? {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), l.Nodup → ∀ (a : α) (ia : Nat), l[ia]? = some a → l.idxOf a = ia := by
  intro l
  induction l with
  | nil => intro _ _ ia h; exact absurd h (by simp)
  | cons x xs ih =>
    intro hn a ia h
    obtain ⟨hxn, hxs⟩ := List.nodup_cons.mp hn
    cases ia with
    | zero =>
      have hax : a = x := by simpa using (Option.some.inj h).symm
      rw [hax, List.idxOf_cons_self]
    | succ ia' =>
      have hxne : x ≠ a := by
        intro he
        exact hxn (by rw [he]; exact List.mem_of_getElem? h)
      have hxeq : (x == a) = false := by simpa using hxne
      rw [List.idxOf_cons, hxeq]
      have hrest : xs.idxOf a = ia' := ih hxs a ia' (by simpa using h)
      simp [hrest]

private theorem idxOf_inj {α : Type} [BEq α] [LawfulBEq α] {l : List α}
    (hn : l.Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l) (h : l.idxOf a = l.idxOf b) :
    a = b := by
  obtain ⟨ia, hia⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨ib, hib⟩ := List.mem_iff_getElem?.mp hb
  rw [idxOf_eq_of_getElem? l hn a ia hia, idxOf_eq_of_getElem? l hn b ib hib] at h
  have hidx : ia = ib := by omega
  rw [← hidx] at hib
  exact Option.some.inj (hia.symm.trans hib)

private theorem idxOf_lt_of_lt {α : Type} [BEq α] [LawfulBEq α] {l : List α}
    (hn : l.Nodup) {a b : α} {ia ib : Nat} (ha : l[ia]? = some a) (hb : l[ib]? = some b)
    (h : ia < ib) : l.idxOf a < l.idxOf b := by
  rw [idxOf_eq_of_getElem? l hn a ia ha, idxOf_eq_of_getElem? l hn b ib hb]
  exact h

theorem slot_eq_def (g : Family) (i : Nat) (p : Lanes.Timeline.Period) :
    slot g i p =
      if p.sectionIndex < 0 then (members g (-1)).idxOf i
      else first g p.sectionIndex.toNat + (members g p.sectionIndex).idxOf i :=
  rfl

private theorem slot_neg {g : Family} {i p} (hs : p.sectionIndex = -1) :
    slot g i p = (members g (-1)).idxOf i := by
  unfold slot
  rw [hs]
  simp

private theorem slot_pos {g : Family} {i p} (hs : 0 ≤ p.sectionIndex) :
    slot g i p = first g p.sectionIndex.toNat + (members g p.sectionIndex).idxOf i := by
  unfold slot
  exact ite_eq_right (by omega)

private theorem first_ge_base (g : Family) (s : Nat) :
    (members g (-1)).length ≤ first g s := by
  unfold first
  omega

private theorem first_succ (g : Family) (s : Nat) :
    first g (s + 1) = first g s + span g s := by
  unfold first
  rw [List.range_succ, List.map_append, List.sum_append]
  simp [Nat.add_assoc]

private theorem first_mono (g : Family) : ∀ (s t : Nat), s ≤ t → first g s ≤ first g t := by
  intro s t
  induction t with
  | zero =>
    intro h
    have : s = 0 := Nat.le_zero.mp h
    subst s
    exact Nat.le_refl _
  | succ t ih =>
    intro h
    by_cases h' : s ≤ t
    · refine Nat.le_trans (ih h') ?_
      rw [first_succ]
      exact Nat.le_add_right _ _
    · have he : s = t + 1 := by omega
      rw [he]
      exact Nat.le_refl _

private theorem span_ge_members (g : Family) (s : Nat) :
    (members g s).length ≤ span g s := by
  have hdef : span g s = max 1 (members g s).length := rfl
  have hle := Nat.le_max_right 1 (members g s).length
  omega

private theorem toNat_mono_of_nonneg {a b : Int} (ha : 0 ≤ a) (h : a < b) :
    a.toNat < b.toNat := by
  have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
  have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg (Int.le_trans ha (Int.le_of_lt h))
  have h3 : (a.toNat : Int) < (b.toNat : Int) := by omega
  exact Int.ofNat_lt.mp h3

private theorem span_ge_members' (g : Family) {s : Int} (hs : 0 ≤ s) :
    (members g s).length ≤ span g s.toNat := by
  have hcast : (s.toNat : Int) = s := Int.toNat_of_nonneg hs
  have h := span_ge_members g s.toNat
  rw [hcast] at h
  exact h

theorem slot_inj {g : Family} {i j : Nat} {p q : Lanes.Timeline.Period}
    (hb : ∀ r ∈ g.periods, r.sectionIndex = -1 ∨ 0 ≤ r.sectionIndex)
    (hi : g.periods[i]? = some p) (hj : g.periods[j]? = some q)
    (h : slot g i p = slot g j q) : i = j := by
  have hpm : p.sectionIndex = -1 ∨ 0 ≤ p.sectionIndex := hb p (List.mem_of_getElem? hi)
  have hqm : q.sectionIndex = -1 ∨ 0 ≤ q.sectionIndex := hb q (List.mem_of_getElem? hj)
  rcases hpm with hp1 | hp2 <;> rcases hqm with hq1 | hq2
  · rw [slot_neg hp1, slot_neg hq1] at h
    exact idxOf_inj (members_nodup g (-1))
      (mem_members_of_getElem? hi hp1) (mem_members_of_getElem? hj hq1) h
  · rw [slot_neg hp1, slot_pos hq2] at h
    have h1 := List.idxOf_lt_length_of_mem (mem_members_of_getElem? hi hp1)
    have h2 := first_ge_base g q.sectionIndex.toNat
    omega
  · rw [slot_pos hp2, slot_neg hq1] at h
    have h1 := List.idxOf_lt_length_of_mem (mem_members_of_getElem? hj hq1)
    have h2 := first_ge_base g p.sectionIndex.toNat
    omega
  · rw [slot_pos hp2, slot_pos hq2] at h
    have him : i ∈ members g p.sectionIndex := mem_members_of_getElem? hi rfl
    have hjm : j ∈ members g q.sectionIndex := mem_members_of_getElem? hj rfl
    by_cases hab : p.sectionIndex = q.sectionIndex
    · rw [hab] at him h
      exact idxOf_inj (members_nodup g q.sectionIndex) him hjm (by omega)
    · rcases Int.lt_or_gt_of_ne hab with hlt | hgt
      · have hcast := toNat_mono_of_nonneg hp2 hlt
        have h1 := List.idxOf_lt_length_of_mem him
        have h2 := span_ge_members' g hp2
        have h3 := first_mono g (p.sectionIndex.toNat + 1) q.sectionIndex.toNat
          (by omega)
        rw [first_succ] at h3
        omega
      · have hcast := toNat_mono_of_nonneg hq2 hgt
        have h1 := List.idxOf_lt_length_of_mem hjm
        have h2 := span_ge_members' g hq2
        have h3 := first_mono g (q.sectionIndex.toNat + 1) p.sectionIndex.toNat
          (by omega)
        rw [first_succ] at h3
        omega

private theorem slot_neg_lt_first0 (g : Family) {k : Nat} {p : Lanes.Timeline.Period}
    (hs : p.sectionIndex = -1) (hk : k ∈ members g (-1)) :
    slot g k p < (members g (-1)).length := by
  rw [slot_neg hs]
  exact List.idxOf_lt_length_of_mem hk

private theorem slot_ge_block (g : Family) {k : Nat} {p : Lanes.Timeline.Period}
    (hs : 0 ≤ p.sectionIndex) (_hp : g.periods[k]? = some p) :
    first g p.sectionIndex.toNat ≤ slot g k p := by
  rw [slot_pos hs]
  exact Nat.le_add_right _ _

private theorem slot_lt_block (g : Family) (s : Int)
    (hb : ∀ r ∈ g.periods, r.sectionIndex = -1 ∨ 0 ≤ r.sectionIndex)
    {k : Nat} {p : Lanes.Timeline.Period}
    (hk : k ∈ members g s) (hp : g.periods[k]? = some p) (hs : p.sectionIndex = s) :
    slot g k p < first g s.toNat + span g s.toNat := by
  have hbound := hb p (List.mem_of_getElem? hp)
  rcases hbound with h1 | h2
  · rw [slot_neg h1]
    have hsneg : s = -1 := hs.symm.trans h1
    subst s
    rw [h1] at hk ⊢
    have hidx := List.idxOf_lt_length_of_mem hk
    have hbase := first_ge_base g 0
    have hspan : 1 ≤ span g 0 := Nat.le_max_left ..
    have hcast : ((-1 : Int).toNat) = 0 := by decide
    rw [hcast]
    omega
  · rw [slot_pos h2, hs]
    have hidx := List.idxOf_lt_length_of_mem hk
    have hspan := span_ge_members' g (hs ▸ h2)
    omega

private theorem getElem?_zip_index {α β : Type} {l : List α} {m : List β} {i : Nat}
    {a : α} {b : β} (h : (l.zip m)[i]? = some (a, b)) :
    l[i]? = some a ∧ m[i]? = some b := by
  induction l generalizing m i with
  | nil => cases m <;> cases h
  | cons x xs ih =>
    cases m with
    | nil => simp [List.zip] at h
    | cons y ys =>
      cases i with
      | zero =>
        simp only [List.zip_cons_cons, List.getElem?_cons_zero, Option.some.injEq] at h
        cases h
        exact ⟨rfl, rfl⟩
      | succ i' =>
        simp only [List.zip_cons_cons, List.getElem?_cons_succ] at h
        obtain ⟨h1, h2⟩ := ih h
        exact ⟨by simpa using h1, by simpa using h2⟩

theorem plan_period_rect_eq {g : Family} {c : TimelineConsts} {i : Nat}
    {p : Lanes.Timeline.Period} {a : Rect}
    (hi : g.periods[i]? = some p) (ha : (horizontalPlan g c).periods[i]? = some a) :
    a = Lanes.Timeline.periodColumn c (cardWidth g c) (periodHeight g c)
      (contentTop g c + if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap)
      (slot g i p) := by
  have h := horizontal_period_rect hi (c := c)
  rw [ha] at h
  exact Option.some.inj h

theorem plan_section_rect_eq {g : Family} {c : TimelineConsts} {i : Nat} {s : Lanes.Timeline.Card}
    {a : Rect} (hi : g.sections[i]? = some s)
    (ha : (horizontalPlan g c).sections[i]? = some a) :
    a = ⟨c.leftMargin + ((first g i : Int)) * (cardWidth g c + c.columnGap),
      contentTop g c,
      ((span g i : Int)) * (cardWidth g c + c.columnGap) - c.columnGap,
      sectionHeight g c⟩ := by
  unfold horizontalPlan at ha
  simp only [List.getElem?_map, List.getElem?_zipIdx, hi, Option.map_some] at ha
  simpa using ha.symm

theorem slot_outside_section_range (g : Family)
    (hb : ∀ r ∈ g.periods, r.sectionIndex = -1 ∨ 0 ≤ r.sectionIndex)
    {k : Nat} {p : Lanes.Timeline.Period} (hp : g.periods[k]? = some p) (t : Nat)
    (hne : p.sectionIndex ≠ (t : Int)) :
    slot g k p < first g t ∨ first g t + span g t ≤ slot g k p := by
  have hbound := hb p (List.mem_of_getElem? hp)
  rcases hbound with h1 | h2
  · refine Or.inl ?_
    have hlt := slot_neg_lt_first0 g h1 (mem_members_of_getElem? hp h1)
    have hbase := first_ge_base g t
    omega
  · rcases Nat.lt_or_ge p.sectionIndex.toNat t with hlt | hge
    · refine Or.inl ?_
      have hslt := slot_lt_block g p.sectionIndex hb
        (mem_members_of_getElem? hp rfl) hp rfl
      have hmono := first_mono g (p.sectionIndex.toNat + 1) t (by omega)
      rw [first_succ] at hmono
      omega
    · refine Or.inr ?_
      have hslot := slot_ge_block g h2 hp
      have hcast : (p.sectionIndex.toNat : Int) = p.sectionIndex :=
        Int.toNat_of_nonneg h2
      have hne' : t ≠ p.sectionIndex.toNat := by
        intro he
        exact hne (by rw [he]; exact hcast.symm)
      have hlt' : t < p.sectionIndex.toNat := by omega
      have hmono := first_mono g (t + 1) p.sectionIndex.toNat (by omega)
      rw [first_succ] at hmono
      exact Nat.le_trans hmono hslot

/-! ### Horizontal plan geometry -/

theorem horizontalPlan_title_facts {g : Family} {c : TimelineConsts}
    {t : Lanes.Timeline.Card} (ht : g.title = some t) :
    (horizontalPlan g c).title.y = 0 ∧ (horizontalPlan g c).title.w = t.caption.w ∧
      (horizontalPlan g c).title.h = t.caption.h := by
  unfold horizontalPlan
  rw [ht]
  exact ⟨rfl, rfl, rfl⟩

private theorem column_x_le (c : TimelineConsts) {w : Int} (hw : 0 < w)
    (hgap : 0 ≤ c.columnGap) {k l : Nat} (h : k + 1 ≤ l) :
    (Lanes.Timeline.periodColumn c w 0 0 k).x + w ≤ (Lanes.Timeline.periodColumn c w 0 0 l).x ∧
      (Lanes.Timeline.periodColumn c w 0 0 k).x < (Lanes.Timeline.periodColumn c w 0 0 l).x := by
  have hS : 0 ≤ w + c.columnGap := by omega
  have hcast : ((k + 1 : Nat) : Int) ≤ ((l : Nat) : Int) := by exact_mod_cast h
  have h1 : ((k : Int) + 1) * (w + c.columnGap) ≤ ((l : Int)) * (w + c.columnGap) :=
    Int.mul_le_mul_of_nonneg_right hcast hS
  have hd : ((k : Int) + 1) * (w + c.columnGap) =
      ((k : Int)) * (w + c.columnGap) + (w + c.columnGap) := by
    rw [Int.add_mul, Int.one_mul]
  unfold Lanes.Timeline.periodColumn
  refine ⟨?_, ?_⟩ <;> dsimp only <;> omega

private theorem pairwise_stack_separated {rects : List Rect}
    (h : rects.Pairwise (fun a b => a.y + a.h ≤ b.y ∧ Disjoint a b)) {x y : Rect}
    (hx : x ∈ rects) (hy : y ∈ rects) (hne : x ≠ y) :
    x.y + x.h ≤ y.y ∨ y.y + y.h ≤ x.y := by
  induction rects with
  | nil => cases hx
  | cons r rest ih =>
    obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp hx with he | hx'
    · subst he
      rcases List.mem_cons.mp hy with he2 | hy'
      · exact absurd he2.symm hne
      · exact Or.inl (hfirst y hy').1
    · rcases List.mem_cons.mp hy with he2 | hy'
      · subst he2
        exact Or.inr (hfirst x hx').1
      · exact ih hrest hx' hy'

theorem horizontalPlan_events_row {g : Family} {c : TimelineConsts}
    {period : Lanes.Timeline.Period} {rects : List Rect}
    (hmem : (period, rects) ∈ g.periods.zip (horizontalPlan g c).events) :
    ∃ j : Nat, ∃ pr : Rect,
      g.periods[j]? = some period ∧
      (horizontalPlan g c).periods[j]? = some pr ∧
        rects = Lanes.Timeline.eventRects c pr.x (cardWidth g c)
          (contentTop g c +
            (if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap) +
            periodHeight g c + c.sectionGap) period.events := by
  obtain ⟨j, hpair⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨hj, hr⟩ := getElem?_zip_index hpair
  change (((g.periods.zip (horizontalPlan g c).periods).map
      fun (pair : Lanes.Timeline.Period × Rect) =>
        Lanes.Timeline.eventRects c pair.2.x (cardWidth g c)
          (contentTop g c +
            (if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap) +
            periodHeight g c + c.sectionGap) pair.1.events)[j]?) = some rects at hr
  rw [List.getElem?_map] at hr
  cases hpairs : (g.periods.zip (horizontalPlan g c).periods)[j]? with
  | none => simp only [hpairs, Option.map_none] at hr; cases hr
  | some pair =>
    obtain ⟨hjp, hpr⟩ := getElem?_zip_index hpairs
    have hpe : pair.1 = period := Option.some.inj (hjp.symm.trans hj)
    refine ⟨j, pair.2, hj, hpr, ?_⟩
    simp only [hpairs, Option.map_some, Option.some.injEq] at hr
    rw [hpe] at hr
    exact hr.symm

private theorem contentTop_of_title {g : Family} {c : TimelineConsts}
    {t : Lanes.Timeline.Card} (ht : g.title = some t) :
    contentTop g c = t.caption.h + c.eventGap := by
  unfold contentTop
  rw [ht]
  simp

end Elegant.Kinds.Timeline



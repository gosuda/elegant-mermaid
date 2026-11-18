import Elegant.TimelineValidity
import Elegant.Kinds.TimelineIdentityFacts

set_option autoImplicit false

namespace Elegant.Kinds.Timeline

open Lanes Lanes.Timeline

private theorem foldl_preserves {α β : Type} (step : β → α → β) (P : β → Prop)
    (hstep : ∀ state item, P state → P (step state item)) :
    ∀ (items : List α) (initial : β), P initial → P (items.foldl step initial) := by
  intro items
  induction items with
  | nil => intro initial hi; exact hi
  | cons item items ih =>
    intro initial hi
    exact ih (step initial item) (hstep initial item hi)

private theorem pairwise_disjoint_of_below (rs : List Rect)
    (h : rs.Pairwise (fun a b => a.y + a.h ≤ b.y ∧ Disjoint a b)) :
    rs.Pairwise Disjoint := by
  induction rs with
  | nil => exact .nil
  | cons a rs ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
    exact List.pairwise_cons.mpr ⟨fun b hb => (ha b hb).2, ih ht⟩

private theorem set_outside {α : Type} (xs : List α) (i : Nat) (a : α)
    (hi : xs.length ≤ i) : xs.set i a = xs := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons b xs ih =>
    cases i with
    | zero => simp at hi
    | succ i =>
      change b :: xs.set i a = b :: xs
      rw [ih i (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using hi)]


private theorem disjoint_symm {a b : Rect} (h : Disjoint a b) : Disjoint b a := by
  unfold Disjoint Rect.meetsInterior at *
  omega

private theorem disjoint_below {a b : Rect} (h : a.y + a.h ≤ b.y) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  omega

private theorem disjoint_left {a b : Rect} (h : a.x + a.w ≤ b.x) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  omega

private theorem pairwise_set (xs : List Rect) (i : Nat) (r : Rect)
    (hp : xs.Pairwise Disjoint) (hr : ∀ a ∈ xs, Disjoint r a) :
    (xs.set i r).Pairwise Disjoint := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, hx⟩ := List.pairwise_cons.mp hp
    cases i with
    | zero =>
      exact List.pairwise_cons.mpr ⟨fun b hb => hr b (List.mem_cons_of_mem _ hb), hx⟩
    | succ i =>
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih i hx (fun b hb => hr b (List.mem_cons_of_mem _ hb))⟩
      intro b hb
      rcases List.mem_or_eq_of_mem_set hb with hold | hnew
      · exact ha b hold
      · subst b
        exact disjoint_symm (hr a (List.mem_cons_self ..))

private theorem pairwise_flatten_set (xs : List (List Rect)) (i : Nat) (rs : List Rect)
    (hp : xs.flatten.Pairwise Disjoint) (hn : rs.Pairwise Disjoint)
    (hr : ∀ a ∈ rs, ∀ b ∈ xs.flatten, Disjoint a b) :
    (xs.set i rs).flatten.Pairwise Disjoint := by
  induction xs generalizing i with
  | nil => simp
  | cons first rest ih =>
    change (first ++ rest.flatten).Pairwise Disjoint at hp
    obtain ⟨hf, ht, hc⟩ := List.pairwise_append.mp hp
    cases i with
    | zero =>
      change (rs ++ rest.flatten).Pairwise Disjoint
      exact List.pairwise_append.mpr ⟨hn, ht,
        fun a ha b hb => hr a ha b (List.mem_append_right _ hb)⟩
    | succ i =>
      change (first ++ (rest.set i rs).flatten).Pairwise Disjoint
      apply List.pairwise_append.mpr
      refine ⟨hf, ih i ht (fun a ha b hb => hr a ha b (List.mem_append_right _ hb)), ?_⟩
      intro a ha b hb
      obtain ⟨block, hblock, hbin⟩ := List.mem_flatten.mp hb
      rcases List.mem_or_eq_of_mem_set hblock with hold | hnew
      · exact hc a ha b (List.mem_flatten.mpr ⟨block, hold, hbin⟩)
      · subst block
        exact disjoint_symm (hr b hbin a (List.mem_append_left _ ha))

private theorem fold_bottom (rs : List Rect) (initial : Int) :
    initial ≤ rs.foldl (fun y r => max y (r.y + r.h)) initial ∧
      ∀ r ∈ rs, r.y + r.h ≤ rs.foldl (fun y r => max y (r.y + r.h)) initial := by
  induction rs generalizing initial with
  | nil => exact ⟨Int.le_refl _, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons r rs ih =>
    obtain ⟨hstart, hrest⟩ := ih (max initial (r.y + r.h))
    refine ⟨Int.le_trans (Int.le_max_left ..) hstart, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with he | hm
    · subst b
      exact Int.le_trans (Int.le_max_right ..) hstart
    · exact hrest b hm

def verticalStateRects (st : VerticalState) : List Rect :=
  st.sections ++ (st.periods ++ st.events.flatten)

structure VerticalFrontier (g : Family) (c : TimelineConsts) (st : VerticalState) : Prop where
  sections_length : st.sections.length = g.sections.length
  periods_length : st.periods.length = g.periods.length
  events_length : st.events.length = g.periods.length
  routes_length : st.routes.length = g.periods.length
  nonnegative : 0 ≤ st.y
  content_top : contentTop g c ≤ st.y
  rectangles : ∀ r ∈ verticalStateRects st,
    0 ≤ r.x ∧ 0 ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧ r.y + r.h ≤ st.y
  disjoint : (verticalStateRects st).Pairwise Disjoint
  above_content : ∀ r ∈ verticalStateRects st, r = zeroRect ∨ contentTop g c ≤ r.y
  corridor_sides : ∀ r ∈ verticalStateRects st,
    r.x + r.w ≤ c.leftMargin + cardWidth g c ∨
      c.leftMargin + cardWidth g c + c.columnGap ≤ r.x

private theorem eventRects_sizes (c : TimelineConsts) (x w top : Int)
    (es : List Lanes.Timeline.Event) (hx : 0 ≤ x) (hw : 0 ≤ w) (ht : 0 ≤ top)
    (hg : 0 ≤ c.eventGap) (hh : ∀ e ∈ es, 0 ≤ eventHeight c e) :
    ∀ r ∈ eventRects c x w top es,
      0 ≤ r.x ∧ 0 ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h := by
  induction es generalizing top with
  | nil => intro r hr; cases hr
  | cons e es ih =>
    intro r hr
    have he := hh e (List.mem_cons_self ..)
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      exact ⟨hx, ht, hw, he⟩
    · exact ih _ (by omega) (fun a ha => hh a (List.mem_cons_of_mem _ ha)) r hr

private theorem verticalRow_frontier_y (g : Family) (c : TimelineConsts) (i : Nat)
    (st : VerticalState) (hh : 0 ≤ periodHeight g c) (hg : 0 ≤ c.sectionGap) :
    st.y ≤ (verticalRow g c i st).y := by
  have hb := (fold_bottom
    (eventRects c (c.leftMargin + cardWidth g c + c.columnGap)
      (cardWidth g c) st.y (((g.periods[i]?).map (·.events)).getD []))
    (st.y + periodHeight g c)).1
  change st.y ≤
    (eventRects c (c.leftMargin + cardWidth g c + c.columnGap)
      (cardWidth g c) st.y (((g.periods[i]?).map (·.events)).getD [])).foldl
      (fun y r => max y (r.y + r.h)) (st.y + periodHeight g c) + c.sectionGap
  omega

theorem verticalRow_frontier (g : Family) (c : TimelineConsts) (i : Nat)
    (st : VerticalState) (hs : VerticalFrontier g c st)
    (hl : 0 ≤ c.leftMargin) (hw : 0 ≤ cardWidth g c)
    (hh : 0 ≤ periodHeight g c) (hsg : 0 ≤ c.sectionGap)
    (heg : 0 ≤ c.eventGap) (hcg : 0 ≤ c.columnGap)
    (heights : ∀ event ∈ ((g.periods[i]?).map (·.events)).getD [],
      0 ≤ eventHeight c event) :
    VerticalFrontier g c (verticalRow g c i st) := by
  let p : Rect := ⟨c.leftMargin, st.y, cardWidth g c, periodHeight g c⟩
  let es := eventRects c (c.leftMargin + cardWidth g c + c.columnGap)
    (cardWidth g c) st.y (((g.periods[i]?).map (·.events)).getD [])
  let bottom := es.foldl (fun y r => max y (r.y + r.h)) (p.y + p.h)
  have hb := fold_bottom es (p.y + p.h)
  have hmono := verticalRow_frontier_y g c i st hh hsg
  have hesize := eventRects_sizes c (c.leftMargin + cardWidth g c + c.columnGap)
    (cardWidth g c) st.y _ (by omega) hw hs.nonnegative heg heights
  have helower := Lanes.Timeline.eventRects_lower c
    (c.leftMargin + cardWidth g c + c.columnGap) (cardWidth g c) st.y _ heg heights
  have old_p : ∀ r ∈ verticalStateRects st, Disjoint p r := by
    intro r hr
    exact disjoint_symm (disjoint_below (hs.rectangles r hr).2.2.2.2)
  have old_e : ∀ e ∈ es, ∀ r ∈ verticalStateRects st, Disjoint e r := by
    intro e he r hr
    have hlo := helower e he
    have hhi := (hs.rectangles r hr).2.2.2.2
    exact disjoint_symm (disjoint_below (by omega))
  have pe : ∀ e ∈ es, Disjoint p e := by
    intro e he
    have hx := (eventRects_horizontal c _ _ _ st.y e he).1
    apply disjoint_left
    dsimp only [p]
    omega
  have hep : es.Pairwise Disjoint := by
    have hstack := Lanes.Timeline.timeline_events_stack_disjoint c
      (c.leftMargin + cardWidth g c + c.columnGap) (cardWidth g c) st.y
      (((g.periods[i]?).map (·.events)).getD []) heg heights
    exact pairwise_disjoint_of_below es hstack
  obtain ⟨hsec, htail, hsecCross⟩ := List.pairwise_append.mp hs.disjoint
  obtain ⟨hper, hev, hperCross⟩ := List.pairwise_append.mp htail
  have newDisjoint : (verticalStateRects (verticalRow g c i st)).Pairwise Disjoint := by
    change (st.sections ++ (st.periods.set i p ++ (st.events.set i es).flatten)).Pairwise Disjoint
    apply List.pairwise_append.mpr
    refine ⟨hsec, ?_, ?_⟩
    · apply List.pairwise_append.mpr
      refine ⟨pairwise_set st.periods i p hper (fun r hr => old_p r (by simp [verticalStateRects, hr])),
        pairwise_flatten_set st.events i es hev hep
          (fun e he r hr => old_e e he r (by simp [verticalStateRects, hr])), ?_⟩
      intro a ha b hb
      obtain ⟨block, hblock, hbin⟩ := List.mem_flatten.mp hb
      rcases List.mem_or_eq_of_mem_set ha with ha | ha
      · rcases List.mem_or_eq_of_mem_set hblock with hold | hnew
        · exact hperCross a ha b (List.mem_flatten.mpr ⟨block, hold, hbin⟩)
        · subst block
          exact disjoint_symm (old_e b hbin a (by simp [verticalStateRects, ha]))
      · subst a
        rcases List.mem_or_eq_of_mem_set hblock with hold | hnew
        · exact old_p b (by simp [verticalStateRects, List.mem_flatten.mpr ⟨block, hold, hbin⟩])
        · subst block
          exact pe b hbin
    · intro a ha b hb
      rcases List.mem_append.mp hb with hp | he
      · rcases List.mem_or_eq_of_mem_set hp with hold | hnew
        · exact hsecCross a ha b (List.mem_append_left _ hold)
        · subst b
          exact disjoint_symm (old_p a (by simp [verticalStateRects, ha]))
      · obtain ⟨block, hblock, hbin⟩ := List.mem_flatten.mp he
        rcases List.mem_or_eq_of_mem_set hblock with hold | hnew
        · exact hsecCross a ha b
            (List.mem_append_right _ (List.mem_flatten.mpr ⟨block, hold, hbin⟩))
        · subst block
          exact disjoint_symm (old_e b hbin a (by simp [verticalStateRects, ha]))
  refine ⟨hs.sections_length, ?_, ?_, ?_, Int.le_trans hs.nonnegative hmono,
    Int.le_trans hs.content_top hmono, ?_, newDisjoint, ?_, ?_⟩
  · simpa only [verticalRow, List.length_set] using hs.periods_length
  · simpa only [verticalRow, List.length_set] using hs.events_length
  · simpa only [verticalRow, List.length_set] using hs.routes_length
  · intro r hr
    change r ∈ st.sections ++ (st.periods.set i p ++ (st.events.set i es).flatten) at hr
    have old (hr : r ∈ verticalStateRects st) := hs.rectangles r hr
    have old_result (hr : r ∈ verticalStateRects st) :
        0 ≤ r.x ∧ 0 ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h ∧ r.y + r.h ≤ (verticalRow g c i st).y := by
      obtain ⟨hx, hy, hw, hh, hb⟩ := old hr
      exact ⟨hx, hy, hw, hh, Int.le_trans hb hmono⟩
    rcases List.mem_append.mp hr with hs | ht
    · exact old_result (by simp [verticalStateRects, hs])
    · rcases List.mem_append.mp ht with hp | he
      · rcases List.mem_or_eq_of_mem_set hp with hold | hnew
        · exact old_result (by simp [verticalStateRects, hold])
        · subst r
          refine ⟨hl, hs.nonnegative, hw, hh, ?_⟩
          change p.y + p.h ≤ bottom + c.sectionGap
          exact Int.le_trans hb.1 (by omega)
      · obtain ⟨block, hblock, hbin⟩ := List.mem_flatten.mp he
        rcases List.mem_or_eq_of_mem_set hblock with hold | hnew
        · exact old_result (by simp [verticalStateRects, List.mem_flatten.mpr ⟨block, hold, hbin⟩])
        · subst block
          obtain ⟨hx, hy, hw, hh⟩ := hesize r hbin
          refine ⟨hx, hy, hw, hh, ?_⟩
          have hbound := hb.2 r hbin
          change r.y + r.h ≤ bottom + c.sectionGap
          omega
  · intro r hr
    change r ∈ st.sections ++ (st.periods.set i p ++ (st.events.set i es).flatten) at hr
    rcases List.mem_append.mp hr with hsec | htail
    · exact hs.above_content r (by simp [verticalStateRects, hsec])
    · rcases List.mem_append.mp htail with hperiod | hevent
      · rcases List.mem_or_eq_of_mem_set hperiod with hold | hnew
        · exact hs.above_content r (by simp [verticalStateRects, hold])
        · subst r
          exact Or.inr hs.content_top
      · obtain ⟨block, hblock, hbin⟩ := List.mem_flatten.mp hevent
        rcases List.mem_or_eq_of_mem_set hblock with hold | hnew
        · exact hs.above_content r
            (by simp [verticalStateRects, List.mem_flatten.mpr ⟨block, hold, hbin⟩])
        · subst block
          exact Or.inr (Int.le_trans hs.content_top (helower r hbin))
  · intro r hr
    change r ∈ st.sections ++ (st.periods.set i p ++ (st.events.set i es).flatten) at hr
    rcases List.mem_append.mp hr with hsec | htail
    · exact hs.corridor_sides r (by simp [verticalStateRects, hsec])
    · rcases List.mem_append.mp htail with hperiod | hevent
      · rcases List.mem_or_eq_of_mem_set hperiod with hold | hnew
        · exact hs.corridor_sides r (by simp [verticalStateRects, hold])
        · subst r
          exact Or.inl (Int.le_refl _)
      · obtain ⟨block, hblock, hbin⟩ := List.mem_flatten.mp hevent
        rcases List.mem_or_eq_of_mem_set hblock with hold | hnew
        · exact hs.corridor_sides r
            (by simp [verticalStateRects, List.mem_flatten.mpr ⟨block, hold, hbin⟩])
        · subst block
          exact Or.inr (by
            rw [(eventRects_horizontal c _ _ _ st.y r hbin).1]
            exact Int.le_refl _)

def verticalSectionState (g : Family) (c : TimelineConsts)
    (st : VerticalState) (s : Nat) : VerticalState :=
  { st with
    y := st.y + sectionHeight g c + c.sectionGap
    sections := st.sections.set s
      ⟨c.leftMargin, st.y, cardWidth g c, sectionHeight g c⟩ }

theorem verticalSection_frontier (g : Family) (c : TimelineConsts)
    (st : VerticalState) (s : Nat) (hs : VerticalFrontier g c st)
    (hl : 0 ≤ c.leftMargin) (hw : 0 ≤ cardWidth g c)
    (hh : 0 ≤ sectionHeight g c) (hg : 0 ≤ c.sectionGap) :
    VerticalFrontier g c (verticalSectionState g c st s) := by
  let r : Rect := ⟨c.leftMargin, st.y, cardWidth g c, sectionHeight g c⟩
  have hmono : st.y ≤ (verticalSectionState g c st s).y := by
    dsimp [verticalSectionState]
    omega
  have fresh : ∀ b ∈ verticalStateRects st, Disjoint r b := by
    intro b hb
    exact disjoint_symm (disjoint_below (hs.rectangles b hb).2.2.2.2)
  obtain ⟨hsec, htail, hcross⟩ := List.pairwise_append.mp hs.disjoint
  refine ⟨?_, hs.periods_length, hs.events_length, hs.routes_length,
    Int.le_trans hs.nonnegative hmono, Int.le_trans hs.content_top hmono, ?_, ?_, ?_, ?_⟩
  · simpa only [verticalSectionState, List.length_set] using hs.sections_length
  · intro b hb
    change b ∈ st.sections.set s r ++ (st.periods ++ st.events.flatten) at hb
    have old (hb : b ∈ verticalStateRects st) :
        0 ≤ b.x ∧ 0 ≤ b.y ∧ 0 ≤ b.w ∧ 0 ≤ b.h ∧
          b.y + b.h ≤ (verticalSectionState g c st s).y := by
      obtain ⟨hx, hy, hw, hh, hbottom⟩ := hs.rectangles b hb
      exact ⟨hx, hy, hw, hh, Int.le_trans hbottom hmono⟩
    rcases List.mem_append.mp hb with hsec | htail
    · rcases List.mem_or_eq_of_mem_set hsec with hold | hnew
      · exact old (by simp [verticalStateRects, hold])
      · subst b
        refine ⟨hl, hs.nonnegative, hw, hh, ?_⟩
        dsimp [r, verticalSectionState]
        omega
    · exact old (List.mem_append_right _ htail)
  · change (st.sections.set s r ++ (st.periods ++ st.events.flatten)).Pairwise Disjoint
    apply List.pairwise_append.mpr
    refine ⟨pairwise_set st.sections s r hsec
      (fun b hb => fresh b (List.mem_append_left _ hb)), htail, ?_⟩
    intro a ha b hb
    rcases List.mem_or_eq_of_mem_set ha with hold | hnew
    · exact hcross a hold b hb
    · subst a
      exact fresh b (List.mem_append_right _ hb)
  · intro b hb
    change b ∈ st.sections.set s r ++ (st.periods ++ st.events.flatten) at hb
    rcases List.mem_append.mp hb with hsec | htail
    · rcases List.mem_or_eq_of_mem_set hsec with hold | hnew
      · exact hs.above_content b (List.mem_append_left _ hold)
      · subst b
        exact Or.inr hs.content_top
    · exact hs.above_content b (List.mem_append_right _ htail)

  · intro b hb
    change b ∈ st.sections.set s r ++ (st.periods ++ st.events.flatten) at hb
    rcases List.mem_append.mp hb with hsec | htail
    · rcases List.mem_or_eq_of_mem_set hsec with hold | hnew
      · exact hs.corridor_sides b (List.mem_append_left _ hold)
      · subst b
        exact Or.inl (Int.le_refl _)
    · exact hs.corridor_sides b (List.mem_append_right _ htail)

def verticalInitialState (g : Family) (c : TimelineConsts) : VerticalState :=
  { y := contentTop g c
    sections := List.replicate g.sections.length zeroRect
    periods := List.replicate g.periods.length zeroRect
    events := List.replicate g.periods.length []
    routes := List.replicate g.periods.length [] }

theorem verticalInitial_frontier (g : Family) (c : TimelineConsts)
    (ht : 0 ≤ contentTop g c) (hl : 0 ≤ c.leftMargin) (hw : 0 ≤ cardWidth g c) :
    VerticalFrontier g c (verticalInitialState g c) := by
  have only_zero : ∀ r ∈ verticalStateRects (verticalInitialState g c), r = zeroRect := by
    intro r hr
    simp only [verticalStateRects, verticalInitialState, List.mem_append] at hr
    rcases hr with hsec | hperiod | hevent
    · exact (List.mem_replicate.mp hsec).2
    · exact (List.mem_replicate.mp hperiod).2
    · obtain ⟨block, hblock, hbin⟩ := List.mem_flatten.mp hevent
      have hempty : block = [] := (List.mem_replicate.mp hblock).2
      subst block
      cases hbin
  refine ⟨List.length_replicate, List.length_replicate, List.length_replicate,
    List.length_replicate, ht, Int.le_refl _, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [only_zero r hr]
    exact ⟨by decide, by decide, by decide, by decide, ht⟩
  · have main : ∀ (rs : List Rect), (∀ r ∈ rs, r = zeroRect) →
        rs.Pairwise Disjoint := by
      intro rs
      induction rs with
      | nil => intro _; exact List.Pairwise.nil
      | cons r rs ih =>
        intro hz
        apply List.pairwise_cons.mpr
        refine ⟨?_, ih (fun b hb => hz b (List.mem_cons_of_mem _ hb))⟩
        intro b hb
        rw [hz r (List.mem_cons_self ..), hz b (List.mem_cons_of_mem _ hb)]
        exact disjoint_below (by decide)
    exact main _ only_zero
  · intro r hr
    exact Or.inl (only_zero r hr)

  · intro r hr
    rw [only_zero r hr]
    exact Or.inl (by dsimp [zeroRect]; omega)

theorem verticalRows_frontier (g : Family) (c : TimelineConsts)
    (indices : List Nat) (st : VerticalState) (hs : VerticalFrontier g c st)
    (hl : 0 ≤ c.leftMargin) (hw : 0 ≤ cardWidth g c)
    (hh : 0 ≤ periodHeight g c) (hsg : 0 ≤ c.sectionGap)
    (heg : 0 ≤ c.eventGap) (hcg : 0 ≤ c.columnGap)
    (heights : ∀ (i : Nat), ∀ event ∈ ((g.periods[i]?).map (·.events)).getD [],
      0 ≤ eventHeight c event) :
    VerticalFrontier g c (indices.foldl (fun st i => verticalRow g c i st) st) := by
  induction indices generalizing st with
  | nil => exact hs
  | cons i rest ih =>
    exact ih _ (verticalRow_frontier g c i st hs hl hw hh hsg heg hcg (heights i))

theorem verticalPlan_frontier (g : Family) (c : TimelineConsts)
    (ht : 0 ≤ contentTop g c) (hl : 0 ≤ c.leftMargin) (hw : 0 ≤ cardWidth g c)
    (hp : 0 ≤ periodHeight g c) (hs : 0 ≤ sectionHeight g c)
    (hsg : 0 ≤ c.sectionGap) (heg : 0 ≤ c.eventGap) (hcg : 0 ≤ c.columnGap)
    (heights : ∀ (i : Nat), ∀ event ∈ ((g.periods[i]?).map (·.events)).getD [],
      0 ≤ eventHeight c event) :
    ∃ st : VerticalState, VerticalFrontier g c st ∧
      (verticalPlan g c).sections = st.sections ∧
      (verticalPlan g c).periods = st.periods ∧
      (verticalPlan g c).events = st.events ∧
      (verticalPlan g c).routes = st.routes := by
  let row := fun st i => verticalRow g c i st
  let sectionStep := fun (st : VerticalState) (s : Nat) =>
    (members g (s : Int)).foldl row (verticalSectionState g c st s)
  let initial := (members g (-1)).foldl row (verticalInitialState g c)
  let final := (List.range g.sections.length).foldl sectionStep initial
  have hi : VerticalFrontier g c initial :=
    verticalRows_frontier g c _ _ (verticalInitial_frontier g c ht hl hw)
      hl hw hp hsg heg hcg heights
  have step (st : VerticalState) (s : Nat) (h : VerticalFrontier g c st) :
      VerticalFrontier g c (sectionStep st s) :=
    verticalRows_frontier g c _ _ (verticalSection_frontier g c st s h hl hw hs hsg)
      hl hw hp hsg heg hcg heights
  have hf : VerticalFrontier g c final :=
    foldl_preserves sectionStep (VerticalFrontier g c) step _ _ hi
  exact ⟨final, hf, rfl, rfl, rfl, rfl⟩

theorem verticalPlan_cardRects_disjoint (g : Family) (c : TimelineConsts)
    (ht : 0 ≤ contentTop g c) (hl : 0 ≤ c.leftMargin) (hw : 0 ≤ cardWidth g c)
    (hp : 0 ≤ periodHeight g c) (hs : 0 ≤ sectionHeight g c)
    (hsg : 0 ≤ c.sectionGap) (heg : 0 ≤ c.eventGap) (hcg : 0 ≤ c.columnGap)
    (heights : ∀ (i : Nat), ∀ event ∈ ((g.periods[i]?).map (·.events)).getD [],
      0 ≤ eventHeight c event) :
    (cardRects g (verticalPlan g c)).Pairwise Disjoint := by
  obtain ⟨st, hst, hsections, hperiods, hevents, _hroutes⟩ :=
    verticalPlan_frontier g c ht hl hw hp hs hsg heg hcg heights
  have hcards : (verticalPlan g c).sections ++
      ((verticalPlan g c).periods ++ (verticalPlan g c).events.flatten) =
      verticalStateRects st := by
    rw [hsections, hperiods, hevents]
    rfl
  unfold cardRects
  rw [List.append_assoc, List.append_assoc]
  rw [hcards]
  cases htitle : g.title with
  | none => simpa [htitle] using hst.disjoint
  | some title =>
    simp only [Option.isSome_some, ↓reduceIte, List.singleton_append]
    apply List.pairwise_cons.mpr
    refine ⟨?_, hst.disjoint⟩
    intro r hr
    have hy : (verticalPlan g c).title.y = 0 := by simp [verticalPlan, htitle]
    have hh : (verticalPlan g c).title.h = title.caption.h := by
      simp [verticalPlan, htitle]
    rcases hst.above_content r hr with hz | habove
    · subst r
      apply disjoint_symm
      apply disjoint_below
      simpa only [zeroRect, Int.zero_add] using (show (0 : Int) ≤ (verticalPlan g c).title.y from by omega)
    · apply disjoint_below
      have htop : contentTop g c = title.caption.h + c.eventGap := by
        simp [contentTop, htitle]
      omega

theorem verticalPlan_absolute_corridor (g : Family) (c : TimelineConsts)
    (hgap : 0 ≤ c.columnGap) :
    ∀ paths ∈ (verticalPlan g c).routes, ∀ points ∈ paths, ∀ point ∈ points,
      c.leftMargin + cardWidth g c ≤ point.x ∧
        point.x ≤ c.leftMargin + cardWidth g c + c.columnGap := by
  apply verticalPlan_arrays_invariant g c
    (fun _ _ routes => ∀ paths ∈ routes, ∀ points ∈ paths, ∀ point ∈ points,
      c.leftMargin + cardWidth g c ≤ point.x ∧
        point.x ≤ c.leftMargin + cardWidth g c + c.columnGap)
  · intro paths hp points hpoints
    have hempty : paths = [] := (List.mem_replicate.mp hp).2
    subst paths
    cases hpoints
  · intro indices st _hp _he hr _bounds initial
    have preserve (st : VerticalState) (i : Nat)
        (good : ∀ paths ∈ st.routes, ∀ points ∈ paths, ∀ point ∈ points,
          c.leftMargin + cardWidth g c ≤ point.x ∧
            point.x ≤ c.leftMargin + cardWidth g c + c.columnGap) :
        ∀ paths ∈ (verticalRow g c i st).routes, ∀ points ∈ paths, ∀ point ∈ points,
          c.leftMargin + cardWidth g c ≤ point.x ∧
            point.x ≤ c.leftMargin + cardWidth g c + c.columnGap := by
      intro paths hpaths
      change paths ∈ st.routes.set i _ at hpaths
      rcases List.mem_or_eq_of_mem_set hpaths with hold | hnew
      · exact good paths hold
      · by_cases hi : i < st.routes.length
        · have hlookup : (verticalRow g c i st).routes[i]? = some paths := by
            simp only [verticalRow, List.getElem?_set_self hi]
            exact congrArg some hnew.symm
          exact verticalRow_route_corridor g c i st hi hgap hlookup
        · have unchanged : st.routes.set i
              ((eventRects c (c.leftMargin + cardWidth g c + c.columnGap)
                (cardWidth g c) st.y (((g.periods[i]?).map (·.events)).getD [])).map
                (fun b => elbow
                  ⟨c.leftMargin + cardWidth g c, st.y + half (periodHeight g c)⟩
                  ⟨b.x, b.y + half b.h⟩
                  (c.leftMargin + cardWidth g c + half c.columnGap))) = st.routes := by
              exact set_outside _ _ _ (by omega)
          rw [unchanged] at hpaths
          exact good paths hpaths
    exact foldl_preserves (fun st i => verticalRow g c i st)
      (fun st => ∀ paths ∈ st.routes, ∀ points ∈ paths, ∀ point ∈ points,
        c.leftMargin + cardWidth g c ≤ point.x ∧
          point.x ≤ c.leftMargin + cardWidth g c + c.columnGap)
      preserve indices st initial

theorem verticalPlan_route_card_corridor (g : Family) (c : TimelineConsts)
    (ht : 0 ≤ contentTop g c) (hl : 0 ≤ c.leftMargin) (hw : 0 ≤ cardWidth g c)
    (hp : 0 ≤ periodHeight g c) (hs : 0 ≤ sectionHeight g c)
    (hsg : 0 ≤ c.sectionGap) (heg : 0 ≤ c.eventGap) (hcg : 0 ≤ c.columnGap)
    (heights : ∀ (i : Nat), ∀ event ∈ ((g.periods[i]?).map (·.events)).getD [],
      0 ≤ eventHeight c event)
    {paths : List (List Point)} {points : List Point} {a b : Point} {r : Rect}
    (hpaths : paths ∈ (verticalPlan g c).routes) (hpoints : points ∈ paths)
    (ha : a ∈ points) (hb : b ∈ points)
    (hrect : r ∈ (verticalPlan g c).sections ++
      ((verticalPlan g c).periods ++ (verticalPlan g c).events.flatten)) :
    (r.x + r.w ≤ a.x ∧ r.x + r.w ≤ b.x) ∨
      (a.x ≤ r.x ∧ b.x ≤ r.x) := by
  obtain ⟨st, hst, hsections, hperiods, hevents, _hroutes⟩ :=
    verticalPlan_frontier g c ht hl hw hp hs hsg heg hcg heights
  rw [hsections, hperiods, hevents] at hrect
  have has := verticalPlan_absolute_corridor g c hcg paths hpaths points hpoints a ha
  have hbs := verticalPlan_absolute_corridor g c hcg paths hpaths points hpoints b hb
  rcases hst.corridor_sides r hrect with hleft | hright
  · exact Or.inl ⟨Int.le_trans hleft has.1, Int.le_trans hleft hbs.1⟩
  · exact Or.inr ⟨Int.le_trans has.2 hright, Int.le_trans hbs.2 hright⟩

theorem verticalRow_indexed_ports (g : Family) (c : TimelineConsts) (i : Nat)
    (st : VerticalState) (hip : i < st.periods.length) (hie : i < st.events.length)
    (hir : i < st.routes.length)
    (hw : 0 ≤ cardWidth g c) (hh : 0 ≤ periodHeight g c)
    (heights : ∀ event ∈ ((g.periods[i]?).map (·.events)).getD [],
      0 ≤ eventHeight c event)
    {period target : Rect} {events : List Rect} {paths : List (List Point)}
    {points : List Point} {j : Nat}
    (hperiod : (verticalRow g c i st).periods[i]? = some period)
    (hevents : (verticalRow g c i st).events[i]? = some events)
    (hpaths : (verticalRow g c i st).routes[i]? = some paths)
    (htarget : events[j]? = some target) (hpoints : paths[j]? = some points) :
    ∃ first last, points.head? = some first ∧ points.getLast? = some last ∧
      Validator.onBoundary first period ∧ Validator.onBoundary last target := by
  obtain ⟨hp, he⟩ := verticalRow_box_lookup g c i st hip hie
  have peq := Option.some.inj (hp.symm.trans hperiod)
  have eeq := Option.some.inj (he.symm.trans hevents)
  subst period
  subst events
  simp only [verticalRow, List.getElem?_set_self hir, Option.some.injEq] at hpaths
  subst paths
  simp only [List.getElem?_map, htarget, Option.map_some, Option.some.injEq] at hpoints
  subst points
  obtain ⟨hf, hl⟩ := elbow_ports
    (⟨c.leftMargin + cardWidth g c, st.y + half (periodHeight g c)⟩ : Point)
    ⟨target.x, target.y + half target.h⟩
    (c.leftMargin + cardWidth g c + half c.columnGap)
  refine ⟨_, _, hf, hl, right_midpoint_boundary _ hw hh, ?_⟩
  have target_sizes : ∀ (es : List Lanes.Timeline.Event) (top : Int),
      (∀ e ∈ es, 0 ≤ eventHeight c e) →
      ∀ r ∈ eventRects c (c.leftMargin + cardWidth g c + c.columnGap)
        (cardWidth g c) top es, r.w = cardWidth g c ∧ 0 ≤ r.h := by
    intro es
    induction es with
    | nil => intro top _ r hr; cases hr
    | cons e es ih =>
      intro top h r hr
      rcases List.mem_cons.mp hr with hr | hr
      · subst r
        exact ⟨rfl, h e (List.mem_cons_self ..)⟩
      · exact ih _ (fun e he => h e (List.mem_cons_of_mem _ he)) r hr
  obtain ⟨hwidth, hheight⟩ := target_sizes _ st.y heights target
    (List.mem_of_getElem? htarget)
  exact left_midpoint_boundary target (hwidth.symm ▸ hw) hheight

theorem verticalPlan_indexed_ports (g : Family) (c : TimelineConsts)
    (hw : 0 ≤ cardWidth g c) (hh : 0 ≤ periodHeight g c)
    (heights : ∀ (i : Nat), ∀ event ∈ ((g.periods[i]?).map (·.events)).getD [],
      0 ≤ eventHeight c event) :
    ∀ (i j : Nat) (period target : Rect) (events : List Rect)
      (paths : List (List Point)) (points : List Point),
      (verticalPlan g c).periods[i]? = some period →
      (verticalPlan g c).events[i]? = some events →
      (verticalPlan g c).routes[i]? = some paths →
      events[j]? = some target → paths[j]? = some points →
      ∃ first last, points.head? = some first ∧ points.getLast? = some last ∧
        Validator.onBoundary first period ∧ Validator.onBoundary last target := by
  apply verticalPlan_arrays_invariant g c
    (fun periods events routes =>
      ∀ (i j : Nat) (period target : Rect) (es : List Rect)
        (paths : List (List Point)) (points : List Point),
        periods[i]? = some period → events[i]? = some es → routes[i]? = some paths →
        es[j]? = some target → paths[j]? = some points →
        ∃ first last, points.head? = some first ∧ points.getLast? = some last ∧
          Validator.onBoundary first period ∧ Validator.onBoundary last target)
  · intro i j period target events paths points _hp _he hr _ht hpoints
    have hempty : paths = [] := (List.mem_replicate.mp (List.mem_of_getElem? hr)).2
    subst paths
    simp at hpoints
  · intro indices st hp he hr bounds initial
    induction indices generalizing st with
    | nil => exact initial
    | cons index rest ih =>
      obtain ⟨hpl, hel, hrl⟩ := verticalRow_lengths g c index st
      apply ih (verticalRow g c index st) (hpl.trans hp) (hel.trans he) (hrl.trans hr)
      · intro i hi
        exact bounds i (List.mem_cons_of_mem _ hi)
      · intro i j period target events paths points hperiod hevents hpaths htarget hpoints
        by_cases same : i = index
        · subst i
          have hb := bounds index (List.mem_cons_self ..)
          exact verticalRow_indexed_ports g c index st
            (hp.symm ▸ hb) (he.symm ▸ hb) (hr.symm ▸ hb)
            hw hh (heights index) hperiod hevents hpaths htarget hpoints
        · simp only [verticalRow, List.getElem?_set_ne (Ne.symm same)] at hperiod hevents hpaths
          exact initial i j period target events paths points
            hperiod hevents hpaths htarget hpoints

theorem verticalPlan_indexed_shifted_ports (g : Family) (c : TimelineConsts)
    (dx dy : Int) (hw : 0 ≤ cardWidth g c) (hh : 0 ≤ periodHeight g c)
    (heights : ∀ (i : Nat), ∀ event ∈ ((g.periods[i]?).map (·.events)).getD [],
      0 ≤ eventHeight c event)
    (i j : Nat) (period target : Rect) (events : List Rect)
    (paths : List (List Point)) (points : List Point)
    (hp : (verticalPlan g c).periods[i]? = some period)
    (he : (verticalPlan g c).events[i]? = some events)
    (hr : (verticalPlan g c).routes[i]? = some paths)
    (ht : events[j]? = some target) (hpoints : paths[j]? = some points) :
    ∃ first last, (points.map (shiftPoint dx dy)).head? = some first ∧
      (points.map (shiftPoint dx dy)).getLast? = some last ∧
      Validator.onBoundary first (shiftRect dx dy period) ∧
      Validator.onBoundary last (shiftRect dx dy target) := by
  obtain ⟨first, last, hf, hl, hs, ht⟩ :=
    verticalPlan_indexed_ports g c hw hh heights i j period target events paths points
      hp he hr ht hpoints
  exact route_ports_shift dx dy points period target first last hf hl hs ht

theorem verticalPlan_shifted_route_card_segMisses (g : Family) (c : TimelineConsts)
    (dx dy : Int)
    (ht : 0 ≤ contentTop g c) (hl : 0 ≤ c.leftMargin) (hw : 0 ≤ cardWidth g c)
    (hp : 0 ≤ periodHeight g c) (hs : 0 ≤ sectionHeight g c)
    (hsg : 0 ≤ c.sectionGap) (heg : 0 ≤ c.eventGap) (hcg : 0 ≤ c.columnGap)
    (heights : ∀ (i : Nat), ∀ event ∈ ((g.periods[i]?).map (·.events)).getD [],
      0 ≤ eventHeight c event)
    {paths : List (List Point)} {points : List Point} {a b : Point} {r : Rect}
    (hpaths : paths ∈ ((verticalPlan g c).shift dx dy).routes)
    (hpoints : points ∈ paths) (ha : a ∈ points) (hb : b ∈ points)
    (hrect : r ∈ ((verticalPlan g c).shift dx dy).sections ++
      (((verticalPlan g c).shift dx dy).periods ++
        ((verticalPlan g c).shift dx dy).events.flatten)) :
    Polyline.segMisses a b r := by
  change paths ∈ (verticalPlan g c).routes.map
    (fun paths => paths.map (fun points => points.map (shiftPoint dx dy))) at hpaths
  obtain ⟨rawPaths, hrawPaths, hpaths⟩ := List.mem_map.mp hpaths
  subst paths
  obtain ⟨rawPoints, hrawPoints, hpoints⟩ := List.mem_map.mp hpoints
  subst points
  obtain ⟨rawA, hrawA, ha⟩ := List.mem_map.mp ha
  obtain ⟨rawB, hrawB, hb⟩ := List.mem_map.mp hb
  subst a
  subst b
  have hrects :
      ((verticalPlan g c).shift dx dy).sections ++
        (((verticalPlan g c).shift dx dy).periods ++
          ((verticalPlan g c).shift dx dy).events.flatten) =
      ((verticalPlan g c).sections ++
        ((verticalPlan g c).periods ++ (verticalPlan g c).events.flatten)).map
          (shiftRect dx dy) := by
    simp only [Plan.shift, List.map_append, List.map_flatten]
  rw [hrects] at hrect
  obtain ⟨rawRect, hrawRect, hrect⟩ := List.mem_map.mp hrect
  subst r
  have hsep := verticalPlan_route_card_corridor g c ht hl hw hp hs hsg heg hcg heights
    hrawPaths hrawPoints hrawA hrawB hrawRect
  rcases hsep with hleft | hright
  · apply Or.inr
    apply Or.inl
    dsimp only [shiftPoint, shiftRect]
    omega
  · apply Or.inl
    dsimp only [shiftPoint, shiftRect]
    omega

theorem layout_vertical_route_card_segMisses
    {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result)
    {g : Family} {r : Lanes.Timeline.Result}
    (hg : decode m = .ok g) (hr : Lanes.Timeline.layout g m.profile = .ok r)
    (hv : horizontal g = false)
    {out : Route} (hout : out ∈ result.scene.layoutDump.routes)
    {a b : Point} (ha : a ∈ out.points) (hb : b ∈ out.points)
    {rect : Rect}
    (hrect : rect ∈ r.geometry.sections ++
      (r.geometry.periods ++ r.geometry.events.flatten)) :
    Polyline.segMisses a b rect := by
  obtain ⟨g', r', period, paths, event, i, j, source, target,
    hg', hr', _hperiod, hpaths, _hevent, hpoints, _hto,
    _hsource, _htarget, _hsourceRect, _htargetRect⟩ :=
    layout_route_indexed_endpoint_rects hwf h hout
  have hgg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have hrr : r' = r := Except.ok.inj (hr'.symm.trans hr)
  subst r'
  have hsizes := (decode_facts hg).1
  obtain ⟨hw, hp, hs, heights, hsg, heg, hcg⟩ := native_sizes hr hsizes
  let c := TimelineConsts.load m.profile
  have hl : 0 ≤ c.leftMargin := by
    change 0 ≤ (TimelineConsts.load m.profile).leftMargin
    cases m.profile <;> decide
  have ht : 0 ≤ contentTop g c := by
    cases htitle : g.title with
    | none => simp only [contentTop, htitle, Option.map_none, Option.getD_none]; omega
    | some title =>
      have hheight := (hsizes.title title htitle).1
      have hgap : 0 ≤ c.eventGap := heg
      simp only [contentTop, htitle, Option.map_some, Option.getD_some]
      omega
  have he : ∀ (index : Nat),
      ∀ event ∈ ((g.periods[index]?).map (·.events)).getD [],
        0 ≤ eventHeight c event := by
    intro index event hm
    cases hperiod : g.periods[index]? with
    | none => simp only [hperiod, Option.map_none, Option.getD_none] at hm; cases hm
    | some period =>
      simp only [hperiod, Option.map_some, Option.getD_some] at hm
      exact heights period (List.mem_of_getElem? hperiod) event hm
  have hgeometry := (native_layout_geometry hr).1
  simp only [plan, hv, Bool.false_eq_true, ↓reduceIte] at hgeometry
  have hpathMem := List.mem_of_getElem? hpaths
  have hpointMem := List.mem_of_getElem? hpoints
  rw [hgeometry] at hpathMem hrect
  exact verticalPlan_shifted_route_card_segMisses g c _ _
    ht hl (Int.le_of_lt hw) hp hs hsg heg hcg he
    hpathMem hpointMem ha hb hrect

private theorem elbow_y_lower (a b : Point) (x floor : Int)
    (ha : floor ≤ a.y) (hb : floor ≤ b.y) :
    ∀ point ∈ elbow a b x, floor ≤ point.y := by
  intro point hm
  unfold elbow at hm
  split at hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> assumption
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> assumption

theorem verticalPlan_routes_above_content (g : Family) (c : TimelineConsts)
    (ht : 0 ≤ contentTop g c) (hl : 0 ≤ c.leftMargin) (hw : 0 ≤ cardWidth g c)
    (hp : 0 ≤ periodHeight g c) (hs : 0 ≤ sectionHeight g c)
    (hsg : 0 ≤ c.sectionGap) (heg : 0 ≤ c.eventGap) (hcg : 0 ≤ c.columnGap)
    (heights : ∀ (i : Nat), ∀ event ∈ ((g.periods[i]?).map (·.events)).getD [],
      0 ≤ eventHeight c event) :
    ∀ paths ∈ (verticalPlan g c).routes, ∀ points ∈ paths, ∀ point ∈ points,
      contentTop g c ≤ point.y := by
  let Above := fun st : VerticalState =>
    ∀ paths ∈ st.routes, ∀ points ∈ paths, ∀ point ∈ points,
      contentTop g c ≤ point.y
  let Good := fun st : VerticalState => VerticalFrontier g c st ∧ Above st
  have row (st : VerticalState) (i : Nat) (h : Good st) :
      Good (verticalRow g c i st) := by
    refine ⟨verticalRow_frontier g c i st h.1 hl hw hp hsg heg hcg (heights i), ?_⟩
    intro paths hpaths points hpoints point hm
    change paths ∈ st.routes.set i _ at hpaths
    rcases List.mem_or_eq_of_mem_set hpaths with hold | hnew
    · exact h.2 paths hold points hpoints point hm
    · subst paths
      obtain ⟨target, htarget, heq⟩ := List.mem_map.mp hpoints
      subst points
      have hlo := eventRects_lower c
        (c.leftMargin + cardWidth g c + c.columnGap) (cardWidth g c)
        st.y _ heg (heights i) target htarget
      have hsize := eventRects_sizes c
        (c.leftMargin + cardWidth g c + c.columnGap) (cardWidth g c)
        st.y _ (by omega) hw h.1.nonnegative heg (heights i) target htarget
      have hph : 0 ≤ half (periodHeight g c) :=
        Int.fdiv_nonneg hp (by decide)
      have heh : 0 ≤ half target.h :=
        Int.fdiv_nonneg hsize.2.2.2 (by decide)
      apply elbow_y_lower _ _ _ _ ?_ ?_ point hm
      · have htop := h.1.content_top
        dsimp only
        omega
      · have htop := h.1.content_top
        dsimp only
        omega
  have rows (indices : List Nat) (st : VerticalState) :
      Good st → Good (indices.foldl (fun st i => verticalRow g c i st) st) :=
    foldl_preserves _ Good row indices st
  have initial : Good (verticalInitialState g c) := by
    refine ⟨verticalInitial_frontier g c ht hl hw, ?_⟩
    intro paths hpaths points hpoints
    have heq : paths = [] := (List.mem_replicate.mp hpaths).2
    subst paths
    cases hpoints
  have sectionStep (st : VerticalState) (s : Nat) (h : Good st) :
      Good (verticalSectionState g c st s) :=
    ⟨verticalSection_frontier g c st s h.1 hl hw hs hsg, h.2⟩
  have step (st : VerticalState) (s : Nat) (h : Good st) :
      Good ((members g (s : Int)).foldl (fun st i => verticalRow g c i st)
        (verticalSectionState g c st s)) :=
    rows _ _ (sectionStep st s h)
  have final := foldl_preserves _ Good step (List.range g.sections.length)
    ((members g (-1)).foldl (fun st i => verticalRow g c i st)
      (verticalInitialState g c)) (rows _ _ initial)
  exact final.2

theorem verticalPlan_shifted_route_title_segMisses (g : Family) (c : TimelineConsts)
    (dx dy : Int)
    (ht : 0 ≤ contentTop g c) (hl : 0 ≤ c.leftMargin) (hw : 0 ≤ cardWidth g c)
    (hp : 0 ≤ periodHeight g c) (hs : 0 ≤ sectionHeight g c)
    (hsg : 0 ≤ c.sectionGap) (heg : 0 ≤ c.eventGap) (hcg : 0 ≤ c.columnGap)
    (heights : ∀ (i : Nat), ∀ event ∈ ((g.periods[i]?).map (·.events)).getD [],
      0 ≤ eventHeight c event)
    (title : Lanes.Timeline.Card) (htitle : g.title = some title)
    {paths : List (List Point)} {points : List Point} {a b : Point}
    (hpaths : paths ∈ ((verticalPlan g c).shift dx dy).routes)
    (hpoints : points ∈ paths) (ha : a ∈ points) (hb : b ∈ points) :
    Polyline.segMisses a b ((verticalPlan g c).shift dx dy).title := by
  change paths ∈ (verticalPlan g c).routes.map
    (fun paths => paths.map (fun points => points.map (shiftPoint dx dy))) at hpaths
  obtain ⟨rawPaths, hrawPaths, hpaths⟩ := List.mem_map.mp hpaths
  subst paths
  obtain ⟨rawPoints, hrawPoints, hpoints⟩ := List.mem_map.mp hpoints
  subst points
  obtain ⟨rawA, hrawA, ha⟩ := List.mem_map.mp ha
  obtain ⟨rawB, hrawB, hb⟩ := List.mem_map.mp hb
  subst a
  subst b
  have hfloor := verticalPlan_routes_above_content g c ht hl hw hp hs hsg heg hcg heights
    rawPaths hrawPaths rawPoints hrawPoints
  have ha := hfloor rawA hrawA
  have hb := hfloor rawB hrawB
  have htop : contentTop g c = title.caption.h + c.eventGap := by
    simp only [contentTop, htitle, Option.map_some, Option.getD_some]
  have hy : (verticalPlan g c).title.y = 0 := by simp [verticalPlan, htitle]
  have hh : (verticalPlan g c).title.h = title.caption.h := by
    simp [verticalPlan, htitle]
  apply Or.inr
  apply Or.inr
  apply Or.inr
  apply Or.inl
  change min (rawA.y + dy) (rawB.y + dy) ≥
    (verticalPlan g c).title.y + dy + (verticalPlan g c).title.h
  omega

theorem layout_vertical_clearance {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result)
    {g : Family} (hg : decode m = .ok g) (hv : horizontal g = false) :
    Validator.C6 result.scene.layoutDump := by
  intro out hout box hbox _hexclusive _hscope
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  have hbox' := hbox
  rw [hdump] at hbox'
  obtain ⟨g', r, modelBox, hg', hr, _hmodelBox, _hcorr, hsource⟩ :=
    scene_box_source hs hbox'
  have hgg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have hcards := rectSource_mem hsource
  have segment : ∀ a ∈ out.points, ∀ b ∈ out.points,
      Polyline.segMisses a b box.rect := by
    intro a ha b hb
    have hcards' := hcards
    unfold cardRects at hcards'
    rw [List.append_assoc, List.append_assoc] at hcards'
    rcases List.mem_append.mp hcards' with htitle | hcard
    · cases ht : g.title with
      | none => simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at htitle
                cases htitle
      | some title =>
        have heq : box.rect = r.geometry.title := by
          simpa only [ht, Option.isSome_some, ↓reduceIte, List.mem_singleton] using htitle
        rw [heq]
        obtain ⟨g', r', period, paths, event, i, j, source, target,
          hg', hr', _hp, hpaths, _he, hpoints, _hto,
          _hs, _ht, _hsr, _htr⟩ := layout_route_indexed_endpoint_rects hwf h hout
        have hgg : g' = g := Except.ok.inj (hg'.symm.trans hg)
        subst g'
        have hrr : r' = r := Except.ok.inj (hr'.symm.trans hr)
        subst r'
        have hsizes := (decode_facts hg).1
        obtain ⟨hw, hp, hs, heights, hsg, heg, hcg⟩ := native_sizes hr hsizes
        let c := TimelineConsts.load m.profile
        have hl : 0 ≤ c.leftMargin := by
          change 0 ≤ (TimelineConsts.load m.profile).leftMargin
          cases m.profile <;> decide
        have htop : 0 ≤ contentTop g c := by
          have hheight := (hsizes.title title ht).1
          have hgap : 0 ≤ c.eventGap := heg
          simp only [contentTop, ht, Option.map_some, Option.getD_some]
          omega
        have heights' : ∀ (index : Nat),
            ∀ event ∈ ((g.periods[index]?).map (·.events)).getD [],
              0 ≤ eventHeight c event := by
          intro index event hm
          cases hp : g.periods[index]? with
          | none => simp only [hp, Option.map_none, Option.getD_none] at hm; cases hm
          | some period =>
            simp only [hp, Option.map_some, Option.getD_some] at hm
            exact heights period (List.mem_of_getElem? hp) event hm
        have hgeometry := (native_layout_geometry hr).1
        simp only [plan, hv, Bool.false_eq_true, ↓reduceIte] at hgeometry
        have hpathMem := List.mem_of_getElem? hpaths
        have hpointMem := List.mem_of_getElem? hpoints
        rw [hgeometry] at hpathMem ⊢
        exact verticalPlan_shifted_route_title_segMisses g c _ _
          htop hl (Int.le_of_lt hw) hp hs hsg heg hcg heights' title ht
          hpathMem hpointMem ha hb
    · exact layout_vertical_route_card_segMisses hwf h hg hr hv hout ha hb hcard
  have all_clear : ∀ points : List Point, (∀ p ∈ points, p ∈ out.points) →
      Polyline.allSegsMiss points box.rect := by
    intro points
    induction points with
    | nil => intro _; trivial
    | cons first rest ih =>
      intro hm
      cases rest with
      | nil => trivial
      | cons second tail =>
        exact ⟨segment first (hm first (List.mem_cons_self ..))
          second (hm second (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
          ih (fun p hp => hm p (List.mem_cons_of_mem _ hp))⟩
  intro hhit
  exact hhit.2.2 (all_clear out.points (fun _ hp => hp))

theorem verticalPlan_index_lengths (g : Family) (c : TimelineConsts) :
    (verticalPlan g c).periods.length = (verticalPlan g c).routes.length ∧
      (verticalPlan g c).events.map List.length =
        (verticalPlan g c).routes.map List.length := by
  apply verticalPlan_arrays_invariant g c
    (fun periods events routes =>
      periods.length = routes.length ∧ events.map List.length = routes.map List.length)
  · simp
  · intro indices st _hp _he _hr _bounds initial
    have step (st : VerticalState) (i : Nat)
        (h : st.periods.length = st.routes.length ∧
          st.events.map List.length = st.routes.map List.length) :
        (verticalRow g c i st).periods.length = (verticalRow g c i st).routes.length ∧
          (verticalRow g c i st).events.map List.length =
            (verticalRow g c i st).routes.map List.length := by
      constructor
      · simpa only [verticalRow, List.length_set] using h.1
      · simpa only [verticalRow, List.map_set, List.length_map] using
          congrArg (fun lengths => lengths.set i
            (eventRects c (c.leftMargin + cardWidth g c + c.columnGap)
              (cardWidth g c) st.y (((g.periods[i]?).map (·.events)).getD [])).length) h.2
    exact foldl_preserves (fun st i => verticalRow g c i st)
      (fun st => st.periods.length = st.routes.length ∧
        st.events.map List.length = st.routes.map List.length)
      step indices st initial

theorem verticalPlan_indexed_rects (g : Family) (c : TimelineConsts)
    {i j : Nat} {paths : List (List Point)} {points : List Point}
    (hr : (verticalPlan g c).routes[i]? = some paths) (hp : paths[j]? = some points) :
    ∃ period events target,
      (verticalPlan g c).periods[i]? = some period ∧
      (verticalPlan g c).events[i]? = some events ∧
      events[j]? = some target := by
  obtain ⟨hpl, hel⟩ := verticalPlan_index_lengths g c
  have index_lt {α : Type} (xs : List α) (index : Nat) (x : α)
      (hx : xs[index]? = some x) : index < xs.length := by
    by_cases hi : index < xs.length
    · exact hi
    · have he : xs[index]? = none := List.getElem?_eq_none (by omega)
      rw [he] at hx
      cases hx
  have hi := index_lt _ _ _ hr
  have hperiod : i < (verticalPlan g c).periods.length := by omega
  have hevents : i < (verticalPlan g c).events.length := by
    have := congrArg List.length hel
    simp only [List.length_map] at this
    omega
  let period := (verticalPlan g c).periods[i]
  let events := (verticalPlan g c).events[i]
  have heq : events.length = paths.length := by
    have he := congrArg (fun lengths => lengths[i]?) hel
    simp only [List.getElem?_map, List.getElem?_eq_getElem hevents, hr,
      Option.map_some, Option.some.injEq] at he
    exact he
  have hj : j < events.length := by
    have := index_lt _ _ _ hp
    omega
  exact ⟨period, events, events[j], List.getElem?_eq_getElem hperiod,
    List.getElem?_eq_getElem hevents, List.getElem?_eq_getElem hj⟩

theorem layout_vertical_ports {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result)
    {g : Family} (hg : decode m = .ok g) (hv : horizontal g = false) :
    Validator.C5 result.scene.layoutDump := by
  intro out hout
  obtain ⟨g', r, period, paths, event, before, after, i, j,
    hg', hr, hperiod, hpaths, hevent, hpoints, _hsplit, hto, hfrom⟩ :=
    layout_route_event_indices hwf h hout
  have hgg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have hdir : (m.options.direction == .LR) = false := by
    simpa only [horizontal, decode_direction_horizontal hg] using hv
  simp only [hdir, Bool.false_eq_true, ↓reduceIte] at hfrom
  obtain ⟨g', r', _period, _paths, _event, _i, _j, source, target,
    hg', hr', _hp, _hpaths, _he, _hpoints, _hto,
    hsource, htarget, hsourceRect, htargetRect⟩ :=
    layout_route_indexed_endpoint_rects hwf h hout
  have hgg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have hrr : r' = r := Except.ok.inj (hr'.symm.trans hr)
  subst r'
  let c := TimelineConsts.load m.profile
  let raw := verticalPlan g c
  let ext := raw.extent g m.profile
  let dx := c.canvasMargin - ext.x
  let dy := c.canvasMargin - ext.y
  have hgeometry : r.geometry = raw.shift dx dy := by
    have hh := (native_layout_geometry hr).1
    simpa only [plan, hv, Bool.false_eq_true, ↓reduceIte] using hh
  have hrawPaths : ∃ rawPaths,
      raw.routes[i]? = some rawPaths ∧
        paths = rawPaths.map (fun points => points.map (shiftPoint dx dy)) := by
    rw [hgeometry] at hpaths
    change (raw.routes.map
      (fun paths => paths.map (fun points => points.map (shiftPoint dx dy))))[i]? =
        some paths at hpaths
    rw [List.getElem?_map] at hpaths
    cases hlookup : raw.routes[i]? with
    | none => simp only [hlookup, Option.map_none] at hpaths; cases hpaths
    | some rawPaths =>
      simp only [hlookup, Option.map_some, Option.some.injEq] at hpaths
      exact ⟨rawPaths, rfl, hpaths.symm⟩
  obtain ⟨rawPaths, hrawPaths, hpathEq⟩ := hrawPaths
  subst paths
  have hrawPoints : ∃ rawPoints,
      rawPaths[j]? = some rawPoints ∧ out.points = rawPoints.map (shiftPoint dx dy) := by
    rw [List.getElem?_map] at hpoints
    cases hlookup : rawPaths[j]? with
    | none => simp only [hlookup, Option.map_none] at hpoints; cases hpoints
    | some rawPoints =>
      simp only [hlookup, Option.map_some, Option.some.injEq] at hpoints
      exact ⟨rawPoints, rfl, hpoints.symm⟩
  obtain ⟨rawPoints, hrawPoints, hpointEq⟩ := hrawPoints
  obtain ⟨rawPeriod, rawEvents, rawTarget, hrawPeriod, hrawEvents, hrawTarget⟩ :=
    verticalPlan_indexed_rects g c hrawPaths hrawPoints
  have hshiftPeriod :
      r.geometry.periods[i]? = some (shiftRect dx dy rawPeriod) := by
    rw [hgeometry]
    change ((verticalPlan g c).periods.map (shiftRect dx dy))[i]? = _
    simp only [List.getElem?_map, hrawPeriod, Option.map_some]
  have hshiftEvents :
      r.geometry.events[i]? = some (rawEvents.map (shiftRect dx dy)) := by
    rw [hgeometry]
    change ((verticalPlan g c).events.map (fun events => events.map (shiftRect dx dy)))[i]? = _
    simp only [List.getElem?_map, hrawEvents, Option.map_some]
  have hshiftTarget :
      (rawEvents.map (shiftRect dx dy))[j]? = some (shiftRect dx dy rawTarget) := by
    simp only [List.getElem?_map, hrawTarget, Option.map_some]
  have zip_some {α β : Type} (xs : List α) (ys : List β) (index : Nat)
      (x : α) (y : β) (hx : xs[index]? = some x) (hy : ys[index]? = some y) :
      (xs.zip ys)[index]? = some (x, y) := by
    induction xs generalizing ys index with
    | nil => simp only [List.getElem?_nil] at hx; cases hx
    | cons first rest ih =>
      cases ys with
      | nil => simp only [List.getElem?_nil] at hy; cases hy
      | cons second tail =>
        cases index with
        | zero =>
          change some first = some x at hx
          change some second = some y at hy
          have hfirst := Option.some.inj hx
          have hsecond := Option.some.inj hy
          subst x
          subst y
          rfl
        | succ index =>
          change rest[index]? = some x at hx
          change tail[index]? = some y at hy
          exact ih tail index hx hy
  have hsourceProvenance :
      RectSource g r.geometry out.fromId (shiftRect dx dy rawPeriod) :=
    Or.inr (Or.inr (Or.inl ⟨i, period, hperiod, hfrom.symm, hshiftPeriod⟩))
  have htargetProvenance :
      RectSource g r.geometry out.toId (shiftRect dx dy rawTarget) :=
    Or.inr (Or.inr (Or.inr
      ⟨period, rawEvents.map (shiftRect dx dy), event,
        List.mem_iff_getElem?.mpr ⟨i, zip_some _ _ _ _ _ hperiod hshiftEvents⟩,
        List.mem_iff_getElem?.mpr ⟨j, zip_some _ _ _ _ _ hevent hshiftTarget⟩,
        hto.symm⟩))
  have hsourceEq : source.rect = shiftRect dx dy rawPeriod :=
    rectSource_unique hwf hg (rectFor_source hsourceRect) hsourceProvenance
  have htargetEq : target.rect = shiftRect dx dy rawTarget :=
    rectSource_unique hwf hg (rectFor_source htargetRect) htargetProvenance
  have hsizes := (decode_facts hg).1
  obtain ⟨hw, hp, _hs, heights, _hsg, _heg, _hcg⟩ := native_sizes hr hsizes
  have heights' : ∀ (index : Nat),
      ∀ event ∈ ((g.periods[index]?).map (·.events)).getD [],
        0 ≤ eventHeight c event := by
    intro index event hm
    cases hp : g.periods[index]? with
    | none => simp only [hp, Option.map_none, Option.getD_none] at hm; cases hm
    | some period =>
      simp only [hp, Option.map_some, Option.getD_some] at hm
      exact heights period (List.mem_of_getElem? hp) event hm
  obtain ⟨first, last, hfirst, hlast, hfirstBoundary, hlastBoundary⟩ :=
    verticalPlan_indexed_shifted_ports g c dx dy (Int.le_of_lt hw) hp heights'
      i j rawPeriod rawTarget rawEvents rawPaths rawPoints
      hrawPeriod hrawEvents hrawPaths hrawTarget hrawPoints
  refine ⟨first, last, source, target, ?_, ?_, hsource, htarget, ?_, ?_⟩
  · simpa only [hpointEq] using hfirst
  · simpa only [hpointEq] using hlast
  · simpa only [hsourceEq] using hfirstBoundary
  · simpa only [htargetEq] using hlastBoundary

theorem layout_vertical_box_clearance {m : Model} {result : Layered.FamilyResult}
    (_hwf : WellFormed m) (h : layout m = .ok result)
    {g : Family} (hg : decode m = .ok g) (hv : horizontal g = false) :
    Validator.C2 result.scene.layoutDump ∧ Validator.C8a result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  obtain ⟨g', r, hg', hr, _hc, _hl, _hboxes, _hroutes⟩ := scene_execution hs
  have hgg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have hsizes := (decode_facts hg).1
  obtain ⟨hw, hp, hsection, heights, hsg, heg, hcg⟩ := native_sizes hr hsizes
  let c := TimelineConsts.load m.profile
  have hl : 0 ≤ c.leftMargin := by
    change 0 ≤ (TimelineConsts.load m.profile).leftMargin
    cases m.profile <;> decide
  have ht : 0 ≤ contentTop g c := by
    cases htitle : g.title with
    | none => simp only [contentTop, htitle, Option.map_none, Option.getD_none]; omega
    | some title =>
      have hh := (hsizes.title title htitle).1
      have hgap : 0 ≤ c.eventGap := heg
      simp only [contentTop, htitle, Option.map_some, Option.getD_some]
      omega
  have heights' : ∀ (index : Nat),
      ∀ event ∈ ((g.periods[index]?).map (·.events)).getD [],
        0 ≤ eventHeight c event := by
    intro index event hm
    cases hp : g.periods[index]? with
    | none => simp only [hp, Option.map_none, Option.getD_none] at hm; cases hm
    | some period =>
      simp only [hp, Option.map_some, Option.getD_some] at hm
      exact heights period (List.mem_of_getElem? hp) event hm
  have hraw := verticalPlan_cardRects_disjoint g c ht hl (Int.le_of_lt hw)
    hp hsection hsg heg hcg heights'
  have hnative : (cardRects g r.geometry).Pairwise Disjoint := by
    apply native_cardRects_disjoint hr
    simpa only [plan, hv, Bool.false_eq_true, ↓reduceIte] using hraw
  have all_boxes : ∀ left ∈ result.scene.layoutDump.boxes,
      ∀ right ∈ result.scene.layoutDump.boxes,
        left.id ≠ right.id → Disjoint left.rect right.rect := by
    intro left hleft right hright hne
    rw [hdump] at hleft hright
    obtain ⟨gl, rl, _bl, hgl, hrl, _hbl, _hcl, hsl⟩ := scene_box_source hs hleft
    obtain ⟨gr, rr, _br, hgr, hrr, _hbr, _hcr, hsr⟩ := scene_box_source hs hright
    have hel : gl = g := Except.ok.inj (hgl.symm.trans hg)
    subst gl
    have her : gr = g := Except.ok.inj (hgr.symm.trans hg)
    subst gr
    have hrel : rl = r := Except.ok.inj (hrl.symm.trans hr)
    subst rl
    have hrer : rr = r := Except.ok.inj (hrr.symm.trans hr)
    subst rr
    exact named_disjoint (hnative.sublist (namedRects_sublist g r.geometry))
      (rectSource_named hsl) (rectSource_named hsr) hne
  constructor
  · intro left hleft right hright hne _hexclusiveL _hexclusiveR _hparent
    exact all_boxes left hleft right hright hne
  · intro frame hframe _hrole box hbox hne _hancestor _hdescendant
    exact all_boxes frame hframe box hbox (Ne.symm hne)

end Elegant.Kinds.Timeline

import Elegant.Kinds.Timeline
import Elegant.TimelineValidity
import Elegant.LanesFacts
import Elegant.LanesConsts

set_option autoImplicit false

namespace Elegant.Kinds.Timeline

open Lanes Lanes.Timeline

/-! ### Rectangle disjointness helpers -/

theorem Disjoint.symm' {a b : Rect} (h : Disjoint a b) : Disjoint b a := by
  unfold Disjoint at h ⊢
  intro hb
  exact h ((Rect.meetsInterior_comm a b).mpr hb)

theorem disjoint_zeroRect_left (r : Rect) : Disjoint Lanes.zeroRect r := by
  have hz : Lanes.zeroRect = (⟨0, 0, 0, 0⟩ : Rect) := rfl
  rw [hz]
  unfold Disjoint Rect.meetsInterior
  intro h
  have h1 : max (0 : Int) r.x < min ((0 : Int) + 0) (r.x + r.w) := h.1
  omega

theorem disjoint_zeroRect_right (r : Rect) : Disjoint r Lanes.zeroRect :=
  Disjoint.symm' (disjoint_zeroRect_left r)

/-- Two rectangles whose vertical extents do not overlap are disjoint. -/
theorem disjoint_of_y_le {a b : Rect} (h : a.y + a.h ≤ b.y) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  omega

/-- Two rectangles whose horizontal extents do not overlap are disjoint. -/
theorem disjoint_of_x_le {a b : Rect} (h : a.x + a.w ≤ b.x) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  omega

theorem disjoint_of_mem_ne {l : List Rect} (h : l.Pairwise Disjoint)
    {a b : Rect} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) : Disjoint a b := by
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb
  have hij : i ≠ j := by
    intro he
    subst he
    exact hne (hia.symm.trans hjb)
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · have hd := List.Pairwise.rel_getElem_of_lt hi hj h hlt
    rwa [hia, hjb] at hd
  · exact absurd heq hij
  · have hd := List.Pairwise.rel_getElem_of_lt hj hi h hgt
    rw [hjb, hia] at hd
    exact Disjoint.symm' hd

/-! ### Event-rectangle facts -/


theorem getElem?_zip' {α β : Type} {l : List α} {m : List β} {i : Nat}
    {a : α} {b : β} (h : (l.zip m)[i]? = some (a, b)) :
    l[i]? = some a ∧ m[i]? = some b := by
  induction l generalizing m i with
  | nil => cases m <;> cases h
  | cons x xs ih =>
    cases m with
    | nil => cases h
    | cons y ys =>
      cases i with
      | zero =>
        have h' : ((x, y) :: xs.zip ys)[0]? = some (a, b) := h
        rw [List.getElem?_cons_zero] at h'
        have hp : (x, y) = (a, b) := Option.some.inj h'
        simp only [Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨rfl, rfl⟩
      | succ i =>
        have h' : ((x, y) :: xs.zip ys)[i + 1]? = some (a, b) := h
        rw [List.getElem?_cons_succ] at h'
        have ⟨hx, hy⟩ := ih h'
        constructor
        · simpa only [List.getElem?_cons_succ] using hx
        · simpa only [List.getElem?_cons_succ] using hy
/-! ### Horizontal plan card-rectangle disjointness -/


theorem section_mem_spec {g : Family} {c : TimelineConsts} {r : Rect}
    (hr : r ∈ (horizontalPlan g c).sections) :
    ∃ i s, g.sections[i]? = some s ∧
      r = ⟨c.leftMargin + ((first g i : Int)) * (cardWidth g c + c.columnGap),
        contentTop g c,
        ((span g i : Int)) * (cardWidth g c + c.columnGap) - c.columnGap,
        sectionHeight g c⟩ := by
  unfold horizontalPlan at hr
  dsimp only at hr
  obtain ⟨⟨s, i⟩, hmem, heq⟩ := List.mem_map.mp hr
  have hsi : g.sections[i]? = some s := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  refine ⟨i, s, hsi, ?_⟩
  have := heq.symm
  simp only [] at this
  exact this

theorem period_mem_spec {g : Family} {c : TimelineConsts} {r : Rect}
    (hr : r ∈ (horizontalPlan g c).periods) :
    ∃ i p, g.periods[i]? = some p ∧
      r = periodColumn c (cardWidth g c) (periodHeight g c)
        (contentTop g c +
          (if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap))
        (slot g i p) := by
  unfold horizontalPlan at hr
  dsimp only at hr
  obtain ⟨⟨p, i⟩, hmem, heq⟩ := List.mem_map.mp hr
  have hpi : g.periods[i]? = some p := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  refine ⟨i, p, hpi, ?_⟩
  have := heq.symm
  simp only [] at this
  exact this

section

variable {g : Family} {c : TimelineConsts}

private theorem first_succ' (g : Family) (s : Nat) :
    first g (s + 1) = first g s + span g s := by
  unfold first
  rw [List.range_succ, List.map_append, List.sum_append]
  simp [Nat.add_assoc]

private theorem first_mono' (g : Family) : ∀ (s t : Nat), s ≤ t → first g s ≤ first g t := by
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
      rw [first_succ']
      exact Nat.le_add_right _ _
    · have he : s = t + 1 := by omega
      rw [he]
      exact Nat.le_refl _

private theorem periodColumn_sep_left {c : TimelineConsts} {w h y : Int}
    (hw : 0 < w) (hcg : 0 ≤ c.columnGap) {i j : Nat} (hij : i < j) :
    (periodColumn c w h y i).x + w ≤ (periodColumn c w h y j).x := by
  have hS : 0 ≤ w + c.columnGap := by omega
  have hij' : (i : Int) + 1 ≤ (j : Int) := by omega
  have hm := Int.mul_le_mul_of_nonneg_right hij' hS
  rw [Int.add_mul, Int.one_mul] at hm
  unfold periodColumn
  dsimp only
  omega

theorem horizontalPlan_events_getElem {g : Family} {c : TimelineConsts} {i : Nat}
    {rs : List Rect} (h : (horizontalPlan g c).events[i]? = some rs) :
    ∃ (p : Lanes.Timeline.Period) (pr : Rect), g.periods[i]? = some p ∧
      (horizontalPlan g c).periods[i]? = some pr ∧
      rs = eventRects c pr.x (cardWidth g c)
        (contentTop g c +
          (if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap) +
          periodHeight g c + c.sectionGap) p.events := by
  have h' : (((g.periods.zip (horizontalPlan g c).periods).map
      fun (pair : Lanes.Timeline.Period × Rect) =>
        eventRects c pair.2.x (cardWidth g c)
          (contentTop g c +
            (if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap) +
            periodHeight g c + c.sectionGap) pair.1.events)[i]?) = some rs := h
  rw [List.getElem?_map] at h'
  cases hp : (g.periods.zip (horizontalPlan g c).periods)[i]? with
  | none => simp only [hp, Option.map_none] at h'; cases h'
  | some pair =>
    obtain ⟨p', pr'⟩ := pair
    rw [hp, Option.map_some] at h'
    obtain ⟨hpg, hpp⟩ := getElem?_zip' hp
    have hfi : eventRects c pr'.x (cardWidth g c)
        (contentTop g c +
          (if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap) +
          periodHeight g c + c.sectionGap) p'.events = rs :=
      Option.some.inj h'
    exact ⟨p', pr', hpg, hpp, hfi.symm⟩

theorem getElem?_of_lt {α : Type} {l : List α} {i : Nat} (h : i < l.length) :
    ∃ a, l[i]? = some a := by
  refine ⟨l[i]'h, ?_⟩
  rw [List.getElem?_eq_getElem h]

theorem plan_periods_length {g : Family} {c : TimelineConsts} :
    (horizontalPlan g c).periods.length = g.periods.length := by
  unfold horizontalPlan
  dsimp only
  rw [List.length_map, List.length_zipIdx]


/-- The y-band of a section band rectangle. -/
theorem section_rect_y {g : Family} {c : TimelineConsts} {r : Rect}
    (hr : r ∈ (horizontalPlan g c).sections) :
    r.y = contentTop g c ∧ r.h = sectionHeight g c := by
  obtain ⟨i, s, _, rfl⟩ := section_mem_spec hr
  exact ⟨rfl, rfl⟩

/-- The y-band of a period column rectangle. -/
theorem period_rect_y {g : Family} {c : TimelineConsts} {r : Rect}
    (hr : r ∈ (horizontalPlan g c).periods) :
    r.y = contentTop g c +
        (if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap) ∧
      r.h = periodHeight g c := by
  obtain ⟨i, p, _, rfl⟩ := period_mem_spec hr
  exact ⟨rfl, rfl⟩

theorem top_le_periodY {g : Family} {c : TimelineConsts}
    (hsh : 0 ≤ sectionHeight g c) (hsg : 0 ≤ c.sectionGap) :
    contentTop g c ≤ contentTop g c +
      (if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap) := by
  split <;> omega
theorem periodY_ph_le_eventTop {g : Family} {c : TimelineConsts}
    (_hph : 0 ≤ periodHeight g c) (hsg : 0 ≤ c.sectionGap) :
    contentTop g c +
        (if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap) +
      periodHeight g c ≤
      contentTop g c +
        (if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap) +
        periodHeight g c + c.sectionGap := by
  omega

theorem section_bottom_le_periodY {g : Family} {c : TimelineConsts} {r : Rect}
    (hr : r ∈ (horizontalPlan g c).sections)
    (_hsh : 0 ≤ sectionHeight g c) (hsg : 0 ≤ c.sectionGap) :
    r.y + r.h ≤ contentTop g c +
      (if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap) := by
  obtain ⟨hy, hh⟩ := section_rect_y hr
  have hne : g.sections ≠ [] := by
    intro he
    obtain ⟨i, s, hsi, _⟩ := section_mem_spec hr
    rw [he] at hsi
    simp at hsi
  have hb : g.sections.isEmpty = false := by simp [hne]
  rw [hy, hh]
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  omega

theorem event_y_ge {g : Family} {c : TimelineConsts} {r : Rect}
    (hr : r ∈ (horizontalPlan g c).events.flatten)
    (heg : 0 ≤ c.eventGap)
    (heh : ∀ p ∈ g.periods, ∀ e ∈ p.events, 0 ≤ eventHeight c e) :
    contentTop g c +
        (if g.sections.isEmpty then 0 else sectionHeight g c + c.sectionGap) +
      periodHeight g c + c.sectionGap ≤ r.y := by
  rw [List.mem_flatten] at hr
  obtain ⟨rs, hrs, hrr⟩ := hr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hrs
  obtain ⟨p, pr, hpi, hpri, hrects⟩ := horizontalPlan_events_getElem hi
  have hpm : p ∈ g.periods := List.mem_of_getElem? hpi
  have hlow := eventRects_lower c pr.x (cardWidth g c) _ p.events heg
    (fun e he => heh p hpm e he) r (hrects ▸ hrr)
  exact hlow

/-- Every non-title card rectangle sits at or below `contentTop`. -/
theorem card_y_ge_top {g : Family} {c : TimelineConsts} {r : Rect}
    (hr : r ∈ (horizontalPlan g c).sections ∨ r ∈ (horizontalPlan g c).periods ∨
      r ∈ (horizontalPlan g c).events.flatten)
    (hph : 0 ≤ periodHeight g c) (hsh : 0 ≤ sectionHeight g c)
    (hsg : 0 ≤ c.sectionGap) (heg : 0 ≤ c.eventGap)
    (heh : ∀ p ∈ g.periods, ∀ e ∈ p.events, 0 ≤ eventHeight c e) :
    contentTop g c ≤ r.y := by
  rcases hr with hs | hp | he
  · obtain ⟨hy, _⟩ := section_rect_y hs
    omega
  · obtain ⟨hy, _⟩ := period_rect_y hp
    rw [hy]
    exact top_le_periodY hsh hsg
  · have hge := event_y_ge he heg heh
    have h1 := top_le_periodY hsh hsg
    have h2 := periodY_ph_le_eventTop hph hsg
    omega

theorem disjoint_title_card {g : Family} {c : TimelineConsts}
    (hph : 0 ≤ periodHeight g c) (hsh : 0 ≤ sectionHeight g c)
    (hsg : 0 ≤ c.sectionGap) (heg : 0 ≤ c.eventGap)
    (heh : ∀ p ∈ g.periods, ∀ e ∈ p.events, 0 ≤ eventHeight c e)
    {t : Lanes.Timeline.Card} (ht : g.title = some t) {r : Rect}
    (hr : r ∈ (horizontalPlan g c).sections ∨ r ∈ (horizontalPlan g c).periods ∨
      r ∈ (horizontalPlan g c).events.flatten) :
    Disjoint (horizontalPlan g c).title r := by
  obtain ⟨hfy, _hfw, hfh⟩ := horizontalPlan_title_facts ht
  have hytop := card_y_ge_top hr hph hsh hsg heg heh
  have htop : contentTop g c = t.caption.h + c.eventGap := by
    unfold contentTop
    rw [ht]
    rfl
  have htb : (horizontalPlan g c).title.y + (horizontalPlan g c).title.h ≤ r.y := by
    rw [hfy, hfh]
    have h1 : t.caption.h ≤ t.caption.h + c.eventGap := by omega
    have h2 : t.caption.h + c.eventGap ≤ r.y := by
      rw [← htop]
      exact hytop
    omega
  exact disjoint_of_y_le htb

/-! ### Pairwise disjointness of the horizontal plan -/

theorem plan_sections_length {g : Family} {c : TimelineConsts} :
    (horizontalPlan g c).sections.length = g.sections.length := by
  unfold horizontalPlan
  dsimp only
  rw [List.length_map, List.length_zipIdx]

/-- Sections at distinct indices occupy disjoint x-ranges. -/
theorem sections_pairwise_disjoint {g : Family} {c : TimelineConsts}
    (hw : 0 < cardWidth g c) (hcg : 0 ≤ c.columnGap) :
    (horizontalPlan g c).sections.Pairwise Disjoint := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hipl : i < g.sections.length := by
    rw [← plan_sections_length]; exact hi
  have hjpl : j < g.sections.length := by
    rw [← plan_sections_length]; exact hj
  obtain ⟨s, hs⟩ := getElem?_of_lt hipl
  obtain ⟨t, ht⟩ := getElem?_of_lt hjpl
  have hai := plan_section_rect_eq hs (List.getElem?_eq_getElem hi)
  have hbj := plan_section_rect_eq ht (List.getElem?_eq_getElem hj)
  rw [hai, hbj]
  have hsum_nat : first g i + span g i ≤ first g j := by
    rw [← first_succ']
    exact first_mono' g (i + 1) j (by omega)
  have hsum : (first g i : Int) + (span g i : Int) ≤ (first g j : Int) := by omega
  have hS : 0 ≤ (cardWidth g c + c.columnGap : Int) := by omega
  have hmul := Int.mul_le_mul_of_nonneg_right hsum hS
  rw [Int.add_mul] at hmul
  apply disjoint_of_x_le
  dsimp only
  omega

/-- Period columns at distinct indices occupy disjoint x-ranges. -/
theorem periods_pairwise_disjoint {g : Family} {c : TimelineConsts}
    (hw : 0 < cardWidth g c) (hcg : 0 ≤ c.columnGap)
    (hsec : ∀ period ∈ g.periods, period.sectionIndex = -1 ∨
      0 ≤ period.sectionIndex) :
    (horizontalPlan g c).periods.Pairwise Disjoint := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hipl : i < g.periods.length := by
    rw [← plan_periods_length]; exact hi
  have hjpl : j < g.periods.length := by
    rw [← plan_periods_length]; exact hj
  obtain ⟨p, hp⟩ := getElem?_of_lt hipl
  obtain ⟨q, hq⟩ := getElem?_of_lt hjpl
  have hai := plan_period_rect_eq hp (List.getElem?_eq_getElem hi)
  have hbj := plan_period_rect_eq hq (List.getElem?_eq_getElem hj)
  rw [hai, hbj]
  have hslot : slot g i p ≠ slot g j q := by
    intro heq
    have h1 := slot_inj hsec hp hq heq
    omega
  rcases Nat.lt_trichotomy (slot g i p) (slot g j q) with hlt | heq2 | hgt
  · exact disjoint_of_x_le (periodColumn_sep_left hw hcg hlt)
  · exact absurd heq2 hslot
  · exact Disjoint.symm' (disjoint_of_x_le (periodColumn_sep_left hw hcg hgt))

/-- Every flattened event rectangle comes from one period's event stack. -/
theorem event_member_spec {g : Family} {c : TimelineConsts} {b : Rect}
    (hb : b ∈ (horizontalPlan g c).events.flatten) :
    ∃ (i : Nat) (p : Lanes.Timeline.Period) (pr : Rect), g.periods[i]? = some p ∧
      (horizontalPlan g c).periods[i]? = some pr ∧
      b ∈ Lanes.Timeline.eventRects c pr.x (cardWidth g c)
        (contentTop g c +
          (if g.sections.isEmpty then 0 else
            sectionHeight g c + c.sectionGap) +
          periodHeight g c + c.sectionGap) p.events := by
  rw [List.mem_flatten] at hb
  obtain ⟨rs, hrs, hb⟩ := hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hrs
  obtain ⟨p, pr, hp, hpr, hrs_eq⟩ := horizontalPlan_events_getElem hi
  exact ⟨i, p, pr, hp, hpr, hrs_eq ▸ hb⟩

/-- Event stacks inside one period column are pairwise disjoint. -/
theorem events_flatten_pairwise_disjoint {g : Family} {c : TimelineConsts}
    (hsec : ∀ period ∈ g.periods, period.sectionIndex = -1 ∨
      0 ≤ period.sectionIndex)
    (hw : 0 < cardWidth g c) (hcg : 0 ≤ c.columnGap)
    (heg : 0 ≤ c.eventGap)
    (heh : ∀ period ∈ g.periods, ∀ e ∈ period.events,
      0 ≤ Lanes.Timeline.eventHeight c e) :
    ((horizontalPlan g c).events.flatten).Pairwise Disjoint := by
  rw [List.pairwise_flatten]
  constructor
  · intro rs hrs
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hrs
    obtain ⟨p, pr, hp, _hpr, hrs_eq⟩ := horizontalPlan_events_getElem hi
    rw [hrs_eq]
    exact List.Pairwise.imp (fun h => h.2)
      (timeline_events_stack_disjoint c pr.x (cardWidth g c)
        (contentTop g c +
          (if g.sections.isEmpty then 0 else
            sectionHeight g c + c.sectionGap) +
          periodHeight g c + c.sectionGap) p.events heg
        (fun e he => heh p (List.mem_of_getElem? hp) e he))
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    intro a ha b hb
    obtain ⟨p₁, pr₁, hp₁, hpr₁, hrs₁⟩ := horizontalPlan_events_getElem
      (List.getElem?_eq_getElem hi)
    obtain ⟨p₂, pr₂, hp₂, hpr₂, hrs₂⟩ := horizontalPlan_events_getElem
      (List.getElem?_eq_getElem hj)
    have ha' : a ∈ Lanes.Timeline.eventRects c pr₁.x (cardWidth g c)
        (contentTop g c +
          (if g.sections.isEmpty then 0 else
            sectionHeight g c + c.sectionGap) +
          periodHeight g c + c.sectionGap) p₁.events := hrs₁ ▸ ha
    have hb' : b ∈ Lanes.Timeline.eventRects c pr₂.x (cardWidth g c)
        (contentTop g c +
          (if g.sections.isEmpty then 0 else
            sectionHeight g c + c.sectionGap) +
          periodHeight g c + c.sectionGap) p₂.events := hrs₂ ▸ hb
    obtain ⟨hax, haw⟩ := eventRects_horizontal c pr₁.x (cardWidth g c)
      p₁.events _ a ha'
    obtain ⟨hbx, hbw⟩ := eventRects_horizontal c pr₂.x (cardWidth g c)
      p₂.events _ b hb'
    have hpr₁_eq := plan_period_rect_eq hp₁ hpr₁
    have hpr₂_eq := plan_period_rect_eq hp₂ hpr₂
    have hslot : slot g i p₁ ≠ slot g j p₂ := by
      intro heq
      have h1 := slot_inj hsec hp₁ hp₂ heq
      omega
    rcases Nat.lt_trichotomy (slot g i p₁) (slot g j p₂) with hlt | heq2 | hgt
    · apply disjoint_of_x_le
      rw [hax, haw, hbx, hpr₁_eq, hpr₂_eq]
      exact periodColumn_sep_left hw hcg hlt
    · exact absurd heq2 hslot
    · apply Disjoint.symm'
      apply disjoint_of_x_le
      rw [hbx, hbw, hpr₂_eq, hax, hpr₁_eq]
      exact periodColumn_sep_left hw hcg hgt

/-- A period column and an event rectangle from a different column are disjoint. -/
theorem period_event_cross {g : Family} {c : TimelineConsts}
    (hsec : ∀ period ∈ g.periods, period.sectionIndex = -1 ∨
      0 ≤ period.sectionIndex)
    (hw : 0 < cardWidth g c) (hcg : 0 ≤ c.columnGap)
    (hph : 0 ≤ periodHeight g c) (hsg : 0 ≤ c.sectionGap)
    (heg : 0 ≤ c.eventGap)
    (heh : ∀ period ∈ g.periods, ∀ e ∈ period.events,
      0 ≤ Lanes.Timeline.eventHeight c e)
    {a b : Rect} (ha : a ∈ (horizontalPlan g c).periods)
    (hb : b ∈ (horizontalPlan g c).events.flatten) :
    Disjoint a b := by
  obtain ⟨i, p, hp, ha_eq⟩ := period_mem_spec ha
  obtain ⟨i₂, p₂, pr₂, hp₂, hpr₂, hb₂⟩ := event_member_spec hb
  have hpr₂_eq := plan_period_rect_eq hp₂ hpr₂
  by_cases hie : i = i₂
  · subst hie
    apply disjoint_of_y_le
    rw [ha_eq]
    dsimp only [periodColumn]
    have hlow := eventRects_lower c pr₂.x (cardWidth g c) _ p₂.events heg
      (fun e he => heh p₂ (List.mem_of_getElem? hp₂) e he) b hb₂
    have h4 := periodY_ph_le_eventTop hph hsg
    omega
  · have hslot : slot g i p ≠ slot g i₂ p₂ := by
      intro heq
      have h1 := slot_inj hsec hp hp₂ heq
      exact hie h1
    rcases Nat.lt_trichotomy (slot g i p) (slot g i₂ p₂) with hlt | heq2 | hgt
    · apply disjoint_of_x_le
      have hbx : b.x = pr₂.x :=
        (eventRects_horizontal c pr₂.x (cardWidth g c) p₂.events _ b hb₂).1
      rw [ha_eq, hbx, hpr₂_eq]
      exact periodColumn_sep_left hw hcg hlt
    · exact absurd heq2 hslot
    · apply Disjoint.symm'
      apply disjoint_of_x_le
      have hbx : b.x = pr₂.x :=
        (eventRects_horizontal c pr₂.x (cardWidth g c) p₂.events _ b hb₂).1
      have hbw : b.w = cardWidth g c :=
        (eventRects_horizontal c pr₂.x (cardWidth g c) p₂.events _ b hb₂).2
      rw [hbx, hbw, hpr₂_eq, ha_eq]
      exact periodColumn_sep_left hw hcg hgt

/-- A section band and a period column occupy disjoint y-bands. -/
theorem section_period_cross {g : Family} {c : TimelineConsts}
    (hsh : 0 ≤ sectionHeight g c) (hsg : 0 ≤ c.sectionGap)
    {a b : Rect} (ha : a ∈ (horizontalPlan g c).sections)
    (hb : b ∈ (horizontalPlan g c).periods) :
    Disjoint a b := by
  apply disjoint_of_y_le
  have h1 := section_bottom_le_periodY ha hsh hsg
  have h2 := period_rect_y hb
  rw [h2.1]
  exact h1

/-- A section band and an event rectangle occupy disjoint y-bands. -/
theorem section_event_cross {g : Family} {c : TimelineConsts}
    (hph : 0 ≤ periodHeight g c) (hsh : 0 ≤ sectionHeight g c)
    (hsg : 0 ≤ c.sectionGap) (heg : 0 ≤ c.eventGap)
    (heh : ∀ period ∈ g.periods, ∀ e ∈ period.events,
      0 ≤ Lanes.Timeline.eventHeight c e)
    {a b : Rect} (ha : a ∈ (horizontalPlan g c).sections)
    (hb : b ∈ (horizontalPlan g c).events.flatten) :
    Disjoint a b := by
  apply disjoint_of_y_le
  have h1 := section_bottom_le_periodY ha hsh hsg
  have hge := event_y_ge hb heg heh
  have h4 := periodY_ph_le_eventTop hph hsg
  omega

/-- All card rectangles of the horizontal plan are pairwise disjoint. -/
theorem horizontal_cardRects_disjoint {g : Family} {c : TimelineConsts}
    (hsec : ∀ period ∈ g.periods, period.sectionIndex = -1 ∨
      0 ≤ period.sectionIndex)
    (hw : 0 < cardWidth g c) (hph : 0 ≤ periodHeight g c)
    (hsh : 0 ≤ sectionHeight g c) (heg : 0 ≤ c.eventGap)
    (hsg : 0 ≤ c.sectionGap) (hcg : 0 ≤ c.columnGap)
    (heh : ∀ period ∈ g.periods, ∀ e ∈ period.events,
      0 ≤ Lanes.Timeline.eventHeight c e) :
    (cardRects g (horizontalPlan g c)).Pairwise Disjoint := by
  have hS := sections_pairwise_disjoint hw hcg
  have hP := periods_pairwise_disjoint hw hcg hsec
  have hE := events_flatten_pairwise_disjoint hsec hw hcg heg heh
  unfold cardRects
  simp only [List.append_assoc]
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · cases g.title.isSome <;> simp
  · rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · exact hS
    · rw [List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · exact hP
      · exact hE
      · intro a ha b hb
        exact period_event_cross hsec hw hcg hph hsg heg heh ha hb
    · intro a ha b hb
      rcases List.mem_append.mp hb with hbP | hbE
      · exact section_period_cross hsh hsg ha hbP
      · exact section_event_cross hph hsh hsg heg heh ha hbE
  · intro a ha b hb
    cases h : g.title.isSome with
    | false => simp [h] at ha
    | true =>
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
      have hat : a = (horizontalPlan g c).title := by
        simp only [h, ↓reduceIte, List.mem_singleton] at ha
        exact ha
      rw [hat]
      have hb' : b ∈ (horizontalPlan g c).sections ∨
          b ∈ (horizontalPlan g c).periods ∨
          b ∈ (horizontalPlan g c).events.flatten := by
        rcases List.mem_append.mp hb with h1 | h2
        · exact Or.inl h1
        · rcases List.mem_append.mp h2 with h2' | h2''
          · exact Or.inr (Or.inl h2')
          · exact Or.inr (Or.inr h2'')
      exact disjoint_title_card hph hsh hsg heg heh ht hb'

end
end Elegant.Kinds.Timeline

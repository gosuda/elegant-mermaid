import Elegant.SequenceStep

set_option autoImplicit false

namespace Elegant
namespace Sequence

theorem msgDx_nonneg {pl : Plan} (hpl : pl.Wf) (src dst route : Nat) : 0 ≤ msgDx pl src dst route := by
  unfold msgDx
  have hw := hpl.pos.wrapPadding
  have hl : 0 ≤ msgLw pl route := widest_nonneg _
  split
  · exact Int.le_trans (half_nonneg (by omega)) (Int.le_max_left _ _)
  · exact Int.le_refl _

theorem msgRowH_ge {pl : Plan} (hpl : pl.Wf) (cs : List Int) (w : Walk) (bits src dst route : Nat) :
    pl.c.messageTop + msgCount pl route * pl.c.lineHeight + pl.c.boxMargin ≤ msgRowH pl cs w bits src dst route := by
  unfold msgRowH
  have h1 := createdBox_nonneg pl hpl cs w bits dst (msgY pl w route)
  have h2 := hpl.pos.selfLoopDepth
  split <;> omega

theorem msgRowH_created {pl : Plan} (hpl : pl.Wf) (cs : List Int) (w : Walk) (bits src dst route : Nat)
    (q : Nat × Rect) (hq : createdRect pl cs bits dst (msgY pl w route) = some q) :
    pl.c.messageTop + msgCount pl route * pl.c.lineHeight + pl.c.boxMargin + (q.2.h + pl.c.boxMargin) ≤
      msgRowH pl cs w bits src dst route := by
  unfold msgRowH
  have h2 := hpl.pos.selfLoopDepth
  have hs := createdBox_snd pl cs w bits dst (msgY pl w route)
  rw [hq] at hs
  have hs' : (createdBox pl cs w bits dst (msgY pl w route)).2 = q.2.h + pl.c.boxMargin := hs
  split <;> omega

theorem msg_fit {pl : Plan} (hpl : pl.Wf) {steps : List Step} {cs : List Int} (hcs : cs = columns pl steps)
    {bits src dst route : Nat} {destroyed : Int} (hs : Step.message bits src dst route destroyed ∈ steps)
    (hne : src ≠ dst) (hsrc : src < pl.widths.length) (hdst : dst < pl.widths.length) :
    msgLw pl route + 2 * pl.c.wrapPadding + pl.c.actorMargin ≤
      max (cs.getD src 0) (cs.getD dst 0) - min (cs.getD src 0) (cs.getD dst 0) := by
  have h := sequence_span_label_fits pl hpl.widths steps bits src dst route destroyed hs hne
    (by omega)
  have hlw : msgLw pl route = pl.labelWidth (routeLabelPos pl.m route) := by
    unfold msgLw Plan.labelWidth
    rw [linesAt_routeLabel]
  rw [hlw]
  subst hcs
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hord := sequence_columns_ordered pl hpl steps src dst hlt hdst
    rw [Nat.max_eq_right (Nat.le_of_lt hlt), Nat.min_eq_left (Nat.le_of_lt hlt)] at h
    omega
  · have hord := sequence_columns_ordered pl hpl steps dst src hgt hsrc
    rw [Nat.max_eq_left (Nat.le_of_lt hgt), Nat.min_eq_right (Nat.le_of_lt hgt)] at h
    omega

theorem inv_message {pl : Plan} {hdr lab0 : List Rect} {stack placed : List Nat} {w : Walk}
    {E : List Ent} {steps : List Step} {cs : List Int} (hpl : pl.Wf) (hfm : ModelFacts pl.m)
    (hI : Inv pl hdr lab0 stack placed w E) (hcs : cs = columns pl steps)
    {bits src dst route : Nat} {destroyed : Int}
    (hs : Step.message bits src dst route destroyed ∈ steps)
    (hsrc : src < pl.widths.length) (hdst : dst < pl.widths.length)
    (hcreate : ∀ bi r, createdRect pl cs bits dst (msgY pl w route) = some (bi, r) →
      bi < pl.m.boxes.length ∧ bi ∉ placed ∧ boxParent pl.m bi = topId pl.m stack ∧
        ¬ IsGroupAt pl.m bi) :
    ∃ E', Inv pl hdr lab0 stack
      (((createdRect pl cs bits dst (msgY pl w route)).map (·.1)).toList ++ placed)
      (stepMessage pl cs w bits src dst route destroyed) E' := by
  have hbm := hpl.pos.boxMargin
  have hmt := hpl.pos.messageTop
  have hwp := hpl.pos.wrapPaddingPos
  have hn : 0 ≤ msgCount pl route * pl.c.lineHeight :=
    Int.mul_nonneg (Int.natCast_nonneg _) hpl.pos.lineHeight
  have hmg := hpl.pos.margin
  have hge := msgRowH_ge hpl cs w bits src dst route
  have hdx := msgDx_nonneg hpl src dst route
  have hlw : 0 ≤ msgLw pl route := widest_nonneg _
  refine inv_leaf hfm hI (w' := stepMessage pl cs w bits src dst route destroyed)
    (createdRect pl cs bits dst (msgY pl w route))
    ((messageLabelAt pl route).map fun p => (p, msgLabelRect pl cs w src dst route))
    (((createdRect pl cs bits dst (msgY pl w route)).map (·.2)).toList ++
      [msgMember pl cs w bits src dst route])
    (w.cursor + msgRowH pl cs w bits src dst route)
    (stepMessage_boxRects_eq pl cs w bits src dst route destroyed) ?_
    (stepMessage_fragments_eq pl cs w bits src dst route destroyed)
    (stepMessage_cursor_eq pl cs w bits src dst route destroyed) (by omega) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [stepMessage_labelRects_eq]
    cases messageLabelAt pl route <;> rfl
  · intro n r h
    obtain ⟨h1, h2, h3, h4⟩ := hcreate n r h
    have hr := createdRect_spec _ _ _ _ _ _ _ h
    have hq := msgRowH_created hpl cs w bits src dst route (n, r) h
    have hh := hpl.heights dst
    have hw0 := hpl.widths dst
    refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_⟩
    all_goals rw [hr]
    · show w.cursor ≤ msgY pl w route
      unfold msgY; omega
    · exact hw0
    · exact hh
    · show msgY pl w route + pl.heights.getD dst 0 ≤ w.cursor + msgRowH pl cs w bits src dst route
      unfold msgY
      dsimp only at hq
      have hrh : r.h = pl.heights.getD dst 0 := by rw [hr]
      omega
  · intro p r h
    cases hm : messageLabelAt pl route with
    | none => simp [hm] at h
    | some a =>
      simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      show w.cursor ≤ w.cursor + pl.c.messageTop ∧ 0 ≤ msgLw pl route ∧
        0 ≤ msgCount pl route * pl.c.lineHeight ∧
          w.cursor + pl.c.messageTop + msgCount pl route * pl.c.lineHeight ≤ w.cursor + msgRowH pl cs w bits src dst route
      omega
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · cases hc : createdRect pl cs bits dst (msgY pl w route) with
      | none => rw [hc] at hr; simp at hr
      | some q =>
        rw [hc] at hr
        simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hr
        subst hr
        have hr0 := createdRect_spec _ _ _ _ _ _ _ hc
        have hq := msgRowH_created hpl cs w bits src dst route q hc
        have hh := hpl.heights dst
        have hw0 := hpl.widths dst
        rw [hr0]
        refine ⟨?_, hw0, hh, ?_⟩
        · show w.cursor ≤ msgY pl w route
          unfold msgY; omega
        · show msgY pl w route + pl.heights.getD dst 0 ≤ w.cursor + msgRowH pl cs w bits src dst route
          unfold msgY
          have hqh : q.2.h = pl.heights.getD dst 0 := by rw [hr0]
          omega
    · have hr' : r = msgMember pl cs w bits src dst route := by simpa using hr
      subst hr'
      show w.cursor ≤ w.cursor ∧
        0 ≤ (max (cs.getD src 0) (cs.getD dst 0) - min (cs.getD src 0) (cs.getD dst 0)) + 2 * msgDx pl src dst route ∧
          0 ≤ msgRowH pl cs w bits src dst route ∧ w.cursor + msgRowH pl cs w bits src dst route ≤ w.cursor + msgRowH pl cs w bits src dst route
      omega
  · intro n r h
    rw [h]
    simp
  · intro p r h
    refine ⟨msgMember pl cs w bits src dst route, List.mem_append_right _ (by simp), ?_⟩
    cases hm : messageLabelAt pl route with
    | none => simp [hm] at h
    | some a =>
      simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      by_cases hsd : src = dst
      · subst hsd
        have hd : msgDx pl src src route = max (half (msgLw pl route + 2 * pl.c.wrapPadding)) pl.c.selfLoopMinDx := by
          unfold msgDx; simp
        have hrow := msgRowH_ge hpl cs w bits src src route
        have hhalf := half_div (msgLw pl route + 2 * pl.c.wrapPadding)
        have hhalf2 := half_div (msgLw pl route)
        have hc2 := half_div (cs.getD src 0 + cs.getD src 0)
        show min (cs.getD src 0) (cs.getD src 0) - msgDx pl src src route ≤
            half (cs.getD src 0 + cs.getD src 0) - half (msgLw pl route) ∧
          half (cs.getD src 0 + cs.getD src 0) - half (msgLw pl route) + msgLw pl route ≤
            min (cs.getD src 0) (cs.getD src 0) - msgDx pl src src route +
              ((max (cs.getD src 0) (cs.getD src 0) - min (cs.getD src 0) (cs.getD src 0)) + 2 * msgDx pl src src route) ∧
          w.cursor ≤ w.cursor + pl.c.messageTop ∧
          w.cursor + pl.c.messageTop + msgCount pl route * pl.c.lineHeight ≤ w.cursor + msgRowH pl cs w bits src src route
        omega
      · have hfit := msg_fit hpl hcs hs hsd hsrc hdst
        have hd : msgDx pl src dst route = 0 := by
          unfold msgDx
          have : (src == dst) = false := by simpa using hsd
          simp [this]
        have hrow := msgRowH_ge hpl cs w bits src dst route
        have hhalf := half_div (cs.getD src 0 + cs.getD dst 0)
        have hhalf2 := half_div (msgLw pl route)
        show min (cs.getD src 0) (cs.getD dst 0) - msgDx pl src dst route ≤
            half (cs.getD src 0 + cs.getD dst 0) - half (msgLw pl route) ∧
          half (cs.getD src 0 + cs.getD dst 0) - half (msgLw pl route) + msgLw pl route ≤
            min (cs.getD src 0) (cs.getD dst 0) - msgDx pl src dst route +
              ((max (cs.getD src 0) (cs.getD dst 0) - min (cs.getD src 0) (cs.getD dst 0)) + 2 * msgDx pl src dst route) ∧
          w.cursor ≤ w.cursor + pl.c.messageTop ∧
          w.cursor + pl.c.messageTop + msgCount pl route * pl.c.lineHeight ≤ w.cursor + msgRowH pl cs w bits src dst route
        omega
  · intro n r h
    exact (hcreate n r h).2.2.2

end Sequence
end Elegant

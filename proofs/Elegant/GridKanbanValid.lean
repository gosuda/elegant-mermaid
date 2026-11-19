import Elegant.GridKanbanLoop

set_option autoImplicit false

namespace Elegant.GridKanban

def sourceColumns (m : Model) : List ModelBox :=
  m.boxes.filter (fun b => b.role == .group || b.parent == "")

def sourceCards (m : Model) : List ModelBox :=
  m.boxes.filter (fun b => !(b.role == .group || b.parent == ""))

/-- These are consequences of the actual native prelude, not extra admission
conditions: every successful scene has nonnegative configured dimensions, a
positive card width, and top-level section frames. -/
theorem scene_prelude {m : Model} {value : Scene}
    (h : Kinds.Kanban.scene m = .ok value) :
    ∃ width pad,
      Kinds.Kanban.configured m "sectionWidth" (LayoutConst.kanban_section_width.get m.profile) = .ok width ∧
      Kinds.Kanban.configured m "padding" (LayoutConst.kanban_padding.get m.profile) = .ok pad ∧
      0 ≤ width ∧ 0 ≤ pad ∧
      0 < width - Int.fdiv (3 * LayoutConst.kanban_gutter.get m.profile) 2 ∧
      ∀ col ∈ sourceColumns m, col.parent = "" := by
  unfold Kinds.Kanban.scene at h
  simp only [Kinds.Kanban.isSection] at h
  dsimp only [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map,
    throw, throwThe, MonadExceptOf.throw] at h
  cases hw : Kinds.Kanban.configured m "sectionWidth"
      (LayoutConst.kanban_section_width.get m.profile) with
  | error error => rw [hw] at h; cases h
  | ok width =>
    rw [hw] at h
    dsimp only [Bind.bind, Except.bind] at h
    cases hp : Kinds.Kanban.configured m "padding"
        (LayoutConst.kanban_padding.get m.profile) with
    | error error => rw [hp] at h; cases h
    | ok pad =>
      rw [hp] at h
      dsimp only [Bind.bind, Except.bind] at h
      by_cases hc : width - Int.fdiv (3 * LayoutConst.kanban_gutter.get m.profile) 2 ≤ 0
      · rw [ite_eq_left hc] at h
        cases h
      · rw [ite_eq_right hc] at h
        by_cases hg : (sourceColumns m).any (fun b => b.parent != "") = true
        · change (m.boxes.filter Kinds.Kanban.isSection).any
            (fun b => b.parent != "") = true at hg
          rw [ite_eq_left hg] at h
          cases h
        · have hwidth := configured_spec (m := m) (key := "sectionWidth")
            (fallback := LayoutConst.kanban_section_width.get m.profile)
            (by cases m.profile <;> decide) (by cases m.profile <;> decide) hw
          have hpad := configured_spec (m := m) (key := "padding")
            (fallback := LayoutConst.kanban_padding.get m.profile)
            (by cases m.profile <;> decide) (by cases m.profile <;> decide) hp
          refine ⟨width, pad, rfl, rfl, hwidth.1, hpad.1, by omega, ?_⟩
          intro col hcol
          by_cases hparent : col.parent = ""
          · exact hparent
          · have hany : (sourceColumns m).any (fun b => b.parent != "") = true :=
              List.any_eq_true.mpr ⟨col, hcol, by simp [hparent]⟩
            exact False.elim (hg hany)

def bandFrom (profile : Profile) (titles : List (List Measure.Line)) : Int :=
  titles.foldl (fun h ls => max h
    (Int.ofNat ls.length * LayoutConst.line_h.get profile + LayoutConst.node_border.get profile))
    (LayoutConst.kanban_label_band_min.get profile)

def cardHeightFrom (profile : Profile) (input : ModelBox × List Measure.Line) : Int :=
  Int.ofNat (max 1 input.2.length) * LayoutConst.line_h.get profile +
    2 * LayoutConst.kanban_card_pad_y.get profile + 2 * LayoutConst.node_border.get profile

structure NativeRunData (m : Model) (value : Scene) where
  width : Int
  pad : Int
  titles : List (List Measure.Line)
  texts : List (List Measure.Line)
  cardFinal : NativeCardState
  sectionFinal : NativeSectionState
  widthNonnegative : 0 ≤ width
  padNonnegative : 0 ≤ pad
  cardWidthPositive : 0 < width - Int.fdiv (3 * LayoutConst.kanban_gutter.get m.profile) 2
  roots : ∀ col ∈ sourceColumns m, col.parent = ""
  titleCount : titles.length = (sourceColumns m).length
  textCount : texts.length = (sourceCards m).length
  cardGeometry : NativeCardInvariant (sourceColumns m) (sourceCards m) pad width
    (LayoutConst.kanban_card_gap.get m.profile)
    (width - Int.fdiv (3 * LayoutConst.kanban_gutter.get m.profile) 2)
    (bandFrom m.profile titles) cardFinal
  sectionGeometry : SectionInvariant (((sourceColumns m).zip titles).zipIdx) cardFinal.2.1
    (sectionFor cardFinal.1 pad width (LayoutConst.kanban_card_gap.get m.profile)
      (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile titles)
      (LayoutConst.kanban_label_band_min.get m.profile)
      (LayoutConst.kanban_section_min_height.get m.profile)) pad sectionFinal
  cardIds : cardFinal.2.1.map (·.1) = (sourceCards m).map (·.id)
  sectionIds : sectionFinal.1.map (·.1) = (sourceCards m).map (·.id) ++ (sourceColumns m).map (·.id)
  cardOwners : ∀ entry ∈ cardFinal.2.1, ∃ card ∈ sourceCards m, ∃ owner,
    entry.1 = card.id ∧
    (sourceColumns m).findIdx? (fun col => col.id == card.parent) = some owner
  retainedCards : ∀ entry ∈ cardFinal.2.1, entry ∈ sectionFinal.1
  sectionPlacements : sectionFinal.1 = cardFinal.2.1 ++
    (((sourceColumns m).zip titles).zipIdx).map (fun input =>
      (input.1.1.id, sectionFor cardFinal.1 pad width
        (LayoutConst.kanban_card_gap.get m.profile)
        (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile titles)
        (LayoutConst.kanban_label_band_min.get m.profile)
        (LayoutConst.kanban_section_min_height.get m.profile) input))
  assembled : value = Kinds.Kanban.assemble m
    ⟨sectionFinal.2.2.1 + pad, sectionFinal.2.2.2 + pad⟩ sectionFinal.1
    (sectionFinal.2.1 ++ cardFinal.2.2)

theorem source_card_ids_nodup (m : Model) (hw : Elegant.WellFormed m) :
    ((sourceCards m).map (·.id)).Nodup := by
  apply List.Nodup.sublist _ (model_ids_nodup m hw)
  exact List.Sublist.map _ List.filter_sublist

theorem scene_phase_invariants {m : Model} {value : Scene}
    (hwf : Elegant.WellFormed m) (h : Kinds.Kanban.scene m = .ok value) :
    Nonempty (NativeRunData m value) := by
  obtain ⟨width, pad, hw, hp, hw0, hp0, hcw, hroots⟩ := scene_prelude h
  have hcwNot : ¬ width - Int.fdiv (3 * LayoutConst.kanban_gutter.get m.profile) 2 ≤ 0 := by omega
  have hgroups : ¬ (sourceColumns m).any (fun b => b.parent != "") = true := by
    intro hg
    obtain ⟨col, hcol, hbad⟩ := List.any_eq_true.mp hg
    simp [hroots col hcol] at hbad
  unfold Kinds.Kanban.scene at h
  simp only [Kinds.Kanban.isSection] at h
  change ¬ (m.boxes.filter Kinds.Kanban.isSection).any
    (fun b => b.parent != "") = true at hgroups
  dsimp only [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map,
    throw, throwThe, MonadExceptOf.throw] at h
  rw [hw, hp] at h
  dsimp only [Bind.bind, Except.bind] at h
  rw [ite_eq_right hcwNot, ite_eq_right hgroups] at h
  cases hm : Kinds.Common.labelMetric m.profile with
  | error error => rw [hm] at h; cases h
  | ok metric =>
    rw [hm] at h
    dsimp only [Bind.bind, Except.bind] at h
    split at h
    · cases h
    · rename_i titles ht
      split at h
      · cases h
      · rename_i texts hx
        split at h
        · cases h
        · rename_i cardFinal hcard
          split at h
          · cases h
          · rename_i sectionFinal hsection
            split at h
            · cases h
            · have htlen : titles.length = (sourceColumns m).length :=
                measured_map_length _ _ _ ht
              have hxlen : texts.length = (sourceCards m).length :=
                measured_map_length _ _ _ hx
              have hcardInv : NativeCardInvariant (sourceColumns m) (sourceCards m) pad width
                  (LayoutConst.kanban_card_gap.get m.profile)
                  (width - Int.fdiv (3 * LayoutConst.kanban_gutter.get m.profile) 2)
                  (bandFrom m.profile titles) cardFinal := by
                exact card_pass_invariant (sourceColumns m) (sourceCards m)
                  ((sourceCards m).zip texts) _ _ pad width
                  (LayoutConst.kanban_card_gap.get m.profile)
                  (width - Int.fdiv (3 * LayoutConst.kanban_gutter.get m.profile) 2)
                  (bandFrom m.profile titles) (cardHeightFrom m.profile)
                  cardFinal (source_card_ids_nodup m hwf)
                  (fun input hi => (List.of_mem_zip hi).1)
                  (native_parameters_nonnegative m.profile).2.1
                  (fun input _ => native_card_height_nonnegative m.profile input.2.length)
                  (fun input output hs => (Kinds.Kanban.checked_spec hs).1) hcard
              have hcardIds : cardFinal.2.1.map (·.1) = (sourceCards m).map (·.id) := by
                rw [← card_inputs_ids (sourceCards m) texts hxlen]
                exact card_pass_ids (sourceColumns m) ((sourceCards m).zip texts) _ _ pad width
                  (LayoutConst.kanban_card_gap.get m.profile)
                  (width - Int.fdiv (3 * LayoutConst.kanban_gutter.get m.profile) 2)
                  (bandFrom m.profile titles) (cardHeightFrom m.profile) cardFinal
                  (fun input output hs => (Kinds.Kanban.checked_spec hs).1) hcard
              have hstepData : ∃ step : SectionInput → NativeSectionState →
                  Except LayoutError (ForInStep NativeSectionState),
                  forIn (((sourceColumns m).zip titles).zipIdx) (cardFinal.2.1, [], pad, pad)
                    step = .ok sectionFinal ∧
                  ∀ input ∈ (((sourceColumns m).zip titles).zipIdx), ∀ state next,
                    step input state = Except.ok next →
                    SectionStepShape
                      (sectionFor cardFinal.1 pad width (LayoutConst.kanban_card_gap.get m.profile)
                        (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile titles)
                        (LayoutConst.kanban_label_band_min.get m.profile)
                        (LayoutConst.kanban_section_min_height.get m.profile)) input state next := by
                refine ⟨_, hsection, ?_⟩
                intro input _ state next hs
                split at hs
                · cases hs
                · rename_i rect hrect
                  have heq := (Kinds.Kanban.checked_spec hrect).1
                  subst rect
                  split at hs
                  · cases hs
                  · rename_i titleRect htitleRect
                    have heq := (Kinds.Kanban.checked_spec htitleRect).1
                    subst titleRect
                    cases hs
                    exact ⟨_, rfl⟩
              have hcardOwners : ∀ entry ∈ cardFinal.2.1,
                  ∃ card ∈ sourceCards m, ∃ owner, entry.1 = card.id ∧
                    (sourceColumns m).findIdx? (fun col => col.id == card.parent) = some owner := by
                intro entry he
                obtain ⟨input, hi, owner, hid, ho⟩ :=
                  card_pass_owner_coverage (sourceColumns m) ((sourceCards m).zip texts)
                    _ _ pad width (LayoutConst.kanban_card_gap.get m.profile)
                    (width - Int.fdiv (3 * LayoutConst.kanban_gutter.get m.profile) 2)
                    (bandFrom m.profile titles) (cardHeightFrom m.profile) cardFinal
                    (fun input output hs => (Kinds.Kanban.checked_spec hs).1) hcard entry he
                exact ⟨input.1, (List.of_mem_zip hi).1, owner, hid, ho⟩
              obtain ⟨step, hstepRun, hshape⟩ := hstepData
              have hsectionInv := native_section_pass_preserves
                (((sourceColumns m).zip titles).zipIdx) cardFinal.2.1
                (sectionFor cardFinal.1 pad width (LayoutConst.kanban_card_gap.get m.profile)
                  (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile titles)
                  (LayoutConst.kanban_label_band_min.get m.profile)
                  (LayoutConst.kanban_section_min_height.get m.profile))
                pad step sectionFinal hshape hstepRun
              have hsectionIds := native_section_pass_ids
                (((sourceColumns m).zip titles).zipIdx) cardFinal.2.1
                (sectionFor cardFinal.1 pad width (LayoutConst.kanban_card_gap.get m.profile)
                  (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile titles)
                  (LayoutConst.kanban_label_band_min.get m.profile)
                  (LayoutConst.kanban_section_min_height.get m.profile))
                pad step sectionFinal hshape hstepRun
              have hidFinal : sectionFinal.1.map (·.1) =
                  (sourceCards m).map (·.id) ++ (sourceColumns m).map (·.id) := by
                simpa [hcardIds, section_inputs_ids (sourceColumns m) titles htlen] using hsectionIds
              have hvalue := Except.ok.inj h
              exact ⟨⟨width, pad, titles, texts, cardFinal, sectionFinal, hw0, hp0, hcw,
                hroots, htlen, hxlen, hcardInv, hsectionInv, hcardIds, hidFinal,
                hcardOwners, native_section_pass_retains_cards _ _ _ pad step sectionFinal
                  hshape hstepRun,
                native_section_pass_placements _ _ _ pad step sectionFinal hshape hstepRun,
                hvalue.symm⟩⟩

theorem NativeRunData.placement_unique {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m) :
    (run.sectionFinal.1.map (·.1)).Nodup :=
  partition_placement_unique m run.sectionFinal.1
    (fun b => b.role == .group || b.parent == "") hw run.sectionIds

theorem NativeRunData.placement_covers {m : Model} {value : Scene}
    (run : NativeRunData m value) :
    ∀ b ∈ m.boxes, ∃ r, (b.id, r) ∈ run.sectionFinal.1 :=
  partition_placement_covers m run.sectionFinal.1
    (fun b => b.role == .group || b.parent == "") run.sectionIds

theorem NativeRunData.card_containment {m : Model} {value : Scene}
    (run : NativeRunData m value) :
    ∀ entry ∈ run.cardFinal.2.1,
      (Kinds.Kanban.sectionRect run.pad run.width
        (LayoutConst.kanban_card_gap.get m.profile)
        (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile run.titles)
        (LayoutConst.kanban_label_band_min.get m.profile)
        (LayoutConst.kanban_section_min_height.get m.profile)
        (run.cardFinal.1.getD
          (ownerIndex (sourceColumns m) (sourceCards m) entry.1) (bandFrom m.profile run.titles))
        (ownerIndex (sourceColumns m) (sourceCards m) entry.1)).Contained entry.2 := by
  exact native_placed_card_containment _ _ _ _ _ _ _ _ _ _ _
    run.cardGeometry.2.1 run.cardGeometry.2.2
    (native_band_nonnegative m.profile run.titles)
    (native_card_width_bounds m.profile run.width run.cardWidthPositive).2
    (kanban_native_header_clearance m.profile)

theorem NativeRunData.cards_disjoint {m : Model} {value : Scene}
    (run : NativeRunData m value) (a b : String × Rect)
    (ha : a ∈ run.cardFinal.2.1) (hb : b ∈ run.cardFinal.2.1)
    (hne : a.1 ≠ b.1)
    (howner : ownerIndex (sourceColumns m) (sourceCards m) a.1 =
      ownerIndex (sourceColumns m) (sourceCards m) b.1) : Disjoint a.2 b.2 :=
  native_card_members_disjoint _ _ a b
    (native_card_pairwise _ _ _ _ _ _ run.cardGeometry.2.1) ha hb hne howner

theorem NativeRunData.section_in_canvas {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m) (input : SectionInput)
    (hi : input ∈ ((sourceColumns m).zip run.titles).zipIdx) :
    (⟨0, 0, run.sectionFinal.2.2.1 + run.pad,
      run.sectionFinal.2.2.2 + run.pad⟩ : Rect).Contained
      (sectionFor run.cardFinal.1 run.pad run.width
        (LayoutConst.kanban_card_gap.get m.profile)
        (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile run.titles)
        (LayoutConst.kanban_label_band_min.get m.profile)
        (LayoutConst.kanban_section_min_height.get m.profile) input) := by
  let rectFor := sectionFor run.cardFinal.1 run.pad run.width
    (LayoutConst.kanban_card_gap.get m.profile)
    (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile run.titles)
    (LayoutConst.kanban_label_band_min.get m.profile)
    (LayoutConst.kanban_section_min_height.get m.profile)
  have he : (input.1.1.id, rectFor input) ∈ run.sectionFinal.1 := by
    rw [run.sectionPlacements]
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨input, hi, rfl⟩))
  have hbaseNot : (input.1.1.id, rectFor input) ∉ run.cardFinal.2.1 := by
    intro hb
    have hid : input.1.1.id ∈ (sourceCards m).map (·.id) := by
      rw [← run.cardIds]
      exact List.mem_map.mpr ⟨_, hb, rfl⟩
    obtain ⟨card, hc, heq⟩ := List.mem_map.mp hid
    have hinput : input.1 ∈ (sourceColumns m).zip run.titles := by
      have hm : input.1 ∈ (((sourceColumns m).zip run.titles).zipIdx).map (·.1) :=
        List.mem_map.mpr ⟨input, hi, rfl⟩
      rw [List.zipIdx_map_fst] at hm
      exact hm
    have hcol := (List.of_mem_zip hinput).1
    have hcardLookup := model_lookup_self m.boxes card (model_ids_nodup m hw)
      (List.mem_filter.mp hc).1
    have hcolLookup := model_lookup_self m.boxes input.1.1 (model_ids_nodup m hw)
      (List.mem_filter.mp hcol).1
    rw [heq, hcolLookup] at hcardLookup
    have hsame : input.1.1 = card := Option.some.inj hcardLookup
    have hcnot := (List.mem_filter.mp hc).2
    have hcolyes := (List.mem_filter.mp hcol).2
    rw [hsame] at hcolyes
    change (!(card.role == .group || card.parent == "")) = true at hcnot
    change (card.role == .group || card.parent == "") = true at hcolyes
    simp [hcolyes] at hcnot
  obtain ⟨_, _, hentries⟩ := run.sectionGeometry
  rcases hentries (input.1.1.id, rectFor input) he with hb | ⟨other, _, heq, hr, hb⟩
  · exact False.elim (hbaseNot hb)
  · have hx := section_origin_nonnegative run.pad run.width
      (LayoutConst.kanban_card_gap.get m.profile)
      (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile run.titles)
      (LayoutConst.kanban_label_band_min.get m.profile)
      (LayoutConst.kanban_section_min_height.get m.profile)
      (run.cardFinal.1.getD input.2 (bandFrom m.profile run.titles)) input.2
      run.padNonnegative run.widthNonnegative (native_parameters_nonnegative m.profile).2.1
    change 0 ≤ (rectFor input).x ∧ 0 ≤ (rectFor input).y at hx
    change (rectFor input).x + (rectFor input).w ≤ run.sectionFinal.2.2.1 at hr
    change (rectFor input).y + (rectFor input).h ≤ run.sectionFinal.2.2.2 at hb
    change (⟨0, 0, run.sectionFinal.2.2.1 + run.pad,
      run.sectionFinal.2.2.2 + run.pad⟩ : Rect).Contained (rectFor input)
    dsimp [Rect.Contained]
    have hp := run.padNonnegative
    omega

theorem NativeRunData.card_lookup {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m)
    (entry : String × Rect) (he : entry ∈ run.cardFinal.2.1) :
    Kinds.Kanban.placedRect run.sectionFinal.1 entry.1 = entry.2 :=
  placedRect_eq_of_mem _ _ _ (run.placement_unique hw) (run.retainedCards entry he)

theorem NativeRunData.section_lookup {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m) (input : SectionInput)
    (hi : input ∈ ((sourceColumns m).zip run.titles).zipIdx) :
    Kinds.Kanban.placedRect run.sectionFinal.1 input.1.1.id =
      sectionFor run.cardFinal.1 run.pad run.width
        (LayoutConst.kanban_card_gap.get m.profile)
        (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile run.titles)
        (LayoutConst.kanban_label_band_min.get m.profile)
        (LayoutConst.kanban_section_min_height.get m.profile) input := by
  apply placedRect_eq_of_mem _ _ _ (run.placement_unique hw)
  rw [run.sectionPlacements]
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨input, hi, rfl⟩))

theorem NativeRunData.card_owner {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m)
    (entry : String × Rect) (he : entry ∈ run.cardFinal.2.1) :
    ∃ card ∈ sourceCards m, ∃ owner,
      entry.1 = card.id ∧
      (sourceColumns m).findIdx? (fun col => col.id == card.parent) = some owner ∧
      ownerIndex (sourceColumns m) (sourceCards m) entry.1 = owner := by
  obtain ⟨card, hc, owner, hid, ho⟩ := run.cardOwners entry he
  refine ⟨card, hc, owner, hid, ho, ?_⟩
  rw [hid]
  exact ownerIndex_spec _ _ card owner (source_card_ids_nodup m hw) hc ho

theorem NativeRunData.same_parent_cards_disjoint {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m)
    (a b : ModelBox) (ha : a ∈ sourceCards m) (hb : b ∈ sourceCards m)
    (ar br : Rect) (har : (a.id, ar) ∈ run.cardFinal.2.1)
    (hbr : (b.id, br) ∈ run.cardFinal.2.1) (hne : a.id ≠ b.id)
    (hparent : a.parent = b.parent) : Disjoint ar br := by
  apply run.cards_disjoint (a.id, ar) (b.id, br) har hbr hne
  simp only [ownerIndex, model_lookup_self (sourceCards m) a
    (source_card_ids_nodup m hw) ha, model_lookup_self (sourceCards m) b
    (source_card_ids_nodup m hw) hb]
  rw [hparent]

theorem NativeRunData.relational_clauses {m : Model} {value : Scene}
    (run : NativeRunData m value) :
    Validator.C4 value.layoutDump ∧ Validator.C5 value.layoutDump ∧
      Validator.C6 value.layoutDump ∧ Validator.C7 value.layoutDump ∧
      Validator.C8b value.layoutDump := by
  rw [run.assembled]
  exact assemble_relational_clauses _ _ _ _

theorem NativeRunData.card_in_canvas {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m)
    (entry : String × Rect) (he : entry ∈ run.cardFinal.2.1) :
    (⟨0, 0, run.sectionFinal.2.2.1 + run.pad,
      run.sectionFinal.2.2.2 + run.pad⟩ : Rect).Contained entry.2 := by
  obtain ⟨card, _, owner, _, ho, hindex⟩ := run.card_owner hw entry he
  obtain ⟨hi, _⟩ := owner_lookup_spec (sourceColumns m) card.parent owner ho
  obtain ⟨input, hinput, hposition, _⟩ :=
    measured_section_at (sourceColumns m) run.titles run.titleCount owner hi
  have hframe := run.section_in_canvas hw input hinput
  have hcard := run.card_containment entry he
  rw [hindex] at hcard
  have hinside : (sectionFor run.cardFinal.1 run.pad run.width
      (LayoutConst.kanban_card_gap.get m.profile)
      (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile run.titles)
      (LayoutConst.kanban_label_band_min.get m.profile)
      (LayoutConst.kanban_section_min_height.get m.profile) input).Contained entry.2 := by
    simpa only [sectionFor, hposition] using hcard
  exact Rect.Contained.trans hframe hinside

theorem NativeRunData.canvas_coverage {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m) :
    ∀ b ∈ m.boxes, ∃ r, (b.id, r) ∈ run.sectionFinal.1 ∧
      (⟨0, 0, run.sectionFinal.2.2.1 + run.pad,
        run.sectionFinal.2.2.2 + run.pad⟩ : Rect).Contained r := by
  intro b hb
  obtain ⟨r, hr⟩ := run.placement_covers b hb
  refine ⟨r, hr, ?_⟩
  have hsplit := hr
  rw [run.sectionPlacements] at hsplit
  rcases List.mem_append.mp hsplit with hcard | hsection
  · exact run.card_in_canvas hw (b.id, r) hcard
  · obtain ⟨input, hi, heq⟩ := List.mem_map.mp hsection
    have hrect : sectionFor run.cardFinal.1 run.pad run.width
        (LayoutConst.kanban_card_gap.get m.profile)
        (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile run.titles)
        (LayoutConst.kanban_label_band_min.get m.profile)
        (LayoutConst.kanban_section_min_height.get m.profile) input = r :=
      congrArg Prod.snd heq
    rw [← hrect]
    exact run.section_in_canvas hw input hi

theorem NativeRunData.canvas_clause {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m) :
    Validator.C1 value.layoutDump := by
  rw [run.assembled]
  exact canvas_from_placement_coverage _ _ _ _ (run.placement_unique hw)
    (run.canvas_coverage hw)

theorem model_boxes_eq_of_id {m : Model} (hw : Elegant.WellFormed m)
    {a b : ModelBox} (ha : a ∈ m.boxes) (hb : b ∈ m.boxes) (hid : a.id = b.id) :
    a = b := by
  have hlookup := model_lookup_self m.boxes a (model_ids_nodup m hw) ha
  rw [hid, model_lookup_self m.boxes b (model_ids_nodup m hw) hb] at hlookup
  exact (Option.some.inj hlookup).symm

theorem NativeRunData.nonroot_is_card {m : Model} {value : Scene}
    (run : NativeRunData m value) (b : ModelBox) (hb : b ∈ m.boxes)
    (hp : b.parent ≠ "") : b ∈ sourceCards m := by
  apply List.mem_filter.mpr
  refine ⟨hb, ?_⟩
  by_cases hs : (b.role == .group || b.parent == "") = true
  · have hcol : b ∈ sourceColumns m := List.mem_filter.mpr ⟨hb, hs⟩
    exact False.elim (hp (run.roots b hcol))
  · simp [hs]

theorem NativeRunData.parent_coverage {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m) :
    ∀ b ∈ m.boxes, b.parent ≠ "" → ∀ p ∈ m.boxes, p.id = b.parent →
      ∃ child outer, (b.id, child) ∈ run.sectionFinal.1 ∧
        (p.id, outer) ∈ run.sectionFinal.1 ∧ outer.Contained child := by
  intro b hb hparent p _ hp
  have hcard := run.nonroot_is_card b hb hparent
  have hid : b.id ∈ run.cardFinal.2.1.map (·.1) := by
    rw [run.cardIds]
    exact List.mem_map.mpr ⟨b, hcard, rfl⟩
  obtain ⟨entry, he, heid⟩ := List.mem_map.mp hid
  obtain ⟨card, hc, owner, hcardid, ho, howner⟩ := run.card_owner hw entry he
  have hsame : card = b := model_boxes_eq_of_id hw (List.mem_filter.mp hc).1 hb
    (hcardid.symm.trans heid)
  subst card
  obtain ⟨hi, hownerid⟩ := owner_lookup_spec (sourceColumns m) b.parent owner ho
  obtain ⟨input, hinput, hposition, hcolumn⟩ :=
    measured_section_at (sourceColumns m) run.titles run.titleCount owner hi
  let outer := sectionFor run.cardFinal.1 run.pad run.width
    (LayoutConst.kanban_card_gap.get m.profile)
    (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile run.titles)
    (LayoutConst.kanban_label_band_min.get m.profile)
    (LayoutConst.kanban_section_min_height.get m.profile) input
  have houterid : input.1.1.id = p.id := by rw [hcolumn, hownerid, hp]
  have houter : (p.id, outer) ∈ run.sectionFinal.1 := by
    rw [run.sectionPlacements]
    apply List.mem_append.mpr
    right
    exact List.mem_map.mpr ⟨input, hinput, by simp only [houterid]; rfl⟩
  refine ⟨entry.2, outer, ?_, houter, ?_⟩
  · have hretained := run.retainedCards entry he
    cases entry with
    | mk id rect =>
      dsimp at heid
      subst id
      exact hretained
  · have hcontains := run.card_containment entry he
    simpa only [outer, sectionFor, hposition, howner] using hcontains

theorem NativeRunData.parent_clause {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m) :
    Validator.C3 value.layoutDump := by
  rw [run.assembled]
  exact parent_from_placement_coverage _ _ _ _ (run.placement_unique hw)
    (run.parent_coverage hw)

def NativeRunData.frame {m : Model} {value : Scene}
    (run : NativeRunData m value) (input : SectionInput) : Rect :=
  sectionFor run.cardFinal.1 run.pad run.width
    (LayoutConst.kanban_card_gap.get m.profile)
    (LayoutConst.kanban_gutter.get m.profile) (bandFrom m.profile run.titles)
    (LayoutConst.kanban_label_band_min.get m.profile)
    (LayoutConst.kanban_section_min_height.get m.profile) input

theorem NativeRunData.column_placement {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m)
    (b : ModelBox) (hb : b ∈ sourceColumns m) :
    ∃ input ∈ ((sourceColumns m).zip run.titles).zipIdx,
      input.1.1.id = b.id ∧
        Kinds.Kanban.placedRect run.sectionFinal.1 b.id = run.frame input := by
  obtain ⟨r, hr⟩ := run.placement_covers b (List.mem_filter.mp hb).1
  rw [run.sectionPlacements] at hr
  rcases List.mem_append.mp hr with hc | hs
  · have hid : b.id ∈ (sourceCards m).map (·.id) := by
      rw [← run.cardIds]
      exact List.mem_map.mpr ⟨(b.id, r), hc, rfl⟩
    obtain ⟨card, hcard, heq⟩ := List.mem_map.mp hid
    have he := model_boxes_eq_of_id hw (List.mem_filter.mp hcard).1
      (List.mem_filter.mp hb).1 heq
    subst card
    have hno := (List.mem_filter.mp hcard).2
    have hyes := (List.mem_filter.mp hb).2
    change (!(b.role == .group || b.parent == "")) = true at hno
    change (b.role == .group || b.parent == "") = true at hyes
    simp [hyes] at hno
  · obtain ⟨input, hi, he⟩ := List.mem_map.mp hs
    have hid : input.1.1.id = b.id := congrArg Prod.fst he
    refine ⟨input, hi, hid, ?_⟩
    rw [← hid]
    exact run.section_lookup hw input hi

theorem NativeRunData.card_placement {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m)
    (b : ModelBox) (hb : b ∈ sourceCards m) :
    ∃ input ∈ ((sourceColumns m).zip run.titles).zipIdx,
      input.1.1.id = b.parent ∧
        (run.frame input).Contained (Kinds.Kanban.placedRect run.sectionFinal.1 b.id) ∧
        (b.id, Kinds.Kanban.placedRect run.sectionFinal.1 b.id) ∈ run.cardFinal.2.1 := by
  have hid : b.id ∈ run.cardFinal.2.1.map (·.1) := by
    rw [run.cardIds]
    exact List.mem_map.mpr ⟨b, hb, rfl⟩
  obtain ⟨⟨id, r⟩, he, hid⟩ := List.mem_map.mp hid
  dsimp at hid
  subst id
  obtain ⟨card, hc, owner, hcardid, ho, howner⟩ := run.card_owner hw (b.id, r) he
  have hsame : card = b := model_boxes_eq_of_id hw (List.mem_filter.mp hc).1
    (List.mem_filter.mp hb).1 hcardid.symm
  subst card
  obtain ⟨hi, hownerid⟩ := owner_lookup_spec (sourceColumns m) b.parent owner ho
  obtain ⟨input, hinput, hposition, hcolumn⟩ :=
    measured_section_at (sourceColumns m) run.titles run.titleCount owner hi
  have hlookup := run.card_lookup hw (b.id, r) he
  refine ⟨input, hinput, by rw [hcolumn, hownerid], ?_, ?_⟩
  · rw [hlookup]
    have hcontains := run.card_containment (b.id, r) he
    simpa only [NativeRunData.frame, sectionFor, hposition, howner] using hcontains
  · rw [hlookup]
    exact he

theorem NativeRunData.frames_disjoint {m : Model} {value : Scene}
    (run : NativeRunData m value) (a b : SectionInput)
    (ha : a ∈ ((sourceColumns m).zip run.titles).zipIdx)
    (hb : b ∈ ((sourceColumns m).zip run.titles).zipIdx)
    (hne : a.1.1.id ≠ b.1.1.id) :
    Disjoint (run.frame a) (run.frame b) := by
  by_cases he : a.2 = b.2
  · have hgetA := List.mem_zipIdx_iff_getElem?.mp ha
    have hgetB := List.mem_zipIdx_iff_getElem?.mp hb
    rw [he, hgetB] at hgetA
    have hsame := Option.some.inj hgetA
    exact False.elim (hne (congrArg (fun input => input.1.id) hsame.symm))
  · rcases Nat.lt_or_gt_of_ne he with hab | hba
    · exact kanban_columns_disjoint_final _ _ _ _ _ _ _ _ _ _ _
        run.widthNonnegative (native_parameters_nonnegative m.profile).2.1 hab
    · exact (Disjoint.comm _ _).mp
        (kanban_columns_disjoint_final _ _ _ _ _ _ _ _ _ _ _
          run.widthNonnegative (native_parameters_nonnegative m.profile).2.1 hba)

theorem source_card_nonroot {m : Model} {b : ModelBox} (hb : b ∈ sourceCards m) :
    b.parent ≠ "" := by
  intro hp
  have hno := (List.mem_filter.mp hb).2
  change (!(b.role == .group || b.parent == "")) = true at hno
  simp [hp] at hno

theorem NativeRunData.sibling_rects {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m)
    (a : ModelBox) (ha : a ∈ m.boxes) (b : ModelBox) (hb : b ∈ m.boxes)
    (hne : a.id ≠ b.id) (hparent : a.parent = b.parent) :
    Disjoint (Kinds.Kanban.placedRect run.sectionFinal.1 a.id)
      (Kinds.Kanban.placedRect run.sectionFinal.1 b.id) := by
  by_cases hac : (a.role == .group || a.parent == "") = true
  · have hasec : a ∈ sourceColumns m := List.mem_filter.mpr ⟨ha, hac⟩
    by_cases hbc : (b.role == .group || b.parent == "") = true
    · have hbsec : b ∈ sourceColumns m := List.mem_filter.mpr ⟨hb, hbc⟩
      obtain ⟨ai, hai, haid, har⟩ := run.column_placement hw a hasec
      obtain ⟨bi, hbi, hbid, hbr⟩ := run.column_placement hw b hbsec
      rw [har, hbr]
      exact run.frames_disjoint ai bi hai hbi (by simpa only [haid, hbid] using hne)
    · have hbcard : b ∈ sourceCards m :=
        List.mem_filter.mpr ⟨hb, by simp [hbc]⟩
      exact False.elim (source_card_nonroot hbcard (hparent ▸ run.roots a hasec))
  · have hacard : a ∈ sourceCards m :=
      List.mem_filter.mpr ⟨ha, by simp [hac]⟩
    by_cases hbc : (b.role == .group || b.parent == "") = true
    · have hbsec : b ∈ sourceColumns m := List.mem_filter.mpr ⟨hb, hbc⟩
      exact False.elim (source_card_nonroot hacard (hparent.symm ▸ run.roots b hbsec))
    · have hbcard : b ∈ sourceCards m :=
        List.mem_filter.mpr ⟨hb, by simp [hbc]⟩
      obtain ⟨_, _, _, _, har⟩ := run.card_placement hw a hacard
      obtain ⟨_, _, _, _, hbr⟩ := run.card_placement hw b hbcard
      exact run.same_parent_cards_disjoint hw a b hacard hbcard _ _ har hbr hne hparent

theorem NativeRunData.foreign_rects {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m)
    (g : ModelBox) (hg : g ∈ m.boxes) (hrole : g.role.id = "group")
    (b : ModelBox) (hb : b ∈ m.boxes) (hne : b.id ≠ g.id)
    (hparent : b.parent = "" ∨ b.parent ≠ g.id) :
    Disjoint (Kinds.Kanban.placedRect run.sectionFinal.1 g.id)
      (Kinds.Kanban.placedRect run.sectionFinal.1 b.id) := by
  have hgroup : g.role = .group := by
    cases hr : g.role <;> simp_all [BoxRole.id]
  have hgsec : g ∈ sourceColumns m := List.mem_filter.mpr ⟨hg, by simp [hgroup]⟩
  obtain ⟨gi, hgi, hgid, hgr⟩ := run.column_placement hw g hgsec
  by_cases hbc : (b.role == .group || b.parent == "") = true
  · have hbsec : b ∈ sourceColumns m := List.mem_filter.mpr ⟨hb, hbc⟩
    obtain ⟨bi, hbi, hbid, hbr⟩ := run.column_placement hw b hbsec
    rw [hgr, hbr]
    exact run.frames_disjoint gi bi hgi hbi (by
      intro he
      exact hne (hbid.symm.trans (he.symm.trans hgid)))
  · have hbcard : b ∈ sourceCards m :=
      List.mem_filter.mpr ⟨hb, by simp [hbc]⟩
    obtain ⟨bi, hbi, hbid, hinside, _⟩ := run.card_placement hw b hbcard
    have hpne : b.parent ≠ g.id := by
      rcases hparent with hempty | hne
      · exact False.elim (source_card_nonroot hbcard hempty)
      · exact hne
    rw [hgr]
    exact disjoint_contained_right _ _ _
      (run.frames_disjoint gi bi hgi hbi (by
        intro he
        exact hpne (hbid.symm.trans (he.symm.trans hgid)))) hinside

theorem NativeRunData.placement_evidence {m : Model} {value : Scene}
    (run : NativeRunData m value) (hw : Elegant.WellFormed m) :
    PlacementEvidence m
      ⟨run.sectionFinal.2.2.1 + run.pad, run.sectionFinal.2.2.2 + run.pad⟩
      run.sectionFinal.1 := by
  refine ⟨run.placement_unique hw, run.canvas_coverage hw, ?_,
    run.parent_coverage hw, run.foreign_rects hw⟩
  intro a ha b hb hne _ _ hparent
  obtain ⟨ar, har⟩ := run.placement_covers a ha
  obtain ⟨br, hbr⟩ := run.placement_covers b hb
  refine ⟨ar, br, har, hbr, ?_⟩
  have hd := run.sibling_rects hw a ha b hb hne hparent
  rw [placedRect_eq_of_mem _ _ _ (run.placement_unique hw) har,
    placedRect_eq_of_mem _ _ _ (run.placement_unique hw) hbr] at hd
  exact hd

theorem kanban_valid {m : Model} {result : Layered.FamilyResult}
    (hw : Elegant.WellFormed m) (_hl : WithinLimits m)
    (h : Kinds.Kanban.layout m = .ok result) :
    HardConstraints result.scene.layoutDump := by
  obtain ⟨hs, _, _⟩ := Kinds.Kanban.layout_spec h
  obtain ⟨run⟩ := scene_phase_invariants hw hs
  rw [run.assembled]
  exact assemble_valid_from_coverage _ _ _ _ hw (run.placement_evidence hw)

end Elegant.GridKanban

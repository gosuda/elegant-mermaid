import Elegant.GridKanban

set_option autoImplicit false

namespace Elegant.GridKanban

/-- The dump lookup returns the placement belonging to an id, not a default rectangle,
when the placement pass emitted that id once. -/
theorem placedRect_eq_of_mem (placed : List (String × Rect)) (id : String) (r : Rect)
    (hunique : (placed.map (·.1)).Nodup) (hmem : (id, r) ∈ placed) :
    Kinds.Kanban.placedRect placed id = r := by
  induction placed with
  | nil => simp at hmem
  | cons first rest ih =>
    obtain ⟨hfresh, hrest⟩ := List.nodup_cons.mp hunique
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · simp [Kinds.Kanban.placedRect]
    · have hne : first.1 ≠ id := by
        intro heq
        exact hfresh (List.mem_map.mpr ⟨(id, r), hmem, heq.symm⟩)
      have hr := ih hrest hmem
      simpa [Kinds.Kanban.placedRect, hne] using hr

/-- The assembly phase preserves every semantic field authored by the model. -/
theorem assemble_metadata (m : Model) (canvas : Size) (placed : List (String × Rect))
    (groups : List Group) :
    ((Kinds.Kanban.assemble m canvas placed groups).boxes.map
      (fun b => (b.id, b.role, b.parent, b.exclusive))) =
      m.boxes.map (fun b => (b.id, b.role.id, b.parent, b.exclusive)) := by
  simp [Kinds.Kanban.assemble, Kinds.Kanban.sceneBox, List.map_map]

/-- Geometric bounds proved on emitted placements transfer to each original model box. -/
theorem model_placement_bounds (m : Model) (placed : List (String × Rect)) (bound : Rect → Prop)
    (hunique : (placed.map (·.1)).Nodup)
    (hcover : ∀ b ∈ m.boxes, ∃ r, (b.id, r) ∈ placed ∧ bound r) :
    ∀ b ∈ m.boxes, bound (Kinds.Kanban.placedRect placed b.id) := by
  intro b hb
  obtain ⟨r, hr, hbound⟩ := hcover b hb
  rw [placedRect_eq_of_mem placed b.id r hunique hr]
  exact hbound

/-- Lookup membership lets the canvas proof use the native max fold over emitted frames. -/
theorem canvas_from_placement_coverage (m : Model) (canvas : Size)
    (placed : List (String × Rect)) (groups : List Group)
    (hunique : (placed.map (·.1)).Nodup)
    (hcover : ∀ b ∈ m.boxes, ∃ r, (b.id, r) ∈ placed ∧
      (⟨0, 0, canvas.w, canvas.h⟩ : Rect).Contained r) :
    Validator.C1 (Kinds.Kanban.assemble m canvas placed groups).layoutDump :=
  assemble_canvas_transfer m canvas placed groups
    (model_placement_bounds m placed _ hunique hcover)

/-- Parent containment is established on the two emitted rectangles before the dump
uses its id lookup; this transports the same rectangles without changing the relation. -/
theorem parent_from_placement_coverage (m : Model) (canvas : Size)
    (placed : List (String × Rect)) (groups : List Group)
    (hunique : (placed.map (·.1)).Nodup)
    (hcover : ∀ b ∈ m.boxes, b.parent ≠ "" → ∀ p ∈ m.boxes, p.id = b.parent →
      ∃ child outer, (b.id, child) ∈ placed ∧ (p.id, outer) ∈ placed ∧ outer.Contained child) :
    Validator.C3 (Kinds.Kanban.assemble m canvas placed groups).layoutDump := by
  apply assemble_parent_transfer
  intro b hb hparent p hp heq
  obtain ⟨child, outer, hc, ho, hcontains⟩ := hcover b hb hparent p hp heq
  rw [placedRect_eq_of_mem placed p.id outer hunique ho,
    placedRect_eq_of_mem placed b.id child hunique hc]
  exact hcontains

/-- The placement loops preserve a state predicate on every successful iteration. -/
theorem forIn_preserves {α β : Type} (inputs : List α)
    (step : α → β → Except LayoutError (ForInStep β)) (invariant : β → Prop)
    (initial final : β) (hinit : invariant initial)
    (hstep : ∀ a ∈ inputs, ∀ state next, invariant state →
      step a state = .ok next → invariant next.value)
    (hrun : forIn inputs initial step = .ok final) : invariant final := by
  induction inputs generalizing initial with
  | nil =>
    have heq : initial = final := by
      simpa only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] using hrun
    simpa [← heq] using hinit
  | cons a inputs ih =>
    rw [List.forIn_cons] at hrun
    cases hs : step a initial with
    | error error => simp [hs, bind, Except.bind] at hrun
    | ok next =>
      have hinext := hstep a (by simp) initial next hinit hs
      cases next with
      | done state =>
        have heq : state = final := by
          simpa [hs, bind, Except.bind, pure, Except.pure] using hrun
        simpa [← heq] using hinext
      | yield state =>
        have hrest : ∀ b ∈ inputs, ∀ old new, invariant old →
            step b old = .ok new → invariant new.value := by
          intro b hb old new hold hnew
          exact hstep b (by simp [hb]) old new hold hnew
        have htail : forIn inputs state step = .ok final := by
          simpa [hs, bind, Except.bind] using hrun
        exact ih state hinext hrest htail

theorem siblings_from_placement_coverage (m : Model) (canvas : Size)
    (placed : List (String × Rect)) (groups : List Group)
    (hunique : (placed.map (·.1)).Nodup)
    (hcover : ∀ a ∈ m.boxes, ∀ b ∈ m.boxes,
      a.id ≠ b.id → a.exclusive = true → b.exclusive = true → a.parent = b.parent →
      ∃ ar br, (a.id, ar) ∈ placed ∧ (b.id, br) ∈ placed ∧ Disjoint ar br) :
    Validator.C2 (Kinds.Kanban.assemble m canvas placed groups).layoutDump := by
  apply assemble_siblings_transfer
  intro a ha b hb hne hae hbe hparent
  obtain ⟨ar, br, har, hbr, hd⟩ := hcover a ha b hb hne hae hbe hparent
  rw [placedRect_eq_of_mem placed a.id ar hunique har,
    placedRect_eq_of_mem placed b.id br hunique hbr]
  exact hd

theorem box_lookup_self (boxes : List Box) (b : Box)
    (hunique : (boxes.map (·.id)).Nodup) (hmem : b ∈ boxes) :
    boxes.find? (fun candidate => candidate.id == b.id) = some b := by
  induction boxes with
  | nil => simp at hmem
  | cons first rest ih =>
    obtain ⟨hfresh, hrest⟩ := List.nodup_cons.mp hunique
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · simp
    · have hne : first.id ≠ b.id := by
        intro heq
        exact hfresh (List.mem_map.mpr ⟨b, hmem, heq.symm⟩)
      simpa [hne] using ih hrest hmem

theorem parent_mem_ancestors {d : LayoutDump} {b : Box}
    (hlookup : d.box? b.id = some b) (hparent : b.parent ≠ "") :
    b.parent ∈ d.ancestors b.id := by
  cases hboxes : d.boxes with
  | nil => simp [LayoutDump.box?, hboxes] at hlookup
  | cons first rest =>
    simp [LayoutDump.ancestors, LayoutDump.ancestors.go, hboxes, hlookup, hparent]

theorem assemble_foreign_transfer (m : Model) (canvas : Size)
    (placed : List (String × Rect)) (groups : List Group)
    (hunique : (m.boxes.map (·.id)).Nodup)
    (hrect : ∀ g ∈ m.boxes, g.role.id = "group" → ∀ b ∈ m.boxes,
      b.id ≠ g.id → (b.parent = "" ∨ b.parent ≠ g.id) →
      Disjoint (Kinds.Kanban.placedRect placed g.id) (Kinds.Kanban.placedRect placed b.id)) :
    Validator.C8a (Kinds.Kanban.assemble m canvas placed groups).layoutDump := by
  let d := (Kinds.Kanban.assemble m canvas placed groups).layoutDump
  have hdunique : (d.boxes.map (·.id)).Nodup := by
    simp only [d, Kinds.Kanban.assemble, Scene.layoutDump, List.map_map]
    change (m.boxes.map (·.id)).Nodup
    exact hunique
  intro g hg hrole b hb hne hnotChild _hnotAncestor
  have hlookup : d.box? b.id = some b := box_lookup_self d.boxes b hdunique hb
  have hparent : b.parent = "" ∨ b.parent ≠ g.id := by
    by_cases hempty : b.parent = ""
    · exact Or.inl hempty
    · refine Or.inr ?_
      intro heq
      have ha := parent_mem_ancestors hlookup hempty
      rw [heq] at ha
      exact hnotChild ha
  change g ∈ m.boxes.map (Kinds.Kanban.sceneBox placed) at hg
  change b ∈ m.boxes.map (Kinds.Kanban.sceneBox placed) at hb
  obtain ⟨originalG, hgm, rfl⟩ := List.mem_map.mp hg
  obtain ⟨originalB, hbm, rfl⟩ := List.mem_map.mp hb
  exact hrect originalG hgm hrole originalB hbm hne hparent

private theorem dedup_loop_sublist (xs seen : List String) :
    List.Sublist (List.eraseDupsBy.loop (fun a b : String => a == b) xs seen) (seen.reverse ++ xs) := by
  induction xs generalizing seen with
  | nil => simp [List.eraseDupsBy.loop]
  | cons a xs ih =>
    cases hseen : seen.any (fun b => a == b) with
    | true =>
      have hskip : List.Sublist (seen.reverse ++ xs) (seen.reverse ++ a :: xs) :=
        (List.Sublist.cons a (List.Sublist.refl xs)).append_left seen.reverse
      simpa [List.eraseDupsBy.loop, hseen] using (ih seen).trans hskip
    | false =>
      simpa [List.eraseDupsBy.loop, hseen, List.reverse_cons, List.append_assoc] using ih (a :: seen)

private theorem dedup_loop_nodup (xs seen : List String) (hseen : seen.Nodup) :
    (List.eraseDupsBy.loop (fun a b : String => a == b) xs seen).Nodup := by
  induction xs generalizing seen with
  | nil =>
    have hr : seen.reverse.Nodup :=
      List.pairwise_reverse.mpr (hseen.imp (fun h => Ne.symm h))
    simpa [List.eraseDupsBy.loop] using hr
  | cons a xs ih =>
    cases hfound : seen.any (fun b => a == b) with
    | true => simpa [List.eraseDupsBy.loop, hfound] using ih seen hseen
    | false =>
      have hfresh : a ∉ seen := by
        intro hmem
        have hany : seen.any (fun b => a == b) = true :=
          List.any_eq_true.mpr ⟨a, hmem, by simp⟩
        rw [hfound] at hany
        contradiction
      simpa [List.eraseDupsBy.loop, hfound] using
        ih (a :: seen) (List.nodup_cons.mpr ⟨hfresh, hseen⟩)

theorem nodup_of_dedup_length (ids : List String) (h : ids.eraseDups.length = ids.length) :
    ids.Nodup := by
  have hsub : List.Sublist ids.eraseDups ids := by
    simpa [List.eraseDups, List.eraseDupsBy] using dedup_loop_sublist ids []
  have hn : ids.eraseDups.Nodup := by
    simpa [List.eraseDups, List.eraseDupsBy] using dedup_loop_nodup ids [] (by simp)
  rw [hsub.eq_of_length h] at hn
  exact hn

theorem model_ids_nodup (m : Model) (hw : Elegant.WellFormed m) :
    (m.boxes.map (·.id)).Nodup := by
  have hh := hw
  simp only [Elegant.WellFormed, modelWellFormed, Bool.and_eq_true] at hh
  have hunique := hh.1.1.1.1.1.1
  change ((m.boxes.map (·.id)).eraseDups.length == (m.boxes.map (·.id)).length) = true at hunique
  exact nodup_of_dedup_length _ (by simpa only [beq_iff_eq] using hunique)

structure PlacementEvidence (m : Model) (canvas : Size) (placed : List (String × Rect)) : Prop where
  unique : (placed.map (·.1)).Nodup
  withinCanvas : ∀ b ∈ m.boxes, ∃ r, (b.id, r) ∈ placed ∧
    (⟨0, 0, canvas.w, canvas.h⟩ : Rect).Contained r
  siblings : ∀ a ∈ m.boxes, ∀ b ∈ m.boxes,
    a.id ≠ b.id → a.exclusive = true → b.exclusive = true → a.parent = b.parent →
    ∃ ar br, (a.id, ar) ∈ placed ∧ (b.id, br) ∈ placed ∧ Disjoint ar br
  parent : ∀ b ∈ m.boxes, b.parent ≠ "" → ∀ p ∈ m.boxes, p.id = b.parent →
    ∃ child outer, (b.id, child) ∈ placed ∧ (p.id, outer) ∈ placed ∧ outer.Contained child
  foreign : ∀ g ∈ m.boxes, g.role.id = "group" → ∀ b ∈ m.boxes,
    b.id ≠ g.id → (b.parent = "" ∨ b.parent ≠ g.id) →
    Disjoint (Kinds.Kanban.placedRect placed g.id) (Kinds.Kanban.placedRect placed b.id)

theorem assemble_valid_from_coverage (m : Model) (canvas : Size)
    (placed : List (String × Rect)) (groups : List Group)
    (hw : Elegant.WellFormed m) (he : PlacementEvidence m canvas placed) :
    HardConstraints (Kinds.Kanban.assemble m canvas placed groups).layoutDump :=
  assemble_valid m canvas placed groups
    (canvas_from_placement_coverage m canvas placed groups he.unique he.withinCanvas)
    (siblings_from_placement_coverage m canvas placed groups he.unique he.siblings)
    (parent_from_placement_coverage m canvas placed groups he.unique he.parent)
    (assemble_foreign_transfer m canvas placed groups (model_ids_nodup m hw) he.foreign)

/-- Each successful adapter iteration appends exactly its input box id. Thus a
successful loop has complete declaration-order coverage, even if other state changes. -/
theorem forIn_emits_ids {α β γ : Type} (inputs : List α)
    (step : α → β → Except LayoutError (ForInStep β))
    (key : α → γ) (ids : β → List γ) (initial final : β)
    (hstep : ∀ a ∈ inputs, ∀ state next, step a state = .ok next →
      ∃ value, next = .yield value ∧ ids value = ids state ++ [key a])
    (hrun : forIn inputs initial step = .ok final) :
    ids final = ids initial ++ inputs.map key := by
  induction inputs generalizing initial with
  | nil =>
    have heq : initial = final := by
      simpa only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] using hrun
    simp [← heq]
  | cons a inputs ih =>
    rw [List.forIn_cons] at hrun
    cases hs : step a initial with
    | error error => simp [hs, bind, Except.bind] at hrun
    | ok next =>
      obtain ⟨value, rfl, hids⟩ := hstep a (by simp) initial next hs
      have hrest : ∀ b ∈ inputs, ∀ old new, step b old = .ok new →
          ∃ value, new = .yield value ∧ ids value = ids old ++ [key b] := by
        intro b hb old new hnew
        exact hstep b (by simp [hb]) old new hnew
      have htail : forIn inputs value step = .ok final := by
        simpa [hs, bind, Except.bind] using hrun
      have hout := ih value hrest htail
      simpa [hids, List.append_assoc] using hout

theorem partition_placement_ids (m : Model) (placed : List (String × Rect))
    (selectColumn : ModelBox → Bool)
    (hids : placed.map (·.1) =
      (m.boxes.filter (fun b => !selectColumn b)).map (·.id) ++
        (m.boxes.filter selectColumn).map (·.id)) :
    (placed.map (·.1)).Perm (m.boxes.map (·.id)) := by
  rw [hids, ← List.map_append]
  exact (List.perm_append_comm.trans (List.filter_append_perm selectColumn m.boxes)).map (·.id)

theorem partition_placement_unique (m : Model) (placed : List (String × Rect))
    (selectColumn : ModelBox → Bool) (hw : Elegant.WellFormed m)
    (hids : placed.map (·.1) =
      (m.boxes.filter (fun b => !selectColumn b)).map (·.id) ++
        (m.boxes.filter selectColumn).map (·.id)) :
    (placed.map (·.1)).Nodup :=
  (partition_placement_ids m placed selectColumn hids).symm.nodup (model_ids_nodup m hw)

theorem partition_placement_covers (m : Model) (placed : List (String × Rect))
    (selectColumn : ModelBox → Bool)
    (hids : placed.map (·.1) =
      (m.boxes.filter (fun b => !selectColumn b)).map (·.id) ++
        (m.boxes.filter selectColumn).map (·.id)) :
    ∀ b ∈ m.boxes, ∃ r, (b.id, r) ∈ placed := by
  intro b hb
  have hid : b.id ∈ placed.map (·.1) :=
    (partition_placement_ids m placed selectColumn hids).mem_iff.mpr
      (List.mem_map.mpr ⟨b, hb, rfl⟩)
  obtain ⟨⟨id, r⟩, hr, heq⟩ := List.mem_map.mp hid
  dsimp at heq
  subst id
  exact ⟨r, hr⟩

theorem owner_lookup_spec (columns : List ModelBox) (parent : String) (index : Nat)
    (h : columns.findIdx? (fun col => col.id == parent) = some index) :
    ∃ hi : index < columns.length, (columns[index]'hi).id = parent := by
  obtain ⟨hi, hpred, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨hi, by simpa only [beq_iff_eq] using hpred⟩

theorem owner_lookup_same_parent (columns : List ModelBox) (parentA parentB : String)
    (i j : Nat) (heq : parentA = parentB)
    (ha : columns.findIdx? (fun col => col.id == parentA) = some i)
    (hb : columns.findIdx? (fun col => col.id == parentB) = some j) : i = j := by
  subst parentB
  rw [hb] at ha
  exact Option.some.inj ha.symm

/-- A successful geometry pass always reaches the single dump assembly point. -/
theorem scene_assembly {m : Model} {value : Scene} (h : Kinds.Kanban.scene m = .ok value) :
    ∃ canvas placed groups, value = Kinds.Kanban.assemble m canvas placed groups := by
  unfold Kinds.Kanban.scene at h
  dsimp only [Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure, Except.map,
    MonadExceptOf.throw] at h
  iterate 32 (all_goals first | (split at h) | (cases h) | skip)
  all_goals exact ⟨_, _, _, rfl⟩

theorem layout_preserves_metadata {m : Model} {result : Layered.FamilyResult}
    (h : Kinds.Kanban.layout m = .ok result) :
    result.scene.boxes.map (fun b => (b.id, b.role, b.parent, b.exclusive)) =
      m.boxes.map (fun b => (b.id, b.role.id, b.parent, b.exclusive)) := by
  obtain ⟨hs, _, _⟩ := Kinds.Kanban.layout_spec h
  obtain ⟨canvas, placed, groups, heq⟩ := scene_assembly hs
  rw [heq]
  exact assemble_metadata m canvas placed groups

theorem layout_relational_clauses {m : Model} {result : Layered.FamilyResult}
    (h : Kinds.Kanban.layout m = .ok result) :
    Validator.C4 result.scene.layoutDump ∧ Validator.C5 result.scene.layoutDump ∧
      Validator.C6 result.scene.layoutDump ∧ Validator.C7 result.scene.layoutDump ∧
      Validator.C8b result.scene.layoutDump := by
  obtain ⟨hs, _, _⟩ := Kinds.Kanban.layout_spec h
  obtain ⟨canvas, placed, groups, heq⟩ := scene_assembly hs
  rw [heq]
  exact assemble_relational_clauses m canvas placed groups

theorem native_parameters_nonnegative (profile : Profile) :
    0 ≤ LayoutConst.kanban_gutter.get profile ∧
    0 ≤ LayoutConst.kanban_card_gap.get profile ∧
    0 ≤ LayoutConst.line_h.get profile ∧
    0 ≤ LayoutConst.kanban_card_pad_y.get profile ∧
    0 ≤ LayoutConst.node_border.get profile := by
  cases profile <;> decide

theorem native_card_height_nonnegative (profile : Profile) (lineCount : Nat) :
    0 ≤ Int.ofNat (max 1 lineCount) * LayoutConst.line_h.get profile +
      2 * LayoutConst.kanban_card_pad_y.get profile + 2 * LayoutConst.node_border.get profile := by
  obtain ⟨_, _, hline, hpad, hborder⟩ := native_parameters_nonnegative profile
  have hn : 0 ≤ Int.ofNat (max 1 lineCount) := Int.natCast_nonneg _
  have hmul := Int.mul_nonneg hn hline
  omega

theorem native_band_lower_bound (profile : Profile) (titles : List (List Measure.Line)) :
    LayoutConst.kanban_label_band_min.get profile ≤
      titles.foldl (fun h ls => max h
        (Int.ofNat ls.length * LayoutConst.line_h.get profile +
          LayoutConst.node_border.get profile))
        (LayoutConst.kanban_label_band_min.get profile) := by
  simpa only [List.foldl_map] using
    max_fold_ge_init (titles.map (fun ls =>
      Int.ofNat ls.length * LayoutConst.line_h.get profile +
        LayoutConst.node_border.get profile))
      (LayoutConst.kanban_label_band_min.get profile)

theorem native_band_nonnegative (profile : Profile) (titles : List (List Measure.Line)) :
    0 ≤ titles.foldl (fun h ls => max h
      (Int.ofNat ls.length * LayoutConst.line_h.get profile +
        LayoutConst.node_border.get profile))
      (LayoutConst.kanban_label_band_min.get profile) := by
  have hminimum : 0 ≤ LayoutConst.kanban_label_band_min.get profile := by
    cases profile <;> decide
  exact Int.le_trans hminimum (native_band_lower_bound profile titles)

theorem config_units_nonnegative (profile : Profile) (px : Int) (hp : 0 ≤ px) :
    0 ≤ (if profile == .cell then Int.fdiv (px + 7) 8 else px * 64) := by
  split
  · exact Int.fdiv_nonneg (by omega) (by decide)
  · exact Int.mul_nonneg hp (by decide)

theorem native_card_width_bounds (profile : Profile) (width : Int)
    (hpositive : 0 < width - Int.fdiv (3 * LayoutConst.kanban_gutter.get profile) 2) :
    0 ≤ width ∧ width - Int.fdiv (3 * LayoutConst.kanban_gutter.get profile) 2 ≤ width := by
  have hg := (native_parameters_nonnegative profile).1
  have hf : 0 ≤ Int.fdiv (3 * LayoutConst.kanban_gutter.get profile) 2 :=
    Int.fdiv_nonneg (by omega) (by decide)
  omega

theorem section_origin_nonnegative (pad width gap gutter band minimum minHeight cursor : Int)
    (index : Nat) (hp : 0 ≤ pad) (hw : 0 ≤ width) (hg : 0 ≤ gap) :
    0 ≤ (Kinds.Kanban.sectionRect pad width gap gutter band minimum minHeight cursor index).x ∧
      0 ≤ (Kinds.Kanban.sectionRect pad width gap gutter band minimum minHeight cursor index).y := by
  have hi : 0 ≤ Int.ofNat index := Int.natCast_nonneg _
  have hm := Int.mul_nonneg hi (show 0 ≤ width + gap by omega)
  change 0 ≤ pad + Int.ofNat index * (width + gap) ∧ 0 ≤ pad
  omega

theorem configured_spec {m : Model} {key : String} {fallback value : Int}
    (hf : 0 ≤ fallback) (hb : fallback ≤ COORD_LIMIT)
    (h : Kinds.Kanban.configured m key fallback = .ok value) :
    0 ≤ value ∧ value ≤ COORD_LIMIT := by
  unfold Kinds.Kanban.configured at h
  cases he : m.options.config.find? (fun entry => entry.1 == key) with
  | none =>
    simp only [he, Pure.pure, Except.pure] at h
    cases h
    exact ⟨hf, hb⟩
  | some entry =>
    rcases entry with ⟨name, config⟩
    cases config with
    | integer px =>
      simp only [he] at h
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at h
      by_cases hpx : px < 0 ∨ COORD_LIMIT < px
      · rw [ite_eq_left hpx] at h
        cases h
      · rw [ite_eq_right hpx] at h
        by_cases hlimit : COORD_LIMIT <
            (if m.profile == .cell then Int.fdiv (px + 7) 8 else px * 64)
        · rw [ite_eq_left hlimit] at h
          cases h
        · rw [ite_eq_right hlimit] at h
          have heq := Except.ok.inj h
          subst value
          exact ⟨config_units_nonnegative m.profile px (by omega), by omega⟩
    | string text =>
      simp only [he] at h
      cases h
    | boolean flag =>
      simp only [he] at h
      cases h

def numericState (ownerOf : String → Nat) (cursors : List Int)
    (placed : List (String × Rect)) : CardWalk :=
  ⟨cursors, placed.reverse.map (fun entry => (ownerOf entry.1, entry.2))⟩

theorem numeric_step_projection (ownerOf : String → Nat) (cursors : List Int)
    (placed : List (String × Rect)) (id : String) (owner : Nat)
    (pad width gap cardWidth band height : Int) (howner : ownerOf id = owner) :
    numericState ownerOf (Kinds.Kanban.advanceCursor cursors owner height gap band)
      (placed ++ [(id, Kinds.Kanban.cardRect pad width gap cardWidth owner
        (cursors.getD owner band) height)]) =
      (numericState ownerOf cursors placed).step pad width gap cardWidth band owner height := by
  simp [numericState, CardWalk.step, List.reverse_append, howner]

theorem native_card_iteration_preserves (ownerOf : String → Nat) (cursors : List Int)
    (placed : List (String × Rect)) (id : String) (owner : Nat)
    (pad width gap cardWidth band height : Int)
    (hinv : CardInvariant pad gap band (numericState ownerOf cursors placed))
    (howner : ownerOf id = owner) (hi : owner < cursors.length)
    (hh : 0 ≤ height) (hg : 0 ≤ gap) :
    CardInvariant pad gap band
      (numericState ownerOf (Kinds.Kanban.advanceCursor cursors owner height gap band)
        (placed ++ [(id, Kinds.Kanban.cardRect pad width gap cardWidth owner
          (cursors.getD owner band) height)])) := by
  rw [numeric_step_projection ownerOf cursors placed id owner pad width gap cardWidth band height howner]
  exact card_walk_step_preserves _ pad width gap cardWidth band owner height hinv hi hh hg

theorem native_card_horizontal_preserves (ownerOf : String → Nat) (cursors : List Int)
    (placed : List (String × Rect)) (id : String) (owner : Nat)
    (pad width gap cardWidth band height : Int)
    (hinv : CardHorizontal pad width gap cardWidth (numericState ownerOf cursors placed))
    (howner : ownerOf id = owner) :
    CardHorizontal pad width gap cardWidth
      (numericState ownerOf (Kinds.Kanban.advanceCursor cursors owner height gap band)
        (placed ++ [(id, Kinds.Kanban.cardRect pad width gap cardWidth owner
          (cursors.getD owner band) height)])) := by
  rw [numeric_step_projection ownerOf cursors placed id owner pad width gap cardWidth band height howner]
  exact card_horizontal_step _ pad width gap cardWidth band owner height hinv

theorem native_placed_card_containment (ownerOf : String → Nat) (cursors : List Int)
    (placed : List (String × Rect))
    (pad width gap cardWidth gutter band minimum minHeight : Int)
    (hv : CardInvariant pad gap band (numericState ownerOf cursors placed))
    (hx : CardHorizontal pad width gap cardWidth (numericState ownerOf cursors placed))
    (hband : 0 ≤ band) (hcw : cardWidth ≤ width)
    (hclear : minimum ≤ Int.fdiv gutter 2 + 3 * gutter) :
    ∀ entry ∈ placed,
      (Kinds.Kanban.sectionRect pad width gap gutter band minimum minHeight
        (cursors.getD (ownerOf entry.1) band) (ownerOf entry.1)).Contained entry.2 := by
  intro entry he
  have hn : (ownerOf entry.1, entry.2) ∈ (numericState ownerOf cursors placed).placed := by
    exact List.mem_map.mpr ⟨entry, by simpa using he, rfl⟩
  exact card_walk_all_inside_final_columns _ pad width gap cardWidth gutter band minimum
    minHeight hv hx hband hcw hclear _ hn

theorem model_lookup_self (boxes : List ModelBox) (b : ModelBox)
    (hunique : (boxes.map (·.id)).Nodup) (hmem : b ∈ boxes) :
    boxes.find? (fun candidate => candidate.id == b.id) = some b := by
  induction boxes with
  | nil => simp at hmem
  | cons first rest ih =>
    obtain ⟨hfresh, hrest⟩ := List.nodup_cons.mp hunique
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · simp
    · have hne : first.id ≠ b.id := by
        intro heq
        exact hfresh (List.mem_map.mpr ⟨b, hmem, heq.symm⟩)
      simpa [hne] using ih hrest hmem

def ownerIndex (columns cards : List ModelBox) (id : String) : Nat :=
  match cards.find? (fun b => b.id == id) with
  | none => 0
  | some b => (columns.findIdx? (fun col => col.id == b.parent)).getD 0

theorem ownerIndex_spec (columns cards : List ModelBox) (b : ModelBox) (owner : Nat)
    (hunique : (cards.map (·.id)).Nodup) (hmem : b ∈ cards)
    (hlookup : columns.findIdx? (fun col => col.id == b.parent) = some owner) :
    ownerIndex columns cards b.id = owner := by
  simp [ownerIndex, model_lookup_self cards b hunique hmem, hlookup]

theorem native_card_box_iteration (columns cards : List ModelBox)
    (cursors : List Int) (placed : List (String × Rect)) (b : ModelBox) (owner : Nat)
    (pad width gap cardWidth band height : Int)
    (hunique : (cards.map (·.id)).Nodup) (hmem : b ∈ cards)
    (hlookup : columns.findIdx? (fun col => col.id == b.parent) = some owner)
    (hlen : cursors.length = columns.length)
    (hinv : CardInvariant pad gap band
      (numericState (ownerIndex columns cards) cursors placed))
    (hh : 0 ≤ height) (hg : 0 ≤ gap) :
    CardInvariant pad gap band
      (numericState (ownerIndex columns cards)
        (Kinds.Kanban.advanceCursor cursors owner height gap band)
        (placed ++ [(b.id, Kinds.Kanban.cardRect pad width gap cardWidth owner
          (cursors.getD owner band) height)])) := by
  obtain ⟨hi, _⟩ := owner_lookup_spec columns b.parent owner hlookup
  apply native_card_iteration_preserves
  · exact hinv
  · exact ownerIndex_spec columns cards b owner hunique hmem hlookup
  · simpa [hlen] using hi
  · exact hh
  · exact hg

end Elegant.GridKanban

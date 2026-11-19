import Elegant.Kinds.Timeline
import Elegant.ForInFacts
import Elegant.Kinds.TimelineValid

set_option autoImplicit false

namespace Elegant.Kinds.Timeline

open Common

def namedRects (g : Family) (p : Lanes.Timeline.Plan) : List (String × Rect) :=
  (g.title.toList.map fun card => (card.id, p.title)) ++
    (g.sections.zip p.sections).map (fun (card, rect) => (card.id, rect)) ++
    (g.periods.zip p.periods).map (fun (period, rect) => (period.id, rect)) ++
    (g.periods.zip p.events).flatMap (fun (period, rects) =>
      (period.events.zip rects).map fun (event, rect) => (event.id, rect))

private theorem zip_rects_sublist {α : Type} (xs : List α) (rs : List Rect)
    (name : α → String) :
    (((xs.zip rs).map fun (x, r) => (name x, r)).map Prod.snd).Sublist rs := by
  induction xs generalizing rs with
  | nil => simp
  | cons x xs ih =>
    cases rs with
    | nil => simp
    | cons r rs => exact List.Sublist.cons_cons r (ih rs)

private theorem event_rects_sublist (periods : List Lanes.Timeline.Period)
    (rows : List (List Rect)) :
    (((periods.zip rows).flatMap fun (period, rects) =>
      (period.events.zip rects).map fun (event, rect) => (event.id, rect)).map
        Prod.snd).Sublist rows.flatten := by
  induction periods generalizing rows with
  | nil => simp
  | cons period periods ih =>
    cases rows with
    | nil => simp
    | cons rects rows =>
      simpa only [List.zip_cons_cons, List.flatMap_cons, List.map_append,
        List.flatten_cons] using
        (zip_rects_sublist period.events rects (·.id)).append (ih rows)

theorem namedRects_sublist (g : Family) (p : Lanes.Timeline.Plan) :
    ((namedRects g p).map Prod.snd).Sublist (cardRects g p) := by
  have ht : ((g.title.toList.map fun card => (card.id, p.title)).map
      Prod.snd).Sublist (if g.title.isSome then [p.title] else []) := by
    cases g.title <;> simp
  simpa only [namedRects, cardRects, List.map_append, List.append_assoc] using
    ht.append ((zip_rects_sublist g.sections p.sections (·.id)).append
      ((zip_rects_sublist g.periods p.periods (·.id)).append
        (event_rects_sublist g.periods p.events)))

theorem getElem_zip_some {α β : Type} {xs : List α} {ys : List β}
    {i : Nat} {x : α} {y : β} (hx : xs[i]? = some x) (hy : ys[i]? = some y) :
    (x, y) ∈ xs.zip ys := by
  induction xs generalizing ys i with
  | nil => simp at hx
  | cons first rest ih =>
    cases ys with
    | nil => simp at hy
    | cons second tail =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
        subst x
        subst y
        exact List.mem_cons_self
      | succ i =>
        exact List.mem_cons_of_mem _ (ih
          (by simpa only [List.getElem?_cons_succ] using hx)
          (by simpa only [List.getElem?_cons_succ] using hy))

theorem rectSource_named {g : Family} {p : Lanes.Timeline.Plan}
    {id : String} {rect : Rect} (h : RectSource g p id rect) :
    (id, rect) ∈ namedRects g p := by
  rcases h with ⟨card, ht, hid, hr⟩ | ⟨i, card, hc, hid, hr⟩ |
    ⟨i, period, hp, hid, hr⟩ | ⟨period, rects, event, hp, he, hid⟩
  · subst id
    subst rect
    simp [namedRects, ht]
  · have hm := getElem_zip_some hc hr
    have hn : (id, rect) ∈
        (g.sections.zip p.sections).map (fun (card, rect) => (card.id, rect)) :=
      List.mem_map.mpr ⟨(card, rect), hm, by simp [hid]⟩
    simp only [namedRects, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hn))
  · have hm := getElem_zip_some hp hr
    have hn : (id, rect) ∈
        (g.periods.zip p.periods).map (fun (period, rect) => (period.id, rect)) :=
      List.mem_map.mpr ⟨(period, rect), hm, by simp [hid]⟩
    simp only [namedRects, List.mem_append]
    exact Or.inl (Or.inr hn)
  · have hn : (id, rect) ∈ (g.periods.zip p.events).flatMap
        (fun (period, rects) =>
          (period.events.zip rects).map fun (event, rect) => (event.id, rect)) :=
      List.mem_flatMap.mpr ⟨(period, rects), hp,
        List.mem_map.mpr ⟨(event, rect), he, by simp [hid]⟩⟩
    simp only [namedRects, List.mem_append]
    exact Or.inr hn

theorem named_disjoint {entries : List (String × Rect)}
    (h : (entries.map Prod.snd).Pairwise Disjoint)
    {a b : String × Rect} (ha : a ∈ entries) (hb : b ∈ entries)
    (hne : a.1 ≠ b.1) : Disjoint a.2 b.2 := by
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb
  have hij : i ≠ j := by
    intro he
    subst j
    exact hne (congrArg Prod.fst (hia.symm.trans hjb))
  have hp : entries.Pairwise (fun x y => Disjoint x.2 y.2) := by
    simpa only [List.pairwise_map] using h
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · simpa only [hia, hjb] using
      (List.Pairwise.rel_getElem_of_lt hi hj hp hlt)
  · exact False.elim (hij heq)
  · exact Disjoint.symm' (by
      simpa only [hia, hjb] using
        (List.Pairwise.rel_getElem_of_lt hj hi hp hgt))

private theorem loop_direction (inputs : List ModelBox)
    (step : ModelBox → Family → Except LayoutError (ForInStep Family))
    (direction : Direction) (initial final : Family)
    (hi : initial.direction = direction)
    (hstep : ∀ item state next, state.direction = direction →
      step item state = .ok next → next.value.direction = direction)
    (h : forIn inputs initial step = .ok final) :
    final.direction = direction := by
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
      have hn := hstep item initial next hi hs
      cases next with
      | done state =>
        dsimp only [ForInStep.value] at hn
        have he : state = final := by
          simpa [hs, Bind.bind, Except.bind, pure, Except.pure] using h
        simpa only [← he] using hn
      | yield state =>
        have htail : forIn rest state step = .ok final := by
          simpa [hs, Bind.bind, Except.bind, pure, Except.pure] using h
        exact ih state hn htail
private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩


def cardIds (g : Family) : List String :=
  g.title.toList.map (·.id) ++ g.sections.map (·.id) ++
    g.periods.flatMap (fun period => period.id :: period.events.map (·.id))

private theorem event_update_ids (state : Family)
    (previous : Lanes.Timeline.Period) (event : Lanes.Timeline.Event)
    (hlast : state.periods.getLast? = some previous) :
    cardIds { state with periods := state.periods.set (state.periods.length - 1) ({ previous with events := previous.events ++ [event] }) } =
      cardIds state ++ [event.id] := by
  obtain ⟨before, hb⟩ := List.getLast?_eq_some_iff.mp hlast
  simp [cardIds, hb, List.set_append_right, List.flatMap_append, List.append_assoc]

/-- Multiplicity is bounded by the actual input occurrences, even before well-formedness. -/
theorem decoded_card_ids_count_le {m : Model} {g : Family}
    (hdecode : decode m = .ok g) (id : String) :
    (cardIds g).count id ≤ (m.boxes.map (·.id)).count id := by
  have hp := decode_parentsRooted hdecode
  unfold decode at hdecode
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hdecode
  obtain ⟨final, hloop, hret⟩ := bind_ok hdecode
  have he : final = g := by
    simpa only [pure, Except.pure, Except.ok.injEq] using hret
  subst g
  refine Elegant.forIn_processed [] m.boxes _ final _
    (fun done state => (cardIds state).count id ≤ (done.map (·.id)).count id)
    ?_ ?_ hloop
  · simp [cardIds]
  · intro done box rest state next _ hs hstep
    split at hstep
    · obtain ⟨caption, _, hstep⟩ := bind_ok hstep
      have he : ForInStep.yield
          ({ state with title := some { id := box.id, caption } } : Family) = next := by
        simpa only [pure, Except.pure, Except.ok.injEq] using hstep
      subst next
      refine ⟨_, rfl, ?_⟩
      simp only [cardIds, List.count_append] at hs
      simp only [cardIds, Option.toList_some, List.map_append, List.map_cons,
        List.map_nil, List.count_append, List.count_cons, List.count_nil]
      split <;> omega
    · obtain ⟨caption, _, hstep⟩ := bind_ok hstep
      have he : ForInStep.yield
          ({ state with sections := state.sections ++ [{ id := box.id, caption }] } :
            Family) = next := by
        simpa only [pure, Except.pure, Except.ok.injEq] using hstep
      subst next
      refine ⟨_, rfl, ?_⟩
      simp only [cardIds, List.count_append] at hs
      simp only [cardIds, List.map_append, List.map_cons,
        List.map_nil, List.count_append, List.count_cons, List.count_nil]
      split <;> omega
    · obtain ⟨sectionIndex, _, hstep⟩ := bind_ok hstep
      split at hstep
      · change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
          .ok next at hstep
        cases hstep
      · obtain ⟨caption, _, hstep⟩ := bind_ok hstep
        have he : ForInStep.yield
            ({ state with periods := state.periods ++
              [{ id := box.id, caption, sectionIndex, events := [] }] } : Family) = next := by
          simpa only [pure, Except.pure, Except.ok.injEq] using hstep
        subst next
        refine ⟨_, rfl, ?_⟩
        simp only [cardIds, List.count_append] at hs
        simp only [cardIds, List.flatMap_append, List.map_append, List.map_cons,
          List.flatMap_cons, List.flatMap_nil, List.map_nil, List.append_nil,
          List.count_append, List.count_cons, List.count_nil]
        split <;> omega
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
            obtain ⟨caption, _, hstep⟩ := bind_ok hstep
            let event : Lanes.Timeline.Event := { id := box.id, caption, link := route.id }
            have he : ForInStep.yield
                ({ state with periods := state.periods.set (state.periods.length - 1) ({ previous with events := previous.events ++ [event] }) } : Family) = next := by
              simpa only [pure, Except.pure, Except.ok.injEq] using hstep
            subst next
            refine ⟨_, rfl, ?_⟩
            rw [event_update_ids state previous event hprevious]
            simp only [List.map_append, List.map_cons, List.map_nil,
              List.count_append, List.count_cons, List.count_nil, event]
            split <;> omega
    · change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
        .ok next at hstep
      cases hstep

theorem decoded_card_ids_nodup {m : Model} {g : Family}
    (hwf : WellFormed m) (hdecode : decode m = .ok g) :
    (cardIds g).Nodup := by
  apply List.nodup_iff_count.mpr
  intro id
  exact Nat.le_trans (decoded_card_ids_count_le hdecode id)
    (List.nodup_iff_count.mp (Model.boxIds_nodup hwf) id)

private theorem findIdx_unique {α : Type} (key : α → String)
    (xs : List α) (id : String) (i : Nat) (a : α)
    (hcount : (xs.map key).count id ≤ 1)
    (hget : xs[i]? = some a) (hid : key a = id) :
    xs.findIdx? (fun x => key x == id) = some i := by
  induction xs generalizing i with
  | nil => simp at hget
  | cons first rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst a
      simp [List.findIdx?_cons, hid]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget
      have hm : id ∈ rest.map key :=
        List.mem_map.mpr ⟨a, List.mem_of_getElem? hget, hid⟩
      have hpos := List.count_pos_iff.mpr hm
      have hne : key first ≠ id := by
        intro he
        simp [he] at hcount
        omega
      have hc : (rest.map key).count id ≤ 1 := by
        simpa [List.count_cons, hne] using hcount
      simp [List.findIdx?_cons, hne, ih i hc hget]

private theorem count_zero_findIdx {α : Type} (key : α → String)
    (xs : List α) (id : String) (hz : (xs.map key).count id = 0) :
    xs.findIdx? (fun x => key x == id) = none := by
  apply List.findIdx?_eq_none_iff.mpr
  intro a ha
  have hn := List.count_eq_zero.mp hz
  have hne : key a ≠ id := by
    intro he
    exact hn (List.mem_map.mpr ⟨a, ha, he⟩)
  simp [hne]

private theorem count_zip_keys_le {α β : Type} (key : α → String)
    (xs : List α) (ys : List β) (id : String) :
    ((xs.zip ys).map (fun pair => key pair.1)).count id ≤
      (xs.map key).count id := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    cases ys with
    | nil => simp
    | cons b ys =>
      have ht := ih ys
      simp only [List.zip_cons_cons, List.map_cons, List.count_cons]
      split <;> omega

private def eventEntries (g : Family) (p : Lanes.Timeline.Plan) :
    List (String × Rect) :=
  (g.periods.zip p.events).flatMap fun (period, rects) =>
    (period.events.zip rects).map fun (event, rect) => (event.id, rect)

private theorem eventEntries_count_le (g : Family) (p : Lanes.Timeline.Plan)
    (id : String) :
    ((eventEntries g p).map Prod.fst).count id ≤
      (g.periods.flatMap (fun period => period.events.map (·.id))).count id := by
  suffices ∀ (periods : List Lanes.Timeline.Period) (rects : List (List Rect)),
      (((periods.zip rects).flatMap fun (period, rs) =>
        (period.events.zip rs).map fun (event, rect) => (event.id, rect)).map
          Prod.fst).count id ≤
        (periods.flatMap (fun period => period.events.map (·.id))).count id by
    exact this g.periods p.events
  intro periods
  induction periods with
  | nil => intro rects; simp
  | cons period periods ih =>
    intro rects
    cases rects with
    | nil => simp
    | cons rs rects =>
      have hhead := count_zip_keys_le (fun e : Lanes.Timeline.Event => e.id)
        period.events rs id
      have htail := ih rects
      simp only [List.zip_cons_cons, List.flatMap_cons, List.map_append,
        List.map_map, List.count_append]
      dsimp only [Function.comp_def] at *
      omega

private theorem cardIds_count_partition (g : Family) (id : String) :
    (cardIds g).count id =
      (g.title.toList.map (·.id)).count id +
      (g.sections.map (·.id)).count id +
      (g.periods.map (·.id)).count id +
      (g.periods.flatMap (fun period => period.events.map (·.id))).count id := by
  have hp : ∀ periods : List Lanes.Timeline.Period,
      (periods.flatMap (fun period => period.id :: period.events.map (·.id))).count id =
        (periods.map (·.id)).count id +
        (periods.flatMap (fun period => period.events.map (·.id))).count id := by
    intro periods
    induction periods with
    | nil => simp
    | cons period periods ih =>
      simp only [List.flatMap_cons, List.map_cons, List.count_append,
        List.count_cons, ih]
      split <;> omega
  simp only [cardIds, List.count_append, hp]
  omega

private theorem pair_lookup_complete (entries : List (String × Rect))
    (id : String) (rect : Rect)
    (hc : (entries.map Prod.fst).count id ≤ 1)
    (hm : (id, rect) ∈ entries) :
    entries.findSome? (fun pair => if pair.1 = id then some pair.2 else none) =
      some rect := by
  induction entries with
  | nil => cases hm
  | cons entry rest ih =>
    rcases List.mem_cons.mp hm with he | ht
    · subst entry
      simp
    · have hpos : 0 < (rest.map Prod.fst).count id :=
        List.count_pos_iff.mpr (List.mem_map.mpr ⟨(id, rect), ht, rfl⟩)
      have hne : entry.1 ≠ id := by
        intro he
        simp [he] at hc
        omega
      have hrest : (rest.map Prod.fst).count id ≤ 1 := by
        simpa [List.count_cons, hne] using hc
      simpa only [List.findSome?_cons, ite_eq_right hne] using ih hrest ht

/-- Inverse lookup uses actual provenance indices, independently of plan geometry. -/
theorem rectFor_complete {m : Model} {g : Family} {p : Lanes.Timeline.Plan}
    (hwf : WellFormed m) (hdecode : decode m = .ok g)
    {id : String} {rect : Rect} (hsource : RectSource g p id rect) :
    rectFor g p id = some rect := by
  have hc := List.nodup_iff_count.mp (decoded_card_ids_nodup hwf hdecode) id
  rw [cardIds_count_partition] at hc
  rcases hsource with ht | hs | hp | he
  · obtain ⟨card, ht, hid, rfl⟩ := ht
    simp [rectFor, ht, hid]
  · obtain ⟨i, card, hi, hid, hr⟩ := hs
    have hpos : 0 < (g.sections.map (·.id)).count id :=
      List.count_pos_iff.mpr
        (List.mem_map.mpr ⟨card, List.mem_of_getElem? hi, hid⟩)
    have htitle : g.title.map (·.id) ≠ some id := by
      intro ht
      cases ho : g.title with
      | none => simp [ho] at ht
      | some title =>
        have hid : title.id = id := by simpa [ho] using ht
        simp [ho, hid] at hc
        omega
    have hidx := findIdx_unique (fun c : Lanes.Timeline.Card => c.id)
      g.sections id i card (by omega) hi hid
    simp only [rectFor, beq_iff_eq, htitle, ↓reduceIte, hidx]
    exact hr
  · obtain ⟨i, period, hi, hid, hr⟩ := hp
    have hpos : 0 < (g.periods.map (·.id)).count id :=
      List.count_pos_iff.mpr
        (List.mem_map.mpr ⟨period, List.mem_of_getElem? hi, hid⟩)
    have hsec : (g.sections.map (·.id)).count id = 0 := by omega
    have htitle : g.title.map (·.id) ≠ some id := by
      intro ht
      cases ho : g.title with
      | none => simp [ho] at ht
      | some title =>
        have hid : title.id = id := by simpa [ho] using ht
        simp [ho, hid] at hc
        omega
    have hidx := findIdx_unique (fun p : Lanes.Timeline.Period => p.id)
      g.periods id i period (by omega) hi hid
    simp only [rectFor, beq_iff_eq, htitle, ↓reduceIte,
      count_zero_findIdx (fun c : Lanes.Timeline.Card => c.id) g.sections id hsec,
      hidx]
    exact hr
  · obtain ⟨period, rects, event, hp, he, hid⟩ := he
    have hmem : (id, rect) ∈ eventEntries g p := by
      apply List.mem_flatMap.mpr
      refine ⟨(period, rects), hp, ?_⟩
      exact List.mem_map.mpr ⟨(event, rect), he, by simp [hid]⟩
    have hec := eventEntries_count_le g p id
    have hpos : 0 < ((eventEntries g p).map Prod.fst).count id :=
      List.count_pos_iff.mpr (List.mem_map.mpr ⟨(id, rect), hmem, rfl⟩)
    have hsec : (g.sections.map (·.id)).count id = 0 := by omega
    have hperiod : (g.periods.map (·.id)).count id = 0 := by omega
    have htitle : g.title.map (·.id) ≠ some id := by
      intro ht
      cases ho : g.title with
      | none => simp [ho] at ht
      | some title =>
        have hid : title.id = id := by simpa [ho] using ht
        simp [ho, hid] at hc
        omega
    simp only [rectFor, beq_iff_eq, htitle, ↓reduceIte,
      count_zero_findIdx (fun c : Lanes.Timeline.Card => c.id) g.sections id hsec,
      count_zero_findIdx (fun p : Lanes.Timeline.Period => p.id) g.periods id hperiod]
    exact pair_lookup_complete (eventEntries g p) id rect (by omega) hmem

theorem rectSource_unique {m : Model} {g : Family} {p : Lanes.Timeline.Plan}
    (hwf : WellFormed m) (hdecode : decode m = .ok g)
    {id : String} {left right : Rect}
    (hl : RectSource g p id left) (hr : RectSource g p id right) :
    left = right := by
  exact Option.some.inj
    ((rectFor_complete hwf hdecode hl).symm.trans (rectFor_complete hwf hdecode hr))

theorem decode_direction_horizontal {m : Model} {g : Family}
    (hg : decode m = .ok g) : g.direction = m.options.direction := by
  have hp := decode_parentsRooted hg
  unfold decode at hg
  simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hg
  obtain ⟨final, hloop, hret⟩ := bind_ok hg
  have hfinal : final = g := by
    simpa only [pure, Except.pure, Except.ok.injEq] using hret
  subst g
  refine loop_direction _ _ m.options.direction _ _ rfl ?_ hloop
  intro box state next hs hstep
  split at hstep
  · obtain ⟨caption, _hcaption, hstep⟩ := bind_ok hstep
    have he : ForInStep.yield
        ({ state with title := some { id := box.id, caption } } : Family) = next := by
      simpa only [pure, Except.pure, Except.ok.injEq] using hstep
    subst next
    exact hs
  · obtain ⟨caption, _hcaption, hstep⟩ := bind_ok hstep
    have he : ForInStep.yield
        ({ state with sections := state.sections ++ [{ id := box.id, caption }] } :
          Family) = next := by
      simpa only [pure, Except.pure, Except.ok.injEq] using hstep
    subst next
    exact hs
  · obtain ⟨sectionIndex, _hsection, hstep⟩ := bind_ok hstep
    split at hstep
    · change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
        .ok next at hstep
      cases hstep
    · obtain ⟨caption, _hcaption, hstep⟩ := bind_ok hstep
      have he : ForInStep.yield
          ({ state with periods := state.periods ++
            [{ id := box.id, caption, sectionIndex, events := [] }] } : Family) =
          next := by
        simpa only [pure, Except.pure, Except.ok.injEq] using hstep
      subst next
      exact hs
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
        let expected := if m.options.direction == .LR then
          ((previous.events.getLast?).map (·.id)).getD previous.id else previous.id
        by_cases hbad : (route.fromId != expected) = true
        · dsimp only [expected] at hbad
          simp only [hbad, ↓reduceIte] at hstep
          change (Except.error LayoutError.domain :
            Except LayoutError (ForInStep Family)) = .ok next at hstep
          cases hstep
        · dsimp only [expected] at hbad
          simp only [hbad] at hstep
          obtain ⟨caption, _hcaption, hstep⟩ := bind_ok hstep
          let event : Lanes.Timeline.Event := { id := box.id, caption, link := route.id }
          let updated := { previous with events := previous.events ++ [event] }
          have he : ForInStep.yield
              ({ state with periods :=
                state.periods.set (state.periods.length - 1) updated } : Family) =
              next := by
            simpa only [pure, Except.pure, Except.ok.injEq] using hstep
          subst next
          exact hs
  · change (Except.error LayoutError.domain : Except LayoutError (ForInStep Family)) =
      .ok next at hstep
    cases hstep

end Elegant.Kinds.Timeline

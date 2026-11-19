import Elegant.GridKanbanTransfer

set_option autoImplicit false

namespace Elegant.GridKanban

abbrev NativeCardState := List Int × List (String × Rect) × List Group

def NativeCardInvariant (columns cards : List ModelBox)
    (pad width gap cardWidth band : Int) (state : NativeCardState) : Prop :=
  state.1.length = columns.length ∧
  CardInvariant pad gap band (numericState (ownerIndex columns cards) state.1 state.2.1) ∧
  CardHorizontal pad width gap cardWidth (numericState (ownerIndex columns cards) state.1 state.2.1)

theorem native_card_initial (columns cards : List ModelBox)
    (pad width gap cardWidth band : Int) :
    NativeCardInvariant columns cards pad width gap cardWidth band
      (List.replicate columns.length band, [], []) := by
  refine ⟨by simp, ?_, ?_⟩
  · simpa [numericState] using card_walk_init columns.length pad gap band
  · intro old hmem
    simp [numericState] at hmem

/-- This is exactly the cursor/placement update performed by a successful native
card iteration; drawing groups are irrelevant to the geometry invariant. -/
def CardStepShape (columns : List ModelBox) (pad width gap cardWidth band : Int)
    (height : ModelBox × List Measure.Line → Int)
    (input : ModelBox × List Measure.Line) (state : NativeCardState)
    (next : ForInStep NativeCardState) : Prop :=
  ∃ owner groups,
    columns.findIdx? (fun col => col.id == input.1.parent) = some owner ∧
    next = .yield
      (Kinds.Kanban.advanceCursor state.1 owner (height input) gap band,
       state.2.1 ++ [(input.1.id, Kinds.Kanban.cardRect pad width gap cardWidth owner
         (state.1.getD owner band) (height input))], groups)

theorem native_card_shape_preserves (columns cards : List ModelBox)
    (pad width gap cardWidth band : Int)
    (height : ModelBox × List Measure.Line → Int)
    (input : ModelBox × List Measure.Line) (state : NativeCardState)
    (next : ForInStep NativeCardState)
    (hunique : (cards.map (·.id)).Nodup) (hmem : input.1 ∈ cards)
    (hg : 0 ≤ gap) (hh : 0 ≤ height input)
    (hinv : NativeCardInvariant columns cards pad width gap cardWidth band state)
    (hshape : CardStepShape columns pad width gap cardWidth band height input state next) :
    NativeCardInvariant columns cards pad width gap cardWidth band next.value := by
  obtain ⟨hlen, hv, hx⟩ := hinv
  obtain ⟨owner, groups, hlookup, rfl⟩ := hshape
  refine ⟨?_, ?_, ?_⟩
  · simpa [Kinds.Kanban.advanceCursor] using hlen
  · exact native_card_box_iteration columns cards state.1 state.2.1 input.1 owner
      pad width gap cardWidth band (height input) hunique hmem hlookup hlen hv hh hg
  · exact native_card_horizontal_preserves (ownerIndex columns cards) state.1 state.2.1
      input.1.id owner pad width gap cardWidth band (height input) hx
      (ownerIndex_spec columns cards input.1 owner hunique hmem hlookup)

theorem native_card_pass_preserves (columns cards : List ModelBox)
    (inputs : List (ModelBox × List Measure.Line))
    (pad width gap cardWidth band : Int)
    (height : ModelBox × List Measure.Line → Int)
    (step : ModelBox × List Measure.Line → NativeCardState → Except LayoutError (ForInStep NativeCardState))
    (final : NativeCardState) (hunique : (cards.map (·.id)).Nodup)
    (hinputs : ∀ input ∈ inputs, input.1 ∈ cards)
    (hg : 0 ≤ gap) (hh : ∀ input ∈ inputs, 0 ≤ height input)
    (hshape : ∀ input ∈ inputs, ∀ state next, step input state = .ok next →
      CardStepShape columns pad width gap cardWidth band height input state next)
    (hrun : forIn inputs (List.replicate columns.length band, [], []) step = .ok final) :
    NativeCardInvariant columns cards pad width gap cardWidth band final := by
  apply forIn_preserves inputs step
    (NativeCardInvariant columns cards pad width gap cardWidth band)
    (List.replicate columns.length band, [], []) final
    (native_card_initial columns cards pad width gap cardWidth band) ?_ hrun
  intro input hmem state next hinv hstep
  exact native_card_shape_preserves columns cards pad width gap cardWidth band height
    input state next hunique (hinputs input hmem) hg (hh input hmem) hinv
    (hshape input hmem state next hstep)

def cardStep (columns : List ModelBox)
    (check : Rect → Except LayoutError Rect)
    (draw : ModelBox × List Measure.Line → Rect → Group)
    (pad width gap cardWidth band : Int)
    (height : ModelBox × List Measure.Line → Int)
    (input : ModelBox × List Measure.Line) (state : NativeCardState) :
    Except LayoutError (ForInStep NativeCardState) := do
  let some owner := columns.findIdx? (fun col => col.id == input.1.parent) | throw .domain
  let r ← check (Kinds.Kanban.cardRect pad width gap cardWidth owner
    (state.1.getD owner band) (height input))
  pure (.yield (Kinds.Kanban.advanceCursor state.1 owner (height input) gap band,
    state.2.1 ++ [(input.1.id, r)], state.2.2 ++ [draw input r]))

theorem cardStep_shape (columns : List ModelBox)
    (check : Rect → Except LayoutError Rect)
    (draw : ModelBox × List Measure.Line → Rect → Group)
    (pad width gap cardWidth band : Int)
    (height : ModelBox × List Measure.Line → Int)
    (input : ModelBox × List Measure.Line) (state : NativeCardState)
    (next : ForInStep NativeCardState)
    (hcheck : ∀ input output, check input = .ok output → output = input)
    (h : cardStep columns check draw pad width gap cardWidth band height input state = .ok next) :
    CardStepShape columns pad width gap cardWidth band height input state next := by
  unfold cardStep at h
  cases ho : columns.findIdx? (fun col => col.id == input.1.parent) with
  | none =>
    rw [ho] at h
    change Except.error LayoutError.domain = Except.ok next at h
    cases h
  | some owner =>
    rw [ho] at h
    dsimp only [Bind.bind, Except.bind] at h
    cases hr : check (Kinds.Kanban.cardRect pad width gap cardWidth owner
        (state.1.getD owner band) (height input)) with
    | error error =>
      rw [hr] at h
      cases h
    | ok r =>
      have heq := hcheck _ _ hr
      subst r
      rw [hr] at h
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      have hnext : (.yield
          (Kinds.Kanban.advanceCursor state.1 owner (height input) gap band,
           state.2.1 ++ [(input.1.id, Kinds.Kanban.cardRect pad width gap cardWidth owner
             (state.1.getD owner band) (height input))],
           state.2.2 ++ [draw input (Kinds.Kanban.cardRect pad width gap cardWidth owner
             (state.1.getD owner band) (height input))]) : ForInStep NativeCardState) = next := by
        exact Except.ok.inj h
      subst next
      exact ⟨owner, _, ho, rfl⟩

theorem card_pass_invariant (columns cards : List ModelBox)
    (inputs : List (ModelBox × List Measure.Line))
    (check : Rect → Except LayoutError Rect)
    (draw : ModelBox × List Measure.Line → Rect → Group)
    (pad width gap cardWidth band : Int)
    (height : ModelBox × List Measure.Line → Int)
    (final : NativeCardState) (hunique : (cards.map (·.id)).Nodup)
    (hinputs : ∀ input ∈ inputs, input.1 ∈ cards)
    (hg : 0 ≤ gap) (hh : ∀ input ∈ inputs, 0 ≤ height input)
    (hcheck : ∀ input output, check input = .ok output → output = input)
    (hrun : forIn inputs (List.replicate columns.length band, [], [])
      (cardStep columns check draw pad width gap cardWidth band height) = .ok final) :
    NativeCardInvariant columns cards pad width gap cardWidth band final := by
  apply native_card_pass_preserves columns cards inputs pad width gap cardWidth band height
    (cardStep columns check draw pad width gap cardWidth band height) final hunique hinputs hg hh ?_ hrun
  intro input _ state next hstep
  exact cardStep_shape columns check draw pad width gap cardWidth band height input state next hcheck hstep

abbrev SectionInput := (ModelBox × List Measure.Line) × Nat
abbrev NativeSectionState := List (String × Rect) × List Group × Int × Int

def sectionFor (cursors : List Int) (pad width gap gutter band minimum minHeight : Int)
    (input : SectionInput) : Rect :=
  Kinds.Kanban.sectionRect pad width gap gutter band minimum minHeight
    (cursors.getD input.2 band) input.2

def SectionInvariant (inputs : List SectionInput) (base : List (String × Rect))
    (rectFor : SectionInput → Rect) (pad : Int) (state : NativeSectionState) : Prop :=
  pad ≤ state.2.2.1 ∧ pad ≤ state.2.2.2 ∧
  ∀ entry ∈ state.1, entry ∈ base ∨
    ∃ input ∈ inputs, entry = (input.1.1.id, rectFor input) ∧
      entry.2.x + entry.2.w ≤ state.2.2.1 ∧ entry.2.y + entry.2.h ≤ state.2.2.2

def SectionStepShape (rectFor : SectionInput → Rect) (input : SectionInput)
    (state : NativeSectionState) (next : ForInStep NativeSectionState) : Prop :=
  ∃ groups, next = .yield
    (state.1 ++ [(input.1.1.id, rectFor input)], groups,
      max state.2.2.1 ((rectFor input).x + (rectFor input).w),
      max state.2.2.2 ((rectFor input).y + (rectFor input).h))

theorem native_section_shape_preserves (inputs : List SectionInput)
    (base : List (String × Rect)) (rectFor : SectionInput → Rect) (pad : Int)
    (input : SectionInput) (state : NativeSectionState) (next : ForInStep NativeSectionState)
    (hinput : input ∈ inputs) (hinv : SectionInvariant inputs base rectFor pad state)
    (hshape : SectionStepShape rectFor input state next) :
    SectionInvariant inputs base rectFor pad next.value := by
  obtain ⟨hpad, hbottom, hitems⟩ := hinv
  obtain ⟨groups, rfl⟩ := hshape
  refine ⟨Int.le_trans hpad (Int.le_max_left _ _),
    Int.le_trans hbottom (Int.le_max_left _ _), ?_⟩
  intro entry hmem
  change entry ∈ state.1 ++ [(input.1.1.id, rectFor input)] at hmem
  simp only [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | rfl
  · rcases hitems entry hmem with hbase | ⟨old, ho, heq, hr, hb⟩
    · exact Or.inl hbase
    · exact Or.inr ⟨old, ho, heq, Int.le_trans hr (Int.le_max_left _ _),
        Int.le_trans hb (Int.le_max_left _ _)⟩
  · exact Or.inr ⟨input, hinput, rfl, Int.le_max_right _ _, Int.le_max_right _ _⟩

theorem native_section_pass_preserves (inputs : List SectionInput)
    (base : List (String × Rect)) (rectFor : SectionInput → Rect) (pad : Int)
    (step : SectionInput → NativeSectionState → Except LayoutError (ForInStep NativeSectionState))
    (final : NativeSectionState)
    (hshape : ∀ input ∈ inputs, ∀ state next, step input state = .ok next →
      SectionStepShape rectFor input state next)
    (hrun : forIn inputs (base, [], pad, pad) step = .ok final) :
    SectionInvariant inputs base rectFor pad final := by
  apply forIn_preserves inputs step (SectionInvariant inputs base rectFor pad)
    (base, [], pad, pad) final ?_ ?_ hrun
  · exact ⟨Int.le_refl _, Int.le_refl _, fun _ h => Or.inl h⟩
  · intro input hi state next hinv hs
    exact native_section_shape_preserves inputs base rectFor pad input state next hi hinv
      (hshape input hi state next hs)

theorem native_section_pass_ids (inputs : List SectionInput)
    (base : List (String × Rect)) (rectFor : SectionInput → Rect) (pad : Int)
    (step : SectionInput → NativeSectionState → Except LayoutError (ForInStep NativeSectionState))
    (final : NativeSectionState)
    (hshape : ∀ input ∈ inputs, ∀ state next, step input state = .ok next →
      SectionStepShape rectFor input state next)
    (hrun : forIn inputs (base, [], pad, pad) step = .ok final) :
    final.1.map (·.1) = base.map (·.1) ++ inputs.map (fun input => input.1.1.id) := by
  apply forIn_emits_ids inputs step (fun input => input.1.1.id) (fun state => state.1.map (·.1))
    (base, [], pad, pad) final ?_ hrun
  intro input hi state next hs
  obtain ⟨groups, rfl⟩ := hshape input hi state next hs
  exact ⟨_, rfl, by simp⟩

theorem native_section_pass_placements (inputs : List SectionInput)
    (base : List (String × Rect)) (rectFor : SectionInput → Rect) (pad : Int)
    (step : SectionInput → NativeSectionState → Except LayoutError (ForInStep NativeSectionState))
    (final : NativeSectionState)
    (hshape : ∀ input ∈ inputs, ∀ state next, step input state = .ok next →
      SectionStepShape rectFor input state next)
    (hrun : forIn inputs (base, [], pad, pad) step = .ok final) :
    final.1 = base ++ inputs.map (fun input => (input.1.1.id, rectFor input)) := by
  apply forIn_emits_ids inputs step (fun input => (input.1.1.id, rectFor input))
    (fun state => state.1) (base, [], pad, pad) final ?_ hrun
  intro input hi state next hs
  obtain ⟨groups, rfl⟩ := hshape input hi state next hs
  exact ⟨_, rfl, rfl⟩

def sectionStep (rectFor : SectionInput → Rect) (check : Rect → Except LayoutError Rect)
    (draw : SectionInput → Rect → Except LayoutError Group)
    (input : SectionInput) (state : NativeSectionState) :
    Except LayoutError (ForInStep NativeSectionState) := do
  let r ← check (rectFor input)
  let group ← draw input r
  pure (.yield (state.1 ++ [(input.1.1.id, r)], state.2.1 ++ [group],
    max state.2.2.1 ((rectFor input).x + (rectFor input).w),
    max state.2.2.2 ((rectFor input).y + (rectFor input).h)))

theorem sectionStep_shape (rectFor : SectionInput → Rect)
    (check : Rect → Except LayoutError Rect)
    (draw : SectionInput → Rect → Except LayoutError Group)
    (input : SectionInput) (state : NativeSectionState) (next : ForInStep NativeSectionState)
    (hcheck : ∀ input output, check input = .ok output → output = input)
    (h : sectionStep rectFor check draw input state = .ok next) :
    SectionStepShape rectFor input state next := by
  unfold sectionStep at h
  cases hr : check (rectFor input) with
  | error error => simp [hr, Bind.bind, Except.bind] at h
  | ok r =>
    have heq := hcheck _ _ hr
    subst r
    cases hd : draw input (rectFor input) with
    | error error => simp [hr, hd, Bind.bind, Except.bind] at h
    | ok group =>
      have hnext : (.yield (state.1 ++ [(input.1.1.id, rectFor input)],
          state.2.1 ++ [group], max state.2.2.1 ((rectFor input).x + (rectFor input).w),
          max state.2.2.2 ((rectFor input).y + (rectFor input).h)) : ForInStep NativeSectionState) = next := by
        simpa only [hr, hd, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] using h
      subst next
      exact ⟨_, rfl⟩

theorem section_pass_invariant (inputs : List SectionInput)
    (base : List (String × Rect)) (rectFor : SectionInput → Rect) (pad : Int)
    (check : Rect → Except LayoutError Rect)
    (draw : SectionInput → Rect → Except LayoutError Group)
    (final : NativeSectionState)
    (hcheck : ∀ input output, check input = .ok output → output = input)
    (hrun : forIn inputs (base, [], pad, pad) (sectionStep rectFor check draw) = .ok final) :
    SectionInvariant inputs base rectFor pad final := by
  apply native_section_pass_preserves inputs base rectFor pad
    (sectionStep rectFor check draw) final ?_ hrun
  intro input _ state next hs
  exact sectionStep_shape rectFor check draw input state next hcheck hs

theorem measured_map_length {α β : Type} (measure : α → Except LayoutError β)
    (inputs : List α) (output : List β) (h : inputs.mapM measure = .ok output) :
    output.length = inputs.length := by
  induction inputs generalizing output with
  | nil =>
    have heq : [] = output := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h
    simp [← heq]
  | cons input inputs ih =>
    rw [List.mapM_cons] at h
    cases hm : measure input with
    | error error => simp [hm, Bind.bind, Except.bind] at h
    | ok measured =>
      cases ht : inputs.mapM measure with
      | error error => simp [hm, ht, Bind.bind, Except.bind] at h
      | ok tail =>
        have heq : measured :: tail = output := by
          simpa only [hm, ht, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] using h
        subst output
        simp only [List.length_cons]
        rw [ih tail ht]

theorem zipped_sources {α β : Type} (source : List α) (measured : List β)
    (hlen : measured.length = source.length) :
    (source.zip measured).map (·.1) = source := by
  induction source generalizing measured with
  | nil =>
    cases measured with
    | nil => rfl
    | cons value rest => simp at hlen
  | cons value source ih =>
    cases measured with
    | nil => simp at hlen
    | cons text measured =>
      have htail : measured.length = source.length := by simpa using hlen
      simpa using congrArg (List.cons value) (ih measured htail)

theorem measured_section_at (columns : List ModelBox) (titles : List (List Measure.Line))
    (hlen : titles.length = columns.length) (index : Nat) (hi : index < columns.length) :
    ∃ input ∈ (columns.zip titles).zipIdx,
      input.2 = index ∧ input.1.1 = columns[index] := by
  have hz : index < ((columns.zip titles).zipIdx).length := by
    simpa [hlen] using hi
  refine ⟨((columns.zip titles).zipIdx)[index], List.getElem_mem hz, ?_, ?_⟩
  · simp
  · simp

theorem section_inputs_ids (columns : List ModelBox) (titles : List (List Measure.Line))
    (hlen : titles.length = columns.length) :
    ((columns.zip titles).zipIdx).map (fun input => input.1.1.id) = columns.map (·.id) := by
  calc
    _ = (((columns.zip titles).zipIdx).map (·.1)).map (fun input => input.1.id) := by
      rw [List.map_map]
      rfl
    _ = (columns.zip titles).map (fun input => input.1.id) := by
      rw [List.zipIdx_map_fst]
    _ = ((columns.zip titles).map (·.1)).map (·.id) := by
      rw [List.map_map]
      rfl
    _ = columns.map (·.id) := by rw [zipped_sources columns titles hlen]

theorem native_card_pairwise (ownerOf : String → Nat) (cursors : List Int)
    (placed : List (String × Rect)) (pad gap band : Int)
    (hinv : CardInvariant pad gap band (numericState ownerOf cursors placed)) :
    placed.Pairwise (fun a b => ownerOf a.1 = ownerOf b.1 → Disjoint a.2 b.2) := by
  have hp : placed.reverse.Pairwise
      (fun a b => ownerOf a.1 = ownerOf b.1 → Disjoint a.2 b.2) :=
    List.pairwise_map.mp hinv.2.2
  have hr := List.pairwise_reverse.mp hp
  exact hr.imp (fun h heq => (Disjoint.comm _ _).mp (h heq.symm))

theorem native_card_members_disjoint (ownerOf : String → Nat)
    (placed : List (String × Rect)) (a b : String × Rect)
    (hp : placed.Pairwise (fun a b => ownerOf a.1 = ownerOf b.1 → Disjoint a.2 b.2))
    (ha : a ∈ placed) (hb : b ∈ placed) (hne : a.1 ≠ b.1)
    (howner : ownerOf a.1 = ownerOf b.1) : Disjoint a.2 b.2 := by
  induction placed with
  | nil => simp at ha
  | cons head rest ih =>
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hp
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact False.elim (hne rfl)
      · exact hhead b hb howner
    · rcases hb with rfl | hb
      · exact (Disjoint.comm _ _).mp (hhead a ha howner.symm)
      · exact ih hrest ha hb

theorem card_pass_ids (columns : List ModelBox)
    (inputs : List (ModelBox × List Measure.Line))
    (check : Rect → Except LayoutError Rect)
    (draw : ModelBox × List Measure.Line → Rect → Group)
    (pad width gap cardWidth band : Int)
    (height : ModelBox × List Measure.Line → Int)
    (final : NativeCardState)
    (hcheck : ∀ input output, check input = .ok output → output = input)
    (hrun : forIn inputs (List.replicate columns.length band, [], [])
      (cardStep columns check draw pad width gap cardWidth band height) = .ok final) :
    final.2.1.map (·.1) = inputs.map (fun input => input.1.id) := by
  have hids := forIn_emits_ids inputs
    (cardStep columns check draw pad width gap cardWidth band height)
    (fun input => input.1.id) (fun state => state.2.1.map (·.1))
    (List.replicate columns.length band, [], []) final
    (by
      intro input _ state next hs
      obtain ⟨owner, groups, _, rfl⟩ :=
        cardStep_shape columns check draw pad width gap cardWidth band height input state next hcheck hs
      exact ⟨_, rfl, by simp⟩) hrun
  simpa using hids

theorem card_inputs_ids (cards : List ModelBox) (texts : List (List Measure.Line))
    (hlen : texts.length = cards.length) :
    (cards.zip texts).map (fun input => input.1.id) = cards.map (·.id) := by
  calc
    _ = ((cards.zip texts).map (·.1)).map (·.id) := by
      rw [List.map_map]
      rfl
    _ = cards.map (·.id) := by rw [zipped_sources cards texts hlen]

theorem card_pass_owner_coverage (columns : List ModelBox)
    (inputs : List (ModelBox × List Measure.Line))
    (check : Rect → Except LayoutError Rect)
    (draw : ModelBox × List Measure.Line → Rect → Group)
    (pad width gap cardWidth band : Int)
    (height : ModelBox × List Measure.Line → Int)
    (final : NativeCardState)
    (hcheck : ∀ input output, check input = .ok output → output = input)
    (hrun : forIn inputs (List.replicate columns.length band, [], [])
      (cardStep columns check draw pad width gap cardWidth band height) = .ok final) :
    ∀ entry ∈ final.2.1, ∃ input ∈ inputs, ∃ owner,
      entry.1 = input.1.id ∧
      columns.findIdx? (fun col => col.id == input.1.parent) = some owner := by
  let invariant := fun state : NativeCardState =>
    ∀ entry ∈ state.2.1, ∃ input ∈ inputs, ∃ owner,
      entry.1 = input.1.id ∧
      columns.findIdx? (fun col => col.id == input.1.parent) = some owner
  apply forIn_preserves inputs
    (cardStep columns check draw pad width gap cardWidth band height)
    invariant (List.replicate columns.length band, [], []) final ?_ ?_ hrun
  · intro entry hentry
    simp at hentry
  · intro input hi state next hinv hs
    obtain ⟨owner, groups, howner, rfl⟩ :=
      cardStep_shape columns check draw pad width gap cardWidth band height input state next hcheck hs
    intro entry hentry
    change entry ∈ state.2.1 ++ [_] at hentry
    simp only [List.mem_append, List.mem_singleton] at hentry
    rcases hentry with hold | rfl
    · exact hinv entry hold
    · exact ⟨input, hi, owner, rfl, howner⟩

theorem native_section_pass_retains_cards (inputs : List SectionInput)
    (base : List (String × Rect)) (rectFor : SectionInput → Rect) (pad : Int)
    (step : SectionInput → NativeSectionState → Except LayoutError (ForInStep NativeSectionState))
    (final : NativeSectionState)
    (hshape : ∀ input ∈ inputs, ∀ state next, step input state = .ok next →
      SectionStepShape rectFor input state next)
    (hrun : forIn inputs (base, [], pad, pad) step = .ok final) :
    ∀ entry ∈ base, entry ∈ final.1 := by
  apply forIn_preserves inputs step
    (fun state => ∀ entry ∈ base, entry ∈ state.1)
    (base, [], pad, pad) final ?_ ?_ hrun
  · intro entry he
    exact he
  · intro input hi state next hinv hs
    obtain ⟨groups, rfl⟩ := hshape input hi state next hs
    intro entry he
    exact List.mem_append.mpr (Or.inl (hinv entry he))

theorem final_placement_ids (cards columns : List ModelBox)
    (texts titles : List (List Measure.Line))
    (cardFinal : NativeCardState) (sectionFinal : NativeSectionState)
    (htexts : texts.length = cards.length) (htitles : titles.length = columns.length)
    (hcards : cardFinal.2.1.map (·.1) = (cards.zip texts).map (fun input => input.1.id))
    (hcolumns : sectionFinal.1.map (·.1) = cardFinal.2.1.map (·.1) ++
      ((columns.zip titles).zipIdx).map (fun input => input.1.1.id)) :
    sectionFinal.1.map (·.1) = cards.map (·.id) ++ columns.map (·.id) := by
  rw [hcolumns, hcards, card_inputs_ids cards texts htexts, section_inputs_ids columns titles htitles]

end Elegant.GridKanban

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

theorem measured_section_at (columns : List ModelBox) (titles : List (List Measure.Line))
    (hlen : titles.length = columns.length) (index : Nat) (hi : index < columns.length) :
    ∃ input ∈ (columns.zip titles).zipIdx,
      input.2 = index ∧ input.1.1 = columns[index] := by
  have hz : index < ((columns.zip titles).zipIdx).length := by
    simpa [hlen] using hi
  refine ⟨((columns.zip titles).zipIdx)[index], List.getElem_mem hz, ?_, ?_⟩
  · simp
  · simp

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

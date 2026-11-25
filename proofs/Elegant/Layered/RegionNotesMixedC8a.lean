import Elegant.DumpLaminar
import Elegant.Layered.NotesBundleParentAlignment
import Elegant.Layered.NotesC8aRoleRepair
import Elegant.Layered.NotesMirrorFacts
import Elegant.Layered.RecursiveC1C3

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private def mixedInputBox (b : ModelBox) : Box :=
  Box.mk b.id b.role.id ⟨0, 0, 0, 0⟩ b.parent b.exclusive

private theorem mixedInputBox_found {inp : Input} (hf : InputFacts inp) {b : ModelBox}
    (hb : b ∈ inp.boxes) : (inpDumpOf inp).box? b.id = some (mixedInputBox b) := by
  change (modelBoxesToDump inp.boxes).find? (fun q => q.id == (mixedInputBox b).id) =
    some (mixedInputBox b)
  apply Elegant.findBox_eq_self
  · simpa only [modelBoxesToDump, List.map_map, Function.comp_def] using hf.nodup
  · change mixedInputBox b ∈ inp.boxes.map mixedInputBox
    exact List.mem_map_of_mem hb

private theorem mixedInput_length (inp : Input) :
    (inpDumpOf inp).boxes.length = inp.boxes.length := List.length_map _

private theorem mixedInput_walk {inp : Input} (hf : InputFacts inp) (n : Nat)
    {b : ModelBox} (hb : b ∈ inp.boxes) (ht : chainTerm inp.boxes n b.parent = true)
    (m : Nat) (hle : n ≤ m) :
    (Compound.ancestors inp.boxes n b.parent).reverse.filterMap
      (fun i => (inp.boxes[i]?).map (·.id)) =
    LayoutDump.ancestors.go (inpDumpOf inp) m b.id := by
  induction n generalizing b m with
  | zero =>
    have hpar : b.parent = "" := by
      by_cases hp : b.parent = ""
      · exact hp
      · rw [chainTerm.eq_2 _ _ hp] at ht
        cases ht
    have hbox := mixedInputBox_found hf hb
    cases m <;> simp [Compound.ancestors, LayoutDump.ancestors.go, hbox, mixedInputBox, hpar]
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      have hbox := mixedInputBox_found hf hb
      by_cases hpar : b.parent = ""
      · simp [CompoundHelpers.ancestors_empty, hpar, LayoutDump.ancestors.go, hbox, mixedInputBox]
      · rw [chainTerm.eq_3 _ _ _ hpar] at ht
        rw [Compound.ancestors.eq_3 _ _ _ hpar]
        cases hidx : inp.boxes.findIdx? (fun x => x.id == b.parent) with
        | none => simp [hidx] at ht
        | some i =>
          cases hget : inp.boxes[i]? with
          | none => simp [hidx, hget] at ht
          | some p =>
            have htail : chainTerm inp.boxes n p.parent = true := by
              simpa only [hidx, hget] using ht
            obtain ⟨_, htest, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hidx
            obtain ⟨_, hval⟩ := List.getElem?_eq_some_iff.mp hget
            have hpid : p.id = b.parent := by
              rw [← hval]
              exact beq_iff_eq.mp htest
            have hrec := ih (b := p) (m := m) (getElem?_mem' hget) htail
              (Nat.le_of_succ_le_succ hle)
            simp only [hget, List.reverse_append, List.reverse_singleton,
              List.singleton_append, List.filterMap_cons, Option.map_some,
              LayoutDump.ancestors.go, hbox, mixedInputBox, hpar, ↓reduceIte]
            rw [← hpid, hrec]

private theorem mixedInside_ancestor {inp : Input} (hf : InputFacts inp) {a s : String}
    (h : Compound.inside inp.boxes a s = true) : a ∈ (inpDumpOf inp).ancestors s := by
  obtain ⟨b, hb, hbid, i, _, aBox, hai, haId, hi⟩ := inside_spec h
  have ht := hf.term b hb inp.boxes.length (by omega)
  unfold LayoutDump.ancestors
  rw [← hbid, mixedInput_length, ← mixedInput_walk hf inp.boxes.length hb ht _ (Nat.le_refl _)]
  exact List.mem_filterMap.mpr ⟨i, List.mem_reverse.mpr hi, by simp only [hai, Option.map_some, haId]⟩

private theorem mixedAncestor_inside {inp : Input} (hf : InputFacts inp) {a : String}
    {b : ModelBox} (hb : b ∈ inp.boxes) (h : a ∈ (inpDumpOf inp).ancestors b.id) :
    Compound.inside inp.boxes a b.id = true := by
  have ht := hf.term b hb inp.boxes.length (by omega)
  unfold LayoutDump.ancestors at h
  rw [mixedInput_length, ← mixedInput_walk hf inp.boxes.length hb ht _ (Nat.le_refl _)] at h
  obtain ⟨i, hi, himap⟩ := List.mem_filterMap.mp h
  cases hget : inp.boxes[i]? with
  | none => simp [hget] at himap
  | some p =>
    have hpid : p.id = a := Option.some.inj (by simpa only [hget, Option.map_some] using himap)
    have hidx : inp.boxes.findIdx? (fun x => x.id == a) = some i := by
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hget
      apply List.findIdx?_eq_some_iff_getElem.mpr
      refine ⟨hlt, by simp only [heq, hpid, beq_self_eq_true], ?_⟩
      intro j hj htest
      have hji : j = i := by
        apply hf.nodup.eq_of_getElem_eq
          (by simpa only [List.length_map] using Nat.lt_trans hj hlt)
          (by simpa only [List.length_map] using hlt)
        simpa only [List.getElem_map, heq, hpid] using (beq_iff_eq.mp htest)
      omega
    exact inside_of_ancestors hf.nodup hb rfl hidx (List.mem_reverse.mp hi)

private theorem mixedInput_trans {inp : Input} (hf : InputFacts inp) {a top : String}
    {b : ModelBox} (hb : b ∈ inp.boxes) (ha : a ∈ (inpDumpOf inp).ancestors top)
    (htop : top ∈ (inpDumpOf inp).ancestors b.id) : a ∈ (inpDumpOf inp).ancestors b.id := by
  unfold LayoutDump.ancestors at ha htop ⊢
  rw [mixedInput_length] at ha htop ⊢
  have ht := hf.term b hb inp.boxes.length (by omega)
  have hmore := Elegant.go_trans inp.boxes.length inp.boxes.length a top b.id ha htop
  have hsum : inp.boxes.length ≤ inp.boxes.length + inp.boxes.length := by omega
  rw [← mixedInput_walk hf inp.boxes.length hb ht _ hsum] at hmore
  rw [← mixedInput_walk hf inp.boxes.length hb ht _ (Nat.le_refl _)]
  exact hmore

private theorem mixedInput_ancestors_eq {inp : Input} (hf : InputFacts inp) {a b : ModelBox}
    (ha : a ∈ inp.boxes) (hb : b ∈ inp.boxes) (hpar : a.parent = b.parent) :
    (inpDumpOf inp).ancestors a.id = (inpDumpOf inp).ancestors b.id := by
  unfold LayoutDump.ancestors
  cases (inpDumpOf inp).boxes.length with
  | zero => rfl
  | succ _ =>
    simp only [LayoutDump.ancestors.go, mixedInputBox_found hf ha, mixedInputBox_found hf hb,
      mixedInputBox, hpar]

private theorem mixedUnclaimed_not_fragment {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) (hfound : NotesC8aFragFound e) {id : String}
    (hfree : ∀ q ∈ e.fragments, ∀ r : Rect, q.rect id ≠ some r)
    {l : BundleLayout} (hl : l ∈ e.layouts) : fragmentIdOf inp l id ≠ true := by
  intro hfrag
  obtain ⟨p, hp, hboxes⟩ := List.any_eq_true.mp (hfound l hl id hfrag)
  obtain ⟨b, hb, hid⟩ := List.any_eq_true.mp hboxes
  have hpf : p ∈ e.fragments := by
    rw [e.fragments_eq]
    exact placedOf_mem_flatten e.placed_eq hl hp
  cases hfind : p.scene.boxes.find? (fun x => x.id == id) with
  | none => exact (List.find?_eq_none.mp hfind b hb) hid
  | some b' =>
    exact hfree p hpf (shiftRect p.dx p.dy b'.rect) (by simp only [Placed.rect, hfind, Option.map_some])

private theorem mixedPart_input_member {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    {e : NotesExecution base exactIds fuel inp o res} (hfrag : NotesBaseFrag e)
    {l : BundleLayout} (hl : l ∈ e.layouts) {sb : Box} (hsb : sb ∈ l.part.scene.boxes) :
    ∃ b ∈ inp.boxes, b.id = sb.id ∧
      (b.id = l.top.id ∨ Compound.inside inp.boxes l.top.id b.id = true) := by
  obtain ⟨mb, hmb, hid, _, _⟩ := (hfrag l hl).1.2 sb hsb
  let keep : ModelBox → Bool := fun x => x.id == l.top.id || Compound.inside inp.boxes l.top.id x.id
  change mb ∈ ((selectInput inp keep).boxes.map fun b =>
    if b.id == l.top.id then { b with parent := "" } else b) at hmb
  obtain ⟨selected, hs, heq⟩ := List.mem_map.mp hmb
  obtain ⟨b, hb, hkeep, hselectId, _⟩ := selectInput_box_spec inp keep "" hs
  have hmid : selected.id = mb.id := by
    rw [← heq]
    split <;> rfl
  refine ⟨b, hb, (hid.trans (hmid.symm.trans hselectId)).symm, ?_⟩
  simpa only [keep, Bool.or_eq_true, beq_iff_eq] using hkeep

private theorem mixedBaseContract
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    {e : NotesExecution base exactIds fuel inp o res}
    (h : NotesBoxMirror e.contractedInput e.contracted) : NotesBaseContract e := by
  refine ⟨h.1, ?_⟩
  intro c hc
  obtain ⟨b, hb, hid, hpar, hexc, _⟩ := h.2 c hc
  exact ⟨b, hb, hid, hpar, hexc⟩

/-- A kept group unrelated to the bundle top clears the whole envelope,
independently of which fragment supplies the placed box. -/
theorem mixedNotesC8aClear_keptGroup_of_foreignTop
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hbase : ∀ ids sub opt result, base ids sub opt = .ok result → NotesBoxMirror sub result)
    (hfit : NotesC8aEnv e) (hc8a : Validator.C8a e.contracted.scene.layoutDump)
    {l : BundleLayout} (hl : l ∈ e.layouts) {p : Placed}
    (hp : p ∈ placedOf' e.margin e.contracted.scene l)
    {sb cb : Box} (hsb : sb ∈ p.scene.boxes) (hcb : cb ∈ e.contracted.scene.boxes)
    (hfree : ∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r)
    (hforeignTop : cb.id ∉ (inpDumpOf inp).ancestors l.top.id)
    (hgroup : ∃ ib ∈ inp.boxes, ib.id = cb.id ∧ ib.role.id = "group") :
    Disjoint (shiftRect p.dx p.dy sb.rect) cb.rect := by
  have hf := inputFacts_of_wellFormed hwf
  have hboxed := hbase _ _ _ _ e.contracted_eq
  have hcontract := mixedBaseContract (e := e) hboxed
  have hrole := notesC8aContractRoleT_holds e hf.nodup (by
    intro c hc
    obtain ⟨b, hb, hi, _, _, hr⟩ := hboxed.2 c hc
    rw [e.contractedInput_eq] at hb
    exact ⟨b, hb, hi.symm, hr⟩)
  have hfrag := notesBaseFrag_of_box_mirror hbase e
  have hfound := notesC8aFragFound_of_base e hfrag
  have hsubc := notesC6AncC_of_base e hf.nodup hcontract
  obtain ⟨ib, hib, hid, hgr⟩ := hgroup
  have hnot : ∀ {a}, a ∈ e.layouts → fragmentIdOf inp a cb.id ≠ true :=
    fun ha => mixedUnclaimed_not_fragment e hfound hfree ha
  have hne : l.top.id ≠ cb.id := by
    intro heq
    exact hnot hl (by simp only [fragmentIdOf, heq, beq_self_eq_true, Bool.true_or])
  have hcRole : cb.role = "group" := by
    obtain ⟨b, hb, hr⟩ := hrole cb hcb
    rcases hr with hkept | ⟨a, ha, haId, _, _⟩
    · have hbId : b.id = cb.id := beq_iff_eq.mp
        (List.find?_some (p := fun candidate : ModelBox => candidate.id == cb.id) hb)
      have heq := eq_of_mem_id hf.nodup (List.mem_of_find?_eq_some hb) hib (hbId.trans hid.symm)
      rw [← hkept, heq]
      exact hgr
    · exact False.elim (hnot ha (by simp only [fragmentIdOf, haId, beq_self_eq_true, Bool.true_or]))
  have htopNotInCb : l.top.id ∉ (inpDumpOf inp).ancestors cb.id := by
    intro ha
    have hin : Compound.inside inp.boxes l.top.id cb.id = true := by
      rw [← hid] at ha ⊢
      exact mixedAncestor_inside hf hib ha
    exact hnot hl (by simp only [fragmentIdOf, hin, Bool.or_true, Bool.true_or])
  cases henvelope : e.contracted.scene.boxes.find? (fun b => b.id == l.top.id) with
  | none =>
    simp only [placedOf'] at hp
    unfold placedFragments at hp
    rw [henvelope] at hp
    exact absurd (show p ∈ ([] : List Placed) from hp) (by simp)
  | some eb =>
    have heb := List.mem_of_find?_eq_some henvelope
    have heid : eb.id = l.top.id := beq_iff_eq.mp
      (List.find?_some (p := fun candidate : Box => candidate.id == l.top.id) henvelope)
    have ha : cb.id ∉ e.contracted.scene.layoutDump.ancestors eb.id := by
      intro hm
      exact hforeignTop (by simpa only [heid] using hsubc eb.id cb.id hm)
    have hb : eb.id ∉ e.contracted.scene.layoutDump.ancestors cb.id := by
      intro hm
      exact htopNotInCb (by simpa only [heid] using hsubc cb.id eb.id hm)
    have hdisj := hc8a cb hcb hcRole eb heb (by simpa only [heid] using hne) ha hb
    have hcontained := hfit l hl p hp sb hsb
    rw [envRect, henvelope] at hcontained
    exact Disjoint.of_contained_left hcontained ((Disjoint.comm _ _).mp hdisj)

/-- A box in the part inherits its bundle top's ancestors. -/
theorem mixedNotesC8aClear_part_keptGroup
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hbase : ∀ ids sub opt result, base ids sub opt = .ok result → NotesBoxMirror sub result)
    (hfit : NotesC8aEnv e) (hc8a : Validator.C8a e.contracted.scene.layoutDump)
    {l : BundleLayout} (hl : l ∈ e.layouts) {p : Placed}
    (hp : p ∈ placedOf' e.margin e.contracted.scene l) (hpart : p.scene = l.part.scene)
    {sb cb : Box} (hsb : sb ∈ p.scene.boxes) (hcb : cb ∈ e.contracted.scene.boxes)
    (hfree : ∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r)
    (hforeign : cb.id ∉ (inpDumpOf inp).ancestors sb.id)
    (hgroup : ∃ ib ∈ inp.boxes, ib.id = cb.id ∧ ib.role.id = "group") :
    Disjoint (shiftRect p.dx p.dy sb.rect) cb.rect := by
  refine mixedNotesC8aClear_keptGroup_of_foreignTop e hwf hbase hfit hc8a
    hl hp hsb hcb hfree ?_ hgroup
  intro ha
  have hf := inputFacts_of_wellFormed hwf
  have hfrag := notesBaseFrag_of_box_mirror hbase e
  have hsb' : sb ∈ l.part.scene.boxes := hpart ▸ hsb
  obtain ⟨b, hb, hbId, hdesc⟩ := mixedPart_input_member hfrag hl hsb'
  apply hforeign
  rw [← hbId]
  rcases hdesc with hself | hin
  · rw [hself]
    exact ha
  · exact mixedInput_trans hf hb ha (mixedInside_ancestor hf hin)

/-- A placed note and its bundle top have the same input ancestors when the
existing attachment-parent check holds. The note's role plays no part. -/
theorem mixedNotesC8aClear_note_keptGroup
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hparents : attachedNoteParents inp = true)
    (hbase : ∀ ids sub opt result, base ids sub opt = .ok result → NotesBoxMirror sub result)
    (hfit : NotesC8aEnv e) (hc8a : Validator.C8a e.contracted.scene.layoutDump)
    {l : BundleLayout} (hl : l ∈ e.layouts) {p : Placed}
    (hp : p ∈ placedOf' e.margin e.contracted.scene l) (hnote : p.scene ≠ l.part.scene)
    {sb cb : Box} (hsb : sb ∈ p.scene.boxes) (hcb : cb ∈ e.contracted.scene.boxes)
    (hfree : ∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r)
    (hforeign : cb.id ∉ (inpDumpOf inp).ancestors sb.id)
    (hgroup : ∃ ib ∈ inp.boxes, ib.id = cb.id ∧ ib.role.id = "group") :
    Disjoint (shiftRect p.dx p.dy sb.rect) cb.rect := by
  refine mixedNotesC8aClear_keptGroup_of_foreignTop e hwf hbase hfit hc8a
    hl hp hsb hcb hfree ?_ hgroup
  have hf := inputFacts_of_wellFormed hwf
  have hfrag := notesBaseFrag_of_box_mirror hbase e
  have hcontract := mixedBaseContract (e := e) (hbase _ _ _ _ e.contracted_eq)
  have hpar := notesBundleNoteParent_holds e hparents
  obtain ⟨top, ht, htId, hnotes, _⟩ := notesParentAlign_holds e hcontract hpar hf.nodup l hl
  rcases notesFragMirrorT_holds e hfrag hf.nodup l hl p hp with
    ⟨hpart, _, _, _⟩ | ⟨q, hq, _, _, _, hboxes⟩
  · exact (hnote hpart).elim
  · obtain ⟨hid, _, _⟩ := hboxes sb hsb
    obtain ⟨hqmem, hqpar⟩ := hnotes q hq
    have hanc := mixedInput_ancestors_eq hf hqmem ht hqpar
    rw [← htId, ← hanc, ← hid]
    exact hforeign

/-- Mixed clearance outside the part-scene case with a contracted input group. -/
def NotesC8aClearExceptPartKeptGroup
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res) : Prop :=
  ∀ l ∈ e.layouts, ∀ p ∈ placedOf' e.margin e.contracted.scene l,
    ∀ sb ∈ p.scene.boxes, ∀ cb ∈ e.contracted.scene.boxes,
      (∀ q ∈ e.fragments, ∀ r : Rect, q.rect cb.id ≠ some r) →
      sb.id ≠ cb.id →
      sb.id ∉ (inpDumpOf inp).ancestors cb.id →
      cb.id ∉ (inpDumpOf inp).ancestors sb.id →
      (∃ ib ∈ inp.boxes, ib.role.id = "group" ∧ (ib.id = sb.id ∨ ib.id = cb.id)) →
      ¬ (p.scene = l.part.scene ∧ ∃ ib ∈ inp.boxes, ib.id = cb.id ∧ ib.role.id = "group") →
      Disjoint (shiftRect p.dx p.dy sb.rect) cb.rect

/-- Fill the part-versus-kept-group case from the contracted validator clause
and envelope containment, leaving the other mixed pairs to the caller. -/
theorem notesC8aClear_of_exceptPartKeptGroup
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (e : NotesExecution base exactIds fuel inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hbase : ∀ ids sub opt result, base ids sub opt = .ok result → NotesBoxMirror sub result)
    (hremaining : NotesC8aClearExceptPartKeptGroup e)
    (henv : NotesC8aEnv e) (hc8a : Validator.C8a e.contracted.scene.layoutDump) :
    NotesC8aClear e := by
  classical
  unfold NotesC8aClear MixedNotesC8aClear
  intro l hl p hp sb hsb cb hcb hfree hne hanc hforeign hgroup
  by_cases hhandled : p.scene = l.part.scene ∧
      ∃ ib ∈ inp.boxes, ib.id = cb.id ∧ ib.role.id = "group"
  · exact mixedNotesC8aClear_part_keptGroup e hwf hbase henv hc8a hl hp hhandled.1
      hsb hcb hfree hforeign hhandled.2
  · exact hremaining l hl p hp sb hsb cb hcb hfree hne hanc hforeign hgroup hhandled

end Elegant.Layered.PipelineImpl

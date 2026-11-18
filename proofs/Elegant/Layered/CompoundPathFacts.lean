import Elegant.Layered.Compound

set_option autoImplicit false

namespace Elegant.Layered.Compound

private theorem index_of_lookup {boxes : List ModelBox}
    (hids : (boxes.map (·.id)).Nodup) {i : Nat} {box : ModelBox}
    (hb : boxes[i]? = some box) :
    boxes.findIdx? (fun b => b.id == box.id) = some i := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hb
  apply List.findIdx?_eq_some_iff_getElem.mpr
  refine ⟨hi, ?_, ?_⟩
  · simp only [he, beq_self_eq_true]
  · intro j hj hsame
    have hji : j = i := by
      apply hids.eq_of_getElem_eq
        (by simpa only [List.length_map] using Nat.lt_trans hj hi)
        (by simpa only [List.length_map] using hi)
      simpa only [List.getElem_map, he] using (beq_iff_eq.mp hsame)
    omega

private def CountWitness (boxes : List ModelBox) (id : String) : Prop :=
  ∃ d : Nat, ∀ fuel : Nat, (ancestors boxes fuel id).length = min fuel d

private theorem count_root (boxes : List ModelBox) : CountWitness boxes "" := by
  refine ⟨0, ?_⟩
  intro fuel
  cases fuel <;> simp [ancestors]

private theorem count_all (m : Model) (hwf : WellFormed m) :
    ∀ id, CountWitness m.boxes id := by
  have step : ∀ b, b ∈ m.boxes → CountWitness m.boxes b.parent →
      CountWitness m.boxes b.id := by
    intro b hb hp
    by_cases hid : b.id = ""
    · simpa only [hid] using count_root m.boxes
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
      have hf := index_of_lookup (Model.boxIds_nodup hwf) hi
      obtain ⟨d, hd⟩ := hp
      refine ⟨d + 1, ?_⟩
      intro fuel
      cases fuel with
      | zero => simp [ancestors]
      | succ fuel =>
        simp only [ancestors, hf, hi, List.length_append, List.length_singleton]
        rw [hd fuel]
        omega
  have parents := parent_induction m hwf (CountWitness m.boxes) (count_root m.boxes) step
  intro id
  by_cases hid : id = ""
  · subst id
    exact count_root m.boxes
  · cases hf : m.boxes.findIdx? (fun b => b.id == id) with
    | none =>
      refine ⟨0, ?_⟩
      intro fuel
      cases fuel <;> simp [ancestors, hf]
    | some i =>
      obtain ⟨hi, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      have hb : m.boxes[i] ∈ m.boxes := List.getElem_mem hi
      have he : (m.boxes[i]).id = id := beq_iff_eq.mp hmatch
      rw [← he]
      exact step _ hb (parents _ hb)

private noncomputable def height (m : Model) (hwf : WellFormed m) (id : String) : Nat :=
  Classical.choose (count_all m hwf id)

private theorem height_count (m : Model) (hwf : WellFormed m) (id : String) (fuel : Nat) :
    (ancestors m.boxes fuel id).length = min fuel (height m hwf id) :=
  Classical.choose_spec (count_all m hwf id) fuel

private theorem height_step (m : Model) (hwf : WellFormed m) {i : Nat} {b : ModelBox}
    (hb : m.boxes[i]? = some b) (hne : b.id ≠ "") :
    height m hwf b.id = height m hwf b.parent + 1 := by
  have hf := index_of_lookup (Model.boxIds_nodup hwf) hb
  let fuel := max (height m hwf b.id) (height m hwf b.parent) + 1
  have hc := height_count m hwf b.id (fuel + 1)
  have hp := height_count m hwf b.parent fuel
  simp only [ancestors, hf, hb, List.length_append, List.length_singleton] at hc
  dsimp only [fuel] at hc hp
  omega

private theorem ancestors_indices (m : Model) (hwf : WellFormed m) (fuel : Nat) (id : String) :
    (ancestors m.boxes fuel id).Nodup ∧
      ∀ i ∈ ancestors m.boxes fuel id,
        ∃ b, m.boxes[i]? = some b ∧ height m hwf b.id ≤ height m hwf id := by
  induction fuel generalizing id with
  | zero => simp [ancestors]
  | succ fuel ih =>
    by_cases hid : id = ""
    · subst id
      simp [ancestors]
    · cases hf : m.boxes.findIdx? (fun b => b.id == id) with
      | none => simp [ancestors, hf]
      | some i =>
        obtain ⟨hi, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        let b := m.boxes[i]
        have hb : m.boxes[i]? = some b := List.getElem?_eq_getElem hi
        have he : b.id = id := beq_iff_eq.mp hmatch
        have hs := height_step m hwf hb (by simpa only [he] using hid)
        obtain ⟨hnd, hmem⟩ := ih b.parent
        have hnot : i ∉ ancestors m.boxes fuel b.parent := by
          intro hin
          obtain ⟨other, ho, hlt⟩ := hmem i hin
          have heq : other = b := Option.some.inj (ho.symm.trans hb)
          subst other
          omega
        simp only [ancestors, hf, hb]
        constructor
        · apply List.nodup_append.mpr
          refine ⟨hnd, by simp, ?_⟩
          intro a ha c hc
          have hc' : c = i := by simpa using hc
          subst c
          intro hai
          subst a
          exact hnot ha
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨other, ho, hlt⟩ := hmem a ha
            refine ⟨other, ho, ?_⟩
            rw [← he]
            omega
          · have ha' : a = i := by simpa using ha
            subst a
            refine ⟨b, hb, ?_⟩
            rw [← he]
            omega

private theorem height_bound (m : Model) (hwf : WellFormed m) (id : String) :
    height m hwf id ≤ m.boxes.length := by
  let fuel := height m hwf id
  have hi := ancestors_indices m hwf fuel id
  have hsub : ancestors m.boxes fuel id ⊆ List.range m.boxes.length := by
    intro i hm
    obtain ⟨b, hb, _⟩ := hi.2 i hm
    exact List.mem_range.mpr (List.getElem?_eq_some_iff.mp hb).1
  have hlen := hi.1.length_le_of_subset hsub
  have hc := height_count m hwf id fuel
  simp only [List.length_range] at hlen
  dsimp only [fuel] at hc hlen
  omega

private theorem ancestors_suffix (boxes : List ModelBox) (small large : Nat)
    (hle : small ≤ large) (id : String) :
    ancestors boxes small id <:+ ancestors boxes large id := by
  induction small generalizing large id with
  | zero => simp [ancestors]
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      by_cases hid : id = ""
      · subst id
        simp [ancestors]
      · cases hf : boxes.findIdx? (fun b => b.id == id) with
        | none => simp [ancestors, hf]
        | some i =>
          cases hb : boxes[i]? with
          | none => simp [ancestors, hf, hb]
          | some b =>
            obtain ⟨pre, he⟩ := ih large (by omega) b.parent
            refine ⟨pre, ?_⟩
            simp only [ancestors, hf, hb]
            rw [← List.append_assoc, he]

private theorem ancestors_stable (m : Model) (hwf : WellFormed m) (id : String)
    (a b : Nat) (ha : height m hwf id ≤ a) (hb : height m hwf id ≤ b) :
    ancestors m.boxes a id = ancestors m.boxes b id := by
  have hca := height_count m hwf id a
  have hcb := height_count m hwf id b
  have hlen : (ancestors m.boxes a id).length = (ancestors m.boxes b id).length := by
    omega
  rcases Nat.le_total a b with hab | hba
  · exact (ancestors_suffix m.boxes a b hab id).eq_of_length hlen
  · exact ((ancestors_suffix m.boxes b a hba id).eq_of_length hlen.symm).symm

private theorem ancestor_prefix (m : Model) (hwf : WellFormed m) (fuel : Nat)
    (id : String) (hfull : height m hwf id ≤ fuel) {i : Nat} {group : ModelBox}
    (hg : m.boxes[i]? = some group) (hin : i ∈ ancestors m.boxes fuel id) :
    (path m.boxes group ++ [i]) <+: ancestors m.boxes fuel id := by
  induction fuel generalizing id with
  | zero => simp [ancestors] at hin
  | succ fuel ih =>
    by_cases hid : id = ""
    · subst id
      simp [ancestors] at hin
    · cases hf : m.boxes.findIdx? (fun b => b.id == id) with
      | none => simp [ancestors, hf] at hin
      | some k =>
        obtain ⟨hk, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        let b := m.boxes[k]
        have hb : m.boxes[k]? = some b := List.getElem?_eq_getElem hk
        have he : b.id = id := beq_iff_eq.mp hmatch
        have hs := height_step m hwf hb (by simpa only [he] using hid)
        have hp : height m hwf b.parent ≤ fuel := by
          rw [← he] at hfull
          omega
        simp only [ancestors, hf, hb] at hin ⊢
        rcases List.mem_append.mp hin with hin | hin
        · obtain ⟨tail, htail⟩ := ih b.parent hp hin
          refine ⟨tail ++ [k], ?_⟩
          rw [← List.append_assoc, htail]
        · have hik : i = k := by simpa using hin
          subst i
          have hgb : group = b := Option.some.inj (hg.symm.trans hb)
          subst group
          have hstable := ancestors_stable m hwf b.parent m.boxes.length fuel
            (height_bound m hwf b.parent) hp
          have heq : path m.boxes b = ancestors m.boxes fuel b.parent := hstable
          rw [heq]
          exact List.prefix_refl _

theorem path_ancestor_prefix (m : Model) (hwf : WellFormed m)
    {i j : Nat} {group member : ModelBox}
    (hg : m.boxes[i]? = some group) (_hm : m.boxes[j]? = some member)
    (hin : i ∈ path m.boxes member) :
    (path m.boxes group ++ [i]) <+: path m.boxes member :=
  ancestor_prefix m hwf m.boxes.length member.parent (height_bound m hwf member.parent) hg hin

theorem path_of_parent (m : Model) (hwf : WellFormed m)
    {i j : Nat} {parent child : ModelBox}
    (hp : m.boxes[i]? = some parent) (hc : m.boxes[j]? = some child)
    (hparent : child.parent = parent.id) (hne : child.parent ≠ "") :
    path m.boxes child = path m.boxes parent ++ [i] := by
  have hpid : parent.id ≠ "" := by
    rw [← hparent]
    exact hne
  have hf := index_of_lookup (Model.boxIds_nodup hwf) hp
  have hs := height_step m hwf hp hpid
  have hb := height_bound m hwf parent.id
  have hj := (List.getElem?_eq_some_iff.mp hc).1
  have hlen : m.boxes.length = (m.boxes.length - 1) + 1 := by omega
  have hshort : height m hwf parent.parent ≤ m.boxes.length - 1 := by omega
  have hstable := ancestors_stable m hwf parent.parent (m.boxes.length - 1)
    m.boxes.length hshort (height_bound m hwf parent.parent)
  change ancestors m.boxes m.boxes.length child.parent =
    ancestors m.boxes m.boxes.length parent.parent ++ [i]
  rw [hparent]
  calc
    ancestors m.boxes m.boxes.length parent.id =
        ancestors m.boxes ((m.boxes.length - 1) + 1) parent.id :=
      congrArg (fun fuel => ancestors m.boxes fuel parent.id) hlen
    _ = ancestors m.boxes (m.boxes.length - 1) parent.parent ++ [i] := by
      simp only [ancestors, hf, hp]
    _ = ancestors m.boxes m.boxes.length parent.parent ++ [i] :=
      congrArg (fun indices => indices ++ [i]) hstable

theorem findIdx_map (boxes : List ModelBox) (f : ModelBox → ModelBox)
    (hid : ∀ b ∈ boxes, (f b).id = b.id) (id : String) :
    (boxes.map f).findIdx? (fun b => b.id == id) =
      boxes.findIdx? (fun b => b.id == id) := by
  induction boxes with
  | nil => simp
  | cons b boxes ih =>
    simp only [List.map_cons, List.findIdx?_cons, hid b (List.mem_cons_self ..)]
    rw [ih (fun b hb => hid b (List.mem_cons_of_mem _ hb))]

theorem ancestors_map (boxes : List ModelBox) (f : ModelBox → ModelBox)
    (hid : ∀ b ∈ boxes, (f b).id = b.id)
    (hp : ∀ b ∈ boxes, (f b).parent = b.parent) (fuel : Nat) (id : String) :
    ancestors (boxes.map f) fuel id = ancestors boxes fuel id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih =>
    by_cases he : id = ""
    · subst id
      simp [ancestors]
    · simp only [ancestors, findIdx_map boxes f hid id]
      cases hf : boxes.findIdx? (fun b => b.id == id) with
      | none => rfl
      | some i =>
        cases hb : boxes[i]? with
        | none => simp [List.getElem?_map, hb]
        | some b =>
          have hm : b ∈ boxes := List.mem_of_getElem? hb
          simp only [List.getElem?_map, hb, Option.map_some, hp b hm]
          rw [ih]

theorem path_map (boxes : List ModelBox) (f : ModelBox → ModelBox)
    (hid : ∀ b ∈ boxes, (f b).id = b.id)
    (hp : ∀ b ∈ boxes, (f b).parent = b.parent)
    {b : ModelBox} (hb : b ∈ boxes) :
    path (boxes.map f) (f b) = path boxes b := by
  unfold path
  rw [List.length_map, hp b hb]
  exact ancestors_map boxes f hid hp boxes.length b.parent

theorem path_index_map (boxes : List ModelBox) (f : ModelBox → ModelBox)
    (hid : ∀ b ∈ boxes, (f b).id = b.id)
    (hp : ∀ b ∈ boxes, (f b).parent = b.parent)
    {i : Nat} {b : ModelBox} (hb : boxes[i]? = some b) :
    (boxes.map f).length = boxes.length ∧
      (boxes.map f)[i]? = some (f b) ∧
      path (boxes.map f) (f b) = path boxes b := by
  refine ⟨List.length_map f, ?_, path_map boxes f hid hp (List.mem_of_getElem? hb)⟩
  simp only [List.getElem?_map, hb, Option.map_some]

end Elegant.Layered.Compound

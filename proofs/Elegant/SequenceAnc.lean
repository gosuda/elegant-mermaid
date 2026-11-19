import Elegant.Sequence

set_option autoImplicit false

/-! Parent chains of the sequence model: the ancestors of a box by id, the chain of the open fragments,
and the facts about unique ids that the validity proof of `Elegant.SequenceValid` needs. -/

namespace Elegant
namespace Sequence

/-- The ancestor ids of the box with id `s`, following `parent`, with fuel `k`: the walk of
`LayoutDump.ancestors` on the boxes of a model. -/
def ancGo (m : Model) : Nat → String → List String
  | 0, _ => []
  | k + 1, s =>
    match m.boxes.find? (fun b => b.id == s) with
    | none => []
    | some b => if b.parent = "" then [] else b.parent :: ancGo m k b.parent

theorem ancGo_found (m : Model) (k : Nat) (s : String) (b : ModelBox)
    (hb : m.boxes.find? (fun b => b.id == s) = some b) (hp : b.parent ≠ "") :
    ancGo m (k + 1) s = b.parent :: ancGo m k b.parent := by
  simp [ancGo, hb, hp]

theorem ancGo_mono (m : Model) : ∀ (k k' : Nat) (s g : String), k ≤ k' → g ∈ ancGo m k s →
    g ∈ ancGo m k' s := by
  intro k
  induction k with
  | zero => intro k' s g _ h; simp [ancGo] at h
  | succ k ih =>
    intro k' s g hk h
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    unfold ancGo at h ⊢
    cases hb : m.boxes.find? (fun b => b.id == s) with
    | none => simp [hb] at h
    | some b =>
      simp only [hb] at h ⊢
      by_cases hp : b.parent = ""
      · simp [hp] at h
      · simp only [hp, ↓reduceIte, List.mem_cons] at h ⊢
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (ih k'' _ g (by omega) h)

/-- `hid` names a box that `gid` is, or that has `gid` among its ancestors. -/
def ChainS (m : Model) (hid gid : String) : Prop :=
  hid ≠ "" ∧ (gid = hid ∨ gid ∈ ancGo m (m.boxes.length - 1) hid)

/-- The chain of the open fragments: each box has the next box of the stack as its parent, and the
last box has none. -/
def ChainOK (m : Model) : List Nat → Prop
  | [] => True
  | s :: rest => boxParent m s = topId m rest ∧ ChainOK m rest

theorem eraseDups_length_le_aux : ∀ (n : Nat) (l : List String), l.length = n →
    l.eraseDups.length ≤ l.length := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro l hn
    cases l with
    | nil => simp
    | cons a t =>
      rw [List.eraseDups_cons]
      have h2 := List.length_filter_le (fun b => !b == a) t
      have h1 := ih (t.filter fun b => !b == a).length
        (by simp only [List.length_cons] at hn; omega) (t.filter fun b => !b == a) rfl
      simp only [List.length_cons] at hn ⊢
      omega

theorem eraseDups_length_le (l : List String) : l.eraseDups.length ≤ l.length :=
  eraseDups_length_le_aux _ l rfl

theorem eraseDups_length_nodup_aux : ∀ (n : Nat) (l : List String), l.length = n →
    l.eraseDups.length = l.length → l.Nodup := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro l hn h
    cases l with
    | nil => exact List.nodup_nil
    | cons a t =>
      rw [List.eraseDups_cons] at h
      have h2 := List.length_filter_le (fun b => !b == a) t
      have h3 := eraseDups_length_le (t.filter fun b => !b == a)
      simp only [List.length_cons] at h hn
      have h4 : (t.filter fun b => !b == a).length = t.length := by omega
      have hnot : ∀ x ∈ t, (!x == a) = true := List.length_filter_eq_length_iff.mp h4
      have h5 : (t.filter fun b => !b == a) = t := List.filter_eq_self.mpr hnot
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hmem
        have := hnot a hmem
        simp at this
      · refine ih t.length (by omega) t rfl ?_
        have h6 : (t.filter fun b => !b == a).eraseDups.length = t.length := by omega
        rw [h5] at h6
        exact h6

theorem eraseDups_length_nodup (l : List String) (h : l.eraseDups.length = l.length) : l.Nodup :=
  eraseDups_length_nodup_aux _ l rfl h

theorem ids_nodup {m : Model} (h : modelWellFormed m = true) : (m.boxes.map (·.id)).Nodup := by
  unfold modelWellFormed at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hu, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  have hu' : ((m.boxes.map (·.id)).eraseDups.length == (m.boxes.map (·.id)).length) = true := hu
  have := beq_iff_eq.mp hu'
  exact eraseDups_length_nodup _ this

theorem find_box_id (m : Model) (hn : (m.boxes.map (·.id)).Nodup) :
    ∀ (i : Nat), i < m.boxes.length → m.boxes.find? (fun b => b.id == boxId m i) = m.boxes[i]? := by
  have key : ∀ (l : List ModelBox), (l.map (·.id)).Nodup → ∀ i, i < l.length →
      l.find? (fun b => b.id == (l[i]?.map (·.id)).getD "") = l[i]? := by
    intro l
    induction l with
    | nil => intro _ i hi; simp at hi
    | cons b t ih =>
      intro hn i hi
      cases i with
      | zero => simp
      | succ k =>
        have hk : k < t.length := by simpa using hi
        have hn2 : (b.id :: t.map (·.id)).Nodup := by simpa using hn
        have hn' := List.nodup_cons.mp hn2
        have hne : b.id ≠ (t[k]?.map (·.id)).getD "" := by
          intro heq
          apply hn'.1
          rw [List.mem_map]
          refine ⟨t[k], List.getElem_mem hk, ?_⟩
          simpa [List.getElem?_eq_getElem hk] using heq.symm
        simp only [List.find?_cons, List.getElem?_cons_succ]
        have : (b.id == (t[k]?.map (·.id)).getD "") = false := by simpa using hne
        simp only [this]
        exact ih (by simpa using hn'.2) k hk
  intro i hi
  exact key m.boxes hn i hi

theorem boxId_of_getElem (m : Model) (i : Nat) (b : ModelBox) (hb : m.boxes[i]? = some b) :
    boxId m i = b.id := by
  simp [boxId, hb]

theorem boxParent_of_getElem (m : Model) (i : Nat) (b : ModelBox) (hb : m.boxes[i]? = some b) :
    boxParent m i = b.parent := by
  simp [boxParent, hb]

/-- The ancestors of the last box of a chain: exactly the boxes below it in the stack. -/
theorem chainOK_anc (m : Model) (hn : (m.boxes.map (·.id)).Nodup)
    (hne : ∀ i, i < m.boxes.length → boxId m i ≠ "") :
    ∀ (rest : List Nat) (s0 F : Nat), ChainOK m (s0 :: rest) →
      (∀ s ∈ s0 :: rest, s < m.boxes.length) → rest.length ≤ F →
      ancGo m F (boxId m s0) = rest.map (boxId m) := by
  intro rest
  induction rest with
  | nil =>
    intro s0 F hc hlt hF
    have h0 := hlt s0 List.mem_cons_self
    obtain ⟨b, hb⟩ : ∃ b, m.boxes[s0]? = some b := ⟨m.boxes[s0], List.getElem?_eq_getElem h0⟩
    have hfind := find_box_id m hn s0 h0
    rw [hb] at hfind
    have hpar : b.parent = "" := by
      have := hc.1
      rw [boxParent_of_getElem m s0 b hb] at this
      simpa [topId] using this
    cases F with
    | zero => simp [ancGo]
    | succ k => simp [ancGo, hfind, hpar]
  | cons s1 r' ih =>
    intro s0 F hc hlt hF
    have h0 := hlt s0 List.mem_cons_self
    have h1 := hlt s1 (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨b, hb⟩ : ∃ b, m.boxes[s0]? = some b := ⟨m.boxes[s0], List.getElem?_eq_getElem h0⟩
    have hfind := find_box_id m hn s0 h0
    rw [hb] at hfind
    have hpar : b.parent = boxId m s1 := by
      have := hc.1
      rw [boxParent_of_getElem m s0 b hb] at this
      simpa [topId] using this
    have hpne : b.parent ≠ "" := by rw [hpar]; exact hne s1 h1
    obtain ⟨k, rfl⟩ : ∃ k, F = k + 1 := ⟨F - 1, by simp only [List.length_cons] at hF; omega⟩
    rw [boxId_of_getElem m s0 b hb] at *
    rw [ancGo_found m k _ b hfind hpne, hpar]
    have := ih s1 k hc.2 (fun s hs => hlt s (List.mem_cons_of_mem _ hs))
      (by simp only [List.length_cons] at hF; omega)
    rw [this]
    simp

/-- Every box of a stack is the top box or one of its ancestors, within the fuel of `ChainS`. -/
theorem chainS_stack (m : Model) (hn : (m.boxes.map (·.id)).Nodup)
    (hne : ∀ i, i < m.boxes.length → boxId m i ≠ "") (s0 : Nat) (rest : List Nat)
    (hc : ChainOK m (s0 :: rest)) (hlt : ∀ s ∈ s0 :: rest, s < m.boxes.length)
    (hlen : (s0 :: rest).length ≤ m.boxes.length) :
    ∀ f ∈ s0 :: rest, ChainS m (boxId m s0) (boxId m f) := by
  intro f hf
  have h0 := hlt s0 List.mem_cons_self
  refine ⟨hne s0 h0, ?_⟩
  rcases List.mem_cons.mp hf with rfl | hf
  · exact Or.inl rfl
  · right
    rw [chainOK_anc m hn hne rest s0 (m.boxes.length - 1) hc hlt (by simp only [List.length_cons] at hlen; omega)]
    exact List.mem_map_of_mem hf

/-- The id of a placed box is in the ancestors of a box whose host is its stack parent. -/
theorem anc_of_chainS (m : Model) (hn : (m.boxes.map (·.id)).Nodup) (i : Nat)
    (hi : i < m.boxes.length) (g : String) (h : ChainS m (boxParent m i) g) :
    g ∈ ancGo m m.boxes.length (boxId m i) := by
  obtain ⟨b, hb⟩ : ∃ b, m.boxes[i]? = some b := ⟨m.boxes[i], List.getElem?_eq_getElem hi⟩
  have hfind := find_box_id m hn i hi
  rw [hb] at hfind
  rw [boxParent_of_getElem m i b hb] at h
  obtain ⟨hne, hg⟩ := h
  obtain ⟨k, hk⟩ : ∃ k, m.boxes.length = k + 1 := ⟨m.boxes.length - 1, by omega⟩
  rw [hk] at hg ⊢
  rw [ancGo_found m k (boxId m i) b hfind hne]
  simp only [Nat.add_sub_cancel] at hg
  rcases hg with rfl | hg
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ hg

end Sequence
end Elegant

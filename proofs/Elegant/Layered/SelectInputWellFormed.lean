import Elegant.Layered.RecursiveC2

set_option autoImplicit false

/-!
# `selectInput` preserves `WellFormed`: the sub-inputs `layoutRecursive` recurses into

`subInputWellFormedC2` discharges the seam `SubInputWellFormedC2` of
`RecursiveC2.lean`: when `inputModel inp o` is well-formed, the child input
(`selectInput` of the boxes inside `group`, rooted at `group.id`) and the
parent input (`selectInput` of the boxes outside `group`, rooted at `""`,
with arbitrary fixed side tables) are again well-formed.
-/

namespace Elegant.Layered.PipelineImpl

open Validator
open Elegant.Layered.Compound



/-- `List.eraseDups` preserves length on a `Nodup` list: no element is removed. -/
theorem nodup_eraseDups_length : ∀ l : List String, l.Nodup → l.eraseDups.length = l.length := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
    intro h
    have hnot : a ∉ as := (List.nodup_cons.mp h).1
    have hsame : (as.filter fun b => !b == a) = as := by
      apply List.filter_eq_self.mpr
      intro b hb
      have hne : b ≠ a := by intro hba; subst hba; exact hnot hb
      simp [hne]
    rw [List.eraseDups_cons, hsame]
    simp only [List.length_cons]
    exact congrArg (fun n => n + 1) (ih (List.nodup_cons.mp h).2)

/-- The box ids of a `selectInput` sub-input are the kept input box ids. -/
theorem selectInput_boxes_nodup {inp : Input} (keep : ModelBox → Bool) (root : String)
    (h : (inp.boxes.map (·.id)).Nodup) :
    ((selectInput inp keep root).boxes.map (·.id)).Nodup := by
  rw [selectInput_box_ids]
  exact nodup_filter_map keep (·.id) inp.boxes h

/-- `zipIdx` then `map` first projection is the identity. -/
theorem zipIdx_map_fst {α : Type} (n : Nat) : ∀ (l : List α),
    (l.zipIdx n).map (fun q => q.1) = l
  | [] => rfl
  | a :: l => by
    rw [List.zipIdx_cons, List.map_cons]
    have ih := zipIdx_map_fst (n + 1) l
    simp [ih]

/-- Filtering `zipIdx` pairs and projecting back gives a sublist. -/
theorem zipIdx_filter_map_fst_sublist {α : Type} (p : α × Nat → Bool) (l : List α) :
    ((l.zipIdx.filter p).map (fun q => q.1)).Sublist l := by
  have h1 : ((l.zipIdx.filter p).map (fun q => q.1)).Sublist
      (l.zipIdx.map (fun q => q.1)) :=
    List.Sublist.map (fun q => q.1) (List.filter_sublist (p := p))
  rw [zipIdx_map_fst 0 l] at h1
  exact h1

/-- The selected routes form a sublist of the input routes. -/
theorem selectInput_routes_sublist (inp : Input) (keep : ModelBox → Bool) (root : String) :
    (selectInput inp keep root).routes.Sublist inp.routes := by
  unfold selectInput
  dsimp only
  exact zipIdx_filter_map_fst_sublist _ inp.routes

/-- The selected route ids are a sublist of the input route ids. -/
theorem selectInput_routes_ids_sublist (inp : Input) (keep : ModelBox → Bool) (root : String) :
    ((selectInput inp keep root).routes.map (·.id)).Sublist (inp.routes.map (·.id)) := by
  refine List.Sublist.map (fun r => r.id) (selectInput_routes_sublist inp keep root)

/-- The selected route ids are `Nodup` when the input route ids are. -/
theorem selectInput_routes_nodup {inp : Input} (keep : ModelBox → Bool) (root : String)
    (h : (inp.routes.map (·.id)).Nodup) :
    ((selectInput inp keep root).routes.map (·.id)).Nodup :=
  List.Nodup.sublist (selectInput_routes_ids_sublist inp keep root) h

/-- The selected labels form a sublist of the input labels. -/
theorem selectInput_labels_sublist (inp : Input) (keep : ModelBox → Bool) (root : String) :
    (selectInput inp keep root).labels.Sublist inp.labels := by
  unfold selectInput
  dsimp only
  exact List.filter_sublist (p := _)

/-- The selected label ids are `Nodup` when the input label ids are. -/
theorem selectInput_labels_nodup {inp : Input} (keep : ModelBox → Bool) (root : String)
    (h : (inp.labels.map (·.id)).Nodup) :
    ((selectInput inp keep root).labels.map (·.id)).Nodup := by
  refine List.Nodup.sublist (List.Sublist.map (fun l => l.id)
    (selectInput_labels_sublist inp keep root)) h

/-- `(routes.map (·.1)).any` on route ids equals the raw `any` on pairs. -/
theorem routes_any_of_map {s : String} (routes : List (ModelRoute × Nat)) :
    (routes.map (fun q => q.1)).any (fun route => route.id == s)
      = routes.any (fun route => route.1.id == s) := by
  rw [List.any_map]
  rfl

/-- Membership in the selected labels keeps the label and requires a live owner. -/
theorem selectInput_label_mem (inp : Input) (keep : ModelBox → Bool) (root : String)
    (l : ModelLabel) :
    l ∈ (selectInput inp keep root).labels ↔
      l ∈ inp.labels ∧
      ((selectInput inp keep root).boxes.any (fun box => box.id == l.owner) = true ∨
       (selectInput inp keep root).routes.any (fun route => route.id == l.owner) = true) := by
  unfold selectInput
  dsimp only
  constructor
  · intro h
    obtain ⟨hl, hcond⟩ := List.mem_filter.mp h
    refine ⟨hl, ?_⟩
    simp only [Bool.or_eq_true] at hcond ⊢
    rw [routes_any_of_map]
    exact hcond
  · rintro ⟨hl, h1 | h2⟩
    · refine List.mem_filter.mpr ⟨hl, ?_⟩
      simp only [Bool.or_eq_true]
      exact Or.inl h1
    · refine List.mem_filter.mpr ⟨hl, ?_⟩
      rw [← routes_any_of_map]
      simp only [Bool.or_eq_true]
      exact Or.inr h2

/-- Both endpoints of a selected route are ids of selected boxes. -/
theorem selectInput_route_endpoints (inp : Input) (keep : ModelBox → Bool) (root : String)
    (r : ModelRoute) (hr : r ∈ (selectInput inp keep root).routes) :
    r.fromId ∈ (selectInput inp keep root).boxes.map (·.id) ∧
      r.toId ∈ (selectInput inp keep root).boxes.map (·.id) := by
  obtain ⟨_, h1, h2⟩ := (selectInput_route_mem inp keep root r).mp hr
  exact ⟨any_id_iff _ _ |>.mp h1, any_id_iff _ _ |>.mp h2⟩

/-- The owner of a selected label is an id of a selected box or route. -/
theorem selectInput_label_owner (inp : Input) (keep : ModelBox → Bool) (root : String)
    (l : ModelLabel) (hl : l ∈ (selectInput inp keep root).labels) :
    l.owner ∈ (selectInput inp keep root).boxes.map (·.id) ∨
      l.owner ∈ (selectInput inp keep root).routes.map (·.id) := by
  obtain ⟨_, h1 | h2⟩ := (selectInput_label_mem inp keep root l).mp hl
  · exact Or.inl (any_id_iff _ _ |>.mp h1)
  · rw [List.any_eq_true] at h2
    obtain ⟨r, hr, hrid⟩ := h2
    exact Or.inr (List.mem_map.mpr ⟨r, hr, by simpa using hrid⟩)

/-- Selected boxes keep `role` and `exclusive` from an original input box. -/
theorem selectInput_box_fields (inp : Input) (keep : ModelBox → Bool) (root : String)
    {b : ModelBox} (hb : b ∈ (selectInput inp keep root).boxes) :
    ∃ m ∈ inp.boxes, keep m = true ∧ b.role = m.role ∧ b.exclusive = m.exclusive := by
  unfold selectInput at hb
  dsimp only at hb
  obtain ⟨q, hq, hbq⟩ := List.mem_map.mp hb
  obtain ⟨hqzip, hkq⟩ := List.mem_filter.mp hq
  have hget : inp.boxes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hqzip
  refine ⟨q.1, getElem?_mem' hget, hkq, ?_, ?_⟩
  · rw [← hbq]; split <;> rfl
  · rw [← hbq]; split <;> rfl

/-- The no-exclusive-group clause of `modelWellFormed` survives `selectInput`. -/
theorem selectInput_groups_not_exclusive (inp : Input) (keep : ModelBox → Bool)
    (root : String) (h : ∀ m ∈ inp.boxes, m.role != BoxRole.group || !m.exclusive) :
    ∀ b ∈ (selectInput inp keep root).boxes, b.role != BoxRole.group || !b.exclusive := by
  intro b hb
  obtain ⟨m, hmem, _, hrole, hexcl⟩ := selectInput_box_fields inp keep root hb
  rw [hrole, hexcl]
  exact h m hmem

/-- Parent-chain termination (in the public `chainTerm` sense) transports through
`selectInput`: every selected box's parent chain terminates inside the selected
box list, for fuel at least the input length. `hclose` is `keepInside_close` or
`keepOutside_close` at the matching `keep` and `root`. -/
theorem selectInput_chainTerm (inp : Input) (keep : ModelBox → Bool) (root : String)
    (hf : InputFacts inp)
    (hclose : ∀ b ∈ inp.boxes, keep b = true →
      b.parent = "" ∨ (b.parent == root) = true ∨
        ∃ p ∈ inp.boxes, p.id = b.parent ∧ keep p = true)
    (n : Nat) (hle : inp.boxes.length ≤ n + 1)
    (b : ModelBox) (hb : b ∈ (selectInput inp keep root).boxes) :
    chainTerm (selectInput inp keep root).boxes n b.parent = true := by
  obtain ⟨m, hm, hkm, _, hbpar⟩ := selectInput_box_spec inp keep root hb
  rw [hbpar]
  split
  · exact chainTerm.eq_1 (selectInput inp keep root).boxes n
  · rename_i hnotroot
    refine chainTerm_selectInput_mono inp keep root hf.nodup hclose n m.parent ?_ ?_
    · exact hf.term m hm n hle
    · rcases hclose m hm hkm with h0 | h1 | ⟨p, hp, hpid, hkp⟩
      · exact Or.inl h0
      · exact absurd h1 hnotroot
      · exact Or.inr ⟨p, hp, hpid, hkp⟩

/-- Inside-selection keeps parent chains terminating at the group root. -/
theorem selectInput_chainTerm_inside (inp : Input) (group : ModelBox) (hf : InputFacts inp)
    (n : Nat) (hle : inp.boxes.length ≤ n + 1)
    (b : ModelBox)
    (hb : b ∈ (selectInput inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes) :
    chainTerm (selectInput inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes n b.parent = true :=
  selectInput_chainTerm inp (fun box => Compound.inside inp.boxes group.id box.id) group.id hf
    (by
      intro c hc hkept
      exact keepInside_close (group := group.id) hf hc hkept) n hle b hb

/-- Outside-selection keeps parent chains terminating at the document root. -/
theorem selectInput_chainTerm_outside (inp : Input) (group : ModelBox) (hf : InputFacts inp)
    (n : Nat) (hle : inp.boxes.length ≤ n + 1)
    (b : ModelBox)
    (hb : b ∈ (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id)).boxes) :
    chainTerm (selectInput inp
      (fun box => !Compound.inside inp.boxes group.id box.id)).boxes n b.parent = true :=
  selectInput_chainTerm inp (fun box => !Compound.inside inp.boxes group.id box.id) "" hf
    (by
      intro c hc hkept
      exact keepOutside_close (group := group.id) hf hc hkept) n hle b hb

end Elegant.Layered.PipelineImpl

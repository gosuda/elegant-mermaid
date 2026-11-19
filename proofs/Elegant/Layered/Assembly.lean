import Elegant.Scene

namespace Elegant.Layered.Assembly

universe u v

theorem ordered_merge_ids {α : Type u} (key : α → String) (ids : List String)
    (items : List α) (cover : ∀ id ∈ ids, ∃ item ∈ items, key item = id) :
    ((ids.filterMap fun id => items.find? (fun item => key item == id)).map key) = ids := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    obtain ⟨item, hm, hk⟩ := cover id (by simp)
    have ht := ih (fun id h => cover id (by simp [h]))
    cases hf : items.find? (fun item => key item == id) with
    | none =>
      have hn := List.find?_eq_none.mp hf item hm
      simp [hk] at hn
    | some found =>
      have hkf : key found = id := by simpa using List.find?_some hf
      simp [hf, hkf, ht]

theorem ordered_merge_ids_of_perm {α : Type u} (key : α → String)
    (ids : List String) (items : List α) (perm : (items.map key).Perm ids) :
    ((ids.filterMap fun id => items.find? (fun item => key item == id)).map key) = ids := by
  apply ordered_merge_ids
  intro id hid
  exact List.mem_map.mp (perm.mem_iff.mpr hid)

theorem selected_member {α : Type u} (key : α → String) (ids : List String)
    (items : List α) (item : α) :
    item ∈ (ids.filterMap fun id => items.find? (fun a => key a == id)) ↔
      ∃ id ∈ ids, items.find? (fun a => key a == id) = some item := by
  exact List.mem_filterMap

theorem keyed_lookup_eq {α : Type u} (key : α → String) (items : List α)
    (distinct : (items.map key).Nodup) (item : α) (member : item ∈ items) :
    items.find? (fun a => key a == key item) = some item := by
  induction items with
  | nil => simp at member
  | cons a items ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · have hn : key a ≠ key item := by
        intro he
        exact distinct.1 (he ▸ List.mem_map.mpr ⟨item, member, rfl⟩)
      have hb := beq_eq_false_iff_ne.mpr hn
      simp [List.find?, hb, ih distinct.2 member]

theorem keyed_lookup_projection {α : Type u} {β : Type v} (key : α → String)
    (projection : α → β) (items : List α) (distinct : (items.map key).Nodup)
    (item : α) (member : item ∈ items) :
    (items.find? (fun a => key a == key item)).map projection = some (projection item) := by
  rw [keyed_lookup_eq key items distinct item member]
  rfl

end Elegant.Layered.Assembly

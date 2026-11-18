import Elegant.Kinds.Architecture
import Elegant.GridArchitectureClearanceFacts

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Elegant.Grid.Architecture

/-! Shared model-box helpers for the architecture adapter.  The clause proofs
that consume these live in `Elegant.GridArchitectureClauses`; this module stays
tiny because it is imported by the `Elegant` root. -/

/-- Model boxes are determined by their ids. -/
theorem box_eq_of_id_eq {m : Model} (hwf : WellFormed m) {a c : ModelBox}
    (ha : a ∈ m.boxes) (hc : c ∈ m.boxes) (hid : a.id = c.id) : a = c := by
  by_cases hne : a = c
  · exact hne
  · exfalso
    obtain ⟨i, hi, hilen⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨j, hj, hjlen⟩ := List.mem_iff_getElem.mp hc
    have hidx : i ≠ j := by
      intro h
      cases h
      exact hne (hilen.symm.trans hjlen)
    have hi_len : i < (m.boxes.map (fun b : ModelBox => b.id)).length := by
      rw [List.length_map]; exact hi
    have hj_len : j < (m.boxes.map (fun b : ModelBox => b.id)).length := by
      rw [List.length_map]; exact hj
    have mi : (m.boxes.map (fun b : ModelBox => b.id))[i]'hi_len = a.id := by
      rw [List.getElem_map]
      exact congrArg (fun b : ModelBox => b.id) hilen
    have mj : (m.boxes.map (fun b : ModelBox => b.id))[j]'hj_len = c.id := by
      rw [List.getElem_map]
      exact congrArg (fun b : ModelBox => b.id) hjlen
    rcases Nat.lt_or_gt_of_ne hidx with hlt | hgt
    · have hpair := List.pairwise_iff_getElem.mp (Model.boxIds_nodup hwf) i j hi_len hj_len hlt
      rw [mi, mj, hid] at hpair
      exact hpair rfl
    · have hpair := List.pairwise_iff_getElem.mp (Model.boxIds_nodup hwf) j i hj_len hi_len hgt
      rw [mj, mi, hid] at hpair
      exact hpair rfl

/-- A span containing its anchor grid cell is non-degenerate. -/
theorem frame_anchor_nonempty (p : Params) (r : Span) (px : 0 < p.pitchX)
    (anchor : ContainsAnchor p r) : r.x0 ≠ r.x1 ∨ r.y0 ≠ r.y1 := by
  unfold ContainsAnchor at anchor
  obtain ⟨h0, h1, h2, h3⟩ := anchor
  by_cases hxy : r.x0 = r.x1
  · right
    intro heq
    omega
  · exact Or.inl hxy

/-- A successful decoded node parent names an existing group by index. -/
theorem decoded_parent_index {groups : List ModelBox} {id : String} {value : Int}
    (hp : Kinds.Architecture.parentIndex groups id = .ok value) (hempty : id ≠ "") :
    ∃ i, i < groups.length ∧ value = Int.ofNat i ∧
      (List.findIdx? (fun b => b.id == id) groups) = some i := by
  unfold Kinds.Architecture.parentIndex at hp
  have hempty' : id.isEmpty = false := by simp [hempty]
  rw [hempty'] at hp
  cases hf : List.findIdx? (fun b => b.id == id) groups with
  | none => simp only [hf] at hp; cases hp
  | some i =>
    simp only [hf] at hp
    injection hp with hval
    subst hval
    obtain ⟨hbound, -, -⟩ :=
      (List.findIdx?_eq_some_iff_getElem).mp hf
    exact ⟨i, hbound, rfl, rfl⟩

end Elegant.Grid.Architecture

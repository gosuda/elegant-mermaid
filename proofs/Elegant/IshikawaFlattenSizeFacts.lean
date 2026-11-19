import Elegant.Ishikawa

set_option autoImplicit false

namespace Elegant.Ishikawa

private theorem fold_size_balance
    (step : List Entry × List Nat → Nat → List Entry × List Nat)
    (hstep : ∀ st node,
      (step st node).2.length + st.1.length =
        (step st node).1.length + st.2.length)
    (ids : List Nat) (st : List Entry × List Nat) :
    (ids.foldl step st).2.length + st.1.length =
      (ids.foldl step st).1.length + st.2.length := by
  induction ids generalizing st with
  | nil => exact Nat.add_comm _ _
  | cons node rest ih =>
    simp only [List.foldl_cons]
    have hs := hstep st node
    have ht := ih (step st node)
    omega

theorem flatten_size_balance (ns : List Tree.Node) (up : Bool) (fuel : Nat) :
    ∀ (ids : List Nat) (par : Int) (depth : Nat)
      (entries : List Entry) (order : List Nat),
      (flatten ns up fuel ids par depth entries order).2.length + entries.length =
        (flatten ns up fuel ids par depth entries order).1.length + order.length := by
  induction fuel with
  | zero => intros; exact Nat.add_comm _ _
  | succ fuel ih =>
    intro ids par depth entries order
    unfold flatten
    apply fold_size_balance
    intro st node
    rcases st with ⟨es, os⟩
    dsimp only
    have hr := ih (children ns node) (es.length : Int) (depth + 1)
      (es ++ [⟨node, par, depth⟩])
      (if depth % 2 == 0 then os ++ [es.length] else os)
    by_cases hp : depth % 2 == 0
    · simp [hp] at hr ⊢ <;> omega
    · simp [hp] at hr ⊢ <;> omega

theorem flatten_order_length_le (ns : List Tree.Node) (up : Bool) (fuel : Nat)
    (ids : List Nat) (par : Int) (depth : Nat)
    (entries : List Entry) (order : List Nat) (hsize : order.length ≤ entries.length) :
    (flatten ns up fuel ids par depth entries order).2.length ≤
      (flatten ns up fuel ids par depth entries order).1.length := by
  have h := flatten_size_balance ns up fuel ids par depth entries order
  omega

theorem flatten_empty_lengths (ns : List Tree.Node) (up : Bool) (fuel : Nat)
    (ids : List Nat) (par : Int) (depth : Nat) :
    (flatten ns up fuel ids par depth [] []).2.length =
      (flatten ns up fuel ids par depth [] []).1.length := by
  simpa using flatten_size_balance ns up fuel ids par depth [] []

theorem generated_rib_order_length_le (ns : List Tree.Node) (cause k : Nat) :
    (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).2.length ≤
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1.length := by
  exact flatten_order_length_le ns (upper k) 64 (children ns cause) (-1) 2 [] []
    (by simp)

private theorem zipIdx_member_ordinal_lt (order : List Nat) (position : Nat × Nat)
    (hm : position ∈ order.zipIdx) : position.2 < order.length := by
  have hs : position.2 ∈ (order.zipIdx).map Prod.snd :=
    List.mem_map.mpr ⟨position, hm, rfl⟩
  rw [List.zipIdx_map_snd] at hs
  obtain ⟨i, hi, he⟩ := List.mem_range'.mp hs
  simp only [Nat.zero_add, Nat.one_mul] at he
  omega

theorem flatten_empty_found_ordinal_lt (ns : List Tree.Node) (up : Bool)
    (fuel : Nat) (ids : List Nat) (par : Int) (depth idx : Nat)
    (position : Nat × Nat)
    (hfound : ((flatten ns up fuel ids par depth [] []).2.zipIdx).find?
      (fun v => v.1 == idx) = some position) :
    position.2 < (flatten ns up fuel ids par depth [] []).1.length := by
  have hm := List.mem_of_find?_eq_some hfound
  have hb := zipIdx_member_ordinal_lt _ position hm
  have hs := flatten_empty_lengths ns up fuel ids par depth
  omega

theorem generated_rib_found_ordinal_lt (ns : List Tree.Node) (cause k idx : Nat)
    (position : Nat × Nat)
    (hfound : ((flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).2.zipIdx).find?
      (fun v => v.1 == idx) = some position) :
    position.2 < (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1.length := by
  exact flatten_empty_found_ordinal_lt ns (upper k) 64 (children ns cause) (-1) 2
    idx position hfound

end Elegant.Ishikawa

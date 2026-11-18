import Elegant.IshikawaClearanceHardBClose

/-!
# Branch-5 placement counterexample

The conditional branch-5 placement hypothesis that `ishikawa_hard_b_real`
(`Elegant.IshikawaClearanceHardBClose`) takes as `hbranch5` is FALSE for members
of a generated rib. `flatten` walks the children of the cause node one block at
a time: the entries of each cause-child form a contiguous index interval, only
the block heads carry `parent = -1`, and parent indices stay inside their own
block and point backwards. An earlier entry `J` of a *different* block than the
odd entry `I` is neither a root nor a descendant of any sibling of `I`, so both
disjuncts of `HardBBranch5Placement` fail for it.

`hard_b_branch5_placement_counterexample` below is the executed witness: cause
node 2 with two children 3 and 4, earlier entry `j` (node 5) inside block 3,
odd entry `child` (node 6, depth 3) inside block 4.
-/

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-- The witness forest: root 0, filler child 1, cause 2 (child of 0, at zip
index `k = 1`, so `upper 1 = false` keeps block order), cause children 3 and 4,
earlier entry node 5 (child of 3), odd entry node 6 (child of 4). -/
private def witnessNodes : List Tree.Node :=
  [⟨none, 0, 0⟩, ⟨some 0, 0, 0⟩, ⟨some 0, 0, 0⟩, ⟨some 2, 0, 0⟩, ⟨some 2, 0, 0⟩,
    ⟨some 3, 0, 0⟩, ⟨some 4, 0, 0⟩]

private theorem witness_entries :
    (generatedRib witnessNodes (2, 1)).entries =
      [⟨3, -1, 2⟩, ⟨5, 0, 3⟩, ⟨4, -1, 2⟩, ⟨6, 2, 3⟩] := by
  rfl

/-- Every parent pointer of the witness entries is a block head strictly before
its entry. -/
private theorem witness_parent_before (i : Nat) (e : Entry)
    (h : [⟨3, -1, 2⟩, ⟨5, 0, 3⟩, ⟨4, -1, 2⟩, ⟨6, 2, 3⟩][i]? = some e) :
    e.parent = -1 ∨ ∃ p : Nat, e.parent = (p : Int) ∧ p < i := by
  have hb : i < 4 := (List.getElem?_eq_some_iff.mp h).1
  have hsplit : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hsplit with rfl | rfl | rfl | rfl
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact Or.inl rfl
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact Or.inr ⟨0, rfl, by omega⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact Or.inl rfl
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_succ,
      List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact Or.inr ⟨2, rfl, by omega⟩

/-- Ancestor indices precede descendant indices whenever parent pointers point
backwards (mirrors the private `indexedAncestor_lt` of
`Elegant.IshikawaFlattenTemporalFacts`). -/
private theorem witness_ancestor_lt {a c : Nat}
    (h : IndexedAncestor [⟨3, -1, 2⟩, ⟨5, 0, 3⟩, ⟨4, -1, 2⟩, ⟨6, 2, 3⟩] a c) :
    a < c := by
  induction h with
  | edge _ e he hp =>
    rcases witness_parent_before _ e he with hr | ⟨p, hp', hlt⟩
    · omega
    · omega
  | tail _ e he hp ih =>
    rcases witness_parent_before _ e he with hr | ⟨p, hp', hlt⟩ <;> omega

/-- The requested `hard_b_branch5_placement` is false: `child` is the depth-3
entry of the second cause-child block and `j` is an earlier entry of the first
block, yet neither disjunct of `HardBBranch5Placement` holds. The witness is a
real generated rib: cause `2` sits at zip index `k = 1` of `children
witnessNodes 0`, so `generatedRib witnessNodes (2, 1)` is the second rib of the
layout's rib list. -/
theorem hard_b_branch5_placement_counterexample :
    ∃ (ns : List Tree.Node) (cause k : Nat) (child j : Entry) (childIdx jIdx : Nat),
      (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx ∧
      (j, jIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx ∧
      child.depth % 2 ≠ 0 ∧
      jIdx < childIdx ∧
      ¬ HardBBranch5Placement ns cause k (child.parent).toNat childIdx jIdx j := by
  refine ⟨witnessNodes, 2, 1, ⟨6, 2, 3⟩, ⟨5, 0, 3⟩, 3, 1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [witness_entries]
    exact List.mem_zipIdx_iff_getElem?.mpr rfl
  · rw [witness_entries]
    exact List.mem_zipIdx_iff_getElem?.mpr rfl
  · decide
  · decide
  · simp only [HardBBranch5Placement]
    intro h
    rw [witness_entries] at h
    rcases h with ⟨sIdx, S, hget, _hsne, hsp, hanc⟩ | ⟨hroot, _⟩
    · have hlt : sIdx < 1 := witness_ancestor_lt hanc
      have hs0 : sIdx = 0 := by omega
      subst hs0
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      have hS : S = ⟨3, -1, 2⟩ := hget.symm
      rw [hS] at hsp
      exact absurd hsp (by decide)
    · exact absurd hroot (by decide)

end Elegant.Ishikawa

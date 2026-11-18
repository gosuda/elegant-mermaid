import Elegant.IshikawaClearanceHardBClose

/-!
# Branch-5 placement counterexample and corrected classification

The conditional branch-5 placement hypothesis that `ishikawa_hard_b_real`
(`Elegant.IshikawaClearanceHardBClose`) takes as `hbranch5` is FALSE for members
of a generated rib: `flatten` walks the children of the cause node one block at
a time, so an earlier non-root entry of a *different* block than the odd entry
is neither a root nor a descendant of any sibling of that entry.
`hard_b_branch5_placement_counterexample` is the executed witness.

`HardBBranch5PlacementBlock` is the corrected classification (the second
disjunct compares through `j`'s block head); `witness_satisfies_placement_block`
checks the witness against it, and `hard_b_branch5_placement_block` proves it
for members of a generated rib (with the two caller-side negatives the
deeper-earlier branch has in scope, plus two named flatten-order facts).
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

/-- Corrected branch-5 placement: the first disjunct is unchanged (some entry
`S` at `sIdx ≠ jIdx` whose parent is `parentIdx`, i.e. a sibling of `I`, that
is an `IndexedAncestor` of `j`); the second disjunct is stated for `j`'s block
head `H` at `hIdx` (either `j` itself when `j.parent = -1`, or a root ancestor
of `jIdx`): `H.parent = -1` and, whenever the order positions of `hIdx` and
`parentIdx` exist in `rib.order`, `childIdx ≤ jIdx` or the head's position
strictly precedes the parent entry's position. This closes the missing case of
`HardBBranch5Placement`: a non-root earlier entry of an earlier block now
compares through its block head. -/
def HardBBranch5PlacementBlock (ns : List Tree.Node) (cause k parentIdx childIdx jIdx : Nat)
    (J : Entry) : Prop :=
  let rib := generatedRib ns (cause, k)
  (∃ (sIdx : Nat) (S : Entry), rib.entries[sIdx]? = some S ∧ sIdx ≠ jIdx ∧
      S.parent = (parentIdx : Int) ∧ IndexedAncestor rib.entries sIdx jIdx) ∨
  (∃ (hIdx : Nat) (H : Entry), rib.entries[hIdx]? = some H ∧ H.parent = -1 ∧
      ((H = J ∧ hIdx = jIdx) ∨ IndexedAncestor rib.entries hIdx jIdx) ∧
      ∀ (headPos parentPos : Nat × Nat),
        rib.order.zipIdx.find? (fun v => v.1 == hIdx) = some headPos →
        rib.order.zipIdx.find? (fun v => v.1 == parentIdx) = some parentPos →
        childIdx ≤ jIdx ∨ headPos.2 < parentPos.2)

private theorem witness_order :
    (generatedRib witnessNodes (2, 1)).order = [0, 1, 2, 3] := by
  rfl

/-- The counterexample witness satisfies the corrected classification: `j` is a
non-root entry of the first block, so its block head `entries[0]` (the root of
block 3) has order position 0, strictly before the parent entry `entries[2]`
(position 2). The first disjunct is false here, which is exactly the gap of the
original definition. -/
theorem witness_satisfies_placement_block :
    HardBBranch5PlacementBlock witnessNodes 2 1 2 3 1 ⟨5, 0, 3⟩ := by
  refine Or.inr ⟨0, ⟨3, -1, 2⟩, ?_, rfl,
    Or.inr (IndexedAncestor.edge 0 1 ⟨5, 0, 3⟩ ?_ rfl), ?_⟩
  · rw [witness_entries]
    rfl
  · rw [witness_entries]
    rfl
  · rw [witness_order]
    intro headPos parentPos hHead hParent
    have hH : headPos = (0, 0) := by
      simpa using hHead.symm
    have hP : parentPos = (2, 2) := by
      simpa using hParent.symm
    subst hH
    subst hP
    omega

/-! ### Flatten structure: parent pointers point backwards to existing entries -/

/-- One fold step of `flatten`'s top-level child walk, named so the fold
induction stays readable. -/
private def flattenStep (ns : List Tree.Node) (up : Bool) (fuel : Nat) (par : Int)
    (depth : Nat) (st : List Entry × List Nat) (node : Nat) : List Entry × List Nat :=
  let idx := st.1.length
  let es := st.1 ++ [(⟨node, par, depth⟩ : Entry)]
  let os := if depth % 2 == 0 then st.2 ++ [idx] else st.2
  let res := flatten ns up fuel (children ns node) (idx : Int) (depth + 1) es os
  (res.1, if depth % 2 == 0 then res.2 else res.2 ++ [idx])

private theorem flatten_succ_eq_foldl (ns : List Tree.Node) (up : Bool) (fuel : Nat)
    (ids : List Nat) (par : Int) (depth : Nat) (es : List Entry) (os : List Nat) :
    flatten ns up (fuel + 1) ids par depth es os =
      (if up then ids.reverse else ids).foldl (flattenStep ns up fuel par depth) (es, os) := by
  rfl

/-- Every entry a successful `flatten` appends has parent `par` (the call's own
parent parameter) or a parent that is an existing earlier entry of the final
entry list, at a strictly smaller index. Only the entry list is tracked. -/
private theorem flatten_parent_back (ns : List Tree.Node) (up : Bool) :
    ∀ (fuel : Nat) (ids : List Nat) (par : Int) (depth : Nat) (es : List Entry) (os : List Nat),
      ∃ (segE : List Entry),
        (flatten ns up fuel ids par depth es os).1 = es ++ segE ∧
        ∀ (i : Nat) (e : Entry), (es ++ segE)[i]? = some e → es.length ≤ i →
          e.parent = par ∨
          ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧ (es ++ segE)[p]? = some pe := by
  intro fuel
  induction fuel with
  | zero =>
    intro ids par depth es os
    refine ⟨[], by simp [flatten], ?_⟩
    intro i e hlook hle
    rw [List.getElem?_append_right hle, List.getElem?_nil] at hlook
    exact absurd hlook (by simp)
  | succ fuel ih =>
    intro ids par depth es os
    have inner :
        ∀ (ls : List Nat) (st : List Entry × List Nat),
          ∃ (segE : List Entry),
            (ls.foldl (flattenStep ns up fuel par depth) st).1 = st.1 ++ segE ∧
            ∀ (i : Nat) (e : Entry), (st.1 ++ segE)[i]? = some e → st.1.length ≤ i →
              e.parent = par ∨
              ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
                (st.1 ++ segE)[p]? = some pe := by
      intro ls
      induction ls with
      | nil =>
        intro st
        refine ⟨[], by simp, ?_⟩
        intro i e hlook hle
        rw [List.getElem?_append_right hle, List.getElem?_nil] at hlook
        exact absurd hlook (by simp)
      | cons node rest ihrest =>
        intro st
        obtain ⟨dE, hdE, hdprop⟩ :=
          ih (children ns node) (st.1.length : Int) (depth + 1)
            (st.1 ++ [(⟨node, par, depth⟩ : Entry)])
            (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2)
        have hstep : (flattenStep ns up fuel par depth st node).1
              = (st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE := hdE
        obtain ⟨segE', hsegE', hprop'⟩ :=
          ihrest (flattenStep ns up fuel par depth st node)
        rw [hstep] at hsegE' hprop'
        refine ⟨⟨node, par, depth⟩ :: (dE ++ segE'), ?_, ?_⟩
        · rw [List.foldl_cons, hsegE']
          simp [List.append_assoc]
        · intro i e hlook hle
          by_cases hi : i < st.1.length + 1
          · have hieq : i = st.1.length := by omega
            rw [List.getElem?_append_right hle, hieq, Nat.sub_self,
              List.getElem?_cons_zero, Option.some.injEq] at hlook
            exact Or.inl (by rw [← hlook])
          · have hlenA : ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE).length =
                (st.1.length + 1) + dE.length := by
              simp only [List.length_append, List.length_singleton]
            have happ : st.1 ++ (⟨node, par, depth⟩ :: (dE ++ segE'))
                = ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE) ++ segE' := by
              simp [List.append_assoc]
            have hlook2 : (((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE) ++ segE')[i]? = some e := by
              rw [happ] at hlook
              exact hlook
            by_cases hiA : i < (st.1.length + 1) + dE.length
            · have hltiA : i < ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE).length := by
                rw [hlenA]; omega
              have hlookA : ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE)[i]? = some e := by
                rw [List.getElem?_append_left hltiA] at hlook2
                exact hlook2
              have hcase := hdprop i e hlookA
                (by simp only [List.length_append, List.length_singleton]; omega)
              rcases hcase with hpar0 | ⟨p, pe, hpe, hplt, hplook⟩
              · have hlt0 : st.1.length < ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE).length := by
                  rw [hlenA]; omega
                have hlt1 : st.1.length < (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length := by
                  simp only [List.length_append, List.length_singleton]; omega
                refine Or.inr ⟨st.1.length, ⟨node, par, depth⟩, hpar0, by omega, ?_⟩
                rw [happ, List.getElem?_append_left hlt0,
                  List.getElem?_append_left hlt1,
                  List.getElem?_append_right (Nat.le_refl st.1.length),
                  Nat.sub_self, List.getElem?_singleton]
                rfl
              · have hpltA : p < ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE).length := by
                  rw [hlenA]; omega
                refine Or.inr ⟨p, pe, hpe, hplt, ?_⟩
                rw [happ, List.getElem?_append_left hpltA]
                exact hplook
            · have hcase := hprop' i e hlook2 (by rw [hlenA]; omega)
              rcases hcase with hpar0 | ⟨p, pe, hpe, hplt, hplook⟩
              · exact Or.inl hpar0
              · refine Or.inr ⟨p, pe, hpe, hplt, ?_⟩
                rw [happ]
                exact hplook
    obtain ⟨segE, hsegE, hprop⟩ := inner (if up then ids.reverse else ids) (es, os)
    rw [flatten_succ_eq_foldl]
    exact ⟨segE, hsegE, hprop⟩

/-- Ancestor indices are strictly below descendant indices whenever parent
pointers point backwards to existing entries. -/
private theorem chain_lt_of_parent_back (E : List Entry)
    (hback : ∀ (i : Nat) (e : Entry), E[i]? = some e →
      e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        E[p]? = some pe) :
    ∀ (a c : Nat), IndexedAncestor E a c → a < c := by
  intro a c h
  induction h with
  | edge _ e he hp =>
    rcases hback _ e he with hr | ⟨p, pe, hpe, hplt, _⟩
    · rw [hr] at hp
      exact absurd hp (by omega)
    · omega
  | tail _ e he hp ih =>
    rcases hback _ e he with hr | ⟨p, pe, hpe, hplt, _⟩
    · rw [hr] at hp
      exact absurd hp (by omega)
    · omega

/-- Every entry of a backwards-parented list has a root ancestor (possibly
itself) reached through `IndexedAncestor`. -/
private theorem entries_root_exists (E : List Entry)
    (hback : ∀ (i : Nat) (e : Entry), E[i]? = some e →
      e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        E[p]? = some pe) :
    ∀ (n i : Nat), i ≤ n → ∀ (e : Entry), E[i]? = some e →
      ∃ (hIdx : Nat) (H : Entry), E[hIdx]? = some H ∧ H.parent = -1 ∧
        (hIdx = i ∨ IndexedAncestor E hIdx i) := by
  intro n
  induction n with
  | zero =>
    intro i hi e hl
    rcases hback i e hl with hr | ⟨p, pe, _, hplt, _⟩
    · exact ⟨i, e, hl, hr, Or.inl rfl⟩
    · omega
  | succ n ih =>
    intro i hi e hl
    rcases hback i e hl with hr | ⟨p, pe, hpe, hplt, hplook⟩
    · exact ⟨i, e, hl, hr, Or.inl rfl⟩
    · obtain ⟨hIdx, H, hH, hHroot, hchain⟩ := ih p (by omega) pe hplook
      refine ⟨hIdx, H, hH, hHroot, Or.inr ?_⟩
      rcases hchain with heq | hchain
      · rw [heq]
        exact IndexedAncestor.edge p i e hl hpe
      · exact IndexedAncestor.tail hchain e hl hpe

/-- Scanning an ancestor chain top-down: either some entry on the chain (other
than the bottom entry itself) is a child of `parentIdx`, or the chain top
differs from `parentIdx`. No root-side premises are needed. -/
private theorem chain_scan (E : List Entry) (parentIdx : Nat)
    (hback : ∀ (i : Nat) (e : Entry), E[i]? = some e →
      e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        E[p]? = some pe)
    (hlt : ∀ (a c : Nat), IndexedAncestor E a c → a < c) :
    ∀ (hIdx c : Nat), IndexedAncestor E hIdx c → ∀ (ce : Entry),
      E[c]? = some ce → ce.parent ≠ (parentIdx : Int) →
      (∃ (sIdx : Nat) (S : Entry), E[sIdx]? = some S ∧ sIdx ≠ c ∧
        S.parent = (parentIdx : Int) ∧ IndexedAncestor E sIdx c) ∨
      hIdx ≠ parentIdx := by
  intro hIdx c hchain
  induction hchain with
  | edge cIdx e he hp =>
    intro ce hce hcePar
    refine Or.inr ?_
    intro heq
    have hec : e = ce := Option.some.inj (he.symm.trans hce)
    rw [heq] at hp
    exact hcePar (by rw [← hec]; exact hp)
  | @tail b cIdx hab e he hp ih =>
    intro ce hce hcePar
    have hec : e = ce := Option.some.inj (he.symm.trans hce)
    rcases hback cIdx e he with hr | ⟨p, pe, hme, hplt, hplook⟩
    · rw [hr] at hp
      exact absurd hp (by omega)
    · have hpb : b = p := by omega
      rw [← hpb] at hplook hme
      rw [hec] at hp
      by_cases hbePar : pe.parent = (parentIdx : Int)
      · refine Or.inl ⟨b, pe, hplook, by omega, hbePar,
          IndexedAncestor.edge b cIdx ce hce hp⟩
      · rcases ih pe hplook hbePar with hex | hne
        · obtain ⟨sIdx, S, hS, _hsne, hSPar, hchainS⟩ := hex
          have hsB := hlt sIdx b hchainS
          refine Or.inl ⟨sIdx, S, hS, by omega, hSPar,
            IndexedAncestor.tail hchainS ce hce hp⟩
        · exact Or.inr hne

set_option maxHeartbeats 1000000 in
/-- The generated rib's entries are backwards-parented. -/
private theorem rib_parent_back (ns : List Tree.Node) (cause k : Nat) :
    ∀ (i : Nat) (e : Entry), (generatedRib ns (cause, k)).entries[i]? = some e →
      e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        (generatedRib ns (cause, k)).entries[p]? = some pe := by
  obtain ⟨segE, hEq, hProp⟩ :=
    flatten_parent_back ns (upper k) 64 (children ns cause) (-1) 2 [] []
  have hf2 : (generatedRib ns (cause, k)).entries =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1 :=
    congrArg Prod.fst (generated_rib_fields ns cause k).2.2.1
  have hgr : (generatedRib ns (cause, k)).entries = segE := by
    rw [hf2, hEq]
    exact List.nil_append segE
  intro i e hlook
  have hres := hProp i e (by rw [hgr] at hlook; exact hlook) (Nat.zero_le i)
  rw [hgr]
  simpa only [List.nil_append, List.length_nil, Nat.zero_le, true_and, and_true] using hres

/-- Named flatten-order fact: roots and even-depth entries appear in
`rib.order` at positions increasing with their entry index (flatten appends
even-depth entries in traversal order, which is the index order). -/
def Branch5RootOrderFact (ns : List Tree.Node) (cause k : Nat) : Prop :=
  ∀ (a b : Nat) (ae be : Entry) (pa pb : Nat × Nat),
    (generatedRib ns (cause, k)).entries[a]? = some ae → ae.parent = -1 →
    (generatedRib ns (cause, k)).entries[b]? = some be → be.depth % 2 = 0 →
    a < b →
    (generatedRib ns (cause, k)).order.zipIdx.find? (fun v => v.1 == a) = some pa →
    (generatedRib ns (cause, k)).order.zipIdx.find? (fun v => v.1 == b) = some pb →
    pa.2 < pb.2

/-- Named flatten-block fact: root blocks are contiguous, so an entry chained
to a root `r1` stays below the next root `r2`. -/
def Branch5BlockContiguity (ns : List Tree.Node) (cause k : Nat) : Prop :=
  ∀ (r1 r2 i : Nat) (e1 e2 : Entry),
    (generatedRib ns (cause, k)).entries[r1]? = some e1 → e1.parent = -1 →
    (generatedRib ns (cause, k)).entries[r2]? = some e2 → e2.parent = -1 →
    r1 < r2 →
    (r1 = i ∨ IndexedAncestor (generatedRib ns (cause, k)).entries r1 i) →
    i < r2

set_option maxHeartbeats 1000000 in
/-- The corrected branch-5 classification holds for every odd-depth entry `I`
and earlier entry `J` of a generated rib, in the deeper-earlier branch's scope:
`I.parent ≠ jIdx` (the parent-box case is separate) and `J.parent ≠ I.parent`
(the sibling case is separate). The two flatten-order facts enter as the named
hypotheses `horder` and `hcontig`. -/
theorem hard_b_branch5_placement_block (ns : List Tree.Node) (cause k : Nat)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (child j : Entry) (childIdx jIdx : Nat)
    (hchild : (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hj : (j, jIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hodd : child.depth % 2 ≠ 0)
    (hjlt : jIdx < childIdx)
    (hpar : child.parent ≠ (jIdx : Int))
    (hsib : j.parent ≠ child.parent)
    (horder : Branch5RootOrderFact ns cause k)
    (hcontig : Branch5BlockContiguity ns cause k) :
    HardBBranch5PlacementBlock ns cause k (child.parent).toNat childIdx jIdx j := by
  have hbackE := rib_parent_back ns cause k
  have hclt := chain_lt_of_parent_back _ hbackE
  have hcLook : (generatedRib ns (cause, k)).entries[childIdx]? = some child :=
    List.mem_zipIdx_iff_getElem?.mp hchild
  have hjLook : (generatedRib ns (cause, k)).entries[jIdx]? = some j :=
    List.mem_zipIdx_iff_getElem?.mp hj
  have hchildPar : ∃ (p : Nat) (pe : Entry), child.parent = (p : Int) ∧ p < childIdx ∧
      (generatedRib ns (cause, k)).entries[p]? = some pe := by
    rcases hbackE childIdx child hcLook with hr | hex
    · exfalso
      have hroot2 : child.depth = 2 :=
        generated_root_depth ns cause k hlink hcause child childIdx hchild hr
      omega
    · exact hex
  obtain ⟨parentIdx, PE, hcp, hplt, hPE⟩ := hchildPar
  have hpInt : (parentIdx : Int) = child.parent := hcp.symm
  have hpid : (child.parent).toNat = parentIdx := by omega
  have hPEmem : (PE, parentIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hPE
  have hPEeven : PE.depth % 2 = 0 := by
    have hdepth := generated_parent_child_depth ns cause k hlink hcause PE child
      parentIdx childIdx hPEmem hchild hcp
    omega
  have hjParNe : j.parent ≠ (parentIdx : Int) := fun h => hsib (h.trans hpInt)
  have hchildRoot : ∃ (h0 : Nat) (H0 : Entry),
      (generatedRib ns (cause, k)).entries[h0]? = some H0 ∧ H0.parent = -1 ∧
      h0 ≤ parentIdx ∧
      IndexedAncestor (generatedRib ns (cause, k)).entries h0 childIdx := by
    obtain ⟨h0, H0, hH0, hH0root, hdelta0⟩ :=
      entries_root_exists _ hbackE parentIdx parentIdx (Nat.le_refl _) PE hPE
    refine ⟨h0, H0, hH0, hH0root, ?_, ?_⟩
    · rcases hdelta0 with heq | hchain0
      · rw [heq]
        exact Nat.le_refl _
      · exact Nat.le_of_lt (hclt h0 parentIdx hchain0)
    · rcases hdelta0 with heq | hchain0
      · rw [heq]
        exact IndexedAncestor.edge parentIdx childIdx child hcLook hcp
      · exact IndexedAncestor.tail hchain0 child hcLook hcp
  obtain ⟨hIdx, H, hH, hHroot, hdelta⟩ :=
    entries_root_exists _ hbackE jIdx jIdx (Nat.le_refl _) j hjLook
  rw [hpid]
  rcases hdelta with heq | hchain
  · rw [heq] at hH
    have hjRoot : H = j := Option.some.inj (hH.symm.trans hjLook)
    have hjRootPar : j.parent = -1 := by rw [← hjRoot]; exact hHroot
    by_cases hjp : jIdx < parentIdx
    · refine Or.inr ⟨jIdx, j, hjLook, hjRootPar, Or.inl ⟨rfl, rfl⟩,
        fun headPos parentPos hHead hParent =>
          Or.inr (horder jIdx parentIdx j PE headPos parentPos hjLook hjRootPar hPE
            hPEeven hjp hHead hParent)⟩
    · exfalso
      have hlt0 : parentIdx < jIdx := by
        by_cases heq2 : parentIdx = jIdx
        · exact absurd (by rw [← heq2]; exact hcp) hpar
        · omega
      obtain ⟨h0, H0, hH0, hH0root, hle0, hchain0⟩ := hchildRoot
      have hbound := hcontig h0 jIdx childIdx H0 j hH0 hH0root hjLook hjRootPar
        (by omega) (Or.inr hchain0)
      omega
  · have hscan := chain_scan _ parentIdx hbackE hclt hIdx jIdx hchain j
      hjLook hjParNe
    rcases hscan with ⟨sIdx, S, hS, hsne, hSPar, hchainS⟩ | hne
    · exact Or.inl ⟨sIdx, S, hS, hsne, hSPar, hchainS⟩
    by_cases hhp : hIdx < parentIdx
    · refine Or.inr ⟨hIdx, H, hH, hHroot, Or.inr hchain,
        fun headPos parentPos hHead hParent =>
          Or.inr (horder hIdx parentIdx H PE headPos parentPos hH hHroot hPE hPEeven hhp
            hHead hParent)⟩
    · exfalso
      obtain ⟨h0, H0, hH0, hH0root, hle0, hchain0⟩ := hchildRoot
      have hbound := hcontig h0 hIdx childIdx H0 H hH0 hH0root hH hHroot
        (by omega) (Or.inr hchain0)
      have hhj := hclt hIdx jIdx hchain
      omega

/-! ### Block contiguity from the flatten fold -/

/-- Fold-level block structure: every appended entry either is a direct child of
the call's own `par`, or has a parent inside the appended segment with no
direct-`par` entry strictly between that parent and the entry. For the top call
(`par = -1`) the direct entries are exactly the block heads, so no root lies
strictly between an entry's parent and the entry. -/
private theorem flatten_blocks (ns : List Tree.Node) (up : Bool) :
    ∀ (fuel : Nat) (ids : List Nat) (par : Int) (depth : Nat) (es : List Entry)
      (os : List Nat),
      par = -1 ∨ (0 ≤ par ∧ (par.toNat) < es.length) →
      ∃ (segE : List Entry),
        (flatten ns up fuel ids par depth es os).1 = es ++ segE ∧
        ∀ (i : Nat) (e : Entry), (es ++ segE)[i]? = some e → es.length ≤ i →
          e.parent = par ∨
          ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ es.length ≤ p ∧ p < i ∧
            (es ++ segE)[p]? = some pe ∧
            ∀ (r2 : Nat) (re2 : Entry), es.length ≤ r2 ∧ r2 ≤ i ∧
              (es ++ segE)[r2]? = some re2 ∧ re2.parent = par → r2 ≤ p := by
  intro fuel
  induction fuel with
  | zero =>
    intro ids par depth es os _hp0
    refine ⟨[], by simp [flatten], ?_⟩
    intro i e hlook hle
    rw [List.getElem?_append_right hle, List.getElem?_nil] at hlook
    exact absurd hlook (by simp)
  | succ fuel ih =>
    intro ids par depth es os hp0
    have inner :
        ∀ (ls : List Nat) (st : List Entry × List Nat), es.length ≤ st.1.length →
          ∃ (segE : List Entry),
            (ls.foldl (flattenStep ns up fuel par depth) st).1 = st.1 ++ segE ∧
            ∀ (i : Nat) (e : Entry), (st.1 ++ segE)[i]? = some e → st.1.length ≤ i →
              e.parent = par ∨
              ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ st.1.length ≤ p ∧
                p < i ∧ (st.1 ++ segE)[p]? = some pe ∧
                ∀ (r2 : Nat) (re2 : Entry), st.1.length ≤ r2 ∧ r2 ≤ i ∧
                  (st.1 ++ segE)[r2]? = some re2 ∧ re2.parent = par → r2 ≤ p := by
      intro ls
      induction ls with
      | nil =>
        intro st _hst
        refine ⟨[], by simp, ?_⟩
        intro i e hlook hle
        rw [List.getElem?_append_right hle, List.getElem?_nil] at hlook
        exact absurd hlook (by simp)
      | cons node rest ihrest =>
        intro st hst
        obtain ⟨dE, hdE, hdprop⟩ :=
          ih (children ns node) (st.1.length : Int) (depth + 1)
            (st.1 ++ [(⟨node, par, depth⟩ : Entry)])
            (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2)
            (Or.inr ⟨by omega, by
              simp only [List.length_append, List.length_singleton]; omega⟩)
        have hstep : (flattenStep ns up fuel par depth st node).1
              = (st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE := hdE
        obtain ⟨segE', hsegE', hprop'⟩ :=
          ihrest (flattenStep ns up fuel par depth st node)
            (by
              rw [hstep]
              simp only [List.length_append, List.length_singleton]
              omega)
        rw [hstep] at hsegE' hprop'
        have hlen1 : (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length
            = st.1.length + 1 := by
          simp only [List.length_append, List.length_singleton]
        have hlenA : ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE).length
            = (st.1.length + 1) + dE.length := by
          rw [List.length_append, hlen1]
        have happ : st.1 ++ ((⟨node, par, depth⟩ : Entry) :: (dE ++ segE'))
            = ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE) ++ segE' := by
          simp [List.append_assoc]
        have hnlt : par.toNat < st.1.length ∨ par = -1 := by
          rcases hp0 with h | ⟨h1, h2⟩
          · exact Or.inr h
          · exact Or.inl (by omega)
        have hnoPar : ∀ (r2 : Nat) (re2 : Entry),
            (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ r2 →
            ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE)[r2]? = some re2 →
            re2.parent ≠ par := by
          intro r2 re2 hr2 hrlook habs
          rcases hdprop r2 re2 hrlook hr2 with hd | ⟨p, pe, hpe, hpge, _, _, _⟩
          · rw [hd] at habs
            omega
          · rw [hlen1] at hpge
            rw [hpe] at habs
            omega
        refine ⟨(⟨node, par, depth⟩ : Entry) :: (dE ++ segE'), ?_, ?_⟩
        · rw [List.foldl_cons, hsegE']
          exact happ.symm
        · intro i e hlook hle
          by_cases hin : i < st.1.length + 1
          · have hieq : i = st.1.length := by omega
            rw [List.getElem?_append_right hle, hieq, Nat.sub_self,
              List.getElem?_cons_zero, Option.some.injEq] at hlook
            exact Or.inl (by rw [← hlook])
          · by_cases hiA : i < (st.1.length + 1) + dE.length
            · have hlookA : ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE)[i]? = some e := by
                rw [happ, List.getElem?_append_left (by rw [hlenA]; omega)] at hlook
                exact hlook
              have hi1 : (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ i := by
                rw [hlen1]; omega
              rcases hdprop i e hlookA hi1 with
                hd | ⟨p, pe, hpe, hpge, hplt, hplook, hginv⟩
              · refine Or.inr ⟨st.1.length, ⟨node, par, depth⟩, hd, by omega, by omega, ?_, ?_⟩
                · rw [happ, List.getElem?_append_left (by rw [hlenA]; omega),
                    List.getElem?_append_left (by rw [hlen1]; omega),
                    List.getElem?_append_right (Nat.le_refl st.1.length),
                    Nat.sub_self, List.getElem?_singleton]
                  rfl
                · intro r2 re2 hconj
                  obtain ⟨_hr2, _hr2i, hrlook, hrpar⟩ := hconj
                  by_cases hr2n : r2 < st.1.length + 1
                  · omega
                  · rw [happ, List.getElem?_append_left (by rw [hlenA]; omega)] at hrlook
                    exact (hnoPar r2 re2 (by rw [hlen1]; omega) hrlook hrpar).elim
              · refine Or.inr ⟨p, pe, hpe, by omega, hplt, ?_, ?_⟩
                · rw [happ, List.getElem?_append_left (by rw [hlenA]; omega)]
                  exact hplook
                · intro r2 re2 hconj
                  obtain ⟨_hr2, _hr2i, hrlook, hrpar⟩ := hconj
                  by_cases hr2n : r2 < st.1.length + 1
                  · omega
                  · rw [happ, List.getElem?_append_left (by rw [hlenA]; omega)] at hrlook
                    exact (hnoPar r2 re2 (by rw [hlen1]; omega) hrlook hrpar).elim
            · have hlook2 : (((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE) ++ segE')[i]? = some e := by
                rw [← happ]
                exact hlook
              rcases hprop' i e hlook2 (by rw [hlenA]; omega) with hd | hex
              · exact Or.inl hd
              · obtain ⟨p, pe, hpe, hpge, hplt, hplook, hginv⟩ := hex
                refine Or.inr ⟨p, pe, hpe, by omega, hplt, ?_, ?_⟩
                · rw [happ]
                  exact hplook
                intro r2 re2 hconj
                rw [happ] at hconj
                obtain ⟨_hr2, _hr2i, hrlook, hrpar⟩ := hconj
                by_cases hrA : ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE).length ≤ r2
                · exact hginv r2 re2 ⟨hrA, _hr2i, hrlook, hrpar⟩
                · rw [hlenA] at hrA
                  omega
    obtain ⟨segE, hsegE, hprop⟩ :=
      inner (if up then ids.reverse else ids) (es, os) (Nat.le_refl es.length)
    rw [flatten_succ_eq_foldl]
    exact ⟨segE, hsegE, hprop⟩

/-- Rib-level block structure: every entry of a generated rib is a block head
(`parent = -1`) or has an in-rib parent with no block head between that parent
and the entry. -/
private theorem rib_blocks (ns : List Tree.Node) (cause k : Nat) :
    ∀ (i : Nat) (e : Entry), (generatedRib ns (cause, k)).entries[i]? = some e →
      e.parent = -1 ∨
      ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        (generatedRib ns (cause, k)).entries[p]? = some pe ∧
        ∀ (r2 : Nat) (re2 : Entry), r2 ≤ i ∧
          (generatedRib ns (cause, k)).entries[r2]? = some re2 ∧ re2.parent = -1 → r2 ≤ p := by
  obtain ⟨segE, hEq, hProp⟩ :=
    flatten_blocks ns (upper k) 64 (children ns cause) (-1) 2 [] [] (Or.inl rfl)
  have hf2 : (generatedRib ns (cause, k)).entries = [] ++ segE :=
    (congrArg Prod.fst (generated_rib_fields ns cause k).2.2.1).trans hEq
  intro i e hlook
  have hres := hProp i e (by rw [← hf2]; exact hlook) (Nat.zero_le i)
  rw [hf2]
  simpa only [List.nil_append, List.length_nil, Nat.zero_le, true_and, and_true] using hres

/-- No block head lies strictly between a root and a chained descendant. -/
private theorem chain_no_root_between (E : List Entry)
    (hblk : ∀ (i : Nat) (e : Entry), E[i]? = some e →
      e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        E[p]? = some pe ∧
        ∀ (r2 : Nat) (re2 : Entry), r2 ≤ i ∧ E[r2]? = some re2 ∧ re2.parent = -1 → r2 ≤ p) :
    ∀ (a c : Nat), IndexedAncestor E a c → ∀ (ae : Entry), E[a]? = some ae →
      ae.parent = -1 →
      ∀ (w : Nat) (we : Entry), a < w → w ≤ c → E[w]? = some we → we.parent ≠ -1 := by
  intro a c hchain
  induction hchain with
  | edge _cIdx e he hp =>
    intro ae hae _hroot w we hgt hle hlook habs
    rcases hblk _ e he with hd | ⟨p, pe, hpe, hplt, _, hginv⟩
    · rw [hd] at hp
      omega
    · have hwp : w ≤ p := hginv w we ⟨hle, hlook, habs⟩
      rw [hpe] at hp
      omega
  | @tail b _cIdx hab e he hp ih =>
    intro ae hae hroot w we hgt hle hlook habs
    by_cases hw : w ≤ b
    · exact ih ae hae hroot w we hgt hw hlook habs
    · rcases hblk _ e he with hd | ⟨p, pe, hpe, hplt, _, hginv⟩
      · rw [hd] at hp
        omega
      · have hwp : w ≤ p := hginv w we ⟨hle, hlook, habs⟩
        rw [hpe] at hp
        omega

/-- `Branch5BlockContiguity` for the actual generated rib: an entry chained to a
root `r1` stays below the next root `r2`. -/
theorem branch5_block_contiguity (ns : List Tree.Node) (cause k : Nat) :
    Branch5BlockContiguity ns cause k := by
  have hblk := rib_blocks ns cause k
  intro r1 r2 i e1 e2 h1 h1root h2 h2root hlt harm
  rcases harm with rfl | hchain
  · omega
  · rcases Nat.lt_or_ge i r2 with hilt | hile
    · exact hilt
    · exfalso
      exact chain_no_root_between _ hblk r1 i hchain e1 h1 h1root r2 e2 hlt hile h2 h2root

/-! ### Order monotonicity via pairwise even emission order -/

/-- Every even-depth entry appearing earlier in the list has strictly smaller
index than every even-depth entry appearing later. -/
private def EvenBefore (E : List Entry) : List Nat → Prop
  | [] => True
  | x :: rest =>
      (∀ y ∈ rest, ∀ (ye ey : Entry), E[x]? = some ye → ye.depth % 2 = 0 →
        E[y]? = some ey → ey.depth % 2 = 0 → x < y) ∧ EvenBefore E rest

private theorem evenBefore_append {E : List Entry} {l1 l2 : List Nat} :
    EvenBefore E l1 → EvenBefore E l2 →
    (∀ x ∈ l1, ∀ y ∈ l2, ∀ (xe ey : Entry), E[x]? = some xe → xe.depth % 2 = 0 →
      E[y]? = some ey → ey.depth % 2 = 0 → x < y) → EvenBefore E (l1 ++ l2) := by
  induction l1 with
  | nil => intro _ h2 _; exact h2
  | cons x rest ih =>
      intro h1 h2 hc
      obtain ⟨hhead, htail⟩ := h1
      refine ⟨?_, ih htail h2 ?_⟩
      · intro y hy ye ey hxe hxe2 hey hey2
        rcases List.mem_append.mp hy with hy' | hy'
        · exact hhead y hy' ye ey hxe hxe2 hey hey2
        · exact hc x (List.mem_cons_self) y hy' ye ey hxe hxe2 hey hey2
      · intro a ha b hb ae aeven be beven
        exact hc a (List.mem_cons_of_mem _ ha) b hb ae aeven be beven

private theorem evenBefore_append_left {E : List Entry} {l1 l2 : List Nat} :
    EvenBefore E (l1 ++ l2) → EvenBefore E l1 := by
  induction l1 with
  | nil => intro _; exact trivial
  | cons x rest ih =>
      intro h
      obtain ⟨hhead, htail⟩ := h
      refine ⟨?_, ih htail⟩
      intro y hy ye ey hxe hxe2 hey hey2
      exact hhead y (List.mem_append.mpr (Or.inl hy)) ye ey hxe hxe2 hey hey2

private theorem evenBefore_append_right {E : List Entry} {l1 l2 : List Nat} :
    EvenBefore E (l1 ++ l2) → EvenBefore E l2 := by
  induction l1 with
  | nil => intro h; exact h
  | cons x rest ih =>
      intro h
      obtain ⟨_, htail⟩ := h
      exact ih htail

private theorem evenBefore_append_cross {E : List Entry} {l1 l2 : List Nat} :
    EvenBefore E (l1 ++ l2) →
    ∀ x ∈ l1, ∀ y ∈ l2, ∀ (xe ey : Entry), E[x]? = some xe → xe.depth % 2 = 0 →
      E[y]? = some ey → ey.depth % 2 = 0 → x < y := by
  induction l1 with
  | nil => intro _ x hx; exact absurd hx (by simp)
  | cons x rest ih =>
      intro h a ha b hb ae aeven be beven
      obtain ⟨hhead, htail⟩ := h
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact hhead b (List.mem_append.mpr (Or.inr hb)) ae aeven be beven
      · exact ih htail a ha' b hb ae aeven be beven

/-- Two list positions with lookups give the pairwise constraint of
`EvenBefore`. -/
private theorem evenBefore_of_pos {E : List Entry} {l : List Nat}
    (heb : EvenBefore E l) {p q x y : Nat} (hp : l[p]? = some x) (hq : l[q]? = some y)
    (hpq : p < q) {xe ye : Entry} (hx : E[x]? = some xe) (hxe : xe.depth % 2 = 0)
    (hy : E[y]? = some ye) (hye : ye.depth % 2 = 0) : x < y := by
  induction l generalizing p q with
  | nil =>
    rw [List.getElem?_nil] at hp
    exact absurd hp (by simp)
  | cons z rest ih =>
    rcases p with _ | p
    · rw [List.getElem?_cons_zero] at hp
      have hzx : z = x := Option.some.inj hp
      subst hzx
      obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [hq', List.getElem?_cons_succ] at hq
      obtain ⟨hhead, _⟩ := heb
      exact hhead y (List.mem_of_getElem? hq) xe ye hx hxe hy hye
    · rw [List.getElem?_cons_succ] at hp
      rcases q with _ | q
      · omega
      · rw [List.getElem?_cons_succ] at hq
        obtain ⟨_, htail⟩ := heb
        exact ih htail hp hq (by omega)

/-- Extending the entry list does not affect `EvenBefore` for a list of
already-emitted indices. -/
private theorem evenBefore_extend {E : List Entry} {F : List Entry} {l : List Nat}
    (hlook : ∀ x ∈ l, x < E.length) : EvenBefore E l → EvenBefore (E ++ F) l := by
  induction l with
  | nil => intro _; exact trivial
  | cons x rest ih =>
      intro h
      obtain ⟨hhead, htail⟩ := h
      have hrest : ∀ y ∈ rest, y < E.length := fun y hy => hlook y (List.mem_cons_of_mem _ hy)
      refine ⟨?_, ih hrest htail⟩
      intro y hy ye ey hye1 hye2 hey1 hey2
      have hxE : E[x]? = some ye := by
        rw [List.getElem?_append_left (hlook x (List.mem_cons_self))] at hye1
        exact hye1
      have hyE : E[y]? = some ey := by
        have hyj : y < E.length := hlook y (List.mem_cons_of_mem _ hy)
        rw [List.getElem?_append_left hyj] at hey1
        exact hey1
      exact hhead y hy ye ey hxE hye2 hyE hey2

/-- The generated rib's own emissions are its own entry indices, and even-depth
entries are emitted in index order. -/
private theorem flatten_order (ns : List Tree.Node) (up : Bool) :
    ∀ (fuel : Nat) (ids : List Nat) (par : Int) (depth : Nat) (es : List Entry)
      (os : List Nat),
      par = -1 ∨ (0 ≤ par ∧ (par.toNat) < es.length) →
      (∀ (i : Nat) (x : Nat), os[i]? = some x → x < es.length) →
      EvenBefore es os →
      ∃ (segE : List Entry) (segO : List Nat),
        flatten ns up fuel ids par depth es os = (es ++ segE, os ++ segO) ∧
        (∀ (i : Nat) (x : Nat), segO[i]? = some x →
          es.length ≤ x ∧ x < (es ++ segE).length) ∧
        EvenBefore (es ++ segE) (os ++ segO) := by
  intro fuel
  induction fuel with
  | zero =>
    intro ids par depth es os _hp0 _hemit heven
    refine ⟨[], [], by simp [flatten], ?_, ?_⟩
    · intro i x hlook
      exact absurd hlook (by simp)
    · rw [List.append_nil, List.append_nil]
      exact heven
  | succ fuel ih =>
    intro ids par depth es os hp0 hosEmit hosEven
    have inner :
        ∀ (ls : List Nat) (st : List Entry × List Nat), es.length ≤ st.1.length →
          (∀ (i : Nat) (x : Nat), st.2[i]? = some x → x < st.1.length) →
          EvenBefore st.1 st.2 →
          ∃ (segE : List Entry) (segO : List Nat),
            (ls.foldl (flattenStep ns up fuel par depth) st) = (st.1 ++ segE, st.2 ++ segO) ∧
            (∀ (i : Nat) (x : Nat), segO[i]? = some x →
              es.length ≤ x ∧ x < (st.1 ++ segE).length) ∧
            EvenBefore (st.1 ++ segE) (st.2 ++ segO) := by
      intro ls
      induction ls with
      | nil =>
        intro st _hlen _hem hev
        refine ⟨[], [], by simp, ?_, ?_⟩
        · intro i x hlook
          exact absurd hlook (by simp)
        · rw [List.append_nil, List.append_nil]
          exact hev
      | cons node rest ihrest =>
        intro st hstLen hstEmit hstEven
        have hlen1 : (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length = st.1.length + 1 := by
          simp only [List.length_append, List.length_singleton]
        rcases Nat.mod_two_eq_zero_or_one depth with hdp | hdp
        · obtain ⟨dE, dO, hpairI, hsegI, hEvenI⟩ :=
            ih (children ns node) (st.1.length : Int) (depth + 1)
              (st.1 ++ [(⟨node, par, depth⟩ : Entry)]) (st.2 ++ [st.1.length])
              (Or.inr ⟨by omega, by
                simp only [List.length_append, List.length_singleton]; omega⟩)
              (by
                intro i x hlook
                rcases Nat.lt_or_ge i st.2.length with hi | hi
                · rw [List.getElem?_append_left hi] at hlook
                  have hx := hstEmit i x hlook
                  simp only [List.length_append, List.length_singleton] at hx ⊢
                  omega
                · have hib := (List.getElem?_eq_some_iff.mp hlook).1
                  simp only [List.length_append, List.length_singleton] at hib
                  have hieq : i = st.2.length := by omega
                  rw [List.getElem?_append_right (by omega)] at hlook
                  rw [hieq, Nat.sub_self, List.getElem?_cons_zero] at hlook
                  have hx : x = st.1.length := (Option.some.inj hlook).symm
                  simp only [List.length_append, List.length_singleton]
                  omega)
                  (evenBefore_append
                    (evenBefore_extend
                      (E := st.1) (F := [⟨node, par, depth⟩]) (l := st.2)
                      (by
                        intro x hx
                        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
                        exact hstEmit j x hj) hstEven)
                    (⟨by intro y hy ye ey _ _ _ _; exact absurd hy (by simp), trivial⟩ :
                      EvenBefore _ [st.1.length])
                    (by
                      intro x hx y hy xe ey hxe _ hey _
                      have hxy : y = st.1.length := by
                        rcases List.mem_cons.mp hy with rfl | hy'
                        · rfl
                        · exact absurd hy' (by simp)
                      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
                      have hxlt := hstEmit j x hj
                      omega))
          have hstepPair : flattenStep ns up fuel par depth st node
              = ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE,
                  (st.2 ++ [st.1.length]) ++ dO) := by
            simp [flattenStep, hdp, hpairI]
          have hEvenD : EvenBefore ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE) dO := by
            have h := evenBefore_append_right
              (E := (st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE)
              (l1 := st.2 ++ [st.1.length]) (l2 := dO) hEvenI
            exact h
          obtain ⟨segE', segO', hpairR, hsegR, hEvenR⟩ :=
            ihrest (((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE),
              (st.2 ++ [st.1.length]) ++ dO)
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by
                intro i x hlook
                have hmem : x ∈ ((st.2 ++ [st.1.length]) ++ dO) :=
                  List.mem_of_getElem? hlook
                simp only [List.length_append, List.length_singleton]
                rcases List.mem_append.mp hmem with h | h
                · rcases List.mem_append.mp h with hst | hidx
                  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hst
                    have hx := hstEmit j x hj
                    omega
                  · have hx : x = st.1.length := by
                      rcases List.mem_cons.mp hidx with rfl | hnil
                      · rfl
                      · exact absurd hnil (by simp)
                    omega
                · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
                  have hx := (hsegI j x hj).2
                  simp only [List.length_append, List.length_singleton] at hx
                  omega)
              (evenBefore_append
                (E := ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE))
                (l1 := st.2 ++ [st.1.length]) (l2 := dO)
                (evenBefore_append
                  (E := ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE))
                  (l1 := st.2) (l2 := [st.1.length])
                  (evenBefore_extend
                    (E := st.1 ++ [(⟨node, par, depth⟩ : Entry)]) (F := dE) (l := st.2)
                    (by
                      intro x hx
                      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
                      have hxlt := hstEmit j x hj
                      simp only [List.length_append, List.length_singleton]
                      omega)
                    (evenBefore_extend
                      (E := st.1) (F := [(⟨node, par, depth⟩ : Entry)]) (l := st.2)
                      (by
                        intro x hx
                        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
                        exact hstEmit j x hj) hstEven))
                  (⟨by intro y hy ye ey _ _ _ _; exact absurd hy (by simp), trivial⟩ :
                    EvenBefore (((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE)) [st.1.length])
                  (by
                    intro x hx y hy xe ey hxe _ hey _
                    have hxy : y = st.1.length := by
                      rcases List.mem_cons.mp hy with rfl | hy'
                      · rfl
                      · exact absurd hy' (by simp)
                    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
                    have hxlt := hstEmit j x hj
                    omega))
                hEvenD
                (by
                  intro x hx y hy xe ey hxe _ hey _
                  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
                  have hyb := (hsegI j y hj).1
                  simp only [List.length_append, List.length_singleton] at hyb
                  rcases List.mem_append.mp hx with hxst | hxidx
                  · obtain ⟨jj, hjj⟩ := List.mem_iff_getElem?.mp hxst
                    have hxlt := hstEmit jj x hjj
                    omega
                  · have hxeq : x = st.1.length := by
                      rcases List.mem_cons.mp hxidx with rfl | hnil
                      · rfl
                      · exact absurd hnil (by simp)
                    omega))
          have happE : st.1 ++ ((⟨node, par, depth⟩ : Entry) :: (dE ++ segE'))
              = ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE) ++ segE' := by
            simp [List.append_assoc]
          have happO : st.2 ++ ([st.1.length] ++ dO ++ segO')
              = ((st.2 ++ [st.1.length]) ++ dO) ++ segO' := by
            simp [List.append_assoc]
          refine ⟨(⟨node, par, depth⟩ : Entry) :: (dE ++ segE'),
            [st.1.length] ++ dO ++ segO', ?_, ?_, ?_⟩
          · rw [List.foldl_cons, hstepPair, hpairR]
            simp [List.append_assoc]
          · intro i x hlook
            have hmem : x ∈ ([st.1.length] ++ (dO ++ segO')) :=
              List.mem_of_getElem? hlook
            simp only [List.length_append, List.length_cons]
            rcases List.mem_append.mp hmem with h | h
            · rcases List.mem_cons.mp h with hidx | hnil
              · rw [hidx]
                constructor <;> omega
              · exact absurd hnil (by simp)
            · rcases List.mem_append.mp h with hdO | hseg
              · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hdO
                obtain ⟨hlB, huB⟩ := hsegI j x hj
                simp only [List.length_append, List.length_singleton] at hlB huB
                constructor <;> omega
              · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hseg
                obtain ⟨hlB, huB⟩ := hsegR j x hj
                simp only [List.length_append, List.length_singleton] at hlB huB
                constructor <;> omega
          · rw [happE, happO]
            exact hEvenR
        · obtain ⟨dE, dO, hpairI, hsegI, hEvenI⟩ :=
            ih (children ns node) (st.1.length : Int) (depth + 1)
              (st.1 ++ [(⟨node, par, depth⟩ : Entry)]) st.2
              (Or.inr ⟨by omega, by
                simp only [List.length_append, List.length_singleton]; omega⟩)
              (by
                intro i x hlook
                have hx := hstEmit i x hlook
                simp only [List.length_append, List.length_singleton]
                omega)
              (evenBefore_extend
                (E := st.1) (F := [(⟨node, par, depth⟩ : Entry)]) (l := st.2)
                (by
                  intro x hx
                  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
                  exact hstEmit j x hj) hstEven)
          have hstepPair : flattenStep ns up fuel par depth st node
              = ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE,
                  (st.2 ++ dO) ++ [st.1.length]) := by
            simp [flattenStep, hdp, hpairI]
          have hEvenD : EvenBefore ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE) dO := by
            have h := evenBefore_append_right
              (E := (st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE)
              (l1 := st.2) (l2 := dO) hEvenI
            exact h
          obtain ⟨segE', segO', hpairR, hsegR, hEvenR⟩ :=
            ihrest (((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE),
              (st.2 ++ dO) ++ [st.1.length])
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by
                intro i x hlook
                have hmem : x ∈ ((st.2 ++ dO) ++ [st.1.length]) :=
                  List.mem_of_getElem? hlook
                simp only [List.length_append, List.length_singleton]
                rcases List.mem_append.mp hmem with h | h
                · rcases List.mem_append.mp h with hst | hdO
                  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hst
                    have hx := hstEmit j x hj
                    omega
                  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hdO
                    have hx := (hsegI j x hj).2
                    simp only [List.length_append, List.length_singleton] at hx
                    omega
                · have hx : x = st.1.length := by
                    rcases List.mem_cons.mp h with rfl | hnil
                    · rfl
                    · exact absurd hnil (by simp)
                  omega)
              (evenBefore_append
                (E := ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE))
                (l1 := st.2 ++ dO) (l2 := [st.1.length])
                (evenBefore_append
                  (E := ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE))
                  (l1 := st.2) (l2 := dO)
                  (evenBefore_extend
                    (E := st.1 ++ [(⟨node, par, depth⟩ : Entry)]) (F := dE) (l := st.2)
                    (by
                      intro x hx
                      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
                      have hxlt := hstEmit j x hj
                      simp only [List.length_append, List.length_singleton]
                      omega)
                    (evenBefore_extend
                      (E := st.1) (F := [(⟨node, par, depth⟩ : Entry)]) (l := st.2)
                      (by
                        intro x hx
                        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
                        exact hstEmit j x hj) hstEven))
                  hEvenD
                  (by
                    intro x hx y hy xe ey hxe _ hey _
                    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
                    have hxlt := hstEmit j x hj
                    obtain ⟨jj, hjj⟩ := List.mem_iff_getElem?.mp hy
                    have hyb := (hsegI jj y hjj).1
                    simp only [List.length_append, List.length_singleton] at hyb
                    omega))
                (⟨by intro y hy ye ey _ _ _ _; exact absurd hy (by simp), trivial⟩ :
                  EvenBefore (((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE)) [st.1.length])
                (by
                  intro x hx y hy xe ey hxe _ hey heyEven
                  have hxy : y = st.1.length := by
                    rcases List.mem_cons.mp hy with rfl | hy'
                    · rfl
                    · exact absurd hy' (by simp)
                  subst hxy
                  have hlook : (((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE))[st.1.length]?
                      = some ⟨node, par, depth⟩ := by
                    rw [List.getElem?_append_left
                      (by simp only [List.length_append, List.length_singleton]; omega),
                      List.getElem?_append_right (Nat.le_refl st.1.length), Nat.sub_self,
                      List.getElem?_cons_zero]
                  have heq : ey = ⟨node, par, depth⟩ := Option.some.inj (hey.symm.trans hlook)
                  have hdep : depth % 2 = 0 := by rw [heq] at heyEven; exact heyEven
                  omega))
          have happE : st.1 ++ ((⟨node, par, depth⟩ : Entry) :: (dE ++ segE'))
              = ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE) ++ segE' := by
            simp [List.append_assoc]
          have happO : st.2 ++ (dO ++ [st.1.length] ++ segO')
              = ((st.2 ++ dO) ++ [st.1.length]) ++ segO' := by
            simp [List.append_assoc]
          refine ⟨(⟨node, par, depth⟩ : Entry) :: (dE ++ segE'),
            dO ++ [st.1.length] ++ segO', ?_, ?_, ?_⟩
          · rw [List.foldl_cons, hstepPair, hpairR]
            simp [List.append_assoc]
          · intro i x hlook
            have hmem : x ∈ (dO ++ [st.1.length] ++ segO') :=
              List.mem_of_getElem? hlook
            simp only [List.length_append, List.length_cons]
            rcases List.mem_append.mp hmem with h | h
            · rcases List.mem_append.mp h with hdO | hidx
              · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hdO
                obtain ⟨hlB, huB⟩ := hsegI j x hj
                simp only [List.length_append, List.length_singleton] at hlB huB
                constructor <;> omega
              · rcases List.mem_cons.mp hidx with hidx | hnil
                · rw [hidx]
                  constructor <;> omega
                · exact absurd hnil (by simp)
            · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
              obtain ⟨hlB, huB⟩ := hsegR j x hj
              simp only [List.length_append, List.length_singleton] at hlB huB
              constructor <;> omega
          · rw [happE, happO]
            exact hEvenR
    obtain ⟨segE, segO, hpair, hseg, hEven⟩ :=
      inner (if up then ids.reverse else ids) (es, os)
        (Nat.le_refl es.length) hosEmit hosEven
    rw [flatten_succ_eq_foldl]
    exact ⟨segE, segO, hpair, hseg, hEven⟩

/-- `Branch5RootOrderFact` for the actual generated rib: roots and even-depth
entries appear in `rib.order` at positions increasing with their entry index.
The pairwise order comes from `flatten_order`; root entries are even by
`generated_root_depth`. -/
theorem branch5_root_order (ns : List Tree.Node) (cause k : Nat)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0) :
    Branch5RootOrderFact ns cause k := by
  obtain ⟨segE, segO, hpair, _hseg, hEven⟩ :=
    flatten_order ns (upper k) 64 (children ns cause) (-1) 2 [] []
      (Or.inl rfl)
      (by intro i x hlook; rw [List.getElem?_nil] at hlook; simp at hlook)
      trivial
  simp only [List.nil_append] at hEven
  have hE : (generatedRib ns (cause, k)).entries = [] ++ segE :=
    (congrArg Prod.fst (generated_rib_fields ns cause k).2.2.1).trans
      (congrArg Prod.fst hpair)
  have hO : (generatedRib ns (cause, k)).order = [] ++ segO :=
    (congrArg Prod.snd (generated_rib_fields ns cause k).2.2.1).trans
      (congrArg Prod.snd hpair)
  intro a b ae be pa pb ha haRoot hb hbEven hab hfa hfb
  have haE : segE[a]? = some ae := by
    simpa only [hE, List.nil_append] using ha
  have hbE : segE[b]? = some be := by
    simpa only [hE, List.nil_append] using hb
  have haEven : ae.depth % 2 = 0 := by
    have hmem : (ae, a) ∈ (generatedRib ns (cause, k)).entries.zipIdx :=
      List.mem_zipIdx_iff_getElem?.mpr ha
    have hd := generated_root_depth ns cause k hlink hcause ae a hmem haRoot
    omega
  have hpaLook : segO[pa.2]? = some a := by
    have hm := List.mem_of_find?_eq_some hfa
    have hg := List.mem_zipIdx_iff_getElem?.mp hm
    have h1 : pa.1 = a := by simpa using List.find?_some hfa
    rw [h1] at hg
    simpa only [hO, List.nil_append] using hg
  have hpbLook : segO[pb.2]? = some b := by
    have hm := List.mem_of_find?_eq_some hfb
    have hg := List.mem_zipIdx_iff_getElem?.mp hm
    have h1 : pb.1 = b := by simpa using List.find?_some hfb
    rw [h1] at hg
    simpa only [hO, List.nil_append] using hg
  rcases Nat.lt_or_ge pa.2 pb.2 with hlt | hge
  · exact hlt
  · exfalso
    rcases Nat.lt_or_ge pb.2 pa.2 with hb_lt | hb_ge
    · have hcontra := evenBefore_of_pos hEven hpbLook hpaLook hb_lt hbE hbEven haE haEven
      omega
    · have hpos : pb.2 = pa.2 := by omega
      rw [hpos] at hpbLook
      have hab' : a = b := Option.some.inj (hpaLook.symm.trans hpbLook)
      omega

/-- The corrected branch-5 classification with both flatten-order facts
derived: the same statement as `hard_b_branch5_placement_block` with the
`horder` and `hcontig` hypotheses replaced by their proofs. -/
theorem hard_b_branch5_placement_block' (ns : List Tree.Node) (cause k : Nat)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (child j : Entry) (childIdx jIdx : Nat)
    (hchild : (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hj : (j, jIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hodd : child.depth % 2 ≠ 0)
    (hjlt : jIdx < childIdx)
    (hpar : child.parent ≠ (jIdx : Int))
    (hsib : j.parent ≠ child.parent) :
    HardBBranch5PlacementBlock ns cause k (child.parent).toNat childIdx jIdx j :=
  hard_b_branch5_placement_block ns cause k hlink hcause child j childIdx jIdx
    hchild hj hodd hjlt hpar hsib (branch5_root_order ns cause k hlink hcause)
    (branch5_block_contiguity ns cause k)

end Elegant.Ishikawa

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
  simpa only [List.nil_append] using hres

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

end Elegant.Ishikawa

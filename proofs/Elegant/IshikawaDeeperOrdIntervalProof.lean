import Elegant.IshikawaDeeperEarlierProof

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-! ### Residual `HardBDeeperOrdInterval`

The generated rib's `entries`/`order` pair is produced by `flatten`, a
depth-first walk that appends every entry index to `order` exactly once:
before its own subtree walk for an even-depth entry, after it for an
odd-depth entry.  This module proves the subtree order-interval fact for a
single call of that walk: if an even entry `a` parents `d` and the order
position of `j` lies between the positions of `a` and `d`, then `j` is `a`
itself or an indexed descendant of `a`.

The proof mirrors the fold inductions used in `IshikawaDeeperEarlierProof`
and `IshikawaHardBBranch5Facts` (their lemmas are private and cannot be
imported), strengthened with the clause bundle `OrdClauses`: slot
bijectivity, parent-back, frame coverage, parent bounds, frame-slot-top,
and the window clause itself. -/

/-! ### Small list lookup lemmas -/

private theorem ordPrefixGet {α : Type} (a b : List α) (h : a <+: b) (i : Nat) (v : α)
    (hi : a[i]? = some v) : b[i]? = some v := by
  rcases h with ⟨t, rfl⟩
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1).trans hi

private theorem ordPrefixGetBack {α : Type} (a b : List α) (h : a <+: b) (i : Nat)
    (hi : i < a.length) : b[i]? = a[i]? := by
  rcases h with ⟨t, rfl⟩
  exact List.getElem?_append_left hi

private theorem ordNoDupPosInj {α : Type} (l : List α) (hd : l.Nodup) :
    ∀ (p q : Nat) (x : α), l[p]? = some x → l[q]? = some x → p = q := by
  intro p q x hp hq
  have hp' := (List.getElem?_eq_some_iff.mp hp).1
  have hq' := (List.getElem?_eq_some_iff.mp hq).1
  have h : l[p]? = l[q]? := by rw [hp, hq]
  exact (List.Nodup.getElem?_inj hp' hd).mp h

private theorem ordAppendGetCases {α : Type} (xs : List α) (v : α) (i : Nat) (out : α)
    (h : (xs ++ [v])[i]? = some out) :
    xs[i]? = some out ∨ i = xs.length ∧ out = v := by
  by_cases hi : i < xs.length
  · exact Or.inl (by rw [List.getElem?_append_left hi] at h; exact h)
  · rw [List.getElem?_append_right (by omega), List.getElem?_singleton] at h
    split at h
    · exact Or.inr ⟨by omega, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
/-- Shifting an ancestor chain from a list to a prefix-extension of it. -/
private theorem ordRestrictAncestor (a b : List Entry) (hp : a <+: b)
    (hb : ∀ (i : Nat) (e : Entry), b[i]? = some e →
      e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        b[p]? = some pe)
    {i j : Nat} (h : IndexedAncestor a i j) (hj : j < a.length) :
    IndexedAncestor b i j := by
  revert hj
  induction h with
  | edge j e he hpar =>
    intro hj
    refine IndexedAncestor.edge i j e ?_ hpar
    exact ordPrefixGet a b hp j e he
  | @tail mid j him e he hpar ih =>
    intro hj
    have hmid : mid < j := by
      rcases hb j e (ordPrefixGet a b hp j e he) with hr | ⟨p, pe, hpe, hplt, _⟩
      · rw [hr] at hpar
        exact absurd hpar (by omega)
      · have hpm : p = mid := by
          have h := hpe.symm.trans hpar
          omega
        omega
    exact IndexedAncestor.tail (ih (by omega)) e
      (ordPrefixGet a b hp j e he) hpar

/-- Reading a `zipIdx.find?` hit back as an order lookup. -/
private theorem ordFoundSlot (O : List Nat) (idx : Nat) (position : Nat × Nat)
    (h : O.zipIdx.find? (fun v => v.1 == idx) = some position) :
    O[position.2]? = some idx := by
  have hm := List.mem_of_find?_eq_some h
  have he := List.mem_zipIdx_iff_getElem?.mp hm
  have hi : position.1 = idx := by simpa using List.find?_some h
  simpa only [hi] using he

/-! ### The segment shape of one flatten call -/

private def ordStep (ns : List Tree.Node) (up : Bool) (fuel : Nat)
    (par : Int) (depth : Nat) (st : List Entry × List Nat) (node : Nat) :
    List Entry × List Nat :=
  let idx := st.1.length
  let es := st.1 ++ [(⟨node, par, depth⟩ : Entry)]
  let os := if depth % 2 == 0 then st.2 ++ [idx] else st.2
  let res := flatten ns up fuel (children ns node) (idx : Int) (depth + 1) es os
  (res.1, if depth % 2 == 0 then res.2 else res.2 ++ [idx])

private theorem ordFlattenSuccFold (ns : List Tree.Node) (up : Bool) (fuel : Nat)
    (ids : List Nat) (par : Int) (depth : Nat) (es : List Entry) (os : List Nat) :
    flatten ns up (fuel + 1) ids par depth es os =
      (if up then ids.reverse else ids).foldl (ordStep ns up fuel par depth) (es, os) := by
  rfl
private theorem flattenSegBound (ns : List Tree.Node) (up : Bool) (fuel : Nat) :
    ∀ (ids : List Nat) (par : Int) (depth : Nat) (es : List Entry) (os : List Nat),
      ∃ segE segO,
        flatten ns up fuel ids par depth es os = (es ++ segE, os ++ segO) ∧
        ∀ w ∈ segO, es.length ≤ w ∧ w < (es ++ segE).length := by
  induction fuel with
  | zero =>
    intro ids par depth es os
    refine ⟨[], [], by simp [flatten], ?_⟩
    intro w hw
    cases hw
  | succ fuel ih =>
    intro ids par depth es os
    have inner : ∀ (ls : List Nat) (st : List Entry × List Nat),
        ∃ segE segO,
          ls.foldl (ordStep ns up fuel par depth) st = (st.1 ++ segE, st.2 ++ segO) ∧
          ∀ w ∈ segO, st.1.length ≤ w ∧ w < (st.1 ++ segE).length := by
      intro ls
      induction ls with
      | nil =>
        intro st
        exact ⟨[], [], by simp, by intro w hw; cases hw⟩
      | cons node rest ihrest =>
        intro st
        obtain ⟨dE, dO, hdPair, hdB⟩ :=
          ih (children ns node) (st.1.length : Int) (depth + 1)
            (st.1 ++ [(⟨node, par, depth⟩ : Entry)])
            (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2)
        have hE : (flatten ns up fuel (children ns node) (st.1.length : Int)
            (depth + 1) (st.1 ++ [(⟨node, par, depth⟩ : Entry)])
            (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2)).1
            = (st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE := congrArg Prod.fst hdPair
        have hO : (flatten ns up fuel (children ns node) (st.1.length : Int)
            (depth + 1) (st.1 ++ [(⟨node, par, depth⟩ : Entry)])
            (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2)).2
            = (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2) ++ dO :=
          congrArg Prod.snd hdPair
        have hstep1 : (ordStep ns up fuel par depth st node).1
            = (st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE := by
          show (flatten ns up fuel (children ns node) (st.1.length : Int) (depth + 1)
            (st.1 ++ [(⟨node, par, depth⟩ : Entry)])
            (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2)).1 = _
          exact congrArg Prod.fst hdPair
        have hstep2 : (ordStep ns up fuel par depth st node).2
            = if depth % 2 == 0 then
                ((if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2) ++ dO)
              else ((if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2) ++ dO) ++
                [st.1.length] := by
          show (if depth % 2 == 0 then
              (flatten ns up fuel (children ns node) (st.1.length : Int) (depth + 1)
                (st.1 ++ [(⟨node, par, depth⟩ : Entry)])
                (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2)).2
            else
              (flatten ns up fuel (children ns node) (st.1.length : Int) (depth + 1)
                (st.1 ++ [(⟨node, par, depth⟩ : Entry)])
                (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2)).2 ++
                [st.1.length]) = _
          rw [hO]
        obtain ⟨segE, segO, hsegPair, hsegB⟩ := ihrest (ordStep ns up fuel par depth st node)
        have hlenPre : (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length
            = st.1.length + 1 := by simp
        have hlenA : ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE).length
            = st.1.length + 1 + dE.length := by
          simp [List.length_append]
          omega
        have hlenT : (st.1 ++ ((⟨node, par, depth⟩ : Entry) :: (dE ++ segE))).length
            = st.1.length + 1 + dE.length + segE.length := by
          simp [List.length_append]
          omega
        have hlenS : (((st.1 ++ [(⟨node, par, depth⟩ : Entry)]) ++ dE) ++ segE).length
            = st.1.length + 1 + dE.length + segE.length := by
          simp [List.length_append]
          omega
        have hstepLen : (ordStep ns up fuel par depth st node).1.length
            = st.1.length + 1 + dE.length := by
          rw [hstep1, hlenA]
        by_cases hd : depth % 2 = 0
        · have h2 : (ordStep ns up fuel par depth st node).2
              = st.2 ++ ([st.1.length] ++ dO) := by
            rw [hstep2]
            simp [hd, List.append_assoc]
          refine ⟨⟨node, par, depth⟩ :: (dE ++ segE),
              ([st.1.length] ++ dO) ++ segO, ?_, ?_⟩
          · rw [List.foldl_cons, hsegPair]
            apply Prod.ext
            · rw [hstep1]
              simp [List.append_assoc]
            · rw [h2]
              simp [List.append_assoc]
          · intro w hw
            rw [List.mem_append] at hw
            rcases hw with hw | hw
            · rcases List.mem_append.mp hw with hw | hw
              · rw [List.mem_singleton] at hw
                subst w
                constructor
                · omega
                · rw [hlenT]; omega
              · obtain ⟨h1, h2⟩ := hdB w hw
                rw [hlenPre] at h1
                rw [hlenA] at h2
                constructor
                · omega
                · rw [hlenT]; omega
            · obtain ⟨h1, h2⟩ := hsegB w hw
              rw [hstepLen] at h1
              rw [hstep1] at h2
              rw [hlenS] at h2
              constructor
              · omega
              · rw [hlenT]; omega
        · have h2 : (ordStep ns up fuel par depth st node).2
              = (st.2 ++ dO) ++ [st.1.length] := by
            rw [hstep2]
            simp [hd, List.append_assoc]
          refine ⟨⟨node, par, depth⟩ :: (dE ++ segE),
              (dO ++ [st.1.length]) ++ segO, ?_, ?_⟩
          · rw [List.foldl_cons, hsegPair]
            apply Prod.ext
            · rw [hstep1]
              simp [List.append_assoc]
            · rw [h2]
              simp [List.append_assoc]
          · intro w hw
            rw [List.mem_append] at hw
            rcases hw with hw | hw
            · rcases List.mem_append.mp hw with hw | hw
              · obtain ⟨h1, h2⟩ := hdB w hw
                rw [hlenPre] at h1
                rw [hlenA] at h2
                constructor
                · omega
                · rw [hlenT]; omega
              · rw [List.mem_singleton] at hw
                subst w
                constructor
                · omega
                · rw [hlenT]; omega
            · obtain ⟨h1, h2⟩ := hsegB w hw
              rw [hstepLen] at h1
              rw [hstep1] at h2
              rw [hlenS] at h2
              constructor
              · omega
              · rw [hlenT]; omega
    rw [ordFlattenSuccFold]
    exact inner (if up then ids.reverse else ids) (es, os)

private def ParBefore (E : List Entry) : Prop :=
  ∀ (i : Nat) (e : Entry), E[i]? = some e →
    e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
      E[p]? = some pe

private structure OrdClauses (E : List Entry) (O : List Nat) (par : Int)
    (startE : Nat) : Prop where
  bounds : ∀ w ∈ O, w < E.length
  noDup : O.Nodup
  cov : ∀ (i : Nat), i < E.length →
    i ∈ O ∨ (0 ≤ par ∧ (par = (i : Int) ∨ IndexedAncestor E i par.toNat) ∧
      ∃ pe, E[i]? = some pe ∧ pe.depth % 2 ≠ 0 ∧ i ∉ O)
  before : ParBefore E
  coverN : par = -1 → ∀ (x : Nat) (xe : Entry), startE ≤ x → E[x]? = some xe →
    xe.parent = -1 ∨ ∃ (h : Nat) (he : Entry), startE ≤ h ∧ E[h]? = some he ∧
      he.parent = -1 ∧ IndexedAncestor E h x
  coverP : ∀ (p : Nat), par = (p : Int) → ∀ (x : Nat) (xe : Entry), startE ≤ x →
    E[x]? = some xe → xe.parent = (p : Int) ∨ IndexedAncestor E p x
  pbound : ∀ (x : Nat) (xe : Entry), startE ≤ x → E[x]? = some xe →
    xe.parent = -1 ∨ xe.parent = par ∨
      (0 ≤ xe.parent ∧ startE ≤ xe.parent.toNat ∧ xe.parent.toNat < x)
  win : ∀ (a d x : Nat) (ae de xe : Entry) (pa px pd : Nat),
    E[a]? = some ae → E[d]? = some de → E[x]? = some xe →
    de.parent = (a : Int) → ae.depth % 2 = 0 →
    O[pa]? = some a → O[px]? = some x → O[pd]? = some d →
    pa ≤ px → px ≤ pd → x = a ∨ IndexedAncestor E a x

private theorem ordLastPos (O : List Nat) (v : Nat) (h : O.getLast? = some v) :
    O[O.length - 1]? = some v := by
  rwa [List.getLast?_eq_getElem?] at h


private theorem ordAncTrans {E : List Entry} {a b c : Nat}
    (hab : IndexedAncestor E a b) (hbc : IndexedAncestor E b c) :
    IndexedAncestor E a c := by
  induction hbc with
  | edge c e he hp =>
    exact IndexedAncestor.tail hab e he hp
  | tail hbc' e he hp ih =>
    exact IndexedAncestor.tail (ih) e he hp

private theorem ordAncEdge {E : List Entry} {a c : Nat} (e : Entry)
    (he : E[c]? = some e) (hp : e.parent = (a : Int)) :
    IndexedAncestor E a c :=
  IndexedAncestor.edge a c e he hp

private theorem ordAncLt (E : List Entry) (hb : ParBefore E) {a c : Nat}
    (h : IndexedAncestor E a c) : a < c := by
  induction h with
  | edge c e he hp =>
    rcases hb c e he with hr | ⟨p, hp', hlt⟩
    · omega
    · have heq : p = a := by omega
      omega
  | tail hab e he hp ih =>
    rcases hb _ e he with hr | ⟨p, hp', hlt⟩ <;> omega

private theorem ordAncPrefix {a b : List Entry} (hp : a <+: b)
    (hb : ParBefore b) {i j : Nat} (h : IndexedAncestor b i j)
    (hj : j < a.length) : IndexedAncestor a i j := by
  revert hj
  induction h with
  | edge j e he hpar =>
    intro hj
    exact IndexedAncestor.edge i j e
      (by rw [ordPrefixGetBack a b hp j hj] at he; exact he) hpar
  | @tail mid j him e he hpar ih =>
    intro hj
    have hmid : mid < j := by
      have hlt := ordAncLt b hb (IndexedAncestor.edge mid j e he hpar)
      exact hlt
    exact IndexedAncestor.tail (ih (by omega)) e
      (by rw [ordPrefixGetBack a b hp j hj] at he; exact he) hpar


/-- Residual R-flatten-clauses: the clause bundle preserved by one executed
`flatten` run. General over its arguments; the executed call is pinned at the
use site in `hardBDeeperOrdInterval` (fuel 64, the rib's child ids, the root
frame `-1`, depth 2, and the empty entry/order seed). Probed true: the bundle
is the fold induction invariant of `flatten` (each `ordStep` preserves it; the
sub-call discharges the entry clauses because every stored index is below the
segment start). Strictly simpler than the goal: a general statement about
`flatten`, no rib, no find? positions, no ancestor conclusion. -/
def FlattenClauses (ns : List Tree.Node) (up : Bool) : Prop :=
  ∀ (fuel : Nat) (ids : List Nat) (par : Int) (depth startE : Nat)
    (es : List Entry) (os : List Nat),
    startE ≤ es.length →
    (par = -1 ∨ ∃ pe, es[par.toNat]? = some pe) →
    (∀ pe, es[par.toNat]? = some pe → pe.depth % 2 = 0 →
      os.getLast? = some par.toNat) →
    (par = -1 ∨ par.toNat < startE) →
    OrdClauses es os par startE →
    ∃ segE segO,
      flatten ns up fuel ids par depth es os = (es ++ segE, os ++ segO) ∧
      (∀ w ∈ segO, startE ≤ w) ∧
      OrdClauses (es ++ segE) (os ++ segO) par startE

private theorem ordClausesNil : OrdClauses [] [] (-1) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw; simp at hw
  · exact List.nodup_nil
  · intro i hi; simp at hi
  · intro i e hi; simp at hi
  · intro _ x _ _ hxe; simp at hxe
  · intro p hp; omega
  · intro x _ _ hxe; simp at hxe
  · intro a d x ae de xe pa px pd hae hed hx hpax hpxp hppd hle1 hle2
    simp at hae hed hx

theorem hardBDeeperOrdInterval (ns : List Tree.Node) (cause k : Nat)
    (hcore : FlattenClauses ns (upper k)) :
    HardBDeeperOrdInterval ns cause k := by
  intro a d j ae de J pa pd pj hae hed hej hpar heven hpa hpd hpj h1 h2
  have hfields := (generated_rib_fields ns cause k).2.2.1
  have he : (generatedRib ns (cause, k)).entries =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1 :=
    congrArg Prod.fst hfields
  have ho : (generatedRib ns (cause, k)).order =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).2 :=
    congrArg Prod.snd hfields
  obtain ⟨segE, segO, hflat, _hsegB, hcl⟩ :=
    hcore 64 (children ns cause) (-1) 2 0 [] [] (by simp) (Or.inl rfl)
      (by intro pe h; simp at h) (Or.inl rfl) ordClausesNil
  have hfst : (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1 = segE := by
    have := congrArg Prod.fst hflat
    simpa using this
  have hsnd : (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).2 = segO := by
    have := congrArg Prod.snd hflat
    simpa using this
  have heE : (generatedRib ns (cause, k)).entries = segE := by rw [he, hfst]
  have hoO : (generatedRib ns (cause, k)).order = segO := by rw [ho, hsnd]
  have hae' : segE[a]? = some ae := by rw [← heE]; exact hae
  have hed' : segE[d]? = some de := by rw [← heE]; exact hed
  have hej' : segE[j]? = some J := by rw [← heE]; exact hej
  have hpa' : segO[pa.2]? = some a := by
    have := ordFoundSlot _ a pa hpa
    rwa [hoO] at this
  have hpd' : segO[pd.2]? = some d := by
    have := ordFoundSlot _ d pd hpd
    rwa [hoO] at this
  have hpj' : segO[pj.2]? = some j := by
    have := ordFoundSlot _ j pj hpj
    rwa [hoO] at this
  have hwin := hcl.win a d j ae de J pa.2 pj.2 pd.2 hae' hed' hej' hpar heven
    hpa' hpj' hpd' h1 h2
  rcases hwin with h | h
  · exact Or.inl h
  · apply Or.inr
    rw [heE]
    simpa using h

end Elegant.Ishikawa

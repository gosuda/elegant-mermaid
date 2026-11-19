import Elegant.IshikawaDeeperOrdIntervalProof

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-! Mirror of the private `OrdClauses` bundle from
`Elegant.IshikawaDeeperOrdIntervalProof` (whose constructor is module-private,
so the bundle cannot be rebuilt from this module). The eight clause formulas
are copied verbatim; `postPar` is the extra order fact the window clause
needs: every order entry at or after the frame's own slot is the frame itself
or a descendant of it. -/

structure FlatInv (E : List Entry) (O : List Nat) (par : Int)
    (startE : Nat) : Prop where
  bounds : ∀ w ∈ O, w < E.length
  noDup : O.Nodup
  cov : ∀ (i : Nat), i < E.length →
    i ∈ O ∨ (0 ≤ par ∧ (par = (i : Int) ∨ IndexedAncestor E i par.toNat) ∧
      ∃ pe, E[i]? = some pe ∧ pe.depth % 2 ≠ 0 ∧ i ∉ O)
  before : ∀ (i : Nat) (e : Entry), E[i]? = some e →
    e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
      E[p]? = some pe
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
  postPar : par = -1 ∨ ∀ (pa px : Nat) (v : Nat),
    O[pa]? = some par.toNat → O[px]? = some v → pa ≤ px →
    v = par.toNat ∨ IndexedAncestor E par.toNat v

/-! ### List lookup utilities -/

theorem flatAppGetCases {α : Type} (xs : List α) (v : α) (i : Nat) (out : α)
    (h : (xs ++ [v])[i]? = some out) :
    xs[i]? = some out ∨ i = xs.length ∧ out = v := by
  by_cases hi : i < xs.length
  · exact Or.inl (by rw [List.getElem?_append_left hi] at h; exact h)
  · rw [List.getElem?_append_right (by omega), List.getElem?_singleton] at h
    split at h
    · exact Or.inr ⟨by omega, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)

theorem flatLookupOfLt (l : List Entry) (i : Nat) (hi : i < l.length) :
    ∃ out, l[i]? = some out := by
  match hm : l[i]? with
  | some out => exact ⟨out, rfl⟩
  | none =>
    exfalso
    rw [List.getElem?_eq_none_iff] at hm
    omega

theorem flatPrefixGet {α : Type} (a b : List α) (h : a <+: b) (i : Nat) (v : α)
    (hi : a[i]? = some v) : b[i]? = some v := by
  rcases h with ⟨t, rfl⟩
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1).trans hi

theorem flatPrefixGetBack {α : Type} (a b : List α) (h : a <+: b) (i : Nat)
    (hi : i < a.length) : b[i]? = a[i]? := by
  rcases h with ⟨t, rfl⟩
  exact List.getElem?_append_left hi

theorem flatNodupPosInj (l : List Nat) (hd : l.Nodup) :
    ∀ (p q : Nat) (x : Nat), l[p]? = some x → l[q]? = some x → p = q := by
  intro p q x hp hq
  have hp' := (List.getElem?_eq_some_iff.mp hp).1
  have hq' := (List.getElem?_eq_some_iff.mp hq).1
  have h : l[p]? = l[q]? := by rw [hp, hq]
  exact (List.Nodup.getElem?_inj hp' hd).mp h

theorem flatGetLastAppendSingle (l : List Nat) (a : Nat) :
    (l ++ [a]).getLast? = some a := by
  rw [List.getLast?_eq_getElem?]
  have hlen : (l ++ [a]).length - 1 = l.length := by simp
  rw [hlen, List.getElem?_append_right (by omega)]
  have hz : l.length - l.length = 0 := by omega
  rw [hz]
  rfl

private theorem nodupAppendAux (a : Nat) : ∀ (l : List Nat),
    List.Pairwise (fun x y => x ≠ y) l → (∀ x ∈ l, x ≠ a) →
    List.Pairwise (fun x y => x ≠ y) (l ++ [a]) := by
  intro l
  induction l with
  | nil =>
    intro _ _
    exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | cons h t ih =>
    intro hpw hne
    cases hpw with
    | cons hhead htail =>
      have ih' := ih htail (fun x hx heq =>
        hne x (List.mem_cons_of_mem h hx) heq)
      show List.Pairwise (fun x y => x ≠ y) (h :: (t ++ [a]))
      exact List.Pairwise.cons (by
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hhead y hy
        · rw [List.mem_singleton] at hy
          subst y
          exact hne h (by simp : h ∈ h :: t)) ih'

theorem flatNodupAppendSingle (l : List Nat) (a : Nat)
    (hd : l.Nodup) (hm : a ∉ l) : (l ++ [a]).Nodup := by
  have hne : ∀ x ∈ l, x ≠ a := by
    intro x hx heq
    apply hm
    rw [← heq]
    exact hx
  exact nodupAppendAux a l hd hne
theorem flatFoundSlot (O : List Nat) (idx : Nat) (position : Nat × Nat)
    (h : O.zipIdx.find? (fun v => v.1 == idx) = some position) :
    O[position.2]? = some idx := by
  have hm := List.mem_of_find?_eq_some h
  have he := List.mem_zipIdx_iff_getElem?.mp hm
  have hi : position.1 = idx := by simpa using List.find?_some h
  simpa only [hi] using he

/-! ### Ancestor utilities -/

theorem flatAncTrans {E : List Entry} {a b c : Nat}
    (hab : IndexedAncestor E a b) (hbc : IndexedAncestor E b c) :
    IndexedAncestor E a c := by
  induction hbc with
  | edge c e he hp =>
    exact IndexedAncestor.tail hab e he hp
  | tail hbc' e he hp ih =>
    exact IndexedAncestor.tail (ih) e he hp

theorem flatAncEdge {E : List Entry} {a c : Nat} (e : Entry)
    (he : E[c]? = some e) (hp : e.parent = (a : Int)) :
    IndexedAncestor E a c :=
  IndexedAncestor.edge a c e he hp

theorem flatAncLt (E : List Entry) (hb : ∀ (i : Nat) (e : Entry),
    E[i]? = some e → e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry),
      e.parent = (p : Int) ∧ p < i ∧ E[p]? = some pe)
    {a c : Nat} (h : IndexedAncestor E a c) : a < c := by
  induction h with
  | edge c e he hp =>
    rcases hb c e he with hr | ⟨p, hp', hlt⟩
    · omega
    · have heq : p = a := by omega
      omega
  | tail hab e he hp ih =>
    rcases hb _ e he with hr | ⟨p, hp', hlt⟩ <;> omega

theorem flatAncRestrict {a b : List Entry} (hp : a <+: b)
    (hb : ∀ (i : Nat) (e : Entry), b[i]? = some e →
      e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        b[p]? = some pe)
    {i j : Nat} (h : IndexedAncestor b i j) (hj : j < a.length) :
    IndexedAncestor a i j := by
  revert hj
  induction h with
  | edge j e he hpar =>
    intro hj
    exact IndexedAncestor.edge i j e
      (by rw [flatPrefixGetBack a b hp j hj] at he; exact he) hpar
  | @tail mid j him e he hpar ih =>
    intro hj
    have hmid : mid < j := by
      have hlt := flatAncLt b hb (IndexedAncestor.edge mid j e he hpar)
      exact hlt
    exact IndexedAncestor.tail (ih (by omega)) e
      (by rw [flatPrefixGetBack a b hp j hj] at he; exact he) hpar

theorem flatAncFwd {a b : List Entry} (hp : a <+: b)
    {i j : Nat} (h : IndexedAncestor a i j) : IndexedAncestor b i j := by
  induction h with
  | edge j e he hpar =>
    exact IndexedAncestor.edge i j e (flatPrefixGet a b hp j e he) hpar
  | tail hab e he hpar _ih =>
    exact IndexedAncestor.tail _ih e (flatPrefixGet a b hp _ e he) hpar

/-! ### One-step scaffolding -/

private def fstep (ns : List Tree.Node) (up : Bool) (fuel : Nat)
    (par : Int) (depth : Nat) (st : List Entry × List Nat) (node : Nat) :
    List Entry × List Nat :=
  let idx := st.1.length
  let es := st.1 ++ [(⟨node, par, depth⟩ : Entry)]
  let os := if depth % 2 == 0 then st.2 ++ [idx] else st.2
  let res := flatten ns up fuel (children ns node) (idx : Int) (depth + 1) es os
  (res.1, if depth % 2 == 0 then res.2 else res.2 ++ [idx])

private theorem flatSuccFold (ns : List Tree.Node) (up : Bool) (fuel : Nat)
    (ids : List Nat) (par : Int) (depth : Nat) (es : List Entry)
    (os : List Nat) :
    flatten ns up (Nat.succ fuel) ids par depth es os =
      (if up then ids.reverse else ids).foldl
        (fstep ns up fuel par depth) (es, os) := rfl

theorem flatInvNil : FlatInv [] [] (-1) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw; simp at hw
  · exact List.nodup_nil
  · intro i hi; simp at hi
  · intro i e hi; simp at hi
  · intro _ x _ _ hxe; simp at hxe
  · intro p hp; omega
  · intro x _ _ hxe; simp at hxe
  · intro a d x ae de xe pa px pd hae hed hx hpax hpxp hppd hle1 hle2
    simp at hae
  · exact Or.inl rfl

theorem boundsEntry (E : List Entry) (O : List Nat) (node : Nat) (par : Int)
    (depth : Nat) (hb : ∀ w ∈ O, w < E.length) :
    ∀ w ∈ O, w < (E ++ [(⟨node, par, depth⟩ : Entry)]).length := by
  intro w hw
  have h := hb w hw
  simp only [List.length_append, List.length_singleton]
  omega

theorem boundsSlot (E : List Entry) (O : List Nat) (idx : Nat)
    (hb : ∀ w ∈ O, w < E.length) (hi : idx < E.length) :
    ∀ w ∈ O ++ [idx], w < E.length := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact hb w hw
  · rw [List.mem_singleton] at hw
    rw [hw]
    exact hi

theorem noDupPreSlot (E : List Entry) (O : List Nat)
    (hn : O.Nodup) (hb : ∀ w ∈ O, w < E.length) :
    (O ++ [E.length]).Nodup :=
  flatNodupAppendSingle O E.length hn (by intro hm; have h := hb _ hm; omega)

theorem beforeEntry (E : List Entry) (node : Nat) (par : Int) (depth : Nat)
    (hb : ∀ (i : Nat) (e : Entry), E[i]? = some e →
      e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        E[p]? = some pe)
    (hnn : par = -1 ∨ 0 ≤ par)
    (hfr : par = -1 ∨ ∃ pe, E[par.toNat]? = some pe) :
    ∀ (i : Nat) (e : Entry), (E ++ [(⟨node, par, depth⟩ : Entry)])[i]? = some e →
      e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        (E ++ [(⟨node, par, depth⟩ : Entry)])[p]? = some pe := by
  intro i e hi
  have hpre : E <+: E ++ [(⟨node, par, depth⟩ : Entry)] := ⟨_, rfl⟩
  rcases flatAppGetCases E _ i e hi with hold | ⟨rfl, rfl⟩
  · rcases hb i e hold with hr | ⟨p, pe, hpe, hplt, hplook⟩
    · exact Or.inl hr
    · exact Or.inr ⟨p, pe, hpe, hplt, flatPrefixGet E _ hpre p pe hplook⟩
  · by_cases hpar : par = -1
    · exact Or.inl hpar
    · have hnn' : 0 ≤ par := by
        rcases hnn with h | h
        · exact absurd h hpar
        · exact h
      have hrt : ((par.toNat : Nat) : Int) = par := by omega
      rcases hfr with hr | ⟨pe, hpe⟩
      · exact absurd hr hpar
      · refine Or.inr ⟨par.toNat, pe, by rw [hrt], ?_, ?_⟩
        · exact (List.getElem?_eq_some_iff.mp hpe).1
        · exact flatPrefixGet E _ hpre par.toNat pe hpe

theorem pboundEntry (E : List Entry) (node : Nat) (par : Int) (depth startE : Nat)
    (hpb : ∀ (x : Nat) (xe : Entry), startE ≤ x → E[x]? = some xe →
      xe.parent = -1 ∨ xe.parent = par ∨
        (0 ≤ xe.parent ∧ startE ≤ xe.parent.toNat ∧ xe.parent.toNat < x)) :
    ∀ (x : Nat) (xe : Entry), startE ≤ x →
      (E ++ [(⟨node, par, depth⟩ : Entry)])[x]? = some xe →
      xe.parent = -1 ∨ xe.parent = par ∨
        (0 ≤ xe.parent ∧ startE ≤ xe.parent.toNat ∧ xe.parent.toNat < x) := by
  intro x xe hx hlook
  rcases flatAppGetCases E _ x xe hlook with hold | ⟨rfl, rfl⟩
  · exact hpb x xe hx hold
  · exact Or.inr (Or.inl rfl)

theorem covEntryOdd (E : List Entry) (O : List Nat) (node : Nat) (par : Int)
    (depth : Nat)
    (hc : ∀ (i : Nat), i < E.length →
      i ∈ O ∨ (0 ≤ par ∧ (par = (i : Int) ∨ IndexedAncestor E i par.toNat) ∧
        ∃ pe, E[i]? = some pe ∧ pe.depth % 2 ≠ 0 ∧ i ∉ O))
    (hb : ∀ w ∈ O, w < E.length)
    (hodd : depth % 2 ≠ 0) :
    ∀ (i : Nat), i < (E ++ [(⟨node, par, depth⟩ : Entry)]).length →
      i ∈ O ∨ (0 ≤ ((E.length : Nat) : Int) ∧
        ((((E.length : Nat) : Int) = (i : Int)) ∨
          IndexedAncestor (E ++ [(⟨node, par, depth⟩ : Entry)]) i E.length) ∧
        ∃ pe, (E ++ [(⟨node, par, depth⟩ : Entry)])[i]? = some pe ∧
          pe.depth % 2 ≠ 0 ∧ i ∉ O) := by
  intro i hi
  have hpre : E <+: E ++ [(⟨node, par, depth⟩ : Entry)] := ⟨_, rfl⟩
  have hlook : (E ++ [(⟨node, par, depth⟩ : Entry)])[E.length]?
      = some (⟨node, par, depth⟩ : Entry) := by
    rw [List.getElem?_append_right (by simp)]
    have hz : E.length - E.length = 0 := by omega
    rw [hz]
    rfl
  have hfresh : E.length ∉ O := by
    intro hm
    have h := hb _ hm
    omega
  obtain ⟨out, hout2⟩ := flatLookupOfLt _ i hi
  rcases flatAppGetCases E _ i out hout2 with hold | ⟨rfl, rfl⟩
  · have hilt : i < E.length := (List.getElem?_eq_some_iff.mp hold).1
    rcases hc i hilt with hl | ⟨h0, hmid, pe, hpe, hoddpe, hni⟩
    · exact Or.inl hl
    · refine Or.inr ⟨by omega, ?_, pe, flatPrefixGet E _ hpre i pe hpe,
        hoddpe, hni⟩
      have h1 : ((par.toNat : Nat) : Int) = par := by omega
      rcases hmid with hpar | hanc
      · have hpto : par.toNat = i := by omega
        rw [← hpto]
        exact Or.inr (flatAncEdge _ hlook (by rw [h1]))
      · exact Or.inr (IndexedAncestor.tail (flatAncFwd hpre hanc) _ hlook
        (by rw [h1]))
  · refine Or.inr ⟨by omega, Or.inl rfl, _, hlook, hodd, hfresh⟩

theorem covEntryEven (E : List Entry) (O : List Nat) (node : Nat) (par : Int)
    (depth : Nat)
    (hc : ∀ (i : Nat), i < E.length →
      i ∈ O ∨ (0 ≤ par ∧ (par = (i : Int) ∨ IndexedAncestor E i par.toNat) ∧
        ∃ pe, E[i]? = some pe ∧ pe.depth % 2 ≠ 0 ∧ i ∉ O)) :
    ∀ (i : Nat), i < (E ++ [(⟨node, par, depth⟩ : Entry)]).length →
      i ∈ O ++ [E.length] ∨ (0 ≤ ((E.length : Nat) : Int) ∧
        ((((E.length : Nat) : Int) = (i : Int)) ∨
          IndexedAncestor (E ++ [(⟨node, par, depth⟩ : Entry)]) i E.length) ∧
        ∃ pe, (E ++ [(⟨node, par, depth⟩ : Entry)])[i]? = some pe ∧
          pe.depth % 2 ≠ 0 ∧ i ∉ O ++ [E.length]) := by
  intro i hi
  have hpre : E <+: E ++ [(⟨node, par, depth⟩ : Entry)] := ⟨_, rfl⟩
  have hlook : (E ++ [(⟨node, par, depth⟩ : Entry)])[E.length]?
      = some (⟨node, par, depth⟩ : Entry) := by
    rw [List.getElem?_append_right (by simp)]
    have hz : E.length - E.length = 0 := by omega
    rw [hz]
    rfl
  obtain ⟨out, hout2⟩ := flatLookupOfLt _ i hi
  rcases flatAppGetCases E _ i out hout2 with hold | ⟨rfl, rfl⟩
  · have hilt : i < E.length := (List.getElem?_eq_some_iff.mp hold).1
    rcases hc i hilt with hl | ⟨h0, hmid, pe, hpe, hoddpe, hni⟩
    · exact Or.inl (List.mem_append.mpr (Or.inl hl))
    · refine Or.inr ⟨by omega, ?_, pe, flatPrefixGet E _ hpre i pe hpe,
        hoddpe, ?_⟩
      · have h1 : ((par.toNat : Nat) : Int) = par := by omega
        rcases hmid with hpar | hanc
        · have hpto : par.toNat = i := by omega
          rw [← hpto]
          exact Or.inr (flatAncEdge _ hlook (by rw [h1]))
        · exact Or.inr (IndexedAncestor.tail (flatAncFwd hpre hanc) _ hlook
          (by rw [h1]))
      · intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact absurd hm hni
        · rw [List.mem_singleton] at hm
          omega
  · exact Or.inl (by simp)
theorem covChildEven (E0 : List Entry) (O0 : List Nat) (node : Nat) (par : Int)
    (depth startE : Nat)
    (hin : FlatInv E0 O0 par startE)
    (childE : List Entry) (childO segO : List Nat) (segE : List Entry)
    (hchild : FlatInv childE childO ((E0.length : Nat) : Int)
      ((E0 ++ [(⟨node, par, depth⟩ : Entry)]).length))
    (heE : childE = (E0 ++ [(⟨node, par, depth⟩ : Entry)]) ++ segE)
    (heO : childO = (O0 ++ [E0.length]) ++ segO)
    (hseg : ∀ w ∈ segO, (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ w) :
    ∀ (x : Nat), x < childE.length →
      x ∈ childO ∨ (0 ≤ par ∧ (par = (x : Int) ∨ IndexedAncestor childE x par.toNat) ∧
        ∃ pe, childE[x]? = some pe ∧ pe.depth % 2 ≠ 0 ∧ x ∉ childO) := by
  intro x hxb
  obtain ⟨xe, hlook⟩ := flatLookupOfLt _ x hxb
  have hE1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length = E0.length + 1 := by
    simp
  have hpre01 : E0 <+: childE := by
    refine ⟨[(⟨node, par, depth⟩ : Entry)] ++ segE, ?_⟩
    rw [heE, List.append_assoc]
  have htn : ((((E0.length : Nat) : Int)).toNat) = E0.length := rfl
  by_cases hx0 : x = E0.length
  · subst hx0
    exact Or.inl (by rw [heO]; simp)
  · by_cases hx1 : x < E0.length
    · have hsame : childE[x]? = E0[x]? := flatPrefixGetBack E0 childE hpre01 x hx1
      rw [hsame] at hlook
      rcases hin.cov x hx1 with hl | ⟨h0, hmid, pe, hpe, hoddpe, hni⟩
      · have hmem : x ∈ childO := by
          rw [heO]
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hl)))
        exact Or.inl hmem
      · have heq : pe = xe := Option.some.inj (hpe.symm.trans hlook)
        subst heq
        refine Or.inr ⟨h0, ?_, pe, flatPrefixGet E0 childE hpre01 x pe hpe,
          hoddpe, ?_⟩
        · rcases hmid with hpar | hanc
          · exact Or.inl hpar
          · exact Or.inr (flatAncFwd hpre01 hanc)
        · intro hm
          rw [heO, List.mem_append] at hm
          rcases hm with hm | hm
          · rw [List.mem_append] at hm
            rcases hm with hm | hm
            · exact absurd hm hni
            · rw [List.mem_singleton] at hm
              omega
          · have hle := hseg _ hm
            omega
    · have hxs : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ x := by omega
      rcases hchild.cov x hxb with hl | ⟨h0, hmid, pe, hpe, hoddpe, hni⟩
      · exact Or.inl hl
      · exfalso
        rcases hmid with hpar | hanc
        · omega
        · rw [htn] at hanc
          have hlt := flatAncLt childE hchild.before hanc
          omega

theorem covChildOdd (E0 : List Entry) (O0 : List Nat) (node : Nat) (par : Int)
    (depth startE : Nat)
    (hin : FlatInv E0 O0 par startE)
    (childE : List Entry) (childO segO : List Nat) (segE : List Entry)
    (hchild : FlatInv childE childO ((E0.length : Nat) : Int)
      ((E0 ++ [(⟨node, par, depth⟩ : Entry)]).length))
    (heE : childE = (E0 ++ [(⟨node, par, depth⟩ : Entry)]) ++ segE)
    (heO : childO = O0 ++ segO)
    (hseg : ∀ w ∈ segO, (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ w) :
    ∀ (x : Nat), x < childE.length →
      x ∈ childO ++ [E0.length] ∨
        (0 ≤ par ∧ (par = (x : Int) ∨ IndexedAncestor childE x par.toNat) ∧
        ∃ pe, childE[x]? = some pe ∧ pe.depth % 2 ≠ 0 ∧
          x ∉ childO ++ [E0.length]) := by
  intro x hxb
  obtain ⟨xe, hlook⟩ := flatLookupOfLt _ x hxb
  have hE1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length = E0.length + 1 := by
    simp
  have hpre01 : E0 <+: childE := by
    refine ⟨[(⟨node, par, depth⟩ : Entry)] ++ segE, ?_⟩
    rw [heE, List.append_assoc]
  have htn : ((((E0.length : Nat) : Int)).toNat) = E0.length := rfl
  by_cases hx0 : x = E0.length
  · subst hx0
    exact Or.inl (by simp)
  · by_cases hx1 : x < E0.length
    · have hsame : childE[x]? = E0[x]? := flatPrefixGetBack E0 childE hpre01 x hx1
      rw [hsame] at hlook
      rcases hin.cov x hx1 with hl | ⟨h0, hmid, pe, hpe, hoddpe, hni⟩
      · have hmem : x ∈ childO ++ [E0.length] := by
          rw [heO]
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hl)))
        exact Or.inl hmem
      · have heq : pe = xe := Option.some.inj (hpe.symm.trans hlook)
        subst heq
        refine Or.inr ⟨h0, ?_, pe, flatPrefixGet E0 childE hpre01 x pe hpe,
          hoddpe, ?_⟩
        · rcases hmid with hpar | hanc
          · exact Or.inl hpar
          · exact Or.inr (flatAncFwd hpre01 hanc)
        · intro hm
          rw [List.mem_append] at hm
          rcases hm with hm | hm
          · rw [heO, List.mem_append] at hm
            rcases hm with hm | hm
            · exact absurd hm hni
            · have hle := hseg _ hm
              omega
          · rw [List.mem_singleton] at hm
            omega
    · have hxs : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ x := by omega
      rcases hchild.cov x hxb with hl | ⟨h0, hmid, pe, hpe, hoddpe, hni⟩
      · exact Or.inl (List.mem_append.mpr (Or.inl hl))
      · exfalso
        rcases hmid with hpar | hanc
        · omega
        · rw [htn] at hanc
          have hlt := flatAncLt childE hchild.before hanc
          omega

theorem pboundChild (E0 : List Entry) (O0 : List Nat) (node : Nat) (par : Int)
    (depth startE : Nat)
    (hin : FlatInv E0 O0 par startE)
    (childE : List Entry) (childO : List Nat) (segE : List Entry)
    (hchild : FlatInv childE childO ((E0.length : Nat) : Int)
      ((E0 ++ [(⟨node, par, depth⟩ : Entry)]).length))
    (heE : childE = (E0 ++ [(⟨node, par, depth⟩ : Entry)]) ++ segE)
    (hlen0 : startE ≤ E0.length) :
    ∀ (x : Nat) (xe : Entry), startE ≤ x → childE[x]? = some xe →
      xe.parent = -1 ∨ xe.parent = par ∨
        (0 ≤ xe.parent ∧ startE ≤ xe.parent.toNat ∧ xe.parent.toNat < x) := by
  intro x xe hx hlook
  have hE1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length = E0.length + 1 := by
    simp
  have htn : ((((E0.length : Nat) : Int)).toNat) = E0.length := rfl
  have hlookC := hlook
  rw [heE] at hlook
  by_cases hx1 : x < (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length
  · rw [List.getElem?_append_left hx1] at hlook
    rcases flatAppGetCases E0 _ x xe hlook with hold0 | ⟨rfl, rfl⟩
    · exact hin.pbound x xe hx hold0
    · exact Or.inr (Or.inl rfl)
  · have hxs : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ x := by omega
    rcases hchild.pbound x xe hxs hlookC with hr | hpar | ⟨h0, hs, hlt⟩
    · exact Or.inl hr
    · refine Or.inr (Or.inr ⟨by rw [hpar]; omega, ?_, ?_⟩)
      · rw [hpar, htn]
        exact hlen0
      · rw [hpar, htn]
        omega
    · refine Or.inr (Or.inr ⟨h0, ?_, hlt⟩)
      omega

theorem coverNChild (E0 : List Entry) (O0 : List Nat) (node : Nat) (par : Int)
    (depth startE : Nat)
    (hin : FlatInv E0 O0 par startE)
    (childE : List Entry) (childO : List Nat) (segE : List Entry)
    (hchild : FlatInv childE childO ((E0.length : Nat) : Int)
      ((E0 ++ [(⟨node, par, depth⟩ : Entry)]).length))
    (hpar : par = -1)
    (heE : childE = (E0 ++ [(⟨node, par, depth⟩ : Entry)]) ++ segE)
    (hlen0 : startE ≤ E0.length) :
    ∀ (x : Nat) (xe : Entry), startE ≤ x → childE[x]? = some xe →
      xe.parent = -1 ∨ ∃ (h : Nat) (he : Entry), startE ≤ h ∧
        childE[h]? = some he ∧ he.parent = -1 ∧ IndexedAncestor childE h x := by
  intro x xe hx hlook
  have hlookC := hlook
  rw [heE] at hlook
  have hE1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length = E0.length + 1 := by
    simp
  have hpre01 : E0 <+: childE := by
    refine ⟨[(⟨node, par, depth⟩ : Entry)] ++ segE, ?_⟩
    rw [heE, List.append_assoc]
  have hpre1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)]) <+: childE :=
    ⟨segE, heE.symm⟩
  have h1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)])[E0.length]?
      = some (⟨node, par, depth⟩ : Entry) := by
    rw [List.getElem?_append_right (by simp)]
    have hz : E0.length - E0.length = 0 := by omega
    rw [hz]
    rfl
  have hlooke : childE[E0.length]?
      = some (⟨node, par, depth⟩ : Entry) :=
    flatPrefixGet _ childE hpre1 E0.length _ h1
  by_cases hx1 : x < (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length
  · rw [List.getElem?_append_left hx1] at hlook
    rcases flatAppGetCases E0 _ x xe hlook with hold0 | ⟨rfl, rfl⟩
    · rcases hin.coverN hpar x xe hx hold0 with hr | ⟨h, he, hhs, hlookh, hroot, hanc⟩
      · exact Or.inl hr
      · exact Or.inr ⟨h, he, hhs, flatPrefixGet E0 childE hpre01 h he hlookh,
          hroot, flatAncFwd hpre01 hanc⟩
    · exact Or.inl hpar
  · have hxs : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ x := by omega
    rcases hchild.coverP _ rfl x xe hxs hlookC with hpe | hanc
    · refine Or.inr ⟨E0.length, _, hlen0, hlooke, hpar,
        flatAncEdge _ hlookC hpe⟩
    · have hanc' : IndexedAncestor childE E0.length x := hanc
      exact Or.inr ⟨E0.length, _, hlen0, hlooke, hpar, hanc'⟩

theorem coverPChild (E0 : List Entry) (O0 : List Nat) (node : Nat) (par : Int)
    (depth startE p : Nat)
    (hin : FlatInv E0 O0 par startE)
    (childE : List Entry) (childO : List Nat) (segE : List Entry)
    (hchild : FlatInv childE childO ((E0.length : Nat) : Int)
      ((E0 ++ [(⟨node, par, depth⟩ : Entry)]).length))
    (hpp : par = (p : Int))
    (heE : childE = (E0 ++ [(⟨node, par, depth⟩ : Entry)]) ++ segE) :
    ∀ (x : Nat) (xe : Entry), startE ≤ x → childE[x]? = some xe →
      xe.parent = (p : Int) ∨ IndexedAncestor childE p x := by
  intro x xe hx hlook
  have hlookC := hlook
  rw [heE] at hlook
  have hE1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length = E0.length + 1 := by
    simp
  have hpre01 : E0 <+: childE := by
    refine ⟨[(⟨node, par, depth⟩ : Entry)] ++ segE, ?_⟩
    rw [heE, List.append_assoc]
  have hpre1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)]) <+: childE :=
    ⟨segE, heE.symm⟩
  have h1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)])[E0.length]?
      = some (⟨node, par, depth⟩ : Entry) := by
    rw [List.getElem?_append_right (by simp)]
    have hz : E0.length - E0.length = 0 := by omega
    rw [hz]
    rfl
  have hlooke : childE[E0.length]?
      = some (⟨node, par, depth⟩ : Entry) :=
    flatPrefixGet _ childE hpre1 E0.length _ h1
  have hpfresh : IndexedAncestor childE p E0.length :=
    flatAncEdge _ hlooke hpp
  by_cases hx1 : x < (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length
  · rw [List.getElem?_append_left hx1] at hlook
    rcases flatAppGetCases E0 _ x xe hlook with hold0 | ⟨rfl, rfl⟩
    · rcases hin.coverP p hpp x xe hx hold0 with hpe | hanc
      · exact Or.inl hpe
      · exact Or.inr (flatAncFwd hpre01 hanc)
    · exact Or.inl hpp
  · have hxs : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ x := by omega
    rcases hchild.coverP _ rfl x xe hxs hlookC with hpe | hanc
    · exact Or.inr (flatAncTrans hpfresh (flatAncEdge _ hlookC hpe))
    · have hanc' : IndexedAncestor childE E0.length x := hanc
      exact Or.inr (flatAncTrans hpfresh hanc')

theorem noDupPostSlot (E0 : List Entry) (O0 : List Nat)
    (hb0 : ∀ w ∈ O0, w < E0.length)
    (childO segO : List Nat)
    (hchildn : childO.Nodup)
    (heO : childO = O0 ++ segO)
    (hseg : ∀ w ∈ segO, E0.length + 1 ≤ w) :
    (childO ++ [E0.length]).Nodup := by
  apply flatNodupAppendSingle
  · exact hchildn
  · intro hm
    rw [heO, List.mem_append] at hm
    rcases hm with hm | hm
    · have h := hb0 _ hm
      omega
    · have hle := hseg _ hm
      omega

theorem noParentFresh (E0 : List Entry) (node : Nat) (par : Int)
    (depth startE : Nat)
    (hb : ∀ (i : Nat) (e : Entry), E0[i]? = some e →
      e.parent = -1 ∨ ∃ (p : Nat) (pe : Entry), e.parent = (p : Int) ∧ p < i ∧
        E0[p]? = some pe)
    (hparc : par = -1 ∨ par.toNat < startE) (hlen0 : startE ≤ E0.length) :
    ∀ (d : Nat) (de : Entry),
      (E0 ++ [(⟨node, par, depth⟩ : Entry)])[d]? = some de →
      de.parent ≠ ((E0.length : Nat) : Int) := by
  intro d de hlook hcon
  by_cases hd : d = E0.length
  · subst hd
    have h1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)])[E0.length]?
        = some (⟨node, par, depth⟩ : Entry) := by
      rw [List.getElem?_append_right (by simp)]
      have hz : E0.length - E0.length = 0 := by omega
      rw [hz]
      rfl
    rw [h1] at hlook
    have heq := Option.some.inj hlook
    -- de = e, so de.parent = par; hcon says par = fresh
    have hpp : par = ((E0.length : Nat) : Int) := by
      have : de.parent = ((E0.length : Nat) : Int) := hcon
      rw [← heq] at this
      exact this
    omega
  · have hlt : d < E0.length := by
      have hlen : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length
          = E0.length + 1 := by simp
      have hbnd := (List.getElem?_eq_some_iff.mp hlook).1
      omega
    have hold : E0[d]? = some de := by
      rw [List.getElem?_append_left hlt] at hlook
      exact hlook
    rcases hb d de hold with hr | ⟨p, pe, hpe, hplt, hplook⟩
    · omega
    · omega

theorem winEntry (E0 : List Entry) (O0 : List Nat) (node : Nat) (par : Int)
    (depth : Nat)
    (hw : ∀ (a d x : Nat) (ae de xe : Entry) (pa px pd : Nat),
      E0[a]? = some ae → E0[d]? = some de → E0[x]? = some xe →
      de.parent = (a : Int) → ae.depth % 2 = 0 →
      O0[pa]? = some a → O0[px]? = some x → O0[pd]? = some d →
      pa ≤ px → px ≤ pd → x = a ∨ IndexedAncestor E0 a x)
    (hbd : ∀ w ∈ O0, w < E0.length) :
    ∀ (a d x : Nat) (ae de xe : Entry) (pa px pd : Nat),
      (E0 ++ [(⟨node, par, depth⟩ : Entry)])[a]? = some ae →
      (E0 ++ [(⟨node, par, depth⟩ : Entry)])[d]? = some de →
      (E0 ++ [(⟨node, par, depth⟩ : Entry)])[x]? = some xe →
      de.parent = (a : Int) → ae.depth % 2 = 0 →
      O0[pa]? = some a → O0[px]? = some x → O0[pd]? = some d →
      pa ≤ px → px ≤ pd → x = a ∨
        IndexedAncestor (E0 ++ [(⟨node, par, depth⟩ : Entry)]) a x := by
  intro a d x ae de xe pa px pd hae hed hex hpar heven hpa hpx hpd hle1 hle2
  have hpre : E0 <+: E0 ++ [(⟨node, par, depth⟩ : Entry)] := ⟨_, rfl⟩
  have ha : a < E0.length := hbd a (List.mem_of_getElem? hpa)
  have hd : d < E0.length := hbd d (List.mem_of_getElem? hpd)
  have hx : x < E0.length := hbd x (List.mem_of_getElem? hpx)
  have hae0 : E0[a]? = some ae := by
    have hback := flatPrefixGetBack E0 _ hpre a ha
    rw [hback] at hae
    exact hae
  have hed0 : E0[d]? = some de := by
    have hback := flatPrefixGetBack E0 _ hpre d hd
    rw [hback] at hed
    exact hed
  have hex0 : E0[x]? = some xe := by
    have hback := flatPrefixGetBack E0 _ hpre x hx
    rw [hback] at hex
    exact hex
  rcases hw a d x ae de xe pa px pd hae0 hed0 hex0 hpar heven hpa hpx hpd
      hle1 hle2 with h | hanc
  · exact Or.inl h
  · exact Or.inr (flatAncFwd hpre hanc)


theorem freshLookup (E0 : List Entry) (node : Nat) (par : Int) (depth : Nat) :
    (E0 ++ [(⟨node, par, depth⟩ : Entry)])[E0.length]?
      = some (⟨node, par, depth⟩ : Entry) := by
  rw [List.getElem?_append_right (by simp)]
  have hz : E0.length - E0.length = 0 := by omega
  rw [hz]
  rfl

theorem oldPosOfNe (O0 : List Nat) (fresh : Nat) (p v : Nat) (hne : v ≠ fresh)
    (h : (O0 ++ [fresh])[p]? = some v) : O0[p]? = some v := by
  by_cases hp : p < O0.length
  · rw [List.getElem?_append_left hp] at h
    exact h
  · have hlen : (O0 ++ [fresh]).length = O0.length + 1 := by simp
    have hbnd := (List.getElem?_eq_some_iff.mp h).1
    have hpp : p = O0.length := by omega
    subst hpp
    have hfresh : (O0 ++ [fresh])[O0.length]? = some fresh := by
      rw [List.getElem?_append_right (by omega)]
      have hz : O0.length - O0.length = 0 := by omega
      rw [hz]
      rfl
    rw [hfresh] at h
    exact absurd (Option.some.inj h).symm hne

theorem postParEntry (E0 : List Entry) (O0 : List Nat) (node : Nat) (par : Int)
    (depth : Nat)
    (hpp : par = -1 ∨ ∀ (pa px : Nat) (v : Nat),
      O0[pa]? = some par.toNat → O0[px]? = some v → pa ≤ px →
      v = par.toNat ∨ IndexedAncestor E0 par.toNat v) :
    par = -1 ∨ ∀ (pa px : Nat) (v : Nat),
      O0[pa]? = some par.toNat → O0[px]? = some v → pa ≤ px →
      v = par.toNat ∨
        IndexedAncestor (E0 ++ [(⟨node, par, depth⟩ : Entry)]) par.toNat v := by
  rcases hpp with h | h
  · exact Or.inl h
  · exact Or.inr (by
      intro pa px v hpa hpx hle
      have hpre : E0 <+: E0 ++ [(⟨node, par, depth⟩ : Entry)] := ⟨_, rfl⟩
      rcases h pa px v hpa hpx hle with h | hanc
      · exact Or.inl h
      · exact Or.inr (flatAncFwd hpre hanc))
theorem winPreSlotEven (E0 : List Entry) (O0 : List Nat) (node : Nat) (par : Int)
    (depth : Nat)
    (hw : ∀ (a d x : Nat) (ae de xe : Entry) (pa px pd : Nat),
      (E0 ++ [(⟨node, par, depth⟩ : Entry)])[a]? = some ae →
      (E0 ++ [(⟨node, par, depth⟩ : Entry)])[d]? = some de →
      (E0 ++ [(⟨node, par, depth⟩ : Entry)])[x]? = some xe →
      de.parent = (a : Int) → ae.depth % 2 = 0 →
      O0[pa]? = some a → O0[px]? = some x → O0[pd]? = some d →
      pa ≤ px → px ≤ pd → x = a ∨
        IndexedAncestor (E0 ++ [(⟨node, par, depth⟩ : Entry)]) a x)
    (hpp : par = -1 ∨ ∀ (pa px : Nat) (v : Nat),
      O0[pa]? = some par.toNat → O0[px]? = some v → pa ≤ px →
      v = par.toNat ∨
        IndexedAncestor (E0 ++ [(⟨node, par, depth⟩ : Entry)]) par.toNat v)
    (hnp : ∀ (d : Nat) (de : Entry),
      (E0 ++ [(⟨node, par, depth⟩ : Entry)])[d]? = some de →
      de.parent ≠ ((E0.length : Nat) : Int))
    (hfr : E0.length ∉ O0) :
    ∀ (a d x : Nat) (ae de xe : Entry) (pa px pd : Nat),
      (E0 ++ [(⟨node, par, depth⟩ : Entry)])[a]? = some ae →
      (E0 ++ [(⟨node, par, depth⟩ : Entry)])[d]? = some de →
      (E0 ++ [(⟨node, par, depth⟩ : Entry)])[x]? = some xe →
      de.parent = (a : Int) → ae.depth % 2 = 0 →
      (O0 ++ [E0.length])[pa]? = some a → (O0 ++ [E0.length])[px]? = some x →
      (O0 ++ [E0.length])[pd]? = some d →
      pa ≤ px → px ≤ pd → x = a ∨
        IndexedAncestor (E0 ++ [(⟨node, par, depth⟩ : Entry)]) a x := by
  intro a d x ae de xe pa px pd hae hed hex hde heven hpa hpx hpd hle1 hle2
  have h1 := freshLookup E0 node par depth
  have hlen : (O0 ++ [E0.length]).length = O0.length + 1 := by simp
  by_cases ha : a = E0.length
  · subst ha
    exfalso
    exact hnp d de hed hde
  · by_cases hd : d = E0.length
    · subst hd
      have heq : de = (⟨node, par, depth⟩ : Entry) :=
        Option.some.inj (hed.symm.trans h1)
      have hapar : par = (a : Int) := by
        rw [heq] at hde
        exact hde
      have hpdEq : pd = O0.length := by
        by_cases hpdlt : pd < O0.length
        · rw [List.getElem?_append_left hpdlt] at hpd
          -- O0[pd]? = some E0.length contradicts hfr
          exfalso
          exact hfr (List.mem_of_getElem? hpd)
        · have hbnd := (List.getElem?_eq_some_iff.mp hpd).1
          omega
      subst hpdEq
      by_cases hx : x = E0.length
      · subst hx
        exact Or.inr (flatAncEdge _ h1 hapar)
      · have hpx0 : O0[px]? = some x := oldPosOfNe O0 E0.length px x hx hpx
        have hpa0 : O0[pa]? = some a := oldPosOfNe O0 E0.length pa a ha hpa
        have hpto : par.toNat = a := by omega
        have hne : par ≠ -1 := by omega
        rcases hpp with hcon | hpost
        · exact absurd hcon hne
        · have hpaT : O0[pa]? = some par.toNat := by
            rw [hpto]
            exact hpa0
          have hres := hpost pa px x hpaT hpx0 hle1
          rw [hpto] at hres
          exact hres
    · have hpdlt : pd < O0.length := by
        by_cases hlt : pd < O0.length
        · exact hlt
        · have hbnd := (List.getElem?_eq_some_iff.mp hpd).1
          have hpdEq : pd = O0.length := by omega
          subst hpdEq
          have hfresh : (O0 ++ [E0.length])[O0.length]? = some E0.length := by
            rw [List.getElem?_append_right (by omega)]
            have hz : O0.length - O0.length = 0 := by omega
            rw [hz]
            rfl
          rw [hfresh] at hpd
          exact absurd (Option.some.inj hpd).symm hd
      have hpxlt : px < O0.length := by omega
      have hpalt : pa < O0.length := by omega
      have hpa0 : O0[pa]? = some a := by
        rw [List.getElem?_append_left hpalt] at hpa
        exact hpa
      have hpx0 : O0[px]? = some x := by
        rw [List.getElem?_append_left hpxlt] at hpx
        exact hpx
      have hpd0 : O0[pd]? = some d := by
        rw [List.getElem?_append_left hpdlt] at hpd
        exact hpd
      rcases hw a d x ae de xe pa px pd hae hed hex hde heven hpa0 hpx0 hpd0
          hle1 hle2 with h | hanc
      · exact Or.inl h
      · exact Or.inr hanc
theorem freshPosLast (O0 : List Nat) (fresh p : Nat) (hfr : fresh ∉ O0)
    (h : (O0 ++ [fresh])[p]? = some fresh) : p = O0.length := by
  by_cases hp : p < O0.length
  · rw [List.getElem?_append_left hp] at h
    exact absurd (List.mem_of_getElem? h) hfr
  · have hlen : (O0 ++ [fresh]).length = O0.length + 1 := by simp
    have hbnd := (List.getElem?_eq_some_iff.mp h).1
    omega

theorem postParChildEven (E0 : List Entry) (O0 : List Nat) (node : Nat)
    (par : Int) (depth startE : Nat)
    (hpp : par = -1 ∨ ∀ (pa px : Nat) (v : Nat),
      O0[pa]? = some par.toNat → O0[px]? = some v → pa ≤ px →
      v = par.toNat ∨ IndexedAncestor E0 par.toNat v)
    (childE : List Entry) (childO segO : List Nat) (segE : List Entry)
    (hchild : FlatInv childE childO ((E0.length : Nat) : Int)
      ((E0 ++ [(⟨node, par, depth⟩ : Entry)]).length))
    (heE : childE = (E0 ++ [(⟨node, par, depth⟩ : Entry)]) ++ segE)
    (heO : childO = (O0 ++ [E0.length]) ++ segO)
    (hseg : ∀ w ∈ segO, (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ w)
    (hnn : par = -1 ∨ 0 ≤ par)
    (hparc : par = -1 ∨ par.toNat < startE)
    (hlen0 : startE ≤ E0.length) :
    par = -1 ∨ ∀ (pa px : Nat) (v : Nat),
      childO[pa]? = some par.toNat → childO[px]? = some v → pa ≤ px →
      v = par.toNat ∨ IndexedAncestor childE par.toNat v := by
  by_cases hpar : par = -1
  · exact Or.inl hpar
  · have hnn' : 0 ≤ par := by
      rcases hnn with h | h
      · exact absurd h hpar
      · exact h
    have hrt : (((par.toNat : Nat) : Int)) = par := by omega
    have hpto : par.toNat < E0.length := by
      rcases hparc with h | h
      · exact absurd h hpar
      · omega
    have hE1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length
        = E0.length + 1 := by simp
    have hpreLen : ((O0 ++ [E0.length])).length = O0.length + 1 := by simp
    have hpre01 : E0 <+: childE := by
      refine ⟨[(⟨node, par, depth⟩ : Entry)] ++ segE, ?_⟩
      rw [heE, List.append_assoc]
    have hpre1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)]) <+: childE :=
      ⟨segE, heE.symm⟩
    have hlooke : childE[E0.length]?
        = some (⟨node, par, depth⟩ : Entry) :=
      flatPrefixGet _ childE hpre1 E0.length _ (freshLookup E0 node par depth)
    rcases hpp with hcon | hpost
    · exact absurd hcon hpar
    · refine Or.inr (by
        intro pa px v hpa hpx hle
        rw [heO] at hpa hpx
        have hpaPre : pa < (O0 ++ [E0.length]).length := by
          by_cases h : pa < (O0 ++ [E0.length]).length
          · exact h
          · have hle' : (O0 ++ [E0.length]).length ≤ pa := by omega
            rw [List.getElem?_append_right hle'] at hpa
            have hmem : par.toNat ∈ segO := List.mem_of_getElem? hpa
            have hle2 := hseg _ hmem
            omega
        rw [List.getElem?_append_left hpaPre] at hpa
        by_cases hpxPre : px < (O0 ++ [E0.length]).length
        · rw [List.getElem?_append_left hpxPre] at hpx
          by_cases hpx0 : px < O0.length
          · have hpa0 : pa < O0.length := by
              by_cases h : pa < O0.length
              · exact h
              · have hpaEq : pa = O0.length := by omega
                subst hpaEq
                have hfresh : (O0 ++ [E0.length])[O0.length]?
                    = some E0.length := by
                  rw [List.getElem?_append_right (by omega)]
                  have hz : O0.length - O0.length = 0 := by omega
                  rw [hz]
                  rfl
                rw [hfresh] at hpa
                have : E0.length = par.toNat := Option.some.inj hpa
                omega
            have hpa00 : O0[pa]? = some par.toNat := by
              rw [List.getElem?_append_left hpa0] at hpa
              exact hpa
            have hpx00 : O0[px]? = some v := by
              rw [List.getElem?_append_left hpx0] at hpx
              exact hpx
            rcases hpost pa px v hpa00 hpx00 hle with h | hanc
            · exact Or.inl h
            · exact Or.inr (flatAncFwd hpre01 hanc)
          · have hpxEq : px = O0.length := by omega
            subst hpxEq
            have hfresh : (O0 ++ [E0.length])[O0.length]? = some E0.length := by
              rw [List.getElem?_append_right (by omega)]
              have hz : O0.length - O0.length = 0 := by omega
              rw [hz]
              rfl
            rw [hfresh] at hpx
            have hv : v = E0.length := (Option.some.inj hpx).symm
            subst hv
            exact Or.inr (flatAncEdge _ hlooke hrt.symm)
        · have hle' : (O0 ++ [E0.length]).length ≤ px := by omega
          rw [List.getElem?_append_right hle'] at hpx
          have hmem0 : v ∈ segO := List.mem_of_getElem? hpx
          have hvlt : v < childE.length := by
            have hmem : v ∈ childO := by
              rw [heO]
              exact List.mem_append.mpr (Or.inr hmem0)
            exact hchild.bounds v hmem
          obtain ⟨ve, hlook⟩ := flatLookupOfLt _ v hvlt
          have hxs : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ v :=
            hseg _ hmem0
          rcases hchild.coverP _ rfl v ve hxs hlook with hpe | hanc
          · have hpfresh : IndexedAncestor childE par.toNat E0.length :=
              flatAncEdge _ hlooke hrt.symm
            exact Or.inr (flatAncTrans hpfresh (flatAncEdge _ hlook hpe))
          · have hanc' : IndexedAncestor childE E0.length v := hanc
            have hpfresh : IndexedAncestor childE par.toNat E0.length :=
              flatAncEdge _ hlooke hrt.symm
            exact Or.inr (flatAncTrans hpfresh hanc'))

theorem postParPostSlot (childE : List Entry) (childO : List Nat) (fresh : Nat)
    (par : Int) (fe : Entry)
    (hpp : par = -1 ∨ ∀ (pa px : Nat) (v : Nat),
      childO[pa]? = some par.toNat → childO[px]? = some v → pa ≤ px →
      v = par.toNat ∨ IndexedAncestor childE par.toNat v)
    (hfr : fresh ∉ childO)
    (hfe : childE[fresh]? = some fe) (hfepar : fe.parent = par)
    (hnn : par = -1 ∨ 0 ≤ par) :
    par = -1 ∨ ∀ (pa px : Nat) (v : Nat),
      (childO ++ [fresh])[pa]? = some par.toNat →
      (childO ++ [fresh])[px]? = some v → pa ≤ px →
      v = par.toNat ∨ IndexedAncestor childE par.toNat v := by
  by_cases hpar : par = -1
  · exact Or.inl hpar
  · have hnn' : 0 ≤ par := by
      rcases hnn with h | h
      · exact absurd h hpar
      · exact h
    have hrt : (((par.toNat : Nat) : Int)) = par := by omega
    have hlen : (childO ++ [fresh]).length = childO.length + 1 := by simp
    rcases hpp with hcon | hpost
    · exact absurd hcon hpar
    · refine Or.inr (by
        intro pa px v hpa hpx hle
        by_cases htv : par.toNat = fresh
        · have hpaEq : pa = childO.length := by
            have hpa' : (childO ++ [fresh])[pa]? = some fresh := by
              rw [htv] at hpa
              exact hpa
            exact freshPosLast _ _ _ hfr hpa'
          subst hpaEq
          have hbnd := (List.getElem?_eq_some_iff.mp hpx).1
          have hpxEq : px = childO.length := by omega
          subst hpxEq
          have hfresh : (childO ++ [fresh])[childO.length]? = some fresh := by
            rw [List.getElem?_append_right (by omega)]
            have hz : childO.length - childO.length = 0 := by omega
            rw [hz]
            rfl
          rw [hfresh] at hpx
          have hv : v = fresh := (Option.some.inj hpx).symm
          subst hv
          exact Or.inl htv.symm
        · have hpa0 : childO[pa]? = some par.toNat :=
            oldPosOfNe _ _ _ _ htv hpa
          by_cases hvf : v = fresh
          · rw [hvf] at hpx
            have hpxEq : px = childO.length := freshPosLast _ _ _ hfr hpx
            rw [hvf]
            exact Or.inr (flatAncEdge _ hfe (by rw [hfepar]; exact hrt.symm))
          · have hpx0 : childO[px]? = some v :=
              oldPosOfNe _ _ _ _ hvf hpx
            exact hpost pa px v hpa0 hpx0 hle)

theorem winPostSlotOdd (childE : List Entry) (childO : List Nat) (fresh : Nat)
    (par : Int) (fe : Entry)
    (hw : ∀ (a d x : Nat) (ae de xe : Entry) (pa px pd : Nat),
      childE[a]? = some ae → childE[d]? = some de → childE[x]? = some xe →
      de.parent = (a : Int) → ae.depth % 2 = 0 →
      childO[pa]? = some a → childO[px]? = some x → childO[pd]? = some d →
      pa ≤ px → px ≤ pd → x = a ∨ IndexedAncestor childE a x)
    (hpp : par = -1 ∨ ∀ (pa px : Nat) (v : Nat),
      childO[pa]? = some par.toNat → childO[px]? = some v → pa ≤ px →
      v = par.toNat ∨ IndexedAncestor childE par.toNat v)
    (hfr : fresh ∉ childO)
    (hfe : childE[fresh]? = some fe) (hfepar : fe.parent = par)
    (hodd : fe.depth % 2 ≠ 0) :
    ∀ (a d x : Nat) (ae de xe : Entry) (pa px pd : Nat),
      childE[a]? = some ae → childE[d]? = some de → childE[x]? = some xe →
      de.parent = (a : Int) → ae.depth % 2 = 0 →
      (childO ++ [fresh])[pa]? = some a →
      (childO ++ [fresh])[px]? = some x →
      (childO ++ [fresh])[pd]? = some d →
      pa ≤ px → px ≤ pd → x = a ∨ IndexedAncestor childE a x := by
  intro a d x ae de xe pa px pd hae hed hex hde heven hpa hpx hpd hle1 hle2
  have hlen : (childO ++ [fresh]).length = childO.length + 1 := by simp
  by_cases ha : a = fresh
  · rw [ha] at hae
    have heq : ae = fe := Option.some.inj (hae.symm.trans hfe)
    exfalso
    exact hodd (heq ▸ heven)
  · by_cases hd : d = fresh
    · have hpd' : (childO ++ [fresh])[pd]? = some fresh := by
        rw [hd] at hpd
        exact hpd
      have hpdEq : pd = childO.length := freshPosLast _ _ _ hfr hpd'
      have hed' : childE[fresh]? = some de := by
        rw [hd] at hed
        exact hed
      have heqd : de = fe := Option.some.inj (hed'.symm.trans hfe)
      have hapar : par = (a : Int) := by
        rw [heqd, hfepar] at hde
        exact hde
      have hpto : par.toNat = a := by omega
      have hne : par ≠ -1 := by omega
      by_cases hx : x = fresh
      · rw [hx] at hpx
        have hpxEq : px = childO.length := freshPosLast _ _ _ hfr hpx
        rw [hx]
        exact Or.inr (flatAncEdge _ hfe (by rw [hfepar]; exact hapar))
      · have hpx0 : childO[px]? = some x :=
          oldPosOfNe _ _ _ _ hx hpx
        have hpa0 : childO[pa]? = some a :=
          oldPosOfNe _ _ _ _ ha hpa
        rcases hpp with hcon | hpost
        · exact absurd hcon hne
        · have hpaT : childO[pa]? = some par.toNat := by
            rw [hpto]
            exact hpa0
          have hres := hpost pa px x hpaT hpx0 hle1
          rw [hpto] at hres
          exact hres
    · have hfresh : (childO ++ [fresh])[childO.length]? = some fresh := by
        rw [List.getElem?_append_right (by omega)]
        have hz : childO.length - childO.length = 0 := by omega
        rw [hz]
        rfl
      have hpdlt : pd < childO.length := by
        by_cases hlt : pd < childO.length
        · exact hlt
        · have hbnd := (List.getElem?_eq_some_iff.mp hpd).1
          have hpdEq : pd = childO.length := by omega
          rw [hpdEq, hfresh] at hpd
          exact absurd (Option.some.inj hpd).symm hd
      have hpxlt : px < childO.length := by omega
      have hxne : x ≠ fresh := by
        intro hc
        have hpx' : (childO ++ [fresh])[px]? = some fresh := by
          rw [hc] at hpx
          exact hpx
        have hpxEq : px = childO.length := freshPosLast _ _ _ hfr hpx'
        omega
      have hpa0 : childO[pa]? = some a := oldPosOfNe _ _ _ _ ha hpa
      have hpx0 : childO[px]? = some x := oldPosOfNe _ _ _ _ hxne hpx
      have hpd0 : childO[pd]? = some d := by
        rw [List.getElem?_append_left hpdlt] at hpd
        exact hpd
      rcases hw a d x ae de xe pa px pd hae hed hex hde heven hpa0 hpx0 hpd0
          hle1 hle2 with h | hanc
      · exact Or.inl h
      · exact Or.inr hanc

theorem fstepEq (ns : List Tree.Node) (up : Bool) (fuel : Nat)
    (E0 : List Entry) (O0 : List Nat) (node : Nat) (par : Int) (depth : Nat)
    (ce : List Entry) (co : List Nat)
    (heq : flatten ns up fuel (children ns node) ((E0.length : Nat) : Int)
      (depth + 1) (E0 ++ [(⟨node, par, depth⟩ : Entry)])
      (if depth % 2 == 0 then O0 ++ [E0.length] else O0) = (ce, co)) :
    fstep ns up fuel par depth (E0, O0) node =
      (ce, if depth % 2 == 0 then co else co ++ [E0.length]) := by
  show (let res := flatten ns up fuel (children ns node)
          ((E0.length : Nat) : Int) (depth + 1)
          (E0 ++ [(⟨node, par, depth⟩ : Entry)])
          (if depth % 2 == 0 then O0 ++ [E0.length] else O0);
        (res.1, if depth % 2 == 0 then res.2 else res.2 ++ [E0.length])) = _
  rw [heq]

theorem postParChildOdd (E0 : List Entry) (O0 : List Nat) (node : Nat)
    (par : Int) (depth startE : Nat)
    (hpp : par = -1 ∨ ∀ (pa px : Nat) (v : Nat),
      O0[pa]? = some par.toNat → O0[px]? = some v → pa ≤ px →
      v = par.toNat ∨ IndexedAncestor E0 par.toNat v)
    (childE : List Entry) (childO segO : List Nat) (segE : List Entry)
    (hchild : FlatInv childE childO ((E0.length : Nat) : Int)
      ((E0 ++ [(⟨node, par, depth⟩ : Entry)]).length))
    (heE : childE = (E0 ++ [(⟨node, par, depth⟩ : Entry)]) ++ segE)
    (heO : childO = O0 ++ segO)
    (hseg : ∀ w ∈ segO, (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ w)
    (hnn : par = -1 ∨ 0 ≤ par)
    (hparc : par = -1 ∨ par.toNat < startE)
    (hlen0 : startE ≤ E0.length) :
    par = -1 ∨ ∀ (pa px : Nat) (v : Nat),
      childO[pa]? = some par.toNat → childO[px]? = some v → pa ≤ px →
      v = par.toNat ∨ IndexedAncestor childE par.toNat v := by
  by_cases hpar : par = -1
  · exact Or.inl hpar
  · have hnn' : 0 ≤ par := by
      rcases hnn with h | h
      · exact absurd h hpar
      · exact h
    have hrt : (((par.toNat : Nat) : Int)) = par := by omega
    have hpto : par.toNat < E0.length := by
      rcases hparc with h | h
      · exact absurd h hpar
      · omega
    have hE1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length
        = E0.length + 1 := by simp
    have hpre01 : E0 <+: childE := by
      refine ⟨[(⟨node, par, depth⟩ : Entry)] ++ segE, ?_⟩
      rw [heE, List.append_assoc]
    have hpre1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)]) <+: childE :=
      ⟨segE, heE.symm⟩
    have hlooke : childE[E0.length]?
        = some (⟨node, par, depth⟩ : Entry) :=
      flatPrefixGet _ childE hpre1 E0.length _ (freshLookup E0 node par depth)
    rcases hpp with hcon | hpost
    · exact absurd hcon hpar
    · refine Or.inr (by
        intro pa px v hpa hpx hle
        rw [heO] at hpa hpx
        have hpaPre : pa < O0.length := by
          by_cases h : pa < O0.length
          · exact h
          · have hle' : O0.length ≤ pa := by omega
            rw [List.getElem?_append_right hle'] at hpa
            have hmem : par.toNat ∈ segO := List.mem_of_getElem? hpa
            have hle2 := hseg _ hmem
            omega
        rw [List.getElem?_append_left hpaPre] at hpa
        by_cases hpxPre : px < O0.length
        · rw [List.getElem?_append_left hpxPre] at hpx
          rcases hpost pa px v hpa hpx hle with h | hanc
          · exact Or.inl h
          · exact Or.inr (flatAncFwd hpre01 hanc)
        · have hle' : O0.length ≤ px := by omega
          rw [List.getElem?_append_right hle'] at hpx
          have hmem0 : v ∈ segO := List.mem_of_getElem? hpx
          have hvlt : v < childE.length := by
            have hmem : v ∈ childO := by
              rw [heO]
              exact List.mem_append.mpr (Or.inr hmem0)
            exact hchild.bounds v hmem
          obtain ⟨ve, hlook⟩ := flatLookupOfLt _ v hvlt
          have hxs : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ v :=
            hseg _ (List.mem_of_getElem? hpx)
          rcases hchild.coverP _ rfl v ve hxs hlook with hpe | hanc
          · have hpfresh : IndexedAncestor childE par.toNat E0.length :=
              flatAncEdge _ hlooke hrt.symm
            exact Or.inr (flatAncTrans hpfresh (flatAncEdge _ hlook hpe))
          · have hanc' : IndexedAncestor childE E0.length v := hanc
            have hpfresh : IndexedAncestor childE par.toNat E0.length :=
              flatAncEdge _ hlooke hrt.symm
            exact Or.inr (flatAncTrans hpfresh hanc'))

theorem flatStep (ns : List Tree.Node) (up : Bool) (fuel : Nat)
    (E0 : List Entry) (O0 : List Nat) (node : Nat) (par : Int)
    (depth startE : Nat)
    (hin : FlatInv E0 O0 par startE)
    (hlen0 : startE ≤ E0.length)
    (hnn : par = -1 ∨ 0 ≤ par)
    (hparc : par = -1 ∨ par.toNat < startE)
    (segE : List Entry) (segO : List Nat)
    (hchPair : flatten ns up fuel (children ns node) ((E0.length : Nat) : Int)
      (depth + 1) (E0 ++ [(⟨node, par, depth⟩ : Entry)])
      (if depth % 2 == 0 then O0 ++ [E0.length] else O0) =
      ((E0 ++ [(⟨node, par, depth⟩ : Entry)]) ++ segE,
       (if depth % 2 == 0 then O0 ++ [E0.length] else O0) ++ segO))
    (hchLow : ∀ w ∈ segO, (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ w)
    (hchInv : FlatInv ((E0 ++ [(⟨node, par, depth⟩ : Entry)]) ++ segE)
      ((if depth % 2 == 0 then O0 ++ [E0.length] else O0) ++ segO)
      ((E0.length : Nat) : Int)
      ((E0 ++ [(⟨node, par, depth⟩ : Entry)]).length)) :
    ∃ segE' segO',
      fstep ns up fuel par depth (E0, O0) node = (E0 ++ segE', O0 ++ segO') ∧
      (∀ w ∈ segO', startE ≤ w) ∧
      FlatInv (E0 ++ segE') (O0 ++ segO') par startE := by
  have hE1 : (E0 ++ [(⟨node, par, depth⟩ : Entry)]).length
      = E0.length + 1 := by simp
  have hfun := fstepEq ns up fuel E0 O0 node par depth _ _ hchPair
  by_cases hev : depth % 2 = 0
  · have hpre : (if depth % 2 == 0 then O0 ++ [E0.length] else O0)
        = O0 ++ [E0.length] := by simp [hev]
    rw [hpre] at hchPair hchInv
    simp [hev] at hfun
    refine ⟨[(⟨node, par, depth⟩ : Entry)] ++ segE, [E0.length] ++ segO,
      ?_, ?_, ?_⟩
    · simp [hfun]
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton] at hw
        subst hw
        exact hlen0
      · have hle := hchLow _ hw
        omega
    · have hE2 : E0 ++ ([(⟨node, par, depth⟩ : Entry)] ++ segE)
          = (E0 ++ [(⟨node, par, depth⟩ : Entry)]) ++ segE := by
        simp only [List.append_assoc]
      have hO2 : O0 ++ ([E0.length] ++ segO) = (O0 ++ [E0.length]) ++ segO := by
        simp only [List.append_assoc]
      rw [hE2, hO2]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hchInv.bounds
      · exact hchInv.noDup
      · exact covChildEven E0 O0 node par depth startE hin _ _ _ _ hchInv
          rfl rfl hchLow
      · exact hchInv.before
      · by_cases hpar : par = -1
        · intro _
          exact coverNChild E0 O0 node par depth startE hin _ _ _ hchInv
            hpar rfl hlen0
        · intro hcon
          exact absurd hcon hpar
      · intro p hpp
        exact coverPChild E0 O0 node par depth startE p hin _ _ _ hchInv
          hpp rfl
      · exact pboundChild E0 O0 node par depth startE hin _ _ _ hchInv
          rfl hlen0
      · exact hchInv.win
      · exact postParChildEven E0 O0 node par depth startE hin.postPar _ _ _ _
          hchInv rfl rfl hchLow hnn hparc hlen0
  · have hpre : (if depth % 2 == 0 then O0 ++ [E0.length] else O0) = O0 := by
      simp [hev]
    rw [hpre] at hchPair hchInv
    simp [hev] at hfun
    refine ⟨[(⟨node, par, depth⟩ : Entry)] ++ segE, segO ++ [E0.length],
      ?_, ?_, ?_⟩
    · simp [hfun]
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · have hle := hchLow _ hw
        omega
      · rw [List.mem_singleton] at hw
        subst hw
        exact hlen0
    · have hE2 : E0 ++ ([(⟨node, par, depth⟩ : Entry)] ++ segE)
          = (E0 ++ [(⟨node, par, depth⟩ : Entry)]) ++ segE := by
        simp only [List.append_assoc]
      have hO2 : O0 ++ (segO ++ [E0.length]) = (O0 ++ segO) ++ [E0.length] := by
        simp only [List.append_assoc]
      rw [hE2, hO2]
      have hfr : E0.length ∉ (O0 ++ segO) := by
        intro hm
        rcases List.mem_append.mp hm with hm | hm
        · have h := hin.bounds _ hm
          omega
        · have hle := hchLow _ hm
          omega
      have hfe : ((E0 ++ [(⟨node, par, depth⟩ : Entry)]) ++ segE)[E0.length]? =
          some (⟨node, par, depth⟩ : Entry) :=
        flatPrefixGet _ _ ⟨segE, rfl⟩ _ _ (freshLookup E0 node par depth)
      have hppEven := postParChildOdd E0 O0 node par depth startE hin.postPar
        _ _ _ _ hchInv rfl rfl hchLow hnn hparc hlen0
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact boundsSlot _ _ _ hchInv.bounds (by
          rw [List.length_append, hE1]
          omega)
      · exact noDupPostSlot E0 O0 hin.bounds _ _ hchInv.noDup rfl (by
          intro w hw
          have hle := hchLow _ hw
          omega)
      · exact covChildOdd E0 O0 node par depth startE hin _ _ _ _ hchInv
          rfl rfl hchLow
      · exact hchInv.before
      · by_cases hpar : par = -1
        · intro _
          exact coverNChild E0 O0 node par depth startE hin _ _ _ hchInv
            hpar rfl hlen0
        · intro hcon
          exact absurd hcon hpar
      · intro p hpp
        exact coverPChild E0 O0 node par depth startE p hin _ _ _ hchInv
          hpp rfl
      · exact pboundChild E0 O0 node par depth startE hin _ _ _ hchInv
          rfl hlen0
      · exact winPostSlotOdd _ _ _ _ _ hchInv.win hppEven hfr hfe rfl hev
      · exact postParPostSlot _ _ _ _ _ hppEven hfr hfe rfl hnn

theorem flatFold (ns : List Tree.Node) (up : Bool) (fuel : Nat)
    (par : Int) (depth startE : Nat)
    (hnn : par = -1 ∨ 0 ≤ par)
    (hparc : par = -1 ∨ par.toNat < startE)
    (ih : ∀ (ids : List Nat) (par : Int) (depth startE : Nat) (es : List Entry)
      (os : List Nat),
      startE ≤ es.length →
      (par = -1 ∨ ∃ pe, es[par.toNat]? = some pe) →
      (par = -1 ∨ par.toNat < startE) →
      (par = -1 ∨ 0 ≤ par) →
      FlatInv es os par startE →
      ∃ segE segO, flatten ns up fuel ids par depth es os
        = (es ++ segE, os ++ segO) ∧
        (∀ w ∈ segO, startE ≤ w) ∧ FlatInv (es ++ segE) (os ++ segO) par startE) :
    ∀ (walk : List Nat) (st : List Entry × List Nat),
      FlatInv st.1 st.2 par startE → startE ≤ st.1.length →
      (par = -1 ∨ ∃ pe, st.1[par.toNat]? = some pe) →
      ∃ segE segO, walk.foldl (fstep ns up fuel par depth) st
        = (st.1 ++ segE, st.2 ++ segO) ∧
        (∀ w ∈ segO, startE ≤ w) ∧ FlatInv (st.1 ++ segE) (st.2 ++ segO) par startE := by
  intro walk
  induction walk with
  | nil =>
    intro st hP hlen hfr
    exact ⟨[], [], by simp, by intro w hw; simp at hw, by simpa using hP⟩
  | cons node rest ihrest =>
    intro st hP hlen hfr
    have hE1 : (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length
        = st.1.length + 1 := by simp
    have htn : ((((st.1.length : Nat) : Int)).toNat) = st.1.length := rfl
    have hfrFresh : st.1.length ∉ st.2 := by
      intro hm
      have h := hP.bounds _ hm
      omega
    by_cases hev : depth % 2 = 0
    · have hpre : (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2)
          = st.2 ++ [st.1.length] := by simp [hev]
      have hinI : FlatInv (st.1 ++ [(⟨node, par, depth⟩ : Entry)])
          (st.2 ++ [st.1.length]) ((st.1.length : Nat) : Int)
          ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length) := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact boundsSlot _ _ _ (boundsEntry _ _ _ _ _ hP.bounds) (by omega)
        · exact noDupPreSlot _ _ hP.noDup hP.bounds
        · exact covEntryEven _ _ _ _ _ hP.cov
        · exact beforeEntry _ _ _ _ hP.before hnn hfr
        · intro hcon
          omega
        · intro p hp x xe hxs hlook
          have hlt := (List.getElem?_eq_some_iff.mp hlook).1
          omega
        · intro x xe hxs hlook
          have hlt := (List.getElem?_eq_some_iff.mp hlook).1
          omega
        · exact winPreSlotEven _ _ _ _ _ (winEntry _ _ _ _ _ hP.win hP.bounds)
            (postParEntry _ _ _ _ _ hP.postPar)
            (noParentFresh _ _ _ _ _ hP.before hparc hlen) hfrFresh
        · refine Or.inr (by
            intro pa px v hpa hpx hle
            have hpaEq : pa = st.2.length :=
              freshPosLast _ _ _ hfrFresh (by rwa [htn] at hpa)
            subst hpaEq
            have hprelen : (st.2 ++ [st.1.length]).length
                = st.2.length + 1 := by simp
            have hbnd := (List.getElem?_eq_some_iff.mp hpx).1
            have hpxEq : px = st.2.length := by omega
            subst hpxEq
            have hfresh : (st.2 ++ [st.1.length])[st.2.length]?
                = some st.1.length := by
              rw [List.getElem?_append_right (by omega)]
              have hz : st.2.length - st.2.length = 0 := by omega
              rw [hz]
              rfl
            rw [hfresh] at hpx
            have hv : v = st.1.length := (Option.some.inj hpx).symm
            subst hv
            exact Or.inl rfl)
      have hlen' : (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length := by omega
      have hfr' : ((st.1.length : Nat) : Int) = -1 ∨ ∃ pe, (st.1 ++ [(⟨node, par, depth⟩ : Entry)])[(((st.1.length : Nat) : Int)).toNat]? = some pe := Or.inr ⟨_, by rw [htn]; exact freshLookup st.1 node par depth⟩
      have hparc' : ((st.1.length : Nat) : Int) = -1 ∨
          ((((st.1.length : Nat) : Int)).toNat)
            < (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length := by
        refine Or.inr (by rw [htn]; omega)
      have hnn' : ((st.1.length : Nat) : Int) = -1 ∨
          0 ≤ ((st.1.length : Nat) : Int) := Or.inr (by omega)
      have hlastC : ∀ pe, (st.1 ++ [(⟨node, par, depth⟩ : Entry)])[(((st.1.length : Nat) : Int)).toNat]? = some pe → pe.depth % 2 = 0 → (st.2 ++ [st.1.length]).getLast? = some (((st.1.length : Nat) : Int)).toNat := by
        intro _ _ _
        rw [htn]
        exact flatGetLastAppendSingle st.2 st.1.length
      have hlastI : ∀ pe, (st.1 ++ [(⟨node, par, depth⟩ : Entry)])[(((st.1.length : Nat) : Int)).toNat]? = some pe → pe.depth % 2 = 0 → (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2).getLast? = some (((st.1.length : Nat) : Int)).toNat := by
        rw [hpre]
        exact hlastC
      rw [← hpre] at hinI
      obtain ⟨segE, segO, hchPair, hchLow, hchInv⟩ :=
        ih (children ns node) ((st.1.length : Nat) : Int) (depth + 1)
          ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length)
          (st.1 ++ [(⟨node, par, depth⟩ : Entry)])
          (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2)
          hlen' hfr' hparc' hnn' hinI
      obtain ⟨segE', segO', hstepPair, hstepLow, hstepInv⟩ :=
        flatStep ns up fuel st.1 st.2 node par depth startE
          hP hlen hnn hparc segE segO hchPair hchLow hchInv
      have hst'eq : fstep ns up fuel par depth st node
          = (st.1 ++ segE', st.2 ++ segO') := hstepPair
      have hlenStep : startE ≤ (st.1 ++ segE').length := by
        simp only [List.length_append]
        omega
      have hfrStep : par = -1 ∨ ∃ pe, (st.1 ++ segE')[par.toNat]? = some pe := by
        rcases hfr with h | ⟨pe, hpe⟩
        · exact Or.inl h
        · exact Or.inr ⟨pe, flatPrefixGet st.1 _ ⟨segE', rfl⟩ _ _ hpe⟩
      obtain ⟨segE2, segO2, hrestPair, hrestLow, hrestInv⟩ :=
        ihrest (st.1 ++ segE', st.2 ++ segO') hstepInv hlenStep hfrStep
      refine ⟨segE' ++ segE2, segO' ++ segO2, ?_, ?_, ?_⟩
      · show rest.foldl (fstep ns up fuel par depth)
            (fstep ns up fuel par depth st node) = _
        rw [hst'eq, hrestPair]
        show ((st.1 ++ segE') ++ segE2, (st.2 ++ segO') ++ segO2) = _
        simp only [List.append_assoc]
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hstepLow _ hw
        · exact hrestLow _ hw
      · have hE : (st.1 ++ segE') ++ segE2 = st.1 ++ (segE' ++ segE2) :=
          List.append_assoc _ _ _
        have hO : (st.2 ++ segO') ++ segO2 = st.2 ++ (segO' ++ segO2) :=
          List.append_assoc _ _ _
        have hrestInv' : FlatInv ((st.1 ++ segE') ++ segE2)
            ((st.2 ++ segO') ++ segO2) par startE := hrestInv
        rw [hE, hO] at hrestInv'
        exact hrestInv'
    · have hpre : (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2)
          = st.2 := by simp [hev]
      have hinI : FlatInv (st.1 ++ [(⟨node, par, depth⟩ : Entry)]) st.2
          ((st.1.length : Nat) : Int)
          ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length) := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact boundsEntry _ _ _ _ _ hP.bounds
        · exact hP.noDup
        · exact covEntryOdd _ _ _ _ _ hP.cov hP.bounds hev
        · exact beforeEntry _ _ _ _ hP.before hnn hfr
        · intro hcon
          omega
        · intro p hp x xe hxs hlook
          have hlt := (List.getElem?_eq_some_iff.mp hlook).1
          omega
        · intro x xe hxs hlook
          have hlt := (List.getElem?_eq_some_iff.mp hlook).1
          omega
        · exact winEntry _ _ _ _ _ hP.win hP.bounds
        · refine Or.inr (by
            intro pa px v hpa hpx hle
            have hfrF : st.1.length ∉ st.2 := by
              intro hm
              have h := hP.bounds _ hm
              omega
            exfalso
            have hmem : ((((st.1.length : Nat) : Int)).toNat) ∈ st.2 :=
              List.mem_of_getElem? hpa
            rw [htn] at hmem
            exact hfrF hmem)
      have hlen' : (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length ≤ (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length := by omega
      have hfr' : ((st.1.length : Nat) : Int) = -1 ∨ ∃ pe, (st.1 ++ [(⟨node, par, depth⟩ : Entry)])[(((st.1.length : Nat) : Int)).toNat]? = some pe := Or.inr ⟨_, by rw [htn]; exact freshLookup st.1 node par depth⟩
      have hparc' : ((st.1.length : Nat) : Int) = -1 ∨
          ((((st.1.length : Nat) : Int)).toNat)
            < (st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length := by
        refine Or.inr (by rw [htn]; omega)
      have hnn' : ((st.1.length : Nat) : Int) = -1 ∨
          0 ≤ ((st.1.length : Nat) : Int) := Or.inr (by omega)
      have hlastC : ∀ pe, (st.1 ++ [(⟨node, par, depth⟩ : Entry)])[(((st.1.length : Nat) : Int)).toNat]? = some pe → pe.depth % 2 = 0 → st.2.getLast? = some (((st.1.length : Nat) : Int)).toNat := by
        intro pe hpe hpeven
        rw [htn] at hpe
        have heq : pe = (⟨node, par, depth⟩ : Entry) :=
          Option.some.inj (hpe.symm.trans (freshLookup st.1 node par depth))
        have hodd' : (⟨node, par, depth⟩ : Entry).depth % 2 ≠ 0 := hev
        exact absurd (heq ▸ hpeven) hodd'
      have hlastI : ∀ pe, (st.1 ++ [(⟨node, par, depth⟩ : Entry)])[(((st.1.length : Nat) : Int)).toNat]? = some pe → pe.depth % 2 = 0 → (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2).getLast? = some (((st.1.length : Nat) : Int)).toNat := by
        rw [hpre]
        exact hlastC
      rw [← hpre] at hinI
      obtain ⟨segE, segO, hchPair, hchLow, hchInv⟩ :=
        ih (children ns node) ((st.1.length : Nat) : Int) (depth + 1)
          ((st.1 ++ [(⟨node, par, depth⟩ : Entry)]).length)
          (st.1 ++ [(⟨node, par, depth⟩ : Entry)])
          (if depth % 2 == 0 then st.2 ++ [st.1.length] else st.2)
          hlen' hfr' hparc' hnn' hinI
      obtain ⟨segE', segO', hstepPair, hstepLow, hstepInv⟩ :=
        flatStep ns up fuel st.1 st.2 node par depth startE
          hP hlen hnn hparc segE segO hchPair hchLow hchInv
      have hst'eq : fstep ns up fuel par depth st node
          = (st.1 ++ segE', st.2 ++ segO') := hstepPair
      have hlenStep : startE ≤ (st.1 ++ segE').length := by
        simp only [List.length_append]
        omega
      have hfrStep : par = -1 ∨ ∃ pe, (st.1 ++ segE')[par.toNat]? = some pe := by
        rcases hfr with h | ⟨pe, hpe⟩
        · exact Or.inl h
        · exact Or.inr ⟨pe, flatPrefixGet st.1 _ ⟨segE', rfl⟩ _ _ hpe⟩
      obtain ⟨segE2, segO2, hrestPair, hrestLow, hrestInv⟩ :=
        ihrest (st.1 ++ segE', st.2 ++ segO') hstepInv hlenStep hfrStep
      refine ⟨segE' ++ segE2, segO' ++ segO2, ?_, ?_, ?_⟩
      · show rest.foldl (fstep ns up fuel par depth)
            (fstep ns up fuel par depth st node) = _
        rw [hst'eq, hrestPair]
        show ((st.1 ++ segE') ++ segE2, (st.2 ++ segO') ++ segO2) = _
        simp only [List.append_assoc]
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hstepLow _ hw
        · exact hrestLow _ hw
      · have hE : (st.1 ++ segE') ++ segE2 = st.1 ++ (segE' ++ segE2) :=
          List.append_assoc _ _ _
        have hO : (st.2 ++ segO') ++ segO2 = st.2 ++ (segO' ++ segO2) :=
          List.append_assoc _ _ _
        have hrestInv' : FlatInv ((st.1 ++ segE') ++ segE2)
            ((st.2 ++ segO') ++ segO2) par startE := hrestInv
        rw [hE, hO] at hrestInv'
        exact hrestInv'

theorem flatInvFlatten (ns : List Tree.Node) (up : Bool) (fuel : Nat) :
    ∀ (ids : List Nat) (par : Int) (depth startE : Nat) (es : List Entry)
      (os : List Nat),
      startE ≤ es.length →
      (par = -1 ∨ ∃ pe, es[par.toNat]? = some pe) →
      (par = -1 ∨ par.toNat < startE) →
      (par = -1 ∨ 0 ≤ par) →
      FlatInv es os par startE →
      ∃ segE segO, flatten ns up fuel ids par depth es os
        = (es ++ segE, os ++ segO) ∧
        (∀ w ∈ segO, startE ≤ w) ∧ FlatInv (es ++ segE) (os ++ segO) par startE := by
  induction fuel with
  | zero =>
    intro ids par depth startE es os hlen hfr hparc hnn hinv
    exact ⟨[], [], by simp [flatten], by intro w hw; simp at hw,
      by simpa using hinv⟩
  | succ fuel ih =>
    intro ids par depth startE es os hlen hfr hparc hnn hinv
    rw [flatSuccFold]
    exact flatFold ns up fuel par depth startE hnn hparc ih _
      (es, os) hinv hlen hfr

theorem hardBDeeperOrdInterval' (ns : List Tree.Node) (cause k : Nat) :
    HardBDeeperOrdInterval ns cause k := by
  intro a d j ae de J pa pd pj hae hed hej hpar heven hpa hpd hpj h1 h2
  have hfields := (generated_rib_fields ns cause k).2.2.1
  have he : (generatedRib ns (cause, k)).entries =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1 :=
    congrArg Prod.fst hfields
  have ho : (generatedRib ns (cause, k)).order =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).2 :=
    congrArg Prod.snd hfields
  obtain ⟨segE, segO, hflat, _hsegB, hinv⟩ :=
    flatInvFlatten ns (upper k) 64 (children ns cause) (-1) 2 0 [] []
      (by simp) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) flatInvNil
  have hfst : (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1
      = segE := by
    have := congrArg Prod.fst hflat
    simpa using this
  have hsnd : (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).2
      = segO := by
    have := congrArg Prod.snd hflat
    simpa using this
  have heE : (generatedRib ns (cause, k)).entries = segE := by rw [he, hfst]
  have hoO : (generatedRib ns (cause, k)).order = segO := by rw [ho, hsnd]
  have hae' : segE[a]? = some ae := by rw [← heE]; exact hae
  have hed' : segE[d]? = some de := by rw [← heE]; exact hed
  have hej' : segE[j]? = some J := by rw [← heE]; exact hej
  have hpa' : segO[pa.2]? = some a := by
    have := flatFoundSlot _ a pa hpa
    rwa [hoO] at this
  have hpd' : segO[pd.2]? = some d := by
    have := flatFoundSlot _ d pd hpd
    rwa [hoO] at this
  have hpj' : segO[pj.2]? = some j := by
    have := flatFoundSlot _ j pj hpj
    rwa [hoO] at this
  have hwin := hinv.win a d j ae de J pa.2 pj.2 pd.2 hae' hed' hej' hpar heven
    hpa' hpj' hpd' h1 h2
  rcases hwin with h | h
  · exact Or.inl h
  · apply Or.inr
    rw [heE]
    simpa using h

end Elegant.Ishikawa

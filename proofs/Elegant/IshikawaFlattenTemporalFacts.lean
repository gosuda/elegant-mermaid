import Elegant.IshikawaFlattenParentFacts
import Elegant.IshikawaOrthogonalityFacts

set_option autoImplicit false

namespace Elegant.Ishikawa

private def declarationDepth (ns : List Tree.Node) (i : Nat) : Nat :=
  match Tree.parentOf ns i with
  | none => 0
  | some parent =>
    if _h : parent < i then declarationDepth ns parent + 1 else 0
termination_by i

decreasing_by omega

private def declarationDepths (ns : List Tree.Node) : List Nat :=
  (List.range ns.length).map (declarationDepth ns)

private theorem declarationDepths_lookup (ns : List Tree.Node) (i : Nat)
    (hi : i < ns.length) :
    (declarationDepths ns)[i]? = some (declarationDepth ns i) := by
  simp only [declarationDepths, List.getElem?_map, List.getElem?_range hi,
    Option.map_some]

private theorem declarationDepths_children (ns : List Tree.Node)
    (hlink : Tree.link ns = true) (parent depth : Nat)
    (hp : (declarationDepths ns)[parent]? = some depth)
    (node : Nat) (hc : node ∈ children ns parent) :
    (declarationDepths ns)[node]? = some (depth + 1) := by
  have hc' := List.mem_filter.mp hc
  have hn : node < ns.length := List.mem_range.mp hc'.1
  have hparent : Tree.parentOf ns node = some parent := by
    unfold Tree.parentOf
    cases he : ns[node]? with
    | none => simp [he] at hc'
    | some n => simpa [he] using hc'.2
  have hlt := (Tree.link_valid hlink).parentLt node parent hparent
  have hpb : parent < ns.length := by
    have hb := (List.getElem?_eq_some_iff.mp hp).choose
    simpa only [declarationDepths, List.length_map, List.length_range] using hb
  have he := declarationDepths_lookup ns parent hpb
  rw [hp] at he
  have hd : depth = declarationDepth ns parent := Option.some.inj he
  rw [declarationDepths_lookup ns node hn]
  congr 1
  rw [declarationDepth, hparent]
  simp only [dite_eq_left hlt, hd]

private theorem generated_declaration_depth_lookup (ns : List Tree.Node)
    (cause k : Nat) (hlink : Tree.link ns = true)
    (hcause : cause ∈ children ns 0) :
    ∀ e ∈ (generatedRib ns (cause, k)).entries,
      (declarationDepths ns)[e.node]? = some e.depth := by
  have hc := List.mem_filter.mp hcause
  have hcauseBound : cause < ns.length := List.mem_range.mp hc.1
  have hzero : 0 < ns.length := by omega
  have hroot : (declarationDepths ns)[0]? = some 0 := by
    rw [declarationDepths_lookup ns 0 hzero, declarationDepth,
      (Tree.link_valid hlink).rootNone]
  have h := cause_and_flatten_depth_lookup ns (declarationDepths ns) hroot
    (declarationDepths_children ns hlink) cause k hcause
  intro e he
  have hentries : (generatedRib ns (cause, k)).entries =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1 := by
    have hg := generated_rib_fields ns cause k
    exact congrArg Prod.fst hg.2.2.1
  exact h.2 e (hentries ▸ he)

theorem generated_parent_child_depth (ns : List Tree.Node) (cause k : Nat)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (parent child : Entry) (parentIdx childIdx : Nat)
    (hparent : (parent, parentIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hchild : (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hpar : child.parent = (parentIdx : Int)) :
    child.depth = parent.depth + 1 := by
  have hp : parent ∈ (generatedRib ns (cause, k)).entries :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hparent)
  have hc : child ∈ (generatedRib ns (cause, k)).entries :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hchild)
  have hdepth := generated_declaration_depth_lookup ns cause k hlink hcause
  have hstep := declarationDepths_children ns hlink parent.node parent.depth
    (hdepth parent hp) child.node
    (generated_parent_child_membership ns cause k parent child parentIdx childIdx
      hparent hchild hpar)
  rw [hdepth child hc] at hstep
  exact Option.some.inj hstep

theorem generated_root_depth (ns : List Tree.Node) (cause k : Nat)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (e : Entry) (i : Nat)
    (he : (e, i) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hroot : e.parent = -1) : e.depth = 2 := by
  have hcauseBound : cause < ns.length :=
    List.mem_range.mp (List.mem_filter.mp hcause).1
  have hz : 0 < ns.length := by omega
  have hzero : (declarationDepths ns)[0]? = some 0 := by
    rw [declarationDepths_lookup ns 0 hz, declarationDepth,
      (Tree.link_valid hlink).rootNone]
  have hc := declarationDepths_children ns hlink 0 0 hzero cause hcause
  have hn := generated_root_child_membership ns cause k e i he hroot
  have hd := declarationDepths_children ns hlink cause 1 hc e.node hn
  have hm := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he)
  rw [generated_declaration_depth_lookup ns cause k hlink hcause e hm] at hd
  exact Option.some.inj hd

inductive IndexedAncestor (entries : List Entry) : Nat → Nat → Prop where
  | edge (parentIdx childIdx : Nat) (child : Entry)
      (hchild : entries[childIdx]? = some child)
      (hparent : child.parent = (parentIdx : Int)) :
      IndexedAncestor entries parentIdx childIdx
  | tail {a b c : Nat} (hab : IndexedAncestor entries a b) (child : Entry)
      (hchild : entries[c]? = some child) (hparent : child.parent = (b : Int)) :
      IndexedAncestor entries a c

private def ParentBefore (entries : List Entry) : Prop :=
  ∀ i e, entries[i]? = some e →
    e.parent = -1 ∨ ∃ parentIdx : Nat, e.parent = (parentIdx : Int) ∧ parentIdx < i

private theorem indexedAncestor_lt (es : List Entry) (hb : ParentBefore es)
    {a c : Nat} (h : IndexedAncestor es a c) : a < c := by
  induction h with
  | edge c e he hp =>
    rcases hb c e he with hr | ⟨p, hp', hlt⟩
    · omega
    · have heq : p = a := by omega
      omega
  | tail hab e he hp ih =>
    rcases hb _ e he with hr | ⟨p, hp', hlt⟩ <;> omega

private theorem prefix_lookup {α : Type} (a b : List α) (hp : a <+: b)
    (i : Nat) (v : α) (hi : a[i]? = some v) : b[i]? = some v := by
  rcases hp with ⟨rest, rfl⟩
  have hb := (List.getElem?_eq_some_iff.mp hi).choose
  rw [List.getElem?_append_left hb]
  exact hi

private theorem prefix_lookup_back {α : Type} (a b : List α) (hp : a <+: b)
    (i : Nat) (hi : i < a.length) : b[i]? = a[i]? := by
  rcases hp with ⟨rest, rfl⟩
  exact List.getElem?_append_left hi

private theorem indexedAncestor_restrict (a b : List Entry) (hp : a <+: b)
    (hb : ParentBefore b) {i j : Nat} (h : IndexedAncestor b i j)
    (hj : j < a.length) : IndexedAncestor a i j := by
  revert hj
  induction h with
  | edge j e he hpar =>
    intro hj
    exact IndexedAncestor.edge i j e
      (by rw [prefix_lookup_back a b hp j hj] at he; exact he) hpar
  | @tail mid j him e he hpar ih =>
    intro hj
    have hmid : mid < j := by
      exact indexedAncestor_lt b hb (IndexedAncestor.edge mid j e he hpar)
    exact IndexedAncestor.tail (ih (by omega)) e
      (by rw [prefix_lookup_back a b hp j hj] at he; exact he) hpar

private theorem indexedAncestor_last (es : List Entry) {a c : Nat}
    (h : IndexedAncestor es a c) :
    ∃ (p : Nat) (e : Entry), es[c]? = some e ∧ e.parent = (p : Int) ∧
      (a = p ∨ IndexedAncestor es a p) := by
  cases h with
  | edge c e he hp => exact ⟨a, e, he, hp, Or.inl rfl⟩
  | @tail b c hab e he hp => exact ⟨b, e, he, hp, Or.inr hab⟩

private structure TemporalState (es : List Entry) (os : List Nat) : Prop where
  before : ParentBefore es
  bound : ∀ i ∈ os, i < es.length
  ordered : ∀ (a c : Nat) (parent : Entry),
    es[a]? = some parent → IndexedAncestor es a c →
    ∀ (parentPos childPos : Nat), os[parentPos]? = some a → os[childPos]? = some c →
      (parent.depth % 2 = 0 → parentPos < childPos) ∧
      (parent.depth % 2 ≠ 0 → childPos < parentPos)

private def ActiveOwner (es : List Entry) (os : List Nat) (par : Int) : Prop :=
  par = -1 ∨ ∃ (p : Nat) (parent : Entry), es[p]? = some parent ∧ par = (p : Int) ∧
    ∀ a ancestor, es[a]? = some ancestor → (a = p ∨ IndexedAncestor es a p) →
      ancestor.depth % 2 ≠ 0 → a ∉ os

private def Advance (es : List Entry) (os : List Nat)
    (nextEntries : List Entry) (nextOrder : List Nat) : Prop :=
  es <+: nextEntries ∧ ∀ i, i < es.length → i ∈ nextOrder → i ∈ os

private theorem advance_refl (es : List Entry) (os : List Nat) : Advance es os es os :=
  ⟨⟨[], by simp⟩, fun _ _ hm => hm⟩

private theorem advance_trans (es mid out : List Entry) (os ms fs : List Nat)
    (hfirst : Advance es os mid ms) (hsecond : Advance mid ms out fs) :
    Advance es os out fs := by
  refine ⟨hfirst.1.trans hsecond.1, ?_⟩
  intro i hi hm
  exact hfirst.2 i hi (hsecond.2 i (Nat.lt_of_lt_of_le hi hfirst.1.length_le) hm)

private theorem append_lookup_cases {α : Type} (xs : List α) (v : α)
    (i : Nat) (out : α) (h : (xs ++ [v])[i]? = some out) :
    xs[i]? = some out ∨ i = xs.length ∧ out = v := by
  by_cases hi : i < xs.length
  · exact Or.inl (by rw [List.getElem?_append_left hi] at h; exact h)
  · rw [List.getElem?_append_right (by omega), List.getElem?_singleton] at h
    split at h
    · exact Or.inr ⟨by omega, (Option.some.inj h).symm⟩
    · cases h

private theorem active_advance (es nextEntries : List Entry) (os nextOrder : List Nat)
    (par : Int) (ha : ActiveOwner es os par)
    (hf : Advance es os nextEntries nextOrder) (hb : ParentBefore nextEntries) :
    ActiveOwner nextEntries nextOrder par := by
  rcases ha with hr | ⟨p, parent, hp, hpar, hodd⟩
  · exact Or.inl hr
  · refine Or.inr ⟨p, parent, prefix_lookup es nextEntries hf.1 p parent hp, hpar, ?_⟩
    intro a ancestor ha hanc hdepth hm
    have hpb := (List.getElem?_eq_some_iff.mp hp).choose
    have hab : a < es.length := by
      rcases hanc with rfl | hanc
      · exact hpb
      · have hlt := indexedAncestor_lt nextEntries hb hanc
        omega
    have halook : es[a]? = some ancestor := by
      rw [prefix_lookup_back es nextEntries hf.1 a hab] at ha
      exact ha
    apply hodd a ancestor halook _ hdepth (hf.2 a hab hm)
    rcases hanc with heq | hanc
    · exact Or.inl heq
    · exact Or.inr (indexedAncestor_restrict es nextEntries hf.1 hb hanc hpb)

private theorem temporal_append_entry (es : List Entry) (os : List Nat)
    (node : Nat) (par : Int) (depth : Nat)
    (hs : TemporalState es os) (ha : ActiveOwner es os par) :
    TemporalState (es ++ [⟨node, par, depth⟩]) os := by
  let e : Entry := ⟨node, par, depth⟩
  have hp : es <+: es ++ [e] := ⟨_, rfl⟩
  have hb : ParentBefore (es ++ [e]) := by
    intro i out hi
    rcases append_lookup_cases es e i out hi with hold | ⟨rfl, rfl⟩
    · exact hs.before i out hold
    · rcases ha with hr | ⟨p, parent, hparent, hpar, _⟩
      · exact Or.inl hr
      · exact Or.inr ⟨p, hpar, (List.getElem?_eq_some_iff.mp hparent).choose⟩
  refine ⟨hb, ?_, ?_⟩
  · intro i hi
    have hi' := hs.bound i hi
    simp only [List.length_append, List.length_singleton]
    omega
  · intro a c parent hparent hanc pp cp hpp hcp
    have hab := hs.bound a (List.mem_of_getElem? hpp)
    have hcb := hs.bound c (List.mem_of_getElem? hcp)
    have hparentOld : es[a]? = some parent := by
      rw [prefix_lookup_back es (es ++ [e]) hp a hab] at hparent
      exact hparent
    exact hs.ordered a c parent hparentOld
      (indexedAncestor_restrict es (es ++ [e]) hp hb hanc hcb) pp cp hpp hcp

private theorem active_new_entry (es : List Entry) (os : List Nat)
    (node : Nat) (par : Int) (depth : Nat)
    (hs : TemporalState es os) (ha : ActiveOwner es os par) :
    ActiveOwner (es ++ [⟨node, par, depth⟩]) os (es.length : Int) := by
  let e : Entry := ⟨node, par, depth⟩
  have hp : es <+: es ++ [e] := ⟨_, rfl⟩
  have hb := (temporal_append_entry es os node par depth hs ha).before
  refine Or.inr ⟨es.length, e, by simp [e], rfl, ?_⟩
  intro a ancestor halook hanc hodd hm
  have hab : a < es.length := hs.bound a hm
  rcases hanc with heq | hanc
  · omega
  · obtain ⟨p, child, hc, hpar, hprev⟩ := indexedAncestor_last _ hanc
    have hchild : child = e := by
      have he : (es ++ [e])[es.length]? = some e := by simp
      rw [he] at hc
      exact (Option.some.inj hc).symm
    subst child
    rcases ha with hr | ⟨p0, parent, hp0, hpar0, hold⟩
    · change par = (p : Int) at hpar
      omega
    · have heq : p = p0 := by
        change par = (p : Int) at hpar
        omega
      subst p
      have hpb := (List.getElem?_eq_some_iff.mp hp0).choose
      have haOld : es[a]? = some ancestor := by
        rw [prefix_lookup_back es (es ++ [e]) hp a hab] at halook
        exact halook
      apply hold a ancestor haOld _ hodd hm
      rcases hprev with heq | hprev
      · exact Or.inl heq
      · exact Or.inr (indexedAncestor_restrict es (es ++ [e]) hp hb hprev hpb)

private theorem active_append_even (es : List Entry) (os : List Nat)
    (i : Nat) (e : Entry) (hi : es[i]? = some e)
    (heven : e.depth % 2 = 0) (ha : ActiveOwner es os (i : Int)) :
    ActiveOwner es (os ++ [i]) (i : Int) := by
  rcases ha with hr | ⟨p, parent, hp, hpar, hold⟩
  · omega
  · refine Or.inr ⟨p, parent, hp, hpar, ?_⟩
    intro a ancestor ha hanc hodd hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hold a ancestor ha hanc hodd hm
    · have hai : a = i := by simpa using hm
      subst a
      rw [hi] at ha
      have heq := Option.some.inj ha
      subst ancestor
      exact hodd heven

private theorem temporal_append_slot (es : List Entry) (os : List Nat)
    (i : Nat) (e : Entry) (hi : es[i]? = some e)
    (hs : TemporalState es os) (ha : ActiveOwner es os (i : Int))
    (hout : e.depth % 2 = 0 → ∀ c, IndexedAncestor es i c → c ∉ os) :
    TemporalState es (os ++ [i]) := by
  have hodd : ∀ a ancestor, es[a]? = some ancestor → IndexedAncestor es a i →
      ancestor.depth % 2 ≠ 0 → a ∉ os := by
    rcases ha with hr | ⟨p, parent, hp, hpar, hold⟩
    · omega
    · have hpi : p = i := by omega
      subst p
      intro a ancestor halook hanc hd
      exact hold a ancestor halook (Or.inr hanc) hd
  refine ⟨hs.before, ?_, ?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact hs.bound j hj
    · have heq : j = i := by simpa using hj
      subst j
      exact (List.getElem?_eq_some_iff.mp hi).choose
  · intro a c parent hparent hanc pp cp hpp hcp
    rcases append_lookup_cases os i pp a hpp with hpp | ⟨hpp, hai⟩
    · rcases append_lookup_cases os i cp c hcp with hcp | ⟨hcp, hci⟩
      · exact hs.ordered a c parent hparent hanc pp cp hpp hcp
      · subst c
        refine ⟨?_, ?_⟩
        · intro _
          have hb := (List.getElem?_eq_some_iff.mp hpp).choose
          omega
        · intro hd
          exact False.elim (hodd a parent hparent hanc hd (List.mem_of_getElem? hpp))
    · subst a
      rw [hi] at hparent
      have heq := Option.some.inj hparent
      subst parent
      rcases append_lookup_cases os i cp c hcp with hcp | ⟨hcp, hci⟩
      · refine ⟨?_, ?_⟩
        · intro hd
          exact False.elim (hout hd c hanc (List.mem_of_getElem? hcp))
        · intro _
          have hb := (List.getElem?_eq_some_iff.mp hcp).choose
          omega
      · have hlt := indexedAncestor_lt es hs.before hanc
        omega

private theorem fold_execution {α : Type} (step : α → Nat → α)
    (P : α → Prop) (R : α → α → Prop)
    (hrefl : ∀ st, R st st)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hstep : ∀ st node, P st → P (step st node) ∧ R st (step st node))
    (ids : List Nat) (st : α) (hp : P st) :
    P (ids.foldl step st) ∧ R st (ids.foldl step st) := by
  induction ids generalizing st with
  | nil => exact ⟨hp, hrefl st⟩
  | cons node rest ih =>
    have hs := hstep st node hp
    have ht := ih (step st node) hs.1
    exact ⟨ht.1, htrans st _ _ hs.2 ht.2⟩

private theorem flatten_temporal (ns : List Tree.Node) (up : Bool) (fuel : Nat) :
    ∀ (ids : List Nat) (par : Int) (depth : Nat) (es : List Entry) (os : List Nat),
      TemporalState es os → ActiveOwner es os par →
      TemporalState (flatten ns up fuel ids par depth es os).1
        (flatten ns up fuel ids par depth es os).2 ∧
      Advance es os (flatten ns up fuel ids par depth es os).1
        (flatten ns up fuel ids par depth es os).2 := by
  induction fuel with
  | zero =>
    intro ids par depth es os hs _
    exact ⟨hs, advance_refl es os⟩
  | succ fuel ih =>
    intro ids par depth es os hs ha
    let step : List Entry × List Nat → Nat → List Entry × List Nat := fun st node =>
      let idx := st.1.length
      let entries := st.1 ++ [⟨node, par, depth⟩]
      let order := if depth % 2 == 0 then st.2 ++ [idx] else st.2
      let next := flatten ns up fuel (children ns node) (idx : Int) (depth + 1)
        entries order
      (next.1, if depth % 2 == 0 then next.2 else next.2 ++ [idx])
    have hstep : ∀ (st : List Entry × List Nat) (node : Nat),
        TemporalState st.1 st.2 ∧ ActiveOwner st.1 st.2 par →
        (TemporalState (step st node).1 (step st node).2 ∧
          ActiveOwner (step st node).1 (step st node).2 par) ∧
        Advance st.1 st.2 (step st node).1 (step st node).2 := by
      intro st node hst
      rcases st with ⟨es, os⟩
      let e : Entry := ⟨node, par, depth⟩
      let preOrder := if depth % 2 == 0 then os ++ [es.length] else os
      let next := flatten ns up fuel (children ns node) (es.length : Int)
        (depth + 1) (es ++ [e]) preOrder
      let postOrder := if depth % 2 == 0 then next.2 else next.2 ++ [es.length]
      have he : (es ++ [e])[es.length]? = some e := by simp
      have hs0 := temporal_append_entry es os node par depth hst.1 hst.2
      have ha0 := active_new_entry es os node par depth hst.1 hst.2
      have hs1 : TemporalState (es ++ [e]) preOrder := by
        by_cases hd : depth % 2 = 0
        · have hslot := temporal_append_slot (es ++ [e]) os es.length e he hs0 ha0 (by
            intro _ c hanc hm
            have hlt := indexedAncestor_lt (es ++ [e]) hs0.before hanc
            have hbound := hst.1.bound c hm
            change c < es.length at hbound
            omega)
          simpa [preOrder, hd] using hslot
        · simpa [preOrder, hd] using hs0
      have ha1 : ActiveOwner (es ++ [e]) preOrder (es.length : Int) := by
        by_cases hd : depth % 2 = 0
        · have hactive := active_append_even (es ++ [e]) os es.length e he hd ha0
          simpa [preOrder, hd] using hactive
        · simpa [preOrder, hd] using ha0
      have hr := ih (children ns node) (es.length : Int) (depth + 1)
        (es ++ [e]) preOrder hs1 ha1
      have ha2 : ActiveOwner next.1 next.2 (es.length : Int) :=
        active_advance (es ++ [e]) next.1 preOrder next.2 (es.length : Int)
          ha1 hr.2 hr.1.before
      have he2 : next.1[es.length]? = some e :=
        prefix_lookup (es ++ [e]) next.1 hr.2.1 es.length e he
      have hs2 : TemporalState next.1 postOrder := by
        by_cases hd : depth % 2 = 0
        · simpa [postOrder, hd] using hr.1
        · have hslot := temporal_append_slot next.1 next.2 es.length e he2 hr.1 ha2 (by
            intro heven
            exact False.elim (hd heven))
          simpa [postOrder, hd] using hslot
      have hf : Advance es os next.1 postOrder := by
        refine ⟨(show es <+: es ++ [e] from ⟨_, rfl⟩).trans hr.2.1, ?_⟩
        intro i hi hm
        have hm2 : i ∈ next.2 := by
          by_cases hd : depth % 2 = 0
          · simpa [postOrder, hd] using hm
          · have hm' : i ∈ next.2 ∨ i = es.length := by
              simpa [postOrder, hd] using hm
            rcases hm' with hm' | heq
            · exact hm'
            · omega
        have hipre : i < (es ++ [e]).length := by
          simp only [List.length_append, List.length_singleton]
          omega
        have hm1 := hr.2.2 i hipre hm2
        by_cases hd : depth % 2 = 0
        · have hm' : i ∈ os ∨ i = es.length := by simpa [preOrder, hd] using hm1
          rcases hm' with hm' | heq
          · exact hm'
          · omega
        · simpa [preOrder, hd] using hm1
      have hactive := active_advance es next.1 os postOrder par hst.2 hf hs2.before
      exact ⟨⟨hs2, hactive⟩, hf⟩
    let walk := if up then ids.reverse else ids
    have hout := fold_execution step
      (fun st => TemporalState st.1 st.2 ∧ ActiveOwner st.1 st.2 par)
      (fun a b => Advance a.1 a.2 b.1 b.2)
      (fun st => advance_refl st.1 st.2)
      (fun a b c hab hbc => advance_trans a.1 b.1 c.1 a.2 b.2 c.2 hab hbc)
      hstep walk (es, os) ⟨hs, ha⟩
    exact ⟨hout.1.1, hout.2⟩

private theorem generated_temporal_state (ns : List Tree.Node) (cause k : Nat) :
    TemporalState (generatedRib ns (cause, k)).entries
      (generatedRib ns (cause, k)).order := by
  have hinit : TemporalState [] [] := by
    refine ⟨?_, ?_, ?_⟩
    · intro i e hi
      simp at hi
    · intro i hi
      simp at hi
    · intro a c parent hi
      simp at hi
  have hr := flatten_temporal ns (upper k) 64 (children ns cause) (-1) 2 [] []
    hinit (Or.inl rfl)
  have hfields := (generated_rib_fields ns cause k).2.2.1
  have he : (generatedRib ns (cause, k)).entries =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1 :=
    congrArg Prod.fst hfields
  have ho : (generatedRib ns (cause, k)).order =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).2 :=
    congrArg Prod.snd hfields
  rw [he, ho]
  exact hr.1

private theorem found_slot (order : List Nat) (idx : Nat) (position : Nat × Nat)
    (h : order.zipIdx.find? (fun v => v.1 == idx) = some position) :
    order[position.2]? = some idx := by
  have hm := List.mem_of_find?_eq_some h
  have he := List.mem_zipIdx_iff_getElem?.mp hm
  have hi : position.1 = idx := by simpa using List.find?_some h
  simpa only [hi] using he

theorem generated_entry_parent_lower_bound (ns : List Tree.Node) (cause k : Nat)
    (e : Entry) (i : Nat)
    (he : (e, i) ∈ (generatedRib ns (cause, k)).entries.zipIdx) :
    -1 ≤ e.parent := by
  have hlook := List.mem_zipIdx_iff_getElem?.mp he
  rcases (generated_temporal_state ns cause k).before i e hlook with hr | ⟨p, hp, _⟩
  · omega
  · omega

theorem generated_ancestor_order (ns : List Tree.Node) (cause k : Nat)
    (ancestor descendant : Entry) (ancestorIdx descendantIdx : Nat)
    (hancestor : (ancestor, ancestorIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (_hdescendant : (descendant, descendantIdx) ∈
      (generatedRib ns (cause, k)).entries.zipIdx)
    (hchain : IndexedAncestor (generatedRib ns (cause, k)).entries
      ancestorIdx descendantIdx)
    (ancestorPosition descendantPosition : Nat × Nat)
    (hancestorPosition : (generatedRib ns (cause, k)).order.zipIdx.find?
      (fun v => v.1 == ancestorIdx) = some ancestorPosition)
    (hdescendantPosition : (generatedRib ns (cause, k)).order.zipIdx.find?
      (fun v => v.1 == descendantIdx) = some descendantPosition) :
    (ancestor.depth % 2 = 0 → ancestorPosition.2 < descendantPosition.2) ∧
    (ancestor.depth % 2 ≠ 0 → descendantPosition.2 < ancestorPosition.2) := by
  exact (generated_temporal_state ns cause k).ordered ancestorIdx descendantIdx ancestor
    (List.mem_zipIdx_iff_getElem?.mp hancestor) hchain
    ancestorPosition.2 descendantPosition.2
    (found_slot _ ancestorIdx ancestorPosition hancestorPosition)
    (found_slot _ descendantIdx descendantPosition hdescendantPosition)

theorem generated_parent_child_order (ns : List Tree.Node) (cause k : Nat)
    (parent child : Entry) (parentIdx childIdx : Nat)
    (hparent : (parent, parentIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hchild : (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hpar : child.parent = (parentIdx : Int))
    (parentPosition childPosition : Nat × Nat)
    (hparentPosition : (generatedRib ns (cause, k)).order.zipIdx.find?
      (fun v => v.1 == parentIdx) = some parentPosition)
    (hchildPosition : (generatedRib ns (cause, k)).order.zipIdx.find?
      (fun v => v.1 == childIdx) = some childPosition) :
    (parent.depth % 2 = 0 → parentPosition.2 < childPosition.2) ∧
    (parent.depth % 2 ≠ 0 → childPosition.2 < parentPosition.2) := by
  exact generated_ancestor_order ns cause k parent child parentIdx childIdx hparent hchild
    (IndexedAncestor.edge parentIdx childIdx child
      (List.mem_zipIdx_iff_getElem?.mp hchild) hpar)
    parentPosition childPosition hparentPosition hchildPosition

end Elegant.Ishikawa

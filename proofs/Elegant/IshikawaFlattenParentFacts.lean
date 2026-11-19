import Elegant.IshikawaLayoutProvenanceFacts
import Elegant.TreeFacts

set_option autoImplicit false

namespace Elegant.Ishikawa

private theorem child_parent (ns : List Tree.Node) (parent node : Nat)
    (h : node ∈ children ns parent) : Tree.parentOf ns node = some parent := by
  have ht := (List.mem_filter.mp h).2
  unfold Tree.parentOf
  cases hn : ns[node]? with
  | none => simp [hn] at ht
  | some n => simpa [hn] using ht

private theorem children_nodup (ns : List Tree.Node) (parent : Nat) :
    (children ns parent).Nodup := by
  exact List.Nodup.sublist List.filter_sublist List.nodup_range

private def OwnerAt (cause : Nat) (entries : List Entry) (par : Int)
    (ownerNode : Nat) : Prop :=
  (par = -1 ∧ ownerNode = cause) ∨
    ∃ (idx : Nat) (parent : Entry),
      entries[idx]? = some parent ∧ par = (idx : Int) ∧ ownerNode = parent.node

private def Parentage (ns : List Tree.Node) (cause : Nat) (entries : List Entry) : Prop :=
  ∀ e ∈ entries, ∃ ownerNode, OwnerAt cause entries e.parent ownerNode ∧
    e.node ∈ children ns ownerNode

private theorem ownerAt_prefix (cause : Nat) (a b : List Entry)
    (hp : a <+: b) (par : Int) (ownerNode : Nat)
    (ho : OwnerAt cause a par ownerNode) : OwnerAt cause b par ownerNode := by
  rcases ho with hroot | ⟨idx, parent, hi, he, hn⟩
  · exact Or.inl hroot
  · rcases hp with ⟨tail, rfl⟩
    have hb : idx < a.length := (List.getElem?_eq_some_iff.mp hi).choose
    exact Or.inr ⟨idx, parent, by rw [List.getElem?_append_left hb]; exact hi, he, hn⟩

private theorem parentage_append (ns : List Tree.Node) (cause : Nat)
    (es : List Entry) (node : Nat) (par : Int) (depth ownerNode : Nat)
    (he : Parentage ns cause es) (ho : OwnerAt cause es par ownerNode)
    (hc : node ∈ children ns ownerNode) :
    Parentage ns cause (es ++ [⟨node, par, depth⟩]) := by
  have hp : es <+: es ++ [({ node, parent := par, depth } : Entry)] := ⟨_, rfl⟩
  intro e hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨o, hoa, hca⟩ := he e hm
    exact ⟨o, ownerAt_prefix cause _ _ hp _ _ hoa, hca⟩
  · have heq : e = ({ node, parent := par, depth } : Entry) := by simpa using hm
    subst e
    exact ⟨ownerNode, ownerAt_prefix cause _ _ hp _ _ ho, hc⟩

private theorem flatten_parentage (ns : List Tree.Node) (cause : Nat)
    (up : Bool) (fuel : Nat) :
    ∀ (ids : List Nat) (par : Int) (depth : Nat) (es : List Entry) (os : List Nat)
      (ownerNode : Nat),
      Parentage ns cause es → OwnerAt cause es par ownerNode →
      (∀ node ∈ ids, node ∈ children ns ownerNode) →
      es <+: (flatten ns up fuel ids par depth es os).1 ∧
        Parentage ns cause (flatten ns up fuel ids par depth es os).1 := by
  induction fuel with
  | zero =>
    intro ids par depth es os ownerNode he _ _
    exact ⟨⟨[], by simp [flatten]⟩, he⟩
  | succ fuel ih =>
    intro ids par depth es os ownerNode he ho hc
    have hwalk : ∀ (walk : List Nat) (es : List Entry) (os : List Nat),
        Parentage ns cause es → OwnerAt cause es par ownerNode →
        (∀ node ∈ walk, node ∈ children ns ownerNode) →
        es <+: (walk.foldl (fun (es, os) node =>
          let idx := es.length
          let es := es ++ [⟨node, par, depth⟩]
          let os := if depth % 2 == 0 then os ++ [idx] else os
          let next := flatten ns up fuel (children ns node) (idx : Int) (depth + 1) es os
          (next.1, if depth % 2 == 0 then next.2 else next.2 ++ [idx])) (es, os)).1 ∧
        Parentage ns cause (walk.foldl (fun (es, os) node =>
          let idx := es.length
          let es := es ++ [⟨node, par, depth⟩]
          let os := if depth % 2 == 0 then os ++ [idx] else os
          let next := flatten ns up fuel (children ns node) (idx : Int) (depth + 1) es os
          (next.1, if depth % 2 == 0 then next.2 else next.2 ++ [idx])) (es, os)).1 := by
      intro walk
      induction walk with
      | nil => intro es os he _ _; exact ⟨⟨[], by simp⟩, he⟩
      | cons node rest tail =>
        intro es os he ho hc
        have ha := parentage_append ns cause es node par depth ownerNode he ho
          (hc node (by simp))
        have hnew : OwnerAt cause (es ++ [⟨node, par, depth⟩]) (es.length : Int) node := by
          apply Or.inr
          refine ⟨es.length, ⟨node, par, depth⟩, ?_, rfl, rfl⟩
          simp
        have hr := ih (children ns node) (es.length : Int) (depth + 1)
          (es ++ [⟨node, par, depth⟩])
          (if depth % 2 == 0 then os ++ [es.length] else os) node ha hnew
          (fun _ hm => hm)
        have hpre : es <+: (flatten ns up fuel (children ns node) (es.length : Int)
            (depth + 1) (es ++ [⟨node, par, depth⟩])
            (if depth % 2 == 0 then os ++ [es.length] else os)).1 :=
          (show es <+: es ++ [({ node, parent := par, depth } : Entry)] from ⟨_, rfl⟩).trans hr.1
        have ht := tail _
          (if depth % 2 == 0 then
            (flatten ns up fuel (children ns node) (es.length : Int) (depth + 1)
              (es ++ [⟨node, par, depth⟩])
              (if depth % 2 == 0 then os ++ [es.length] else os)).2
          else
            (flatten ns up fuel (children ns node) (es.length : Int) (depth + 1)
              (es ++ [⟨node, par, depth⟩])
              (if depth % 2 == 0 then os ++ [es.length] else os)).2 ++ [es.length])
          hr.2 (ownerAt_prefix cause _ _ hpre _ _ ho)
          (fun n hn => hc n (List.mem_cons_of_mem node hn))
        exact ⟨hpre.trans ht.1, ht.2⟩
    apply hwalk _ es os he ho
    intro node hn
    apply hc node
    cases up <;> simpa using hn

private def Separate (ns : List Tree.Node) (ids : List Nat) : Prop :=
  ∀ a ∈ ids, ∀ b ∈ ids, a ≠ b →
    ∀ d, Tree.Under ns a d → Tree.Under ns b d → False

private theorem children_separate (ns : List Tree.Node)
    (hlt : ∀ c p, Tree.parentOf ns c = some p → p < c) (parent : Nat) :
    Separate ns (children ns parent) := by
  intro a ha b hb hab d had hbd
  exact hab (Tree.under_child_unique hlt (child_parent ns parent a ha)
    (child_parent ns parent b hb) d d (by omega) had hbd)

private theorem flatten_nodes (ns : List Tree.Node)
    (hlt : ∀ c p, Tree.parentOf ns c = some p → p < c)
    (up : Bool) (fuel : Nat) :
    ∀ (ids : List Nat) (par : Int) (depth : Nat) (es : List Entry) (os : List Nat),
      ids.Nodup → Separate ns ids → (es.map Entry.node).Nodup →
      (∀ e ∈ es, ∀ root ∈ ids, ¬ Tree.Under ns root e.node) →
      ((flatten ns up fuel ids par depth es os).1.map Entry.node).Nodup ∧
      (∀ e ∈ (flatten ns up fuel ids par depth es os).1,
        e ∈ es ∨ ∃ root ∈ ids, Tree.Under ns root e.node) := by
  induction fuel with
  | zero =>
    intro ids par depth es os _ _ he _
    exact ⟨he, fun e hm => Or.inl hm⟩
  | succ fuel ih =>
    intro ids par depth es os hi hs he hd
    have hwalk : ∀ (walk : List Nat) (es : List Entry) (os : List Nat),
        walk.Nodup → Separate ns walk → (es.map Entry.node).Nodup →
        (∀ e ∈ es, ∀ root ∈ walk, ¬ Tree.Under ns root e.node) →
        ((walk.foldl (fun (es, os) node =>
          let idx := es.length
          let es := es ++ [⟨node, par, depth⟩]
          let os := if depth % 2 == 0 then os ++ [idx] else os
          let next := flatten ns up fuel (children ns node) (idx : Int) (depth + 1) es os
          (next.1, if depth % 2 == 0 then next.2 else next.2 ++ [idx])) (es, os)).1.map Entry.node).Nodup ∧
        (∀ e ∈ (walk.foldl (fun (es, os) node =>
          let idx := es.length
          let es := es ++ [⟨node, par, depth⟩]
          let os := if depth % 2 == 0 then os ++ [idx] else os
          let next := flatten ns up fuel (children ns node) (idx : Int) (depth + 1) es os
          (next.1, if depth % 2 == 0 then next.2 else next.2 ++ [idx])) (es, os)).1,
          e ∈ es ∨ ∃ root ∈ walk, Tree.Under ns root e.node) := by
      intro walk
      induction walk with
      | nil => intro es os _ _ he _; exact ⟨he, fun e hm => Or.inl hm⟩
      | cons node rest tail =>
        intro es os hi hs he hd
        have hn := List.nodup_cons.mp hi
        have hnew : ((es ++ [({ node, parent := par, depth } : Entry)]).map Entry.node).Nodup := by
          rw [List.map_append]
          apply List.nodup_append.mpr
          refine ⟨he, by simp, ?_⟩
          intro a ha b hb hab
          have hb' : b = node := by simpa using hb
          obtain ⟨e, hem, heq⟩ := List.mem_map.mp ha
          apply hd e hem node (by simp)
          rw [heq, hab, hb']
          exact Tree.Under.refl node
        have hr := ih (children ns node) (es.length : Int) (depth + 1)
          (es ++ [⟨node, par, depth⟩])
          (if depth % 2 == 0 then os ++ [es.length] else os)
          (children_nodup ns node) (children_separate ns hlt node) hnew (by
            intro e hem root hroot hu
            have hp := child_parent ns node root hroot
            rcases List.mem_append.mp hem with hem | hem
            · exact hd e hem node (by simp) (Tree.Under.step hp hu)
            · have heq : e = ({ node, parent := par, depth } : Entry) := by simpa using hem
              subst e
              have hle := hu.le hlt
              have hlt' := hlt root node hp
              simp only at hle
              omega)
        have ht := tail _
          (if depth % 2 == 0 then
            (flatten ns up fuel (children ns node) (es.length : Int) (depth + 1)
              (es ++ [⟨node, par, depth⟩])
              (if depth % 2 == 0 then os ++ [es.length] else os)).2
          else
            (flatten ns up fuel (children ns node) (es.length : Int) (depth + 1)
              (es ++ [⟨node, par, depth⟩])
              (if depth % 2 == 0 then os ++ [es.length] else os)).2 ++ [es.length])
          hn.2
          (fun a ha b hb hab d had hbd => hs a (by simp [ha]) b (by simp [hb]) hab d had hbd)
          hr.1 (by
            intro e hem root hroot hu
            rcases hr.2 e hem with hold | ⟨child, hc, hce⟩
            · rcases List.mem_append.mp hold with hold | hold
              · exact hd e hold root (by simp [hroot]) hu
              · have heq : e = ({ node, parent := par, depth } : Entry) := by simpa using hold
                subst e
                exact hs node (by simp) root (by simp [hroot])
                  (fun heq => hn.1 (by simpa only [heq] using hroot))
                  node (Tree.Under.refl node) hu
            · exact hs node (by simp) root (by simp [hroot])
                (fun heq => hn.1 (by simpa only [heq] using hroot)) e.node
                (Tree.Under.step (child_parent ns node child hc) hce) hu)
        refine ⟨ht.1, ?_⟩
        intro e hem
        rcases ht.2 e hem with hold | ⟨root, hroot, hu⟩
        · rcases hr.2 e hold with hold | ⟨child, hc, hu⟩
          · rcases List.mem_append.mp hold with hold | hold
            · exact Or.inl hold
            · have heq : e = ({ node, parent := par, depth } : Entry) := by simpa using hold
              subst e
              exact Or.inr ⟨node, by simp, Tree.Under.refl node⟩
          · exact Or.inr ⟨node, by simp,
              Tree.Under.step (child_parent ns node child hc) hu⟩
        · exact Or.inr ⟨root, by simp [hroot], hu⟩
    have hw := hwalk (if up then ids.reverse else ids) es os (by
      cases up with
      | false => exact hi
      | true =>
        exact List.pairwise_reverse.mpr (hi.imp fun hne => Ne.symm hne))
      (by
        intro a ha b hb hab d had hbd
        have ha' : a ∈ ids := by cases up <;> simpa using ha
        have hb' : b ∈ ids := by cases up <;> simpa using hb
        exact hs a ha' b hb' hab d had hbd)
      he (by
        intro e hem root hroot
        apply hd e hem root
        cases up <;> simpa using hroot)
    refine ⟨hw.1, ?_⟩
    intro e hem
    rcases hw.2 e hem with hold | ⟨root, hr, hu⟩
    · exact Or.inl hold
    · apply Or.inr
      refine ⟨root, ?_, hu⟩
      cases up <;> simpa using hr

private theorem generated_entries_eq (ns : List Tree.Node) (cause k : Nat) :
    (generatedRib ns (cause, k)).entries =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1 := by
  cases hf : flatten ns (upper k) 64 (children ns cause) (-1) 2 [] [] with
  | mk entries order => simp only [generatedRib, hf]

theorem generated_entry_nodes_nodup (ns : List Tree.Node) (cause k : Nat)
    (hlink : Tree.link ns = true) :
    ((generatedRib ns (cause, k)).entries.map Entry.node).Nodup := by
  rw [generated_entries_eq]
  have h := flatten_nodes ns (Tree.link_valid hlink).parentLt (upper k) 64
    (children ns cause) (-1) 2 [] [] (children_nodup ns cause)
    (children_separate ns (Tree.link_valid hlink).parentLt cause) (by simp)
    (by simp)
  exact h.1

private theorem generated_parentage (ns : List Tree.Node) (cause k : Nat) :
    Parentage ns cause (generatedRib ns (cause, k)).entries := by
  rw [generated_entries_eq]
  have h := flatten_parentage ns cause (upper k) 64 (children ns cause) (-1) 2 [] []
    cause (by simp [Parentage]) (Or.inl ⟨rfl, rfl⟩) (fun _ hm => hm)
  exact h.2

private theorem ownerAt_unique (cause : Nat) (entries : List Entry)
    (par : Int) (owner ownerNode node : Nat)
    (ho : OwnerAt cause entries par node)
    (howner : (owner = 0 ∧ ownerNode = cause) ∨
      ∃ parentEntry parentIdx, (parentEntry, parentIdx) ∈ entries.zipIdx ∧
        owner = parentIdx + 1 ∧ ownerNode = parentEntry.node)
    (hpar : (par + 1).toNat = owner) : node = ownerNode := by
  rcases ho with ⟨hp, hn⟩ | ⟨idx, parent, hi, hp, hn⟩
  · subst par
    change 0 = owner at hpar
    rcases howner with ⟨_, he⟩ | ⟨e, i, _, he, _⟩
    · exact hn.trans he.symm
    · omega
  · subst par
    have hnat : ((idx : Int) + 1).toNat = idx + 1 := by omega
    rw [hnat] at hpar
    rcases howner with ⟨he, _⟩ | ⟨e, i, hm, he, hnode⟩
    · omega
    · have hij : idx = i := by omega
      subst i
      have hi' := List.mem_zipIdx_iff_getElem?.mp hm
      rw [hi] at hi'
      have hep : parent = e := Option.some.inj hi'
      subst e
      exact hn.trans hnode.symm

theorem generated_prefix_odd_child_count_le (ns : List Tree.Node) (cause k : Nat)
    (hlink : Tree.link ns = true) (_hcause : cause ∈ children ns 0)
    (done rest : List (Entry × Nat))
    (hprefix : (generatedRib ns (cause, k)).entries.zipIdx = done ++ rest)
    (owner ownerNode : Nat)
    (howner : (owner = 0 ∧ ownerNode = cause) ∨
      ∃ parentEntry parentIdx,
        (parentEntry, parentIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx ∧
        owner = parentIdx + 1 ∧ ownerNode = parentEntry.node) :
    (done.filter (fun source => (source.1.depth % 2 != 0) &&
      ((source.1.parent + 1).toNat == owner))).length ≤
        (children ns ownerNode).length := by
  let entries := (generatedRib ns (cause, k)).entries
  let selected := done.filter (fun source => (source.1.depth % 2 != 0) &&
    ((source.1.parent + 1).toNat == owner))
  have hsub : List.Sublist selected entries.zipIdx := by
    have hp : done <+: entries.zipIdx := ⟨rest, hprefix.symm⟩
    exact List.filter_sublist.trans hp.sublist
  have hmap : (selected.map (fun source => source.1.node)).Nodup := by
    have hfull : (entries.zipIdx.map (fun source => source.1.node)).Nodup := by
      have he := congrArg (List.map Entry.node) (List.zipIdx_map_fst 0 entries)
      simp only [List.map_map] at he
      change (List.map (Entry.node ∘ Prod.fst) entries.zipIdx).Nodup
      rw [he]
      exact generated_entry_nodes_nodup ns cause k hlink
    exact List.Nodup.sublist (hsub.map _) hfull
  have hbound := hmap.length_le_of_subset (l₂ := children ns ownerNode) (by
    intro node hn
    obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hn
    have hm : source ∈ entries.zipIdx := hsub.subset hs
    have he : source.1 ∈ entries := List.mem_of_getElem?
      (List.mem_zipIdx_iff_getElem?.mp hm)
    obtain ⟨actualOwner, hoa, hc⟩ := generated_parentage ns cause k source.1 he
    have hs' := (List.mem_filter.mp hs).2
    have hpar : (source.1.parent + 1).toNat = owner := by
      simp only [Bool.and_eq_true] at hs'
      simpa using hs'.2
    have ho := ownerAt_unique cause entries source.1.parent owner ownerNode actualOwner
      hoa howner hpar
    simpa only [ho] using hc)
  simpa only [List.length_map] using hbound

theorem generated_parent_child_membership (ns : List Tree.Node) (cause k : Nat)
    (parent child : Entry) (parentIdx childIdx : Nat)
    (hparent : (parent, parentIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hchild : (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hpar : child.parent = (parentIdx : Int)) :
    child.node ∈ children ns parent.node := by
  have he : child ∈ (generatedRib ns (cause, k)).entries :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hchild)
  obtain ⟨actualOwner, ho, hc⟩ := generated_parentage ns cause k child he
  have hnat : (child.parent + 1).toNat = parentIdx + 1 := by
    rw [hpar]
    omega
  have heq := ownerAt_unique cause (generatedRib ns (cause, k)).entries
    child.parent (parentIdx + 1) parent.node actualOwner ho
    (Or.inr ⟨parent, parentIdx, hparent, rfl, rfl⟩) hnat
  simpa only [heq] using hc

theorem generated_root_child_membership (ns : List Tree.Node) (cause k : Nat)
    (e : Entry) (i : Nat)
    (he : (e, i) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hroot : e.parent = -1) : e.node ∈ children ns cause := by
  have hm : e ∈ (generatedRib ns (cause, k)).entries :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he)
  obtain ⟨ownerNode, ho, hc⟩ := generated_parentage ns cause k e hm
  rcases ho with ⟨_, hn⟩ | ⟨idx, parent, _, hp, _⟩
  · simpa only [hn] using hc
  · rw [hroot] at hp
    omega

end Elegant.Ishikawa

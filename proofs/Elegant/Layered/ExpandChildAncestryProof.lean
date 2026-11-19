import Elegant.Layered.RecursiveC1C3
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.ExpandChildC2Facts
import Elegant.Layered.ExpandChildC6StepFacts
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.MergedAncestorsProof
import Elegant.Layered.MergedRouteIdsProof
import Elegant.DumpLaminar

set_option autoImplicit false

/-!
# Ancestry of the recursive `expandChild` steps

For one `expandChild` call inside `layoutRecursive`, the C6 step needs
`ExpandChildC6Anchors` (every child route endpoint carries the expanded
group's scope anchors in the merged dump) and the C8a step needs
`ExpandChildC8aAncestry` (every embedded child box carries those anchors,
and the group is isolated from the other parent boxes).  Both follow from
one general transport lemma proved here,
`expandChild_merged_anchors_of_child`: a box of the embedded child scene
has `group.id` and every parent-scene ancestor of `group.id` among its
merged-dump ancestors.  The group case alone is `expandChild_child_ancestors_group`.

The proof uses only the expansion's assembly facts (`expandChild_sources`,
`expandChild_selected_ids`, `expandChild_boxLookup_transport`,
`expandChild_merge_bounds`), the proved ancestor monotonicity
(`expandChild_ancestor_mono`), and two narrow scene-ancestry residuals below,
each true for executed layouts (scene ids and route endpoints mirror the
selected sub-input models, whose well-formedness and coverage the recursion
supplies) and each strictly simpler than the cross-scene conclusions they
serve.  Every residual is pinned to the executed call by the
`ExpandChildCallContext` hypothesis of the theorems that consume it.
Isolation (`ExpandChildGroupIsolated`) is proved here from the parent mirror
and `inside_of_parent`, so `expandChild_c8a_ancestry` keeps only the two
run-pinned residuals as hypotheses.
-/

namespace Elegant.Layered.PipelineImpl

open Validator

/-- The expanded group is isolated from the other parent boxes: no other
parent-scene box has the group among its ancestors.  Scene parents mirror
model parents, and a model box whose parent is the group lies inside the
group, hence outside the parent sub-input. -/
def ExpandChildGroupIsolated (group : ModelBox) (parent : FamilyResult) : Prop :=
  ∀ pb ∈ parent.scene.boxes, pb.id ≠ group.id →
    group.id ∉ parent.scene.layoutDump.ancestors pb.id

/-! ### Ancestor-walk toolkit for `LayoutDump.ancestors.go` -/

/-- One unfolded step of the ancestor walk. -/
private theorem go_succ {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hne : b.parent ≠ "") :
    LayoutDump.ancestors.go d (k + 1) s =
      b.parent :: LayoutDump.ancestors.go d k b.parent := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hne, ↓reduceIte]

/-- The ancestor walk from a missing id is empty. -/
private theorem go_none {d : LayoutDump} {k : Nat} {s : String}
    (h : d.box? s = none) :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = none := h
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind]

/-- The ancestor walk from a root box is empty. -/
private theorem go_root {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hpar : b.parent = "") :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar, ↓reduceIte]

/-- Fuel monotonicity of the ancestor walk. -/
private theorem ancestors_go_mono {d : LayoutDump} {k k' : Nat} (hle : k ≤ k')
    {s x : String} (hm : x ∈ LayoutDump.ancestors.go d k s) :
    x ∈ LayoutDump.ancestors.go d k' s := by
  induction k' generalizing k s x with
  | zero =>
    have hk : k = 0 := Nat.le_zero.mp hle
    subst hk
    cases hm
  | succ k' ih =>
    cases k with
    | zero => cases hm
    | succ k =>
      have hkk : k ≤ k' := Nat.le_of_succ_le_succ hle
      cases h : d.box? s with
      | none =>
        have e1 := go_none (d := d) (k := k) (s := s) h
        rw [e1] at hm
        cases hm
      | some b =>
        by_cases hp : b.parent = ""
        · have e1 := go_root (d := d) (k := k) (s := s) (b := b) h hp
          rw [e1] at hm
          cases hm
        · have e1 := go_succ (d := d) (k := k) (s := s) (b := b) h hp
          have e2 := go_succ (d := d) (k := k') (s := s) (b := b) h hp
          rw [e1] at hm
          rw [e2]
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact List.mem_cons.mpr (Or.inl rfl)
          · exact List.mem_cons_of_mem _ (ih hkk hm')

/-- A single-parent-step chain. -/
 inductive StepChain (R : String → String → Prop) : List String → Prop where
  | nil : StepChain R []
  | single (a : String) : StepChain R [a]
  | cons {a b : String} {rest : List String} : R a b → StepChain R (b :: rest) → StepChain R (a :: b :: rest)

/-- Every tail member of a step chain lies on the ancestor walk from its
head, with fuel one less than the chain length. -/
private theorem mem_of_stepChain {d : LayoutDump} (c : List String)
    (hchain : StepChain
      (fun s t => ∃ b, d.box? s = some b ∧ b.parent = t ∧ t ≠ "") c)
    (s x : String) (hhead : c.head? = some s) (htail : x ∈ c.tail) :
    x ∈ LayoutDump.ancestors.go d (c.length - 1) s := by
  induction hchain generalizing s x with
  | nil => simp at hhead
  | single a => simp at htail
  | cons hab htailChain ih =>
    rename_i a b rest
    have hs : a = s := by simpa using hhead
    subst hs
    have hlen : (a :: b :: rest).length - 1 = rest.length + 1 := by simp
    rw [hlen]
    obtain ⟨box, hbox, hpar, hne⟩ := hab
    have hne' : box.parent ≠ "" := by rw [hpar]; exact hne
    have hgo := go_succ (d := d) (k := rest.length) (s := a) (b := box) hbox hne'
    rw [hpar] at hgo
    rw [hgo]
    have htail' : x ∈ b :: rest := htail
    rcases List.mem_cons.mp htail' with rfl | hmem
    · exact List.mem_cons.mpr (Or.inl rfl)
    · have hmem' : x ∈ (b :: rest).tail := hmem
      have hhead' : (b :: rest).head? = some b := by simp
      have hmemgo := ih b x hhead' hmem'
      have hlen2 : (b :: rest).length - 1 = rest.length := by simp
      rw [hlen2] at hmemgo
      exact List.mem_cons_of_mem _ hmemgo

/-- Membership in the ancestor walk exhibits a step chain from the start to
the member, of length at most the fuel plus one. -/
private theorem go_chain_of_mem {d : LayoutDump} : ∀ (K : Nat) (s x : String),
    x ∈ LayoutDump.ancestors.go d K s →
    ∃ c, StepChain (fun s t => ∃ b, d.box? s = some b ∧ b.parent = t ∧ t ≠ "") c ∧
      c.head? = some s ∧ c.getLast? = some x ∧ c.length ≤ K + 1
  | 0, s, x, hx => by
    simp only [LayoutDump.ancestors.go] at hx
    cases hx
  | K + 1, s, x, hx => by
    cases h : d.box? s with
    | none =>
      have hfind : d.boxes.find? (fun b => b.id == s) = none := h
      simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind] at hx
      cases hx
    | some b =>
      have hfind : d.boxes.find? (fun b => b.id == s) = some b := h
      by_cases hpar : b.parent = ""
      · simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar,
          ↓reduceIte] at hx
        cases hx
      · have hgo := go_succ (d := d) (k := K) (s := s) (b := b) h hpar
        rw [hgo] at hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · refine ⟨[s, b.parent],
            StepChain.cons ⟨b, h, rfl, hpar⟩ (StepChain.single _),
            by simp, by simp, ?_⟩
          simp only [List.length_cons, List.length_nil]
          omega
        · obtain ⟨c', hchain', hhead', hlast', hlen'⟩ := go_chain_of_mem K b.parent x hx'
          obtain ⟨p', rest', hcsplit⟩ : ∃ p' rest', c' = p' :: rest' := by
            cases c' with
            | nil => simp at hhead'
            | cons p' rest' => exact ⟨p', rest', rfl⟩
          subst hcsplit
          have hpeq : p' = b.parent := by simpa using hhead'
          subst hpeq
          refine ⟨s :: b.parent :: rest', StepChain.cons ⟨b, h, rfl, hpar⟩ hchain',
            by simp, ?_, ?_⟩
          · have hgg : ((s :: b.parent :: rest').getLast? =
              (b.parent :: rest').getLast?) := rfl
            rw [hgg]
            exact hlast'
          · simp only [List.length_cons] at hlen' ⊢
            omega

/-- Concatenating two step chains at their shared endpoint value. -/
private theorem stepChain_concat {R : String → String → Prop} :
    ∀ (l₁ l₂ : List String) (j : String),
    StepChain R l₁ → StepChain R l₂ → l₁.getLast? = some j → l₂.head? = some j →
    ∃ l, StepChain R l ∧ l.head? = l₁.head? ∧ l.getLast? = l₂.getLast? ∧
      l.length + 1 = l₁.length + l₂.length
  | [], l₂, j, _, hchain₂, hlast₁, _ => by
    simp at hlast₁
  | [a], l₂, j, _, hchain₂, hlast₁, hlast₂ => by
    have hj : a = j := by simpa using hlast₁
    subst hj
    cases l₂ with
    | nil => simp at hlast₂
    | cons b rest =>
      have hb : b = a := by simpa using hlast₂
      subst hb
      exact ⟨b :: rest, hchain₂, rfl, rfl, by simp; omega⟩
  | a :: b :: rest, l₂, j, hchain₁, hchain₂, hlast₁, hlast₂ => by
    cases hchain₁ with
    | cons hab htailChain =>
      have hlast₁' : (b :: rest).getLast? = some j := hlast₁
      obtain ⟨l', hl'chain, hl'head, hl'last, hl'len⟩ :=
        stepChain_concat (b :: rest) l₂ j htailChain hchain₂ hlast₁' hlast₂
      obtain ⟨b', rest'', hsplit⟩ : ∃ b' rest'', l' = b' :: rest'' := by
        cases l' with
        | nil => simp at hl'head
        | cons b' rest'' => exact ⟨b', rest'', rfl⟩
      subst hsplit
      have hb'eq : b = b' := by
        have h : b' = b := by simpa using hl'head
        exact h.symm
      subst hb'eq
      refine ⟨a :: b :: rest'', StepChain.cons hab hl'chain, rfl, ?_, ?_⟩
      · have hgg : ((a :: b :: rest'').getLast? = (b :: rest'').getLast?) := rfl
        rw [hgg]
        exact hl'last
      · simp only [List.length_cons] at hl'len ⊢
        omega

 /-! ### Box-lookup and list utilities -/

 /-- A member of a box-id list resolves through `box?`, exposing the box. -/
 private theorem box_of_mem_ids {l : List Box} {s : String}
     (hmem : s ∈ l.map (·.id)) :
     ∃ b, b ∈ l ∧ l.find? (fun b => b.id == s) = some b ∧ b.id = s := by
   match hfind : l.find? (fun b => b.id == s) with
   | none =>
     exfalso
     obtain ⟨b, hb, hbid⟩ := List.mem_map.mp hmem
     have hfalse := List.find?_eq_none.mp hfind b hb
     simp [hbid] at hfalse
   | some b =>
     refine ⟨b, List.mem_of_find?_eq_some hfind, hfind, ?_⟩
     have hpred := List.find?_some hfind
     simpa using hpred


 /-- With nodup ids, `find?` at a member box returns that box. -/
 private theorem find?_of_mem_nodup {l : List Box} {b : Box}
     (hnd : (l.map (·.id)).Nodup) (hmem : b ∈ l) :
     l.find? (fun b' => b'.id == b.id) = some b := by
   match hfind : l.find? (fun b' => b'.id == b.id) with
   | none =>
     exfalso
     have hfalse := List.find?_eq_none.mp hfind b hmem
     simp at hfalse
   | some b' =>
     have hb'mem := List.mem_of_find?_eq_some hfind
     have hid : b'.id = b.id := by
       have hpred := List.find?_some hfind
       simpa using hpred
     have heq : b' = b := expandChild_nodup_map_inj (·.id) hnd hb'mem hmem hid
     rw [heq] at hfind
     exact hfind


 /-- Remove the first occurrence of an id. -/
 private def removeFirst (a : String) : List String → List String
   | [] => []
   | b :: rest => if b = a then rest else b :: removeFirst a rest

 private theorem removeFirst_mem : ∀ (l : List String) (a x : String),
     x ∈ removeFirst a l → x ∈ l
   | [], _, _, h => by cases h
   | b :: rest, a, x, h => by
     simp only [removeFirst] at h
     by_cases heq : b = a
     · simp only [heq, ↓reduceIte] at h
       exact List.mem_cons.mpr (Or.inr h)
     · simp only [heq, ↓reduceIte] at h
       rcases List.mem_cons.mp h with rfl | hmem
       · exact List.mem_cons.mpr (Or.inl rfl)
       · exact List.mem_cons.mpr (Or.inr (removeFirst_mem rest a x hmem))

 private theorem removeFirst_mem_of_ne : ∀ (l : List String) (a x : String),
     x ≠ a → x ∈ l → x ∈ removeFirst a l
   | [], _, _, _, h => by cases h
   | b :: rest, a, x, hne, hmem => by
     simp only [removeFirst]
     by_cases heq : b = a
     · subst heq
       simp only [↓reduceIte]
       rcases List.mem_cons.mp hmem with rfl | hmem'
       · exact absurd rfl hne
       · exact hmem'
     · simp only [heq, ↓reduceIte]
       rcases List.mem_cons.mp hmem with rfl | hmem'
       · exact List.mem_cons.mpr (Or.inl rfl)
       · exact List.mem_cons.mpr (Or.inr (removeFirst_mem_of_ne rest a x hne hmem'))

 private theorem removeFirst_nodup : ∀ (l : List String) (a : String),
     l.Nodup → (removeFirst a l).Nodup
   | [], _, _ => List.nodup_nil
   | b :: rest, a, hnd => by
     rw [List.nodup_cons] at hnd
     simp only [removeFirst]
     by_cases heq : b = a
     · subst heq
       simp only [↓reduceIte]
       exact hnd.2
     · simp only [heq, ↓reduceIte]
       rw [List.nodup_cons]
       refine ⟨?_, removeFirst_nodup rest a hnd.2⟩
       intro hmem
       exact hnd.1 (removeFirst_mem rest a b hmem)

 private theorem removeFirst_length : ∀ (l : List String) (a : String),
     a ∈ l → (removeFirst a l).length + 1 = l.length
   | b :: rest, a, hmem => by
     simp only [removeFirst]
     by_cases heq : b = a
     · subst heq
       simp only [↓reduceIte, List.length_cons]
     · simp only [heq, ↓reduceIte, List.length_cons]
       rcases List.mem_cons.mp hmem with rfl | hmem'
       · exact absurd rfl heq
       · have ih := removeFirst_length rest a hmem'
         omega


 /-- A nodup list covering another nodup list is at least as long. -/
 private theorem nodup_length_le_string : ∀ (l₁ l₂ : List String),
     l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₂.Nodup → l₁.length ≤ l₂.length
   | [], _, _, _, _ => Nat.zero_le _
   | a :: rest, l₂, hnd1, hsub, hnd2 => by
     rw [List.nodup_cons] at hnd1
     have ha : a ∈ l₂ := hsub a (List.mem_cons.mpr (Or.inl rfl))
     have h1 : rest.length ≤ (removeFirst a l₂).length := by
       apply nodup_length_le_string rest (removeFirst a l₂) hnd1.2 _ (removeFirst_nodup l₂ a hnd2)
       intro x hx
       have hx2 := hsub x (List.mem_cons.mpr (Or.inr hx))
       have hxa : x ≠ a := fun heq => hnd1.1 (heq ▸ hx)
       exact removeFirst_mem_of_ne l₂ a x hxa hx2

     have h2 : (removeFirst a l₂).length + 1 = l₂.length :=
       removeFirst_length l₂ a ha
     simp only [List.length_cons]
     omega

 /-- Membership in a list splits it around the member. -/
 private theorem mem_split : ∀ (l : List String) (a : String), a ∈ l →
     ∃ pre suf, l = pre ++ a :: suf
   | b :: rest, a, hmem => by
     rcases List.mem_cons.mp hmem with rfl | hmem'
     · exact ⟨[], rest, rfl⟩
     · obtain ⟨pre, suf, hsplit⟩ := mem_split rest a hmem'
       exact ⟨b :: pre, suf, by simp [hsplit]⟩

 /-- A non-nodup list repeats some element with everything between. -/
 private theorem nodup_split_repeat : ∀ (l : List String), ¬ l.Nodup →
     ∃ pre x mid suf, l = pre ++ x :: mid ++ x :: suf
   | [], h => absurd List.nodup_nil h
   | a :: rest, h => by
     rw [List.nodup_cons] at h
     have hcases : a ∈ rest ∨ ¬ rest.Nodup := by
       by_cases ha : a ∈ rest
       · exact Or.inl ha
       · exact Or.inr (fun hnd => h ⟨ha, hnd⟩)
     rcases hcases with hmem | hrest
     · obtain ⟨pre, suf, hsplit⟩ := mem_split rest a hmem
       exact ⟨[], a, pre, suf, by simp [hsplit]⟩
     · obtain ⟨pre, x, mid, suf, hsplit⟩ := nodup_split_repeat rest hrest
       exact ⟨a :: pre, x, mid, suf, by simp [hsplit]⟩

 /-- Membership in a list has an index. -/
 private theorem mem_index : ∀ (l : List String) (a : String), a ∈ l →
     ∃ n, n < l.length ∧ l[n]? = some a
   | [], _, h => by cases h
   | b :: rest, a, h => by
     rcases List.mem_cons.mp h with rfl | hmem
     · exact ⟨0, by simp, by simp⟩
     · obtain ⟨n, hlt, hget⟩ := mem_index rest a hmem
       exact ⟨n + 1, by simpa using Nat.succ_lt_succ hlt, by simpa using hget⟩

 /-! ### Empty-id facts -/

 private theorem empty_not_mem_ancestors_go {d : LayoutDump} (k : Nat) (s : String) :
     "" ∉ LayoutDump.ancestors.go d k s := by
   revert s
   induction k with
   | zero =>
     intro s hmem
     cases hmem
   | succ k ih =>
     intro s hmem
     simp only [LayoutDump.ancestors.go, LayoutDump.box?] at hmem

     match h : d.boxes.find? (fun b => b.id == s) with
     | none =>
       simp only [h] at hmem
       cases hmem
     | some b =>
       simp only [h] at hmem
       by_cases hp : b.parent = ""
       · simp only [hp, ↓reduceIte] at hmem
         cases hmem
       · simp only [hp, ↓reduceIte, List.mem_cons] at hmem
         have hne : ("" : String) ≠ b.parent := Ne.symm hp
         have hmem' : "" ∈ LayoutDump.ancestors.go d k b.parent := by
           rcases hmem with hcontra | hrest
           · exact absurd hcontra hne
           · exact hrest
         exact ih _ hmem'

 private theorem empty_not_mem_ancestors {d : LayoutDump} (s : String) :
     "" ∉ d.ancestors s := by
   unfold LayoutDump.ancestors
   exact empty_not_mem_ancestors_go d.boxes.length s

 /-- The index of the `""`-id box never occurs in a `Compound.ancestors`
 walk: the walk stops on `""` before looking anything up, and no nonempty
 id resolves to that index. -/
 private theorem compound_ancestors_ne_gidx {boxes : List ModelBox}
     {gidx : Nat} (hg : boxes.findIdx? (fun b => b.id == "") = some gidx)
     (n : Nat) (id : String) :

     gidx ∉ Compound.ancestors boxes n id := by
   revert id
   induction n with
   | zero =>
     intro id hmem
     simp only [Compound.ancestors] at hmem
     exact absurd hmem (by simp)
   | succ n ih =>
     intro id hmem
     by_cases hid : id = ""
     · subst hid
       have h2 : Compound.ancestors boxes (n + 1) "" = [] :=
         Compound.ancestors.eq_2 _ _
       rw [h2] at hmem
       cases hmem
     · have h3 : Compound.ancestors boxes (n + 1) id =
           match boxes.findIdx? (fun box => box.id == id) with
           | none => []
           | some index =>
             match boxes[index]? with
             | none => []
             | some box => Compound.ancestors boxes n box.parent ++ [index] :=
         Compound.ancestors.eq_3 boxes id n hid
       rw [h3] at hmem
       match hf : boxes.findIdx? (fun box => box.id == id) with
       | none =>
         simp only [hf] at hmem
         exact absurd hmem (by simp)
       | some j =>
         simp only [hf] at hmem
         match hb : boxes[j]? with
         | none =>
           simp only [hb] at hmem
           exact absurd hmem (by simp)
         | some bj =>
           simp only [hb, List.mem_append, List.mem_singleton] at hmem
           rcases hmem with hmem | hmem
           · exact ih _ hmem
           · obtain ⟨_, hjid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
             obtain ⟨_, hgid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hg
             subst hmem
             have hjj : boxes[gidx].id = id := beq_iff_eq.mp hjid



             have hgj : boxes[gidx].id = "" := beq_iff_eq.mp hgid
             rw [hgj] at hjj
             exact hid hjj.symm

 /-- No box is inside a group whose id is `""`: the model walk stops on
 `""` before recording any index. -/
 private theorem inside_empty_id {boxes : List ModelBox} (x : String) :
     Compound.inside boxes "" x = false := by
   unfold Compound.inside
   match hfind : boxes.find? (fun box => box.id == x) with
   | none =>
     simp only [hfind]
   | some box =>
     simp only [hfind]
     match hgidx : boxes.findIdx? (fun box => box.id == "") with
     | none =>
       simp only [hgidx]
     | some gidx =>
       simp only [hgidx]
       have hnot : gidx ∉ Compound.ancestors boxes boxes.length box.parent :=
         compound_ancestors_ne_gidx hgidx _ _
       cases hc : (Compound.path boxes box).contains gidx with
       | false => rfl
       | true =>
         simp only [List.contains_iff_mem] at hc
         exact absurd hc hnot




 /-- With an empty group id the child scene is empty: no model box is
 inside `""`, so the child selection keeps nothing and the child layout
 emits no boxes. -/
 private theorem child_empty_of_empty_group {inp : Input} {o : Options}
     {group : ModelBox} {P : Params} {fuel : Nat}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child : FamilyResult} {res : FamilyResult}
     (hgid : group.id = "")
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
       parent child res) :
     child.scene.boxes = [] := by
   obtain ⟨hwf, _, _, hchild, hparent, _⟩ := hctx
   have hcid := (expandChild_selected_ids hwf hchild hparent).1
   have hmap : child.scene.boxes.map (·.id) = [] := by
     rw [hcid]
     have hnil : inp.boxes.filter
         (fun box => Compound.inside inp.boxes group.id box.id) = [] := by
       have hall : ∀ m ∈ inp.boxes,
           Compound.inside inp.boxes group.id m.id = false := by
         intro m _
         rw [hgid]
         exact inside_empty_id m.id
       have key : ∀ (l : List ModelBox),
           (∀ m ∈ l, Compound.inside inp.boxes group.id m.id = false) →
           l.filter (fun box => Compound.inside inp.boxes group.id box.id) = [] := by
         intro l hl
         induction l with
         | nil => rfl
         | cons b rest ih =>
           have hb := hl b (List.mem_cons.mpr (Or.inl rfl))
           simp only [List.filter_cons, hb]
           exact ih (fun m hm => hl m (List.mem_cons.mpr (Or.inr hm)))
       exact key _ hall
     rw [hnil, List.map_nil]
   match hcb : child.scene.boxes with
   | [] => rfl
   | _ :: _ => simp [hcb] at hmap


private theorem filter_not_length_sum {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun x => !(p x))).length = l.length := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    by_cases h : p b = true
    · have h1 : ((b :: rest).filter p) = b :: rest.filter p := by simp [h]
      have h2 : ((b :: rest).filter (fun x => !(p x))) =
          rest.filter (fun x => !(p x)) := by simp [h]
      rw [h1, h2]
      simp only [List.length_cons]
      omega
    · have hpb : p b = false := by cases hb : p b <;> simp_all
      have h1 : ((b :: rest).filter p) = rest.filter p := by simp [hpb]
      have h2 : ((b :: rest).filter (fun x => !(p x))) =
          b :: rest.filter (fun x => !(p x)) := by simp [hpb]
      rw [h1, h2]
      simp only [List.length_cons]
      omega


private theorem filterMap_length_of_all_some {α β : Type} (l : List α)
    (f : α → Option β) (h : ∀ x ∈ l, ∃ y, f x = some y) :
    (l.filterMap f).length = l.length := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    obtain ⟨y, hy⟩ := h b (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ x ∈ rest, ∃ y, f x = some y := fun x hx =>
      h x (List.mem_cons.mpr (Or.inr hx))
    have ih' := ih hrest
    simp only [List.filterMap_cons] at ⊢
    rw [hy]
    simp only [List.length_cons, ih']

private theorem filterMap_map_id_eq {α β : Type} (l : List α)
    (f : α → Option β) (key : β → String) (idOf : α → String)
    (h : ∀ x ∈ l, ∃ y, f x = some y ∧ key y = idOf x) :
    (l.filterMap f).map key = l.map idOf := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    obtain ⟨y, hy, hkey⟩ := h b (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ x ∈ rest, ∃ y, f x = some y ∧ key y = idOf x := fun x hx =>
      h x (List.mem_cons.mpr (Or.inr hx))
    have ih' := ih hrest
    simp only [List.filterMap_cons, hy, List.map_cons]
    rw [hkey, ih']

private theorem merged_length_sum
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hchild : layoutRecursive fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child)
    (hparent : layoutRecursive fuel
      (parentSubInput inp group P titleLines child) o = .ok parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res) :
    child.scene.boxes.length + parent.scene.boxes.length ≤
      res.scene.boxes.length := by
  obtain ⟨hcid, hpid, _hnC, _hnP, _hdisj⟩ :=
    expandChild_selected_ids hwf hchild hparent
  obtain ⟨_frame, _metric, _tl, _lines, dx, dy, _hframe, _hmetric, _htitle,
    _hlines, _hdx, _hdy, _hcanvas, hboxes⟩ := expandChild_sources hexpand
  have hmem : ∀ m ∈ inp.boxes, ∃ b,
      (((child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes).find? (fun box => box.id == m.id)) = some b ∧
      b.id = m.id := by
    intro m hm
    by_cases hinside : Compound.inside inp.boxes group.id m.id = true
    · have hflt : m ∈ inp.boxes.filter
          (fun box => Compound.inside inp.boxes group.id box.id) :=
        List.mem_filter.mpr ⟨hm, hinside⟩
      have hid : m.id ∈ child.scene.boxes.map (·.id) := by
        rw [hcid]
        exact List.mem_map.mpr ⟨m, hflt, rfl⟩
      obtain ⟨cb, hcb, hcbid⟩ := List.mem_map.mp hid
      have hmemE : (embedBox group.id dx dy cb) ∈
          (child.scene.boxes.map (embedBox group.id dx dy)) :=
        List.mem_map.mpr ⟨cb, hcb, rfl⟩
      have hmemU : (embedBox group.id dx dy cb) ∈
          ((child.scene.boxes.map (embedBox group.id dx dy)) ++
            parent.scene.boxes) :=
        List.mem_append_left _ hmemE
      have hkey : (embedBox group.id dx dy cb).id = m.id := hcbid
      have hmemId : m.id ∈ (((child.scene.boxes.map
          (embedBox group.id dx dy)) ++ parent.scene.boxes).map (·.id)) :=
        List.mem_map.mpr ⟨_, hmemU, hkey⟩
      obtain ⟨b, _hbmem, hbfind, hbid⟩ :=
        box_of_mem_ids (l := ((child.scene.boxes.map
          (embedBox group.id dx dy)) ++ parent.scene.boxes)) hmemId
      exact ⟨b, hbfind, hbid⟩
    · have hnot : ((!Compound.inside inp.boxes group.id m.id) = true) := by
        rw [Bool.not_eq_true']
        exact Bool.of_not_eq_true hinside
      have hflt : m ∈ inp.boxes.filter
          (fun box => !Compound.inside inp.boxes group.id box.id) :=
        List.mem_filter.mpr ⟨hm, hnot⟩
      have hid : m.id ∈ parent.scene.boxes.map (·.id) := by
        rw [hpid]
        exact List.mem_map.mpr ⟨m, hflt, rfl⟩
      obtain ⟨pb, hpb, hpbid⟩ := List.mem_map.mp hid
      have hmemU : pb ∈ ((child.scene.boxes.map
          (embedBox group.id dx dy)) ++ parent.scene.boxes) :=
        List.mem_append_right _ hpb
      have hmemId : m.id ∈ (((child.scene.boxes.map
          (embedBox group.id dx dy)) ++ parent.scene.boxes).map (·.id)) :=
        List.mem_map.mpr ⟨pb, hmemU, hpbid⟩
      obtain ⟨b, _hbmem, hbfind, hbid⟩ :=
        box_of_mem_ids (l := ((child.scene.boxes.map
          (embedBox group.id dx dy)) ++ parent.scene.boxes)) hmemId
      exact ⟨b, hbfind, hbid⟩
  have hlenM : res.scene.boxes.length = inp.boxes.length := by
    have h1 := filterMap_length_of_all_some inp.boxes _ (fun x hx =>
      let ⟨b, hb, _⟩ := hmem x hx; ⟨b, hb⟩)
    have heq : res.scene.boxes =
        inp.boxes.filterMap (fun model =>
          ((child.scene.boxes.map (embedBox group.id dx dy)) ++
            parent.scene.boxes).find? (fun box => box.id == model.id)) :=
      hboxes
    rw [heq]
    exact h1
  have hlenC : child.scene.boxes.length =
      (inp.boxes.filter
        (fun box => Compound.inside inp.boxes group.id box.id)).length := by
    have h := congrArg List.length hcid
    simpa using h
  have hlenP : parent.scene.boxes.length =
      (inp.boxes.filter
        (fun box => !Compound.inside inp.boxes group.id box.id)).length := by
    have h := congrArg List.length hpid
    simpa using h
  have hsum := filter_not_length_sum inp.boxes
    (fun box => Compound.inside inp.boxes group.id box.id)
  rw [hlenC, hlenP, hlenM, hsum]
  exact Nat.le_refl _


/-- Every embedded child box reaches the group frame in the merged dump:
there is a merged-dump parent chain from the box to `group.id` whose length
fits in the child scene (plus the group step).  Scene parents mirror the
selected model parents, whose well-founded walk hits the rewritten root;
the merged walk follows child links verbatim and steps from each child root
to the group.  Pinned to the executed merge via `res`; strictly simpler
than the scope conclusion (no parent dump, no scope list). -/
def ExpandChildChildRootChain (group : ModelBox) (child res : FamilyResult) : Prop :=
  ∀ cb ∈ child.scene.boxes, ∃ c : List String,
    StepChain (fun s t => ∃ b, res.scene.layoutDump.box? s = some b ∧
      b.parent = t ∧ t ≠ "") c ∧
    c.head? = some cb.id ∧ c.getLast? = some group.id ∧
    c.length ≤ child.scene.boxes.length + 1

private theorem box_id_of_box_some {d : LayoutDump} {s : String} {b : Box}
    (h : d.box? s = some b) : b.id = s := by
  simp only [LayoutDump.box?] at h
  have hpred := List.find?_some h
  have htrue : (b.id == s) = true := hpred
  exact beq_iff_eq.mp htrue

private theorem parent_chain_lift_of_trans
    {parent res : FamilyResult}
    (htransP : ∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
      res.scene.layoutDump.box? b.id = some b)
    {c : List String}
    (hchain : StepChain (fun s t => ∃ b,
      parent.scene.layoutDump.box? s = some b ∧ b.parent = t ∧ t ≠ "") c) :
    StepChain (fun s t => ∃ b,
      res.scene.layoutDump.box? s = some b ∧ b.parent = t ∧ t ≠ "") c := by
  induction hchain with
  | nil => exact StepChain.nil
  | single a => exact StepChain.single a
  | cons hab htail ih =>
    obtain ⟨bx, hb, hpar, hne⟩ := hab
    have hbid := box_id_of_box_some hb
    have hb' := hbid.symm ▸ hb
    have htrans := htransP bx hb'
    have htransA := hbid ▸ htrans
    exact StepChain.cons ⟨bx, htransA, hpar, hne⟩ ih
/-! ### Last-link extraction from step chains -/

/-- Membership from a successful `getLast?` lookup. -/
private theorem mem_of_getLast? (l : List String) (x : String)
    (h : l.getLast? = some x) : x ∈ l := by
  cases hl : l with
  | nil => simp [hl] at h
  | cons a t =>
    cases ht : t with
    | nil =>
      have hax : a = x := by simpa [hl, ht] using h
      subst hax
      exact List.mem_cons.mpr (Or.inl rfl)
    | cons b t2 =>
      have hT : (a :: b :: t2).getLast? = some x := by
        rw [← ht, ← hl]
        exact h
      have h' : (b :: t2).getLast? = some x := hT
      exact List.mem_cons.mpr (Or.inr (mem_of_getLast? _ _ h'))

/-- A step chain whose ends differ has length at least two. -/
private theorem chain_length_ge_two {c : List String} {s x : String}
    (hhead : c.head? = some s) (hlast : c.getLast? = some x) (hne : s ≠ x) :
    2 ≤ c.length := by
  cases hc : c with
  | nil => simp [hc] at hhead
  | cons a t =>
    cases ht : t with
    | nil =>
      have ha : a = s := by simpa [hc] using hhead
      have hax : a = x := by simpa [hc, ht] using hlast
      exact absurd (ha.symm.trans hax) hne
    | cons b t2 =>
      simp only [List.length_cons]
      omega

/-- A list whose head lookup succeeds is nonempty. -/
private theorem length_ge_one_of_head? {l : List String} {s : String}
    (h : l.head? = some s) : 1 ≤ l.length := by
  cases hl : l with
  | nil => simp [hl] at h
  | cons a t =>
    simp only [List.length_cons]
    omega

/-- The last element of a length-two-or-more list lies in its tail. -/
private theorem last_mem_tail {l : List String} {x : String}
    (hlast : l.getLast? = some x) (h2 : 2 ≤ l.length) : x ∈ l.tail := by
  cases hl : l with
  | nil => simp [hl] at hlast
  | cons a t =>
    show x ∈ t
    have hlastT : (a :: t).getLast? = some x := hl ▸ hlast
    cases ht : t with
    | nil => simp [hl, ht] at h2
    | cons b t2 =>
      have hlastB : (a :: b :: t2).getLast? = some x := ht ▸ hlastT
      have hlast'' : (b :: t2).getLast? = some x := hlastB
      exact mem_of_getLast? _ _ hlast''

/-- The last link of a step chain whose ends differ ends at the last element. -/
private theorem stepChain_last_link {R : String → String → Prop}
    {c : List String} {s x : String}
    (hchain : StepChain R c) (hhead : c.head? = some s)
    (hlast : c.getLast? = some x) (hne : s ≠ x) :
    ∃ y, R y x ∧ y ∈ c := by
  induction hchain generalizing s x with
  | nil => simp at hhead
  | single a =>
    have hs : a = s := by simpa using hhead
    have hx : a = x := by simpa using hlast
    exact absurd (hs.symm.trans hx) hne
  | cons hab htail ih =>
    rename_i a b rest
    have hlast' : (b :: rest).getLast? = some x := hlast
    by_cases hbx : b = x
    · exact ⟨a, hbx ▸ hab, List.mem_cons.mpr (Or.inl rfl)⟩
    · obtain ⟨y, hry, hym⟩ := ih (by simp) hlast' hbx
      exact ⟨y, hry, List.mem_cons.mpr (Or.inr hym)⟩

/-! ### Ancestry conclusions for one `expandChild` call -/

/-- Every embedded child box reaches the group frame in the merged dump:
the residual chain ends at `group.id`, so the group is a merged ancestor. -/
theorem expandChild_child_ancestors_group
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hroot : ExpandChildChildRootChain group child res) :
    ∀ cb ∈ child.scene.boxes, group.id ∈ res.scene.layoutDump.ancestors cb.id := by
  obtain ⟨hwf, hgroup, _, hchild, hparent, _⟩ := hctx
  obtain ⟨hleC, _, hne⟩ :=
    expandChild_merge_bounds hwf hgroup hchild hparent hexpand
  obtain ⟨frame, _tl, _dx, _dy, hframe, _hdx, _hdy, _htransC, _htransP⟩ :=
    expandChild_boxLookup_transport hwf hchild hparent hexpand
  intro cb hcb
  obtain ⟨c, hchain, hhead, hlast, hclen⟩ := hroot cb hcb
  have hcbne : cb.id ≠ group.id := hne frame hframe cb hcb
  have htail : group.id ∈ c.tail :=
    last_mem_tail hlast (chain_length_ge_two hhead hlast hcbne)
  have hmem := mem_of_stepChain c hchain cb.id group.id hhead htail
  have hle : c.length - 1 ≤ res.scene.layoutDump.boxes.length := by
    have hM : res.scene.layoutDump.boxes.length = res.scene.boxes.length := rfl
    omega
  exact ancestors_go_mono hle hmem

/-- Every scope anchor of the expanded group lies on the merged ancestor
chain of every embedded child box: `group.id` by the root chain, and every
parent-scene ancestor of the group by lifting the parent walk through the
merge transport and concatenating. -/
theorem expandChild_merged_anchors_of_child
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hroot : ExpandChildChildRootChain group child res) :
    ∀ cb ∈ child.scene.boxes,
      ∀ x ∈ group.id :: parent.scene.layoutDump.ancestors group.id,
        x ∈ res.scene.layoutDump.ancestors cb.id := by
  have hwf := hctx.1
  have hgroup := hctx.2.1
  have hchild := hctx.2.2.2.1
  have hparent := hctx.2.2.2.2.1
  obtain ⟨frame, _, _, _, hframe, _, _, _, htransP⟩ :=
    expandChild_boxLookup_transport hwf hchild hparent hexpand
  obtain ⟨_, _, hne⟩ :=
    expandChild_merge_bounds hwf hgroup hchild hparent hexpand
  have hsum := merged_length_sum hwf hchild hparent hexpand
  have hPdump : parent.scene.layoutDump.boxes.length = parent.scene.boxes.length := rfl
  intro cb hcb x hx
  have h1 := expandChild_child_ancestors_group hexpand hframed hctx hparams hroot cb hcb
  rcases List.mem_cons.mp hx with h | hxP
  · rw [h]
    exact h1
  · have hxgo : x ∈ LayoutDump.ancestors.go parent.scene.layoutDump
        parent.scene.layoutDump.boxes.length group.id := hxP
    obtain ⟨c₂, hchain₂, hhead₂, hlast₂, hlen₂⟩ := go_chain_of_mem _ _ _ hxgo
    have hchain₂M := parent_chain_lift_of_trans htransP hchain₂
    obtain ⟨c₁, hchain₁, hhead₁, hlast₁, hlen₁⟩ := hroot cb hcb
    have hcbne : cb.id ≠ group.id := hne frame hframe cb hcb
    obtain ⟨c, hchain, hhead, hlast, hclen⟩ :=
      stepChain_concat c₁ c₂ group.id hchain₁ hchain₂M hlast₁ hhead₂
    have hheadX : c.head? = some cb.id := hhead₁ ▸ hhead
    have hlastX : c.getLast? = some x := hlast₂ ▸ hlast
    have htail : x ∈ c.tail :=
      last_mem_tail hlastX (by
        have hc₁2 := chain_length_ge_two hhead₁ hlast₁ hcbne
        have hc₂1 := length_ge_one_of_head? hhead₂
        omega)
    have hmem := mem_of_stepChain c hchain cb.id x hheadX htail
    have hcb : c.length + 1 ≤
        child.scene.boxes.length + parent.scene.boxes.length + 2 := by
      omega
    have hle : c.length - 1 ≤ res.scene.layoutDump.boxes.length := by
      have hM : res.scene.layoutDump.boxes.length = res.scene.boxes.length := rfl
      omega
    exact ancestors_go_mono hle hmem

/-- The scope-anchor remainder of `ExpandChildC6Step`: every anchor id of the
expanded group lies on the merged ancestor chain of an endpoint of every
child-scene route. -/
theorem expandChild_c6_anchors
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hroot : ExpandChildChildRootChain group child res) :
    ExpandChildC6Anchors group parent child res := by
  have h2 := expandChild_merged_anchors_of_child hexpand hframed hctx hparams hroot
  have hend := expandChild_child_route_endpoints hexpand hframed hctx hparams
  intro rt hrt x hx
  obtain ⟨hmF, _hmT⟩ := hend rt hrt
  obtain ⟨cbf, hmemf, heq⟩ := List.mem_map.mp hmF
  have hmem := h2 cbf hmemf x hx
  rw [heq] at hmem
  exact Or.inl hmem

/-- The expanded group is isolated from the other parent boxes: no other
parent-scene box has the group among its ancestors.  A merged ancestor walk
to the group ends in a parent link at the group, which mirrors a kept source
box whose parent is the group; that source lies inside the group by
`inside_of_parent`, against the parent sub-input's outside selection. -/
theorem expandChild_group_isolated
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (_hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ExpandChildGroupIsolated group parent := by
  obtain ⟨hwf, hgroup, hpboxes, _, hparent, _⟩ := hctx
  have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hgsel : group ∈ inp.boxes := List.mem_of_find?_eq_some hgroup
  have hpnodup : ((parentSubInput inp group P titleLines child).boxes.map
      (·.id)).Nodup := by
    rw [hpboxes, selectInput_box_ids]
    exact nodup_filter_map _ _ _ hnodup
  intro pb hpb hne
  by_cases hg : group.id = ""
  · rw [hg]
    exact empty_not_mem_ancestors pb.id
  · intro hmem
    have hxgo : group.id ∈ LayoutDump.ancestors.go parent.scene.layoutDump
        parent.scene.layoutDump.boxes.length pb.id := hmem
    obtain ⟨c₂, hchain₂, hhead₂, hlast₂, _hlen₂⟩ := go_chain_of_mem _ _ _ hxgo
    obtain ⟨y, hry, _hym⟩ := stepChain_last_link hchain₂ hhead₂ hlast₂ hne
    obtain ⟨bb, hbbhit, hbbpar, _hbbne⟩ := hry
    have hbbmem : bb ∈ parent.scene.boxes :=
      List.mem_of_find?_eq_some hbbhit
    obtain ⟨sb, hsbmem, _hsbid, hsbpar⟩ :=
      layoutRecursive_scene_box_parent fuel _ _ _ hpnodup hparent bb hbbmem
    rw [hpboxes] at hsbmem
    obtain ⟨m, hmmem, hkeep, _, hmsbpar⟩ :=
      selectInput_box_spec inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "" hsbmem
    have hsbpar' : sb.parent = group.id := by
      rw [← hsbpar]
      exact hbbpar
    have hmpar : m.parent = group.id := by
      rw [hmsbpar] at hsbpar'
      by_cases he : m.parent = ""
      · rw [he] at hsbpar' ⊢
        simpa using hsbpar'
      · have hcond : (m.parent == "") = false := by
          cases hbe : (m.parent == "") with
          | true => exact absurd (beq_iff_eq.mp hbe) he
          | false => rfl
        simpa [hcond] using hsbpar'
    have hmne : m.parent ≠ "" := by
      rw [hmpar]
      exact hg
    have hin : Compound.inside inp.boxes group.id m.id = true :=
      inside_of_parent hnodup hgsel hmmem hmpar.symm hmne
    simp [hin] at hkeep

/-- Both C8a ancestry conjuncts for one `expandChild` call: scope anchors of
every embedded child box plus isolation of the group in the parent scene. -/
theorem expandChild_c8a_ancestry
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hroot : ExpandChildChildRootChain group child res) :
    ExpandChildC8aAncestry group parent child res := by
  refine ⟨?_, expandChild_group_isolated hexpand hframed hctx hparams⟩
  intro cb hcb x hx
  exact expandChild_merged_anchors_of_child hexpand hframed hctx hparams hroot cb hcb x hx


/-! ### Model-level parent walk toward the expanded group -/

/-- Model-level parent walk toward the expanded group: follows parent
pointers, stopping (with `[b]`) at the first box whose parent is the group.
Mirrors `chainWalk`/`chainTerm` lookups so the fuel induction below aligns
with the existing walk lemmas. -/
private def rootChain (boxes : List ModelBox) (groupId : String) : Nat → String → Option (List ModelBox)
  | 0, _ => none
  | n + 1, id =>
    match boxes.findIdx? (fun b => b.id == id) with
    | none => none
    | some i =>
      match boxes[i]? with
      | none => none
      | some b =>
        if b.parent == groupId then some [b]
        else match rootChain boxes groupId n b.parent with
          | none => none
          | some pre => some (b :: pre)

/-- Unfolding equation for `rootChain` at positive fuel. -/
private theorem rootChain_succ {boxes : List ModelBox} {groupId : String} {n : Nat} {id : String} :
    rootChain boxes groupId (n + 1) id =
      match boxes.findIdx? (fun b => b.id == id) with
      | none => none
      | some i =>
        match boxes[i]? with
        | none => none
        | some b =>
          if b.parent == groupId then some [b]
          else match rootChain boxes groupId n b.parent with
            | none => none
            | some pre => some (b :: pre) := by
  rfl

/-- A `Bool` disequality testifies inequality. -/
private theorem ne_of_beq_false {a b : String} (h : (a == b) = false) : a ≠ b := by
  intro heq
  rw [heq, beq_self_eq_true] at h
  exact Bool.noConfusion h

/-- A successful `rootChain` run returns a nonempty list. -/
private theorem rootChain_ne_nil {boxes : List ModelBox} {groupId : String} {n : Nat} {s : String}
    {pre : List ModelBox} (h : rootChain boxes groupId n s = some pre) : pre ≠ [] := by
  induction n generalizing s pre with
  | zero => simp only [rootChain] at h; cases h
  | succ n ih =>
    rw [rootChain_succ] at h
    cases hf : boxes.findIdx? (fun b => b.id == s) with
    | none => simp only [hf] at h; cases h
    | some i =>
      simp only [hf] at h
      cases hg : boxes[i]? with
      | none => simp only [hg] at h; cases h
      | some b =>
        simp only [hg] at h
        by_cases hc : b.parent == groupId
        · simp only [hc] at h
          obtain rfl := Option.some.inj h
          exact by simp
        · simp only [hc] at h
          cases hr : rootChain boxes groupId n b.parent with
          | none => simp only [hr] at h; cases h
          | some pre' =>
            simp only [hr] at h
            obtain rfl := Option.some.inj h
            exact by simp

/-- The head of a successful `rootChain` run is the box with the start id. -/
private theorem rootChain_head {boxes : List ModelBox} {groupId : String} {n : Nat} {s : String}
    {pre : List ModelBox} (h : rootChain boxes groupId n s = some pre) :
    ∃ b₀ rest, pre = b₀ :: rest ∧ b₀.id = s := by
  induction n generalizing s pre with
  | zero => simp only [rootChain] at h; cases h
  | succ n _ =>
    rw [rootChain_succ] at h
    cases hf : boxes.findIdx? (fun b => b.id == s) with
    | none => simp only [hf] at h; cases h
    | some i =>
      simp only [hf] at h
      cases hg : boxes[i]? with
      | none => simp only [hg] at h; cases h
      | some b =>
        simp only [hg] at h
        have hid : b.id = s := by
          obtain ⟨hlt, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
          have hget : boxes[i]? = some boxes[i] := List.getElem?_eq_getElem hlt
          have hb : b = boxes[i] := (Option.some.inj (hget.symm.trans hg)).symm
          have hbeq : (boxes[i].id == s) = true := hmatch
          rw [hb]
          exact beq_iff_eq.mp hbeq
        by_cases hc : b.parent == groupId
        · simp only [hc] at h
          obtain rfl := Option.some.inj h
          exact ⟨b, [], rfl, hid⟩
        · simp only [hc] at h
          cases hr : rootChain boxes groupId n b.parent with
          | none => simp only [hr] at h; cases h
          | some pre' =>
            simp only [hr] at h
            obtain rfl := Option.some.inj h
            exact ⟨b, pre', rfl, hid⟩

/-- Mapped ids keep nodup when the source boxes have unique ids. -/
private theorem nodup_map_id {boxes : List ModelBox} {l : List ModelBox}
    (hnodup : (boxes.map (·.id)).Nodup)
    (hmem : ∀ b ∈ l, b ∈ boxes) (hnd : l.Nodup) : (l.map (·.id)).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (fun b hb => hmem b (List.mem_cons.mpr (Or.inr hb))) (List.nodup_cons.mp hnd).2⟩
    intro hmemA
    obtain ⟨b, hb, hbid⟩ := List.mem_map.mp hmemA
    have hab : a = b :=
      expandChild_nodup_map_inj (·.id) hnodup (hmem _ (List.mem_cons.mpr (Or.inl rfl)))
        (hmem _ (List.mem_cons.mpr (Or.inr hb))) hbid.symm
    exact (List.nodup_cons.mp hnd).1 (hab ▸ hb)

/-- A `Bool` disequality hypothesis yields the corresponding inequality. -/
private theorem ne_of_nbeq_true {a b : String} (h : ¬((a == b) = true)) : a ≠ b := by
  intro heq
  rw [heq, beq_self_eq_true] at h
  exact absurd rfl h

/-- Head injectivity for cons. -/
private theorem cons_head_eq {α : Type} {a₁ a₂ : α} {l₁ l₂ : List α} (h : a₁ :: l₁ = a₂ :: l₂) :
    a₁ = a₂ := by
  have h1 := congrArg List.head? h
  simp only [List.head?_cons] at h1
  exact Option.some.inj h1

/-- Tail injectivity for cons. -/
private theorem cons_tail_eq {α : Type} {a₁ a₂ : α} {l₁ l₂ : List α} (h : a₁ :: l₁ = a₂ :: l₂) :
    l₁ = l₂ := by
  have h1 := congrArg List.tail h
  simp only [List.tail_cons] at h1
  exact h1

/-- The walk toward the group never gets stuck when the model walk
terminates: every lookup succeeds, so the recursion stops at a child root. -/
private theorem rootChain_some {boxes : List ModelBox} {gid : String}
    (hterm : ∀ b ∈ boxes, ∀ n, boxes.length ≤ n + 1 → chainTerm boxes n b.parent = true)
    (hnodup : (boxes.map (·.id)).Nodup)
    {n : Nat} {s : String}
    (hct : chainTerm boxes n s = true) (hne : s ≠ "")
    (hev : ∀ b ∈ boxes, b.id = s → Compound.inside boxes gid b.id = true) :
    ∃ pre, rootChain boxes gid n s = some pre := by
  induction n generalizing s with
  | zero =>
    rw [chainTerm.eq_2 boxes s hne] at hct
    simp at hct
  | succ n ih =>
    rw [chainTerm.eq_3 boxes s n hne] at hct
    rw [rootChain_succ]
    cases hf : boxes.findIdx? (fun b => b.id == s) with
    | none => simp only [hf] at hct; simp at hct
    | some i =>
      simp only [hf] at hct
      cases hg : boxes[i]? with
      | none => simp only [hg] at hct; simp at hct
      | some b =>
        simp only [hg] at hct
        have hbid : b.id = s := by
          obtain ⟨hlt, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
          have hget : boxes[i]? = some (boxes.get ⟨i, hlt⟩) := List.getElem?_eq_getElem hlt
          have hb : b = boxes.get ⟨i, hlt⟩ := (Option.some.inj (hget.symm.trans hg)).symm
          have hbeq : ((boxes.get ⟨i, hlt⟩).id == s) = true := hmatch
          rw [hb]
          exact beq_iff_eq.mp hbeq
        have hbmem : b ∈ boxes := getElem?_mem' hg
        have hinside : Compound.inside boxes gid b.id = true := hev b hbmem hbid
        have hneB : b.parent ≠ "" := inside_parent_ne_empty hnodup hinside hbmem rfl
        by_cases hc : b.parent == gid
        · exact ⟨[b], by simp [hg, hc]⟩
        · have hev' : ∀ bb ∈ boxes, bb.id = b.parent → Compound.inside boxes gid bb.id = true := by
            intro bb hbbmem hbbid
            rcases inside_parent_step hnodup hterm hbmem hbbmem hbbid hinside with hcon | hpg
            · exact absurd hcon (ne_of_nbeq_true hc)
            · exact hpg
          obtain ⟨pre, hpre⟩ := ih (s := b.parent) hct hneB hev'
          exact ⟨b :: pre, by simp [hg, hc, hpre]⟩

/-- Every successful `rootChain` run reaches the group, stays inside, links
by parent pointers, ends at the unique group child, and mirrors the ancestor
walk. Proved by one fuel induction following the recursion. -/
private theorem rootChain_props {boxes : List ModelBox} {gid : String}
    (hterm : ∀ b ∈ boxes, ∀ n, boxes.length ≤ n + 1 → chainTerm boxes n b.parent = true)
    (hnodup : (boxes.map (·.id)).Nodup)
    {n : Nat} {s : String} {pre : List ModelBox}
    (h : rootChain boxes gid n s = some pre) (hne : s ≠ "")
    (hev : ∀ b ∈ boxes, b.id = s → Compound.inside boxes gid b.id = true) :
    (chainWalk boxes n s = pre ++ chainWalk boxes (n - pre.length) gid) ∧
    (∀ b ∈ pre, b ∈ boxes ∧ Compound.inside boxes gid b.id = true) ∧
    (∀ x y xs ys, pre = xs ++ x :: y :: ys → y.id = x.parent) ∧
    (∀ x ∈ pre, ((x.parent == gid) = true) → pre.getLast? = some x) ∧
    (∃ last, pre.getLast? = some last ∧ ((last.parent == gid) = true)) ∧
    pre ≠ [] := by
  induction n generalizing s pre with
  | zero =>
    simp only [rootChain] at h
    cases h
  | succ n ih =>
    rw [rootChain_succ] at h
    cases hf : boxes.findIdx? (fun b => b.id == s) with
    | none => simp only [hf] at h; cases h
    | some i =>
      simp only [hf] at h
      cases hg : boxes[i]? with
      | none => simp only [hg] at h; cases h
      | some b =>
        simp only [hg] at h
        have hbid : b.id = s := by
          obtain ⟨hlt, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
          have hget : boxes[i]? = some (boxes.get ⟨i, hlt⟩) := List.getElem?_eq_getElem hlt
          have hb : b = boxes.get ⟨i, hlt⟩ := (Option.some.inj (hget.symm.trans hg)).symm
          have hbeq : ((boxes.get ⟨i, hlt⟩).id == s) = true := hmatch
          rw [hb]
          exact beq_iff_eq.mp hbeq
        have hbmem : b ∈ boxes := getElem?_mem' hg
        have hinside : Compound.inside boxes gid b.id = true := hev b hbmem hbid
        have hneB : b.parent ≠ "" := inside_parent_ne_empty hnodup hinside hbmem rfl
        have hwalk : chainWalk boxes (n + 1) s = b :: chainWalk boxes n b.parent := by
          rw [chainWalk_succ hne n]
          simp only [hf, hg]
        by_cases hc : b.parent == gid
        · simp only [hc] at h
          obtain rfl := Option.some.inj h
          have hbeq : b.parent = gid := beq_iff_eq.mp hc
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hwalk, hbeq]; simp
          · intro bb hbb
            rw [List.mem_singleton.mp hbb]
            exact ⟨hbmem, hinside⟩
          · intro x y xs ys hsplit
            have hlen := congrArg List.length hsplit
            simp only [List.length_cons, List.length_nil, List.length_append] at hlen
            omega
          · intro x hx _
            simp [List.mem_singleton.mp hx]
          · exact ⟨b, rfl, hc⟩
          · exact by simp
        · have hev' : ∀ bb ∈ boxes, bb.id = b.parent → Compound.inside boxes gid bb.id = true := by
            intro bb hbbmem hbbid
            rcases inside_parent_step hnodup hterm hbmem hbbmem hbbid hinside with hcon | hpg
            · exact absurd hcon (ne_of_nbeq_true hc)
            · exact hpg
          simp only [hc] at h
          cases hr : rootChain boxes gid n b.parent with
          | none => simp only [hr] at h; cases h
          | some pre' =>
            simp only [hr] at h
            obtain rfl := Option.some.inj h
            obtain ⟨ihS, ihM, ihL, ihN, ihE, ihNe⟩ :=
              ih (s := b.parent) (pre := pre') hr hneB hev'
            have hfu : n + 1 - ((b :: pre').length) = n - pre'.length := by
              simp only [List.length_cons]; omega
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hwalk, ihS, hfu, List.cons_append]
            · intro bb hbb
              rw [List.mem_cons] at hbb
              rcases hbb with rfl | hmem'
              · exact ⟨hbmem, hinside⟩
              · exact ihM _ hmem'
            · intro x y xs ys hsplit
              have hsplit' : b :: pre' = xs ++ x :: y :: ys := hsplit
              cases xs with
              | nil =>
                have hsplit0 : b :: pre' = x :: y :: ys := by simpa using hsplit'
                have hx : b = x := cons_head_eq hsplit0
                have hpre' : pre' = y :: ys := cons_tail_eq hsplit0
                obtain rfl := hx
                have hsync' : chainWalk boxes n b.parent =
                    y :: (ys ++ chainWalk boxes (n - pre'.length) gid) := by
                  rw [hpre'] at ihS ⊢
                  rw [List.cons_append] at ihS
                  exact ihS
                exact chainWalk_head_id hsync'
              | cons x0 xs' =>
                have hsplit' : b :: pre' = x0 :: (xs' ++ x :: y :: ys) := by simpa using hsplit'
                have hpre' : pre' = xs' ++ x :: y :: ys := cons_tail_eq hsplit'
                exact ihL x y xs' ys hpre'
            · intro x hxmem hxpar
              rw [List.mem_cons] at hxmem
              rcases hxmem with hxb | hxmem'
              · have hF : (b.parent == gid) = false := Bool.eq_false_iff.mpr hc
                rw [← hxb] at hF
                rw [hF] at hxpar
                simp at hxpar
              · have htail : pre'.getLast? = some x := ihN x hxmem' hxpar
                cases hpre' : pre' with
                | nil => exact absurd hpre' ihNe
                | cons y ys =>
                  rw [hpre'] at htail
                  rw [List.getLast?_cons_cons]
                  exact htail
            · obtain ⟨last, hlast, hpar⟩ := ihE
              refine ⟨last, ?_, hpar⟩
              cases hpre' : pre' with
              | nil => exact absurd hpre' ihNe
              | cons y ys =>
                rw [hpre'] at hlast
                rw [List.getLast?_cons_cons]
                exact hlast
            · exact List.cons_ne_nil _ _

/-! ### Discharge of `ExpandChildChildRootChain` -/

/-- A list of ids with a parent link after every element forms a step chain. -/
private theorem chain_of_links {R : String → String → Prop} {l : List String} {z : String}
    (h : ∀ x y xs ys, l ++ [z] = xs ++ x :: y :: ys → R x y) :
    StepChain R (l ++ [z]) := by
  induction l with
  | nil => exact StepChain.single z
  | cons a rest ih =>
    cases rest with
    | nil => exact StepChain.cons (h a z [] [] (by simp)) (StepChain.single z)
    | cons b rest' =>
      refine StepChain.cons (h a b [] (rest' ++ [z]) (by simp)) (ih ?_)
      intro x y xs ys hxy
      exact h x y (a :: xs) ys (by simpa using congrArg (fun t => a :: t) hxy)

/-- The index of a member box under nodup ids, with its lookup. -/
private theorem findIdx_of_mem_box {boxes : List ModelBox} {b : ModelBox}
    (hnd : (boxes.map (·.id)).Nodup) (hb : b ∈ boxes) :
    ∃ i, boxes.findIdx? (fun x => x.id == b.id) = some i ∧ boxes[i]? = some b := by
  obtain ⟨i, hget⟩ := mem_getElem? hb
  obtain ⟨hi, hbox⟩ := List.getElem?_eq_some_iff.mp hget
  have hfin : boxes.findIdx? (fun x => x.id == b.id) = some i := by
    refine List.findIdx?_eq_some_iff_getElem.mpr ⟨hi, ?_, ?_⟩
    · rw [hbox, beq_self_eq_true]
    · intro j hj hsame
      have hjid : boxes[j].id = boxes[i].id :=
        (beq_iff_eq.mp hsame).trans (by rw [hbox])
      have hmap : (boxes.map (·.id))[j]'(by simpa using Nat.lt_trans hj hi) =
          (boxes.map (·.id))[i]'(by simpa using hi) := by
        simpa using hjid
      have hji : j = i := (hnd.getElem_inj).mp hmap
      omega
  exact ⟨i, hfin, hget⟩

/-- Recursion: a parent walk whose adjacent links and last link hold yields the
merged step chain from its first id to the group. -/
private theorem merged_chain_rec {R : String → String → Prop} {gid : String} :
    ∀ (pre : List ModelBox),
      (∀ x y xs ys, pre = xs ++ x :: y :: ys → R x.id y.id) →
      (∀ l, pre.getLast? = some l → R l.id gid) →
      StepChain R ((pre.map (·.id)) ++ [gid]) := by
  intro pre
  induction pre with
  | nil => intro _ _; exact StepChain.single gid
  | cons p rest ih =>
    intro hstep hlast
    cases rest with
    | nil => exact StepChain.cons (hlast p (by simp)) (StepChain.single gid)
    | cons q rest' =>
      have hpq : R p.id q.id := hstep p q [] rest' rfl
      have htailStep : ∀ x y xs ys, (q :: rest') = xs ++ x :: y :: ys → R x.id y.id := by
        intro x y xs ys h
        exact hstep x y (p :: xs) ys (by simpa using congrArg (fun t => p :: t) h)
      have htailLast : ∀ l, (q :: rest').getLast? = some l → R l.id gid := by
        intro l h
        exact hlast l h
      exact StepChain.cons hpq (ih htailStep htailLast)

/-- The merged-dump image of an inside model box, with its merged parent. -/
private theorem merged_box_of_inside
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int} {parent child res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hchild : layoutRecursive fuel (childSubInput inp group)
      (childSubOptions o group) = .ok child)
    (hparent : layoutRecursive fuel
      (parentSubInput inp group P titleLines child) o = .ok parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    {p : ModelBox} (hpmem : p ∈ inp.boxes)
    (hinside : Compound.inside inp.boxes group.id p.id = true) :
    ∃ bx, res.scene.layoutDump.box? p.id = some bx ∧
      bx.parent = (if p.parent == group.id then group.id else p.parent) := by
  have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  obtain ⟨hcid, _hpid, hnC, _hnP, _hdisj⟩ := expandChild_selected_ids hwf hchild hparent
  obtain ⟨_frame, _tl, dx, dy, _hf, _hdx, _hdy, htransC, _htp⟩ :=
    expandChild_boxLookup_transport hwf hchild hparent hexpand
  have hppar : p.parent ≠ "" := inside_parent_ne_empty hnodup hinside hpmem rfl
  have hmemIds : p.id ∈ child.scene.boxes.map (·.id) := by
    rw [hcid]
    exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hpmem, hinside⟩, rfl⟩
  obtain ⟨bx0, hbx0mem, hbx0id⟩ := List.mem_map.mp hmemIds
  have hndChild : (child.scene.boxes.map (·.id)).Nodup := by
    rw [hcid]
    exact hnC
  have hfind : child.scene.boxes.find? (fun b => b.id == p.id) = some bx0 := by
    rw [← hbx0id]
    exact find?_of_mem_nodup hndChild hbx0mem
  have hchildNodup : ((childSubInput inp group).boxes.map (·.id)).Nodup := by
    show ((selectInput inp (fun box => Compound.inside inp.boxes group.id box.id)
      group.id).boxes.map (·.id)).Nodup
    rw [selectInput_box_ids]
    exact nodup_filter_map _ _ _ hnodup
  obtain ⟨sb, hsbmem, _hsbid, hsbpar⟩ :=
    layoutRecursive_scene_box_parent fuel (childSubInput inp group)
      (childSubOptions o group) child hchildNodup hchild bx0 hbx0mem
  obtain ⟨m, hmmem, _hkeep, hmsid, hmspar⟩ :=
    selectInput_box_spec inp (fun box => Compound.inside inp.boxes group.id box.id)
      group.id hsbmem
  have hmeq : m = p := by
    refine eq_of_mem_id hnodup hmmem hpmem ?_
    rw [← hmsid, ← hbx0id]
    exact _hsbid
  have hparval : bx0.parent = (if p.parent == group.id then "" else p.parent) := by
    rw [hsbpar, hmspar, hmeq]
  have hcb : child.scene.layoutDump.box? bx0.id = some bx0 := by
    rw [hbx0id]
    exact hfind
  have htrans := htransC bx0 hcb
  refine ⟨embedBox group.id dx dy bx0, ?_, ?_⟩
  · rw [← hbx0id]
    exact htrans
  · have hparentE : (embedBox group.id dx dy bx0).parent =
        (if bx0.parent == "" then group.id else bx0.parent) := rfl
    rw [hparentE, hparval]
    by_cases hp : (p.parent == group.id) = true
    · simp [hp]
    · have hpf : (p.parent == group.id) = false := by
        cases h : (p.parent == group.id)
        · rfl
        · exact absurd h hp
      have hne : (p.parent == "") = false := by
        cases h : (p.parent == "")
        · rfl
        · exact absurd (beq_iff_eq.mp h) hppar
      simp [hpf, hne]

end Elegant.Layered.PipelineImpl

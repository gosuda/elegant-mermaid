import Elegant.Layered.Order
import Init.Data.List.Sort.Lemmas

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open OrderImpl OrderImpl.Sibling

private theorem pair_sublist_or_reverse {α : Type} {xs : List α} {a b : α}
    (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) :
    [a, b].Sublist xs ∨ [b, a].Sublist xs := by
  have hp : xs.Pairwise (fun x y => [x, y].Sublist xs) :=
    List.pairwise_of_forall_sublist (fun h => h)
  exact pairwise_ne_cases hp ha hb hne

private theorem filter_infix_in_filter {xs : List Nat} {pick keep : Nat → Bool}
    (hc : (xs.filter pick).IsInfix xs) :
    ((xs.filter keep).filter pick).IsInfix (xs.filter keep) := by
  simpa only [List.filter_filter, Bool.and_comm] using hc.filter keep

private theorem filter_partition_of_prefix {xs : List Nat} {pick : Nat → Bool}
    (hp : (xs.filter pick).IsPrefix xs) :
    xs.filter pick ++ xs.filter (fun v => !pick v) = xs := by
  obtain ⟨rest, hr⟩ := hp
  have hnone : rest.filter pick = [] := by
    have he := congrArg (List.filter pick) hr
    simp only [List.filter_append, List.filter_filter, Bool.and_self] at he
    exact List.append_cancel_left (he.trans (List.append_nil _).symm)
  have hkeep : rest.filter (fun v => !pick v) = rest := by
    apply List.filter_eq_self.mpr
    intro v hv
    simp [Bool.eq_false_of_ne_true ((List.filter_eq_nil_iff.mp hnone) v hv)]
  have hskip : (xs.filter pick).filter (fun v => !pick v) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    simp [(List.mem_filter.mp hv).2]
  have hrest : xs.filter (fun v => !pick v) = rest := by
    calc
      _ = (xs.filter pick ++ rest).filter (fun v => !pick v) :=
        congrArg (List.filter (fun v => !pick v)) hr.symm
      _ = _ := by rw [List.filter_append, hskip, hkeep, List.nil_append]
  rw [hrest]
  exact hr

private theorem clusterBlocks_flatten_of_contiguous (key : Nat → Option Nat) (fuel : Nat)
    (xs : List Nat) (hf : xs.length ≤ fuel) (hnd : xs.Nodup)
    (hc : ∀ c : Nat, (xs.filter (fun v => key v == some c)).IsInfix xs) :
    (clusterBlocks key fuel xs).flatten = xs := by
  induction fuel generalizing xs with
  | zero => simp [clusterBlocks]
  | succ fuel ih =>
    cases xs with
    | nil => simp [clusterBlocks]
    | cons v vs =>
      rw [List.nodup_cons] at hnd
      have hlen : vs.length ≤ fuel := by
        simp only [List.length_cons] at hf
        omega
      cases hk : key v with
      | none =>
        have hvs : (v :: vs).filter (fun w => w != v) = vs := by
          simp [List.filter_bne_eq_self_of_not_mem hnd.1]
        have htail (c : Nat) : (vs.filter (fun w => key w == some c)).IsInfix vs := by
          rw [← hvs]
          exact filter_infix_in_filter (hc c)
        simp only [clusterBlocks, hk, List.flatten_cons, ih vs hlen hnd.2 htail,
          List.singleton_append]
      | some c =>
        let pick : Nat → Bool := fun w => key w == some c
        let rest := vs.filter (fun w => key w != some c)
        have hp : pick v = true := by simp [pick, hk]
        have hpref : ((v :: vs).filter pick).IsPrefix (v :: vs) := by
          apply (List.infix_cons_iff.mp (hc c)).resolve_right
          intro h
          exact hnd.1 (h.subset (List.mem_filter.mpr ⟨by simp, hp⟩))
        have hrest : (v :: vs).filter (fun w => !pick w) = rest := by
          simp [pick, rest, hk, bne]
        have htail (d : Nat) : (rest.filter (fun w => key w == some d)).IsInfix rest := by
          rw [← hrest]
          exact filter_infix_in_filter (hc d)
        have hrlen : rest.length ≤ fuel := Nat.le_trans (List.length_filter_le _ vs) hlen
        have hrnd : rest.Nodup := List.Nodup.sublist List.filter_sublist hnd.2
        rw [clusterBlocks, hk, List.flatten_cons]
        change (v :: vs.filter pick) ++ (clusterBlocks key fuel rest).flatten = v :: vs
        rw [ih rest hrlen hrnd htail]
        have he := filter_partition_of_prefix hpref
        rw [hrest, List.filter_cons_of_pos hp] at he
        exact he

private theorem cons_prefix_eq (path : List Nat) (c : Nat) (pref : List Nat) :
    (c :: pref).isPrefixOf path = ((path.head? == some c) && pref.isPrefixOf path.tail) := by
  cases path with
  | nil => rfl
  | cons d ds =>
    simp only [List.isPrefixOf_cons_cons, List.head?_cons, List.tail_cons, Option.some_beq_some,
      BEq.comm]

private theorem sibLevel_tied_pair (num : Nat → Nat) (fuel : Nat)
    (path : Nat → List Nat) (nodes pref : List Nat) {a b A B : Nat} {ra rb : List Nat}
    (hf : pref.length < fuel) (hnd : nodes.Nodup)
    (hc : ∀ P : List Nat, (nodes.filter (fun v => P.isPrefixOf (path v))).IsInfix nodes)
    (ha : a ∈ nodes) (hb : b ∈ nodes) (hpa : path a = pref ++ A :: ra)
    (hpb : path b = pref ++ B :: rb) (hne : A ≠ B) (htie : num A = num B)
    (hab : [a, b].Sublist nodes) : [a, b].Sublist (sibLevel num path fuel nodes) := by
  induction fuel generalizing path nodes pref with
  | zero => omega
  | succ fuel ih =>
    let key : Nat → Option Nat := fun v => (path v).head?
    let blocks := clusterBlocks key (nodes.length + 1) nodes
    let g : List Nat → Item := fun X =>
      (key (X.headD 0), if (key (X.headD 0)).isSome then
        sibLevel num (fun v => (path v).tail) fuel X else X)
    change [a, b].Sublist (sibMerge num (blocks.map g))
    obtain ⟨Xa, hXa, haX⟩ := clusterBlocks_mem_block key (nodes.length + 1) nodes ha
    obtain ⟨Xb, hXb, hbX⟩ := clusterBlocks_mem_block key (nodes.length + 1) nodes hb
    have huniform {X : List Nat} {v u c : Nat} (hX : X ∈ blocks)
        (hv : v ∈ X) (hu : u ∈ X) (hk : key v = some c) : key u = some c :=
      (clusterBlocks_uniform key (nodes.length + 1) nodes (Nat.le_succ _) X hX u hu v hv).trans hk
    have hg {X : List Nat} {v c : Nat} (hX : X ∈ blocks) (hv : v ∈ X)
        (hk : key v = some c) :
        g X = (some c, sibLevel num (fun w => (path w).tail) fuel X) := by
      have hhead := huniform hX hv (headD_mem_of_ne_nil (List.ne_nil_of_mem hv)) hk
      rw [List.headD_eq_head?_getD] at hhead
      simp [g, hhead]
    cases pref with
    | nil =>
      have hka : key a = some A := by simp [key, hpa]
      have hkb : key b = some B := by simp [key, hpb]
      have hgA := hg hXa haX hka
      have hgB := hg hXb hbX hkb
      have hblocks : Xa ≠ Xb := by
        intro he
        have h := hgA.symm.trans ((congrArg g he).trans hgB)
        exact hne (Option.some.inj (congrArg Prod.fst h))
      have hpairs : [Xa, Xb].Sublist blocks := by
        rcases pair_sublist_or_reverse hXa hXb hblocks with h | h
        · exact h
        have hflat : blocks.flatten = nodes :=
          clusterBlocks_flatten_of_contiguous key _ nodes (Nat.le_succ _) hnd (fun c => by
            simpa only [key, cons_prefix_eq, List.isPrefixOf_nil_left, Bool.and_true] using hc [c])
        have hrev := pair_sublist_flatten blocks Xb Xa b a h hbX haX
        rw [hflat] at hrev
        exact (Nat.lt_asymm (idxOf_pair_lt hnd hab) (idxOf_pair_lt hnd hrev)).elim
      let items := blocks.map g
      let tagged : Item → Bool := fun t => t.1.isSome
      let le : Item → Item → Bool := fun x y => decide (num (x.1.getD 0) ≤ num (y.1.getD 0))
      have htagA : tagged (g Xa) = true := by simp [tagged, hgA]
      have htagB : tagged (g Xb) = true := by simp [tagged, hgB]
      have htagged : [g Xa, g Xb].Sublist (items.filter tagged) := by
        simpa only [List.map_cons, List.map_nil, List.filter_cons_of_pos htagA,
          List.filter_cons_of_pos htagB, List.filter_nil] using (hpairs.map g).filter tagged
      have hsorted : [g Xa, g Xb].Sublist (sibSorted num items) := by
        unfold sibSorted
        apply List.pair_sublist_mergeSort (le := le)
        · intro x y z hxy hyz
          simp only [le, decide_eq_true_eq] at hxy hyz ⊢
          exact Nat.le_trans hxy hyz
        · intro x y
          rcases Nat.le_total (num (x.1.getD 0)) (num (y.1.getD 0)) with h | h <;>
            simp [le, h]
        · simp [le, hgA, hgB, htie]
        · exact htagged
      have hplace : (place items (sibSorted num items)).filter tagged = sibSorted num items :=
        place_filter _ _ (List.mergeSort_perm _ _).length_eq
          (fun t ht => (List.mem_filter.mp ((List.mergeSort_perm _ _).mem_iff.mp ht)).2)
      have hsub : (sibSorted num items).Sublist (place items (sibSorted num items)) := by
        have hs := List.filter_sublist (p := tagged) (l := place items (sibSorted num items))
        rw [hplace] at hs
        exact hs
      have ha' : a ∈ (g Xa).2 := by
        rw [hgA]
        exact (sibLevel_perm _ _ _ _).mem_iff.mpr haX
      have hb' : b ∈ (g Xb).2 := by
        rw [hgB]
        exact (sibLevel_perm _ _ _ _).mem_iff.mpr hbX
      exact pair_sublist_flatten _ _ _ a b ((hsorted.trans hsub).map Prod.snd) ha' hb'
    | cons q pref =>
      have hka : key a = some q := by simp [key, hpa]
      have hkb : key b = some q := by simp [key, hpb]
      have he := clusterBlocks_same_block key (nodes.length + 1) nodes (Nat.le_succ _)
        hXa hXb haX hbX hka hkb
      subst Xb
      have hXsub : Xa.Sublist nodes := clusterBlocks_sublist key (nodes.length + 1) nodes Xa hXa
      have hXnd : Xa.Nodup := List.Nodup.sublist hXsub hnd
      let keep : Nat → Bool := fun v => key v == some q
      have hself : Xa.filter keep = Xa := List.filter_eq_self.mpr (fun v hv => by
        simp [keep, huniform hXa haX hv hka])
      have hsub := hXsub.filter keep
      rw [hself] at hsub
      have hXeq : Xa = nodes.filter keep := by
        apply hsub.eq_of_length_le
        apply List.Nodup.length_le_of_subset (List.Nodup.sublist List.filter_sublist hnd)
        intro v hv
        obtain ⟨hm, hk⟩ := List.mem_filter.mp hv
        have hk' : key v = some q := by simpa only [keep, beq_iff_eq] using hk
        obtain ⟨X, hX, hvX⟩ := clusterBlocks_mem_block key (nodes.length + 1) nodes hm
        have hsame := clusterBlocks_same_block key (nodes.length + 1) nodes (Nat.le_succ _)
          hX hXa hvX haX hk' hka
        exact hsame ▸ hvX
      have htail (s : List Nat) :
          (Xa.filter (fun v => s.isPrefixOf (path v).tail)).IsInfix Xa := by
        rw [hXeq, List.filter_filter]
        have ht := (hc (q :: s)).filter keep
        simp only [List.filter_filter, cons_prefix_eq, keep, key, Bool.and_self_left] at ht
        simpa only [keep, key, Bool.and_comm] using ht
      have hrec : [a, b].Sublist (sibLevel num (fun v => (path v).tail) fuel Xa) := by
        apply ih (pref := pref)
        · simp only [List.length_cons] at hf
          omega
        · exact hXnd
        · exact htail
        · exact haX
        · exact hbX
        · simp [hpa]
        · simp [hpb]
        · exact sub_pair_restrict hXsub hnd haX hbX hab
      exact hrec.trans (sublist_sibMerge num (List.mem_map.mpr ⟨Xa, hXa, hg hXa haX hka⟩))

theorem siblingLayer_tied_pair_iff
    {p : Proper} {num : Nat → Nat}
    {row pref ra rb : List Nat} {a b A B : Nat}
    (hnd : row.Nodup) (hc : OrderImpl.ClusterContiguous p row)
    (ha : a ∈ row) (hb : b ∈ row)
    (hpa : OrderImpl.nodePath p a = pref ++ A :: ra)
    (hpb : OrderImpl.nodePath p b = pref ++ B :: rb)
    (hne : A ≠ B) (htie : num A = num B) :
    [a, b].Sublist row ↔ [a, b].Sublist (OrderImpl.siblingLayer p num row) := by
  have hf : pref.length < sibFuel p row := by
    have hmax := (fold_max_lower (fun v => (nodePath p v).length) row 0).2 a ha
    simp only [hpa, List.length_append, List.length_cons] at hmax
    unfold sibFuel
    omega
  refine ⟨sibLevel_tied_pair num _ _ row pref hf hnd hc ha hb hpa hpb hne htie, ?_⟩
  intro hab
  have hneab : a ≠ b := by
    intro he
    subst b
    have h := List.append_cancel_left (hpa.symm.trans hpb)
    exact hne (Option.some.inj (congrArg List.head? h))
  rcases pair_sublist_or_reverse ha hb hneab with h | h
  · exact h
  have hrev : [b, a].Sublist (siblingLayer p num row) :=
    sibLevel_tied_pair num _ _ row pref hf hnd hc hb ha hpb hpa hne.symm htie.symm h
  have hout : (siblingLayer p num row).Nodup := (siblingLayer_perm p num row).nodup_iff.mpr hnd
  exact (Nat.lt_asymm (idxOf_pair_lt hout hab) (idxOf_pair_lt hout hrev)).elim

end Elegant.Layered.PipelineImpl

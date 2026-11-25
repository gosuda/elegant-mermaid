import Elegant.Layered.RegionC5ActiveSelected
import Elegant.Layered.FrameClearanceBottomFacts

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private def c5Bottom (cg : Graph) (top : Node) : Option (Node × Nat) :=
  cg.nodes.zipIdx.find? fun q => q.1.border == 2 && q.1.decl == top.decl

private theorem c5PrefixOfDropLast {a b : List Nat} (hp : a <+: b)
    (hne : a ≠ b) : a <+: b.dropLast := by
  obtain ⟨rest, rfl⟩ := hp
  have hr : rest ≠ [] := by
    intro hr
    exact hne (by simp [hr])
  exact ⟨rest.dropLast, (List.dropLast_append_of_ne_nil hr).symm⟩

theorem activeCandidateOriginalFrameRankWindow
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {s : RegionSpec} {index : Nat} {cg : Graph} {run : Run} {rm : ComponentRegions}
    (hrun : componentRunR execution.params (exactDecls exactIds inp) (some s) inp
      (componentCandidateR (some s) execution.graph comp index) execution.measured
      (candidateOrder index) = .ok (cg, run))
    (hactive : newComponentRegions (some s) execution.params inp
      (componentCandidateR (some s) execution.graph comp index) = .ok (some rm))
    {t : Nat} {top : Node} (ht : cg.nodes[t]? = some top) (htop : top.border = -2) :
    ∃ (b : Nat) (bot : Node), cg.nodes[b]? = some bot ∧ bot.border = 2 ∧ bot.decl = top.decl ∧
      bot.clusterPath = top.clusterPath ∧
      (∀ {i : Nat} {m : Node}, cg.nodes[i]? = some m → m.border = 2 → m.decl = top.decl → i = b) ∧
      ∀ {i : Nat} {m : Node}, cg.nodes[i]? = some m → m.clusterPath.contains top.decl = true →
        rk run.proper.rank t ≤ rk run.proper.rank i ∧ rk run.proper.rank i ≤ rk run.proper.rank b := by
  let g := componentCandidateR (some s) execution.graph comp index
  let c := componentCandidate execution.graph comp index
  obtain ⟨_, _, _, _, _, _, _, _, hrank, _, _, _, _, _, _⟩ :=
    componentRunR_active_allocation_stages hrun hactive
  have hnodes : cg.nodes = g.nodes := rankEquivalentR_nodes_eq hrank
  have hcnodes : c.nodes = g.nodes := by
    dsimp [c]
    rw [componentCandidate_nodes]
    rfl
  have hg {i : Nat} {n : Node} (h : g.nodes[i]? = some n) : c.nodes[i]? = some n := by
    rwa [hcnodes]
  have hlines := boxLines_length execution.lines_eq
  have botExists {i : Nat} {n : Node} (hi : g.nodes[i]? = some n) (hb : n.border = -2) :
      ∃ p, c5Bottom g n = some p := by
    unfold c5Bottom
    rw [← hcnodes]
    exact X_componentRun_cg_bottom_find execution.graph0_eq execution.graph_eq hlines hcomp
      (hg hi) hb
  have botFind {i : Nat} {n : Node} (hi : g.nodes[i]? = some n) (hb : n.border = 2) :
      c5Bottom g n = some (n, i) := by
    unfold c5Bottom
    rw [← hcnodes]
    exact X_bottom_find_eq execution.graph0_eq execution.graph_eq hcomp (hg hi) hb
  have botKeys {n : Node} {b : Node × Nat} (hb : c5Bottom g n = some b) :
      g.nodes[b.2]? = some b.1 ∧ b.1.border = 2 ∧ b.1.decl = n.decl := by
    unfold c5Bottom at hb
    exact ⟨List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hb),
      by simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some hb⟩
  have topBox {i : Nat} {n : Node} (hi : g.nodes[i]? = some n) (hb : n.border = -2) :=
    X_cg_group_box execution.graph0_eq execution.graph_eq (hg hi) hb
  have botBox {i : Nat} {n : Node} (hi : g.nodes[i]? = some n) (hb : n.border = 2) :=
    X_cg_bottom_box execution.graph0_eq execution.graph_eq (hg hi) hb
  have botPath {i : Nat} {n : Node} {b : Node × Nat}
      (hi : g.nodes[i]? = some n) (htop : n.border = -2) (hb : c5Bottom g n = some b) :
      b.1.clusterPath = n.clusterPath := by
    obtain ⟨hiB, hbB, hd⟩ := botKeys hb
    obtain ⟨tb, htb, htp⟩ := topBox hi htop
    obtain ⟨bb, hbb, hbp⟩ := botBox hiB hbB
    rw [hd, htb] at hbb
    rw [hbp, htp, hd, Option.some.inj hbb]
  have topOfBot {i : Nat} {n : Node} (hi : g.nodes[i]? = some n) (hb : n.border = 2) :
      ∃ (j : Nat) (a : Node), g.nodes[j]? = some a ∧ a.border = -2 ∧ a.clusterPath = n.clusterPath ∧
        c5Bottom g a = some (n, i) := by
    obtain ⟨a, ha⟩ := X_componentRun_cg_top_of_bottom execution.graph0_eq execution.graph_eq
      hlines hcomp (hg hi) hb
    have hkey : a.1.border = -2 ∧ a.1.clusterPath = n.clusterPath := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some ha
    have hget : c.nodes[a.2]? = some a.1 :=
      List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some ha)
    rw [hcnodes] at hget
    obtain ⟨ab, _, hap⟩ := topBox hget hkey.1
    obtain ⟨nb, _, hnp⟩ := botBox hi hb
    have hd := congrArg List.getLast? hkey.2
    have hd' : a.1.decl = n.decl := by simpa [hap, hnp] using hd
    exact ⟨a.2, a.1, hget, hkey.1, hkey.2, by simpa [c5Bottom, hd'] using botFind hi hb⟩
  have step {a b : Nat} (he : (⟨a, b, 1, 0, false⟩ : Edge) ∈ Compound.constraints g) :
      rk run.proper.rank a < rk run.proper.rank b := by
    obtain ⟨ha, hb⟩ := constraints_bounded g _ he
    have h := componentRunR_compound_feasible hrun he ha hb
    change 1 ≤ rk run.proper.rank b - rk run.proper.rank a at h
    omega
  have nested {a b : Nat} {an bn : Node} {ab bb : Node × Nat}
      (ha : g.nodes[a]? = some an) (hb : g.nodes[b]? = some bn)
      (hta : an.border = -2) (htb : bn.border = -2)
      (hab : c5Bottom g an = some ab) (hbb : c5Bottom g bn = some bb)
      (hp : bn.clusterPath.dropLast = an.clusterPath) :
      rk run.proper.rank a < rk run.proper.rank b ∧
        rk run.proper.rank bb.2 < rk run.proper.rank ab.2 := by
    obtain ⟨hl, hr⟩ := compound_child_constraint_edges (parent := (an, a)) (child := (bn, b))
      (List.mem_zipIdx_iff_getElem?.mpr ha) hta hab
      (List.mem_zipIdx_iff_getElem?.mpr hb) htb hp hbb
    exact ⟨step hl, step hr⟩
  have axisWidth : ∀ (fuel a : Nat) (an : Node) (ab : Node × Nat),
      g.nodes[a]? = some an → an.border = -2 → c5Bottom g an = some ab →
      execution.lines.length + 2 - an.clusterPath.length = fuel →
      rk run.proper.rank a < rk run.proper.rank ab.2 := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | _ fuel ih =>
      intro a an ab ha hta hab hfuel
      let leaves := g.nodes.zipIdx.filter fun m => m.1.border == 0 && m.1.clusterPath.contains an.decl
      let children := (g.nodes.zipIdx.filter fun m => m.1.border == -2).filter
        fun m => m.1.clusterPath.dropLast == an.clusterPath
      by_cases hl : leaves.isEmpty = true
      · by_cases hc : children.isEmpty = true
        · exact step (compound_empty_group_constraint_edge (top := (an, a))
            (List.mem_zipIdx_iff_getElem?.mpr ha) hta hab hl hc)
        · obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil children (fun he => hc (by simp [he]))
          obtain ⟨hq', hpath⟩ := List.mem_filter.mp hq
          obtain ⟨hq'', htag⟩ := List.mem_filter.mp hq'
          have hch := List.mem_zipIdx_iff_getElem?.mp hq''
          have htag' : q.1.border = -2 := by simpa only [beq_iff_eq] using htag
          have hpath' : q.1.clusterPath.dropLast = an.clusterPath := by
            simpa only [beq_iff_eq] using hpath
          obtain ⟨qb, hqb⟩ := botExists hch htag'
          obtain ⟨qbox, _, hqp⟩ := topBox hch htag'
          have hqpos : 0 < q.1.clusterPath.length := by simp [hqp]
          have hqmax : q.1.clusterPath.length ≤ execution.lines.length + 1 := by
            rw [hqp, List.length_append, List.length_singleton, hlines]
            change (Compound.ancestors inp.boxes inp.boxes.length qbox.parent).length + 1 ≤ _
            have hbnd := ancestors_length_le inp.boxes inp.boxes.length qbox.parent
            omega
          have hlen := congrArg List.length hpath'
          rw [List.length_dropLast] at hlen
          have hlt : execution.lines.length + 2 - q.1.clusterPath.length < fuel := by omega
          obtain ⟨hlo, hhi⟩ := nested ha hch hta htag' hab hqb hpath'
          exact Int.lt_trans hlo (Int.lt_trans (ih _ hlt _ _ _ hch htag' hqb rfl) hhi)
      · obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil leaves (fun he => hl (by simp [he]))
        obtain ⟨hq', hcond⟩ := List.mem_filter.mp hq
        obtain ⟨hq0, hpath⟩ := Bool.and_eq_true_iff.mp hcond
        have hwin := componentRunR_compound_leaf_rank_window hrun (top := (an, a)) (member := q)
          (List.mem_zipIdx_iff_getElem?.mpr ha) hta hab hq' (by simpa using hq0) hpath
        exact Int.lt_trans hwin.1 hwin.2
  have nestedWindow : ∀ (fuel a m : Nat) (an mn : Node) (ab mb : Node × Nat),
      g.nodes[a]? = some an → g.nodes[m]? = some mn → an.border = -2 → mn.border = -2 →
      c5Bottom g an = some ab → c5Bottom g mn = some mb →
      an.clusterPath <+: mn.clusterPath → mn.clusterPath.length - an.clusterPath.length = fuel →
      rk run.proper.rank a ≤ rk run.proper.rank m ∧
        rk run.proper.rank mb.2 ≤ rk run.proper.rank ab.2 := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | _ fuel ih =>
      intro a m an mn ab mb ha hm hat hmt hab hmb hp hlen
      by_cases hsame : an.clusterPath = mn.clusterPath
      · have he := X_cg_top_unique execution.graph0_eq execution.graph_eq hcomp
          (hg ha) (hg hm) hat hmt hsame
        subst m
        have he := Option.some.inj (ha.symm.trans hm)
        subst mn
        have hb := Option.some.inj (hab.symm.trans hmb)
        subst mb
        exact ⟨Int.le_refl _, Int.le_refl _⟩
      · have hlt : an.clusterPath.length < mn.clusterPath.length := by
          obtain ⟨rest, he⟩ := hp
          have hn : rest ≠ [] := fun h => hsame (by simpa [h] using he)
          rw [← he, List.length_append]
          have := List.length_pos_iff.mpr hn
          omega
        have hne := (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq
          (hg ha)).2 hat
        obtain ⟨p, hpfind⟩ := X_candidate_parent_top_exists execution.graph0_eq execution.graph_eq
          hlines hwf hfp hcomp index (x := (mn, m))
          (List.mem_zipIdx_iff_getElem?.mpr (hg hm)) hmt hp hlt hne
        have hpm : c.nodes[p.2]? = some p.1 :=
          List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hpfind)
        rw [hcnodes] at hpm
        have hpc : p.1.border = -2 ∧ p.1.clusterPath = mn.clusterPath.dropLast := by
          simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some hpfind
        obtain ⟨pb, hpb⟩ := botExists hpm hpc.1
        have hpp : an.clusterPath <+: p.1.clusterPath := by
          rw [hpc.2]
          exact c5PrefixOfDropLast hp hsame
        have hplen : p.1.clusterPath.length - an.clusterPath.length < fuel := by
          rw [hpc.2, List.length_dropLast]
          omega
        obtain ⟨hl, hr⟩ := ih _ hplen a p.2 an p.1 ab pb ha hpm hat hpc.1 hab hpb hpp rfl
        obtain ⟨hpL, hpR⟩ := nested hpm hm hpc.1 hmt hpb hmb hpc.2.symm
        exact ⟨Int.le_trans hl (Int.le_of_lt hpL), Int.le_trans (Int.le_of_lt hpR) hr⟩
  have ht' : g.nodes[t]? = some top := by rwa [← hnodes]
  obtain ⟨b, hb⟩ := botExists ht' htop
  obtain ⟨hlook, htag, hdecl⟩ := botKeys hb
  refine ⟨b.2, b.1, by rwa [hnodes], htag, hdecl, botPath ht' htop hb, ?_, ?_⟩
  · intro i m hm htM hdM
    rw [hnodes] at hm
    have he : c5Bottom g top = some (m, i) := by
      simpa [c5Bottom, hdM] using botFind hm htM
    exact congrArg Prod.snd (Option.some.inj (he.symm.trans hb))
  · intro i m hm hin
    rw [hnodes] at hm
    rcases (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq
      (hg hm)).1 with hleaf | hmTop | hmBot
    · obtain ⟨hl, hr⟩ := componentRunR_compound_leaf_rank_window hrun
        (top := (top, t)) (member := (m, i))
        (List.mem_zipIdx_iff_getElem?.mpr ht') htop hb
        (List.mem_zipIdx_iff_getElem?.mpr hm) hleaf hin
      exact ⟨Int.le_of_lt hl, Int.le_of_lt hr⟩
    · obtain ⟨mb, hmb⟩ := botExists hm hmTop
      obtain ⟨_, hboxT, hpT⟩ := topBox ht' htop
      obtain ⟨_, hboxM, hpM⟩ := topBox hm hmTop
      have hp := X_cg_scope_prefix hwf hboxT hpT hboxM hpM hin
      obtain ⟨hl, hr⟩ := nestedWindow _ t i top m b mb ht' hm htop hmTop hb hmb hp rfl
      exact ⟨hl, Int.le_trans (Int.le_of_lt (axisWidth _ i m mb hm hmTop hmb rfl)) hr⟩
    · obtain ⟨j, a, ha, htagA, hpathA, hmb⟩ := topOfBot hm hmBot
      obtain ⟨_, hboxT, hpT⟩ := topBox ht' htop
      obtain ⟨_, hboxM, hpM⟩ := botBox hm hmBot
      have hp := X_cg_scope_prefix hwf hboxT hpT hboxM hpM hin
      rw [← hpathA] at hp
      obtain ⟨hl, hr⟩ := nestedWindow _ t j top a b (m, i) ht' ha htop htagA hb hmb hp rfl
      exact ⟨Int.le_trans hl (Int.le_of_lt (axisWidth _ j a (m, i) ha htagA hmb rfl)), hr⟩

end Elegant.Layered.PipelineImpl

import Elegant.Layered.GroupBottomBoundaryProof
import Elegant.Layered.BottomClearanceExistence
import Elegant.Layered.ForeignFrameClearance
import Elegant.Layered.LoopResGroupHullRightMemberProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl
/-- TRUTH FIRST: `LoopResGroupHullRightAncestorRanks` (in
`LoopResGroupHullRightMemberProof`) is TRUE. Probe
(`wip/Probe/LoopResGroupHullRightMemberProbe`: `checkAncRanks` = top order and
bottom reverse order for every nested group-top pair): `ancRanks=true` on all
five candidates of `emptyNested` (empty looping group, no plain nodes),
`nestedGrp`, and three-level `emptyNest3`. Own probe
(`wip/Probe/LoopResGroupHullRightAncestorRanksProbe`): `ancRanks=true` on all
five candidates of `singleSelf` (one root group, self-loop, no plain nodes),
`twoRoots` (two disjoint looping groups), and `badParent` (dangling parent, not
well-formed). Hence this file proves the residual outright: the single nesting
step rides the `Compound.constraints` nested edges (`parentTop -> childTop`
and `childBottom -> parentBottom`) through `ranked_compound_child_interval`,
and the full prefix order follows by strong induction on the path-length gap,
stepping through the executed parent top (`candidate_parent_top_exists`) with
bottom markers from `componentRun_cg_bottom_find`. -/
private theorem lrr_take_is_prefix {α : Type} (l : List α) (n : Nat) :
    l.take n <+: l :=
  ⟨l.drop n, by simp⟩
private theorem lrr_prefix_take_eq {α : Type} {p s : List α} (hp : p <+: s) :
    s.take p.length = p := by
  obtain ⟨r, rfl⟩ := hp
  simp
private theorem lrr_prefix_of_common_prefix {α : Type} {p q s : List α}
    (hp : p <+: s) (hq : q <+: s) (hle : p.length ≤ q.length) : p <+: q := by
  obtain ⟨r₁, rfl⟩ := hp
  obtain ⟨r₂, hr⟩ := hq
  have h1 : (p ++ r₁).take p.length = p := lrr_prefix_take_eq ⟨r₁, rfl⟩
  have h2 : (q ++ r₂).take p.length = q.take p.length := by
    have hz : p.length - q.length = 0 := by omega
    simp [List.take_append, hz]
  rw [← hr] at h1
  rw [h2] at h1
  rw [← h1]
  exact lrr_take_is_prefix q p.length

private theorem lrr_prefix_antisymm {α : Type} {p q : List α}
    (h1 : p <+: q) (h2 : q <+: p) : p = q := by
  have e : q.take p.length = p := lrr_prefix_take_eq h1
  have hle1 : p.length ≤ q.length := by
    obtain ⟨r, rfl⟩ := h1
    rw [List.length_append]
    exact Nat.le_add_right _ _
  have hle2 : q.length ≤ p.length := by
    obtain ⟨r, rfl⟩ := h2
    rw [List.length_append]
    exact Nat.le_add_right _ _
  have hlen : p.length = q.length := by omega
  have e2 : q.take q.length = q := by simp
  rw [← hlen] at e2
  exact e.symm.trans e2
private theorem lrr_prefix_length_lt {α : Type} {p s : List α}
    (hp : p <+: s) (hne : p ≠ s) : p.length < s.length := by
  rcases Nat.lt_or_ge p.length s.length with h | h
  · exact h
  · have h2 : s <+: p :=
      lrr_prefix_of_common_prefix ⟨[], by simp⟩ hp h
    exact absurd (lrr_prefix_antisymm hp h2) hne
private theorem lrr_dropLast_is_prefix {α : Type} (l : List α) : l.dropLast <+: l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    cases as with
    | nil => exact ⟨[a], rfl⟩
    | cons b bs =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨r, by simpa using congrArg (a :: ·) hr⟩
private theorem lrr_cg_path_last {boxes : List ModelBox} {box : ModelBox} {d : Nat}
    {p : List Nat} (h : p = Compound.path boxes box ++ [d]) :
    p.getLast? = some d := by
  rw [h]
  simp
private theorem lrr_cg_group_box {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ box : ModelBox, inp.boxes[node.decl]? = some box ∧
      node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
  obtain ⟨_, ho, hsource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨hdecl, effective, heffective, _, hpath⟩ :=
    measuredGraph_group_origin hgraph hsource hgroup
  rw [hdecl, List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  rw [← hdecl] at hbox
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  refine ⟨box, hbox, ?_⟩
  rw [← hchange] at hpath
  rw [hpathMap] at hpath
  exact hpath
private theorem lrr_cg_top_unique {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {a b : Nat} {na nb : Node}
    (ha : (componentCandidate graph comp candidate).nodes[a]? = some na)
    (hb : (componentCandidate graph comp candidate).nodes[b]? = some nb)
    (hbA : na.border = -2) (hbB : nb.border = -2)
    (hpath : na.clusterPath = nb.clusterPath) : a = b := by
  have hlastA : na.clusterPath.getLast? = some na.decl := by
    obtain ⟨box, hbox, hpathA⟩ := lrr_cg_group_box hgraph ha hbA
    exact lrr_cg_path_last hpathA
  have hlastB : nb.clusterPath.getLast? = some nb.decl := by
    obtain ⟨box, hbox, hpathB⟩ := lrr_cg_group_box hgraph hb hbB
    exact lrr_cg_path_last hpathB
  have hdecl : na.decl = nb.decl := by
    have h := congrArg List.getLast? hpath
    rw [hlastA, hlastB] at h
    exact Option.some.inj h
  obtain ⟨aSrc, haSrc, hsa⟩ := componentCandidate_nonplain_source ha (by omega)
  obtain ⟨bSrc, hbSrc, hsb⟩ := componentCandidate_nonplain_source hb (by omega)
  obtain ⟨hdeclA, _, _, _, _⟩ := measuredGraph_group_origin hgraph hsa hbA
  obtain ⟨hdeclB, _, _, _, _⟩ := measuredGraph_group_origin hgraph hsb hbB
  have hsrc : aSrc = bSrc := by omega
  exact nodup_map_inj_aux (fun x => x)
    (by simpa using components_nodup graph comp hcomp) haSrc hbSrc hsrc
private theorem lrr_nested_top_rank {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
    {rr : RankImpl.RankResult}
    (hrr : rankWithBudget (Compound.rankingGraph
      (componentCandidate graph comp candidate)) = .ok rr) :
    ∀ delta : Nat, ∀ a b : Nat, ∀ na nb : Node,
      (componentCandidate graph comp candidate).nodes[a]? = some na →
      na.border = -2 →
      (componentCandidate graph comp candidate).nodes[b]? = some nb →
      nb.border = -2 →
      na.clusterPath <+: nb.clusterPath →
      nb.clusterPath.length - na.clusterPath.length = delta →
      rk rr.ranks a ≤ rk rr.ranks b := by
  have hparEx := candidate_parent_top_exists hgraph hlines hwf hframed hcomp candidate
  intro delta
  induction delta using Nat.strongRecOn with
  | _ delta ih =>
    intro a b na nb ha hbA hb hbB hpre hdelta
    by_cases heq : na.clusterPath = nb.clusterPath
    · have hab : a = b := lrr_cg_top_unique hgraph hcomp ha hb hbA hbB heq
      subst hab
      exact Int.le_refl _
    · have hlt : na.clusterPath.length < nb.clusterPath.length :=
        lrr_prefix_length_lt hpre heq
      have hbne : nb.clusterPath ≠ [] :=
        (componentCandidate_marker_shape hgraph hb).2 hbB
      have hna_ne : na.clusterPath ≠ [] :=
        (componentCandidate_marker_shape hgraph ha).2 hbA
      obtain ⟨u, hu⟩ := hparEx (nb, b)
        (List.mem_zipIdx_iff_getElem?.mpr hb) hbB na.clusterPath hpre hlt hna_ne
      have huPred := List.find?_some hu
      simp only [Bool.and_eq_true, beq_iff_eq] at huPred
      obtain ⟨huBorder, huPath⟩ := huPred
      have huMem : u ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
        List.mem_of_find?_eq_some hu
      have huLookup : (componentCandidate graph comp candidate).nodes[u.2]? = some u.1 :=
        List.mem_zipIdx_iff_getElem?.mp huMem
      have hdropLen : u.1.clusterPath.length = nb.clusterPath.length - 1 := by
        rw [huPath]
        exact List.length_dropLast ..
      have hnbpos : 0 < nb.clusterPath.length :=
        Nat.pos_of_ne_zero (fun h => hbne (List.length_eq_zero_iff.mp h))
      have hleU : na.clusterPath.length ≤ u.1.clusterPath.length := by omega
      have hpreU : na.clusterPath <+: u.1.clusterPath :=
        lrr_prefix_of_common_prefix hpre
          (huPath ▸ lrr_dropLast_is_prefix nb.clusterPath) hleU
      have hdeltaU : u.1.clusterPath.length - na.clusterPath.length < delta := by omega
      obtain ⟨ubot, hubot⟩ :=
        componentRun_cg_bottom_find hgraph hlines hcomp huLookup huBorder
      obtain ⟨nbbot, hnbbot⟩ := componentRun_cg_bottom_find hgraph hlines hcomp hb hbB
      have hpathUB : nb.clusterPath.dropLast = u.1.clusterPath := huPath.symm
      have hIH := ih _ hdeltaU a u.2 na u.1 ha hbA huLookup huBorder hpreU rfl
      have hinterv := ranked_compound_child_interval (parent := (u.1, u.2))
        (child := (nb, b)) hrr
        (List.mem_zipIdx_iff_getElem?.mpr huLookup) huBorder hubot
        (List.mem_zipIdx_iff_getElem?.mpr hb) hbB hpathUB hnbbot
      have hstep : rk rr.ranks u.2 + 1 ≤ rk rr.ranks b := hinterv.1
      omega
private theorem lrr_nested_bottom_rank {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
    {rr : RankImpl.RankResult}
    (hrr : rankWithBudget (Compound.rankingGraph
      (componentCandidate graph comp candidate)) = .ok rr) :
    ∀ delta : Nat, ∀ a b : Nat, ∀ na nb : Node, ∀ ba bb : Node × Nat,
      (componentCandidate graph comp candidate).nodes[a]? = some na →
      na.border = -2 →
      (componentCandidate graph comp candidate).nodes[b]? = some nb →
      nb.border = -2 →
      na.clusterPath <+: nb.clusterPath →
      nb.clusterPath.length - na.clusterPath.length = delta →
      (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
        entry.1.border == 2 && entry.1.decl == na.decl) = some ba →
      (componentCandidate graph comp candidate).nodes.zipIdx.find? (fun entry =>
        entry.1.border == 2 && entry.1.decl == nb.decl) = some bb →
      rk rr.ranks bb.2 ≤ rk rr.ranks ba.2 := by
  have hparEx := candidate_parent_top_exists hgraph hlines hwf hframed hcomp candidate
  intro delta
  induction delta using Nat.strongRecOn with
  | _ delta ih =>
    intro a b na nb ba bb ha hbA hb hbB hpre hdelta hba hbb
    by_cases heq : na.clusterPath = nb.clusterPath
    · have hab : a = b := lrr_cg_top_unique hgraph hcomp ha hb hbA hbB heq
      subst hab
      have hdecl : na.decl = nb.decl := by
        have hlastA : na.clusterPath.getLast? = some na.decl := by
          obtain ⟨box, hbox, hpathA⟩ := lrr_cg_group_box hgraph ha hbA
          exact lrr_cg_path_last hpathA
        have hlastB : nb.clusterPath.getLast? = some nb.decl := by
          obtain ⟨box, hbox, hpathB⟩ := lrr_cg_group_box hgraph hb hbB
          exact lrr_cg_path_last hpathB
        have h := congrArg List.getLast? heq
        rw [hlastA, hlastB] at h
        exact Option.some.inj h
      rw [hdecl] at hba
      have hbb_eq : bb = ba := Option.some.inj (hbb.symm.trans hba)
      rw [hbb_eq]
      exact Int.le_refl _
    · have hlt : na.clusterPath.length < nb.clusterPath.length :=
        lrr_prefix_length_lt hpre heq
      have hbne : nb.clusterPath ≠ [] :=
        (componentCandidate_marker_shape hgraph hb).2 hbB
      have hna_ne : na.clusterPath ≠ [] :=
        (componentCandidate_marker_shape hgraph ha).2 hbA
      obtain ⟨u, hu⟩ := hparEx (nb, b)
        (List.mem_zipIdx_iff_getElem?.mpr hb) hbB na.clusterPath hpre hlt hna_ne
      have huPred := List.find?_some hu
      simp only [Bool.and_eq_true, beq_iff_eq] at huPred
      obtain ⟨huBorder, huPath⟩ := huPred
      have huMem : u ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
        List.mem_of_find?_eq_some hu
      have huLookup : (componentCandidate graph comp candidate).nodes[u.2]? = some u.1 :=
        List.mem_zipIdx_iff_getElem?.mp huMem
      have hdropLen : u.1.clusterPath.length = nb.clusterPath.length - 1 := by
        rw [huPath]
        exact List.length_dropLast ..
      have hnbpos : 0 < nb.clusterPath.length :=
        Nat.pos_of_ne_zero (fun h => hbne (List.length_eq_zero_iff.mp h))
      have hleU : na.clusterPath.length ≤ u.1.clusterPath.length := by omega
      have hpreU : na.clusterPath <+: u.1.clusterPath :=
        lrr_prefix_of_common_prefix hpre
          (huPath ▸ lrr_dropLast_is_prefix nb.clusterPath) hleU
      have hdeltaU : u.1.clusterPath.length - na.clusterPath.length < delta := by omega
      obtain ⟨ubot, hubot⟩ :=
        componentRun_cg_bottom_find hgraph hlines hcomp huLookup huBorder
      obtain ⟨nbbot, hnbbot⟩ := componentRun_cg_bottom_find hgraph hlines hcomp hb hbB
      have hpathUB : nb.clusterPath.dropLast = u.1.clusterPath := huPath.symm
      have hIH := ih _ hdeltaU a u.2 na u.1 ba ubot ha hbA huLookup huBorder
        hpreU rfl hba hubot
      have hinterv := ranked_compound_child_interval (parent := (u.1, u.2))
        (child := (nb, b)) hrr
        (List.mem_zipIdx_iff_getElem?.mpr huLookup) huBorder hubot
        (List.mem_zipIdx_iff_getElem?.mpr hb) hbB hpathUB hnbbot
      have hbotStep : rk rr.ranks nbbot.2 + 1 ≤ rk rr.ranks ubot.2 := hinterv.2
      have hbbeq : bb = nbbot := Option.some.inj (hbb.symm.trans hnbbot)
      rw [hbbeq]
      omega
/-- Ancestor group tops rank in nesting order, bottoms in reverse: for two
group tops with the outer path prefixing the inner, the outer top ranks at or
above the inner top, and the inner bottom at or below the outer bottom. The
single nesting step is the `Compound.constraints` nested edge pair; the full
prefix order is strong induction on the path-length gap. -/
theorem loopResGroupHullRightAncestorRanks_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    LoopResGroupHullRightAncestorRanks execution hcomp hrun := by
  have hgraph : measuredGraph execution.params inp o execution.lines =
      .ok execution.graph := execution.graph_eq
  have hlines : execution.lines.length = inp.boxes.length :=
    boxLines_length execution.lines_eq
  intro rr hrr a b na nb ha hbA hb hbB hpre
  refine ⟨?_, ?_⟩
  · exact lrr_nested_top_rank hgraph hlines hwf hframed hcomp candidate hrr
      _ a b na nb ha hbA hb hbB hpre rfl
  · intro ba bb hba hbb
    exact lrr_nested_bottom_rank hgraph hlines hwf hframed hcomp candidate hrr
      _ a b na nb ba bb ha hbA hb hbB hpre rfl hba hbb
/-- Closed ordered-marker witness with no residual premise: the ancestor-rank
fact holds on every executed run, so `loopResGroupHullRightWitness_closed`
discharges its only open ingredient. -/
theorem loopResGroupHullRightWitness_closed' {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    LoopResGroupHullRightWitness
      (componentCandidate execution.graph comp candidate) run := by
  have hres : LoopResGroupHullRightAncestorRanks execution hcomp hrun :=
    loopResGroupHullRightAncestorRanks_holds hwf hfp execution hcomp hrun
  exact loopResGroupHullRightWitness_closed hwf hfp execution hcomp hrun hres
end PipelineImpl

end Layered
end Elegant

import Elegant.Layered.FrameClearanceBottomFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RouteImpl

private theorem isEmpty_false_ne_nil {α : Type} {l : List α} (h : l.isEmpty = false) : l ≠ [] := by
  intro hnil
  rw [hnil] at h
  simp at h

private theorem le_foldr_max {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

/-! ### Unit C: every candidate group top ranks strictly below its own bottom marker

Descending fuel induction on `maxLen - top.clusterPath.length` over the group-top markers of
the component candidate graph: a plain member pins the whole rank interval below the top, a
child-less member-less group is pinned by its direct top-to-bottom constraint edge, and a
nested group top descends to its child (whose cluster path is one declaration longer). -/

theorem componentRun_group_top_lt_bottom
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper),
      rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) = .ok rr ∧
      coordinateGraph P labeled = run.coordinateProper ∧
      NodeKeys (componentCandidate graph comp candidate) labeled ∧
      (∀ (key : Nat) (original : Node),
        (componentCandidate graph comp candidate).nodes[key]? = some original →
          labeled.nodes[key]? = some ⟨original, false, none, false⟩) ∧
      (∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
        labeled.rank[key]? = some rank) ∧
      ∀ (topIndex : Nat) (top : Node) (bottom : Node × Nat),
        (componentCandidate graph comp candidate).nodes[topIndex]? = some top →
        top.border = -2 →
        ((componentCandidate graph comp candidate).nodes.zipIdx.find? fun entry =>
          entry.1.border == 2 && entry.1.decl == top.decl) = some bottom →
        rk rr.ranks topIndex + 1 ≤ rk rr.ranks bottom.2 := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks⟩ :=
    componentRun_prepared_titled_source hgraph hcomp hrun
  refine ⟨rr, labeled, hrr, hc, hk, hrecords, hranks, ?_⟩
  let cg := componentCandidate graph comp candidate
  let maxLen := ((cg.nodes.filter fun n => n.border == -2).map
    (fun n => n.clusterPath.length)).foldr max 0
  have hbound : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      node.border = -2 → node.clusterPath.length ≤ maxLen := by
    intro index node hnode hgroup
    have hmem : node ∈ cg.nodes.filter (fun n => n.border == -2) :=
      List.mem_filter.mpr ⟨List.mem_of_getElem? hnode, by simp [hgroup]⟩
    exact le_foldr_max (List.mem_map_of_mem hmem)
  have hnonempty : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      node.border = -2 → node.clusterPath ≠ [] := by
    intro index node hnode hgroup hnil
    exact (componentCandidate_marker_shape hgraph hnode).2 hgroup hnil
  have main : ∀ fuel : Nat, ∀ (topIndex : Nat) (top : Node) (bottom : Node × Nat),
      cg.nodes[topIndex]? = some top →
      top.border = -2 →
      (cg.nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == top.decl) = some bottom →
      maxLen - top.clusterPath.length = fuel →
      rk rr.ranks topIndex + 1 ≤ rk rr.ranks bottom.2 := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | _ fuel ih =>
      intro topIndex top bottom htop hgroup hbottom hfuel
      cases hmemCase : (cg.nodes.zipIdx.filter fun entry =>
          entry.1.border == 0 && entry.1.clusterPath.contains top.decl).isEmpty with
      | false =>
        -- plain member pins the whole subtree interval
        have hmemNe : (cg.nodes.zipIdx.filter fun entry =>
            entry.1.border == 0 && entry.1.clusterPath.contains top.decl) ≠ [] :=
          isEmpty_false_ne_nil hmemCase
        obtain ⟨member, hmember⟩ := List.exists_mem_of_ne_nil _ hmemNe
        obtain ⟨hmemberZip, hmemberCond⟩ := List.mem_filter.mp hmember
        obtain ⟨hmemberPlain, hmemberInside⟩ := Bool.and_eq_true_iff.mp hmemberCond
        have hmemberPlain' : member.1.border = 0 := by simpa using hmemberPlain
        have hmemberInside' : member.1.clusterPath.contains top.decl = true := by
          simpa using hmemberInside
        obtain ⟨hleft, hright⟩ := ranked_compound_member_interval hrr
          (top := (top, topIndex)) (bottom := bottom) (member := member)
          (List.mem_zipIdx_iff_getElem?.mpr htop) hgroup hbottom
          hmemberZip hmemberPlain' hmemberInside'
        have hleft' : rk rr.ranks topIndex + 1 ≤ rk rr.ranks member.2 := hleft
        have hright' : rk rr.ranks member.2 + 1 ≤ rk rr.ranks bottom.2 := hright
        omega
      | true =>
        cases hchildCase : ((cg.nodes.zipIdx.filter fun entry => entry.1.border == -2).filter
            fun entry => entry.1.clusterPath.dropLast == top.clusterPath).isEmpty with
        | false =>
          -- nested group: descend to the child one declaration deeper
          have hchildNe : ((cg.nodes.zipIdx.filter fun entry => entry.1.border == -2).filter
              fun entry => entry.1.clusterPath.dropLast == top.clusterPath) ≠ [] :=
            isEmpty_false_ne_nil hchildCase
          obtain ⟨child, hchildMem⟩ := List.exists_mem_of_ne_nil _ hchildNe
          obtain ⟨hchildTop, hchildPath⟩ := List.mem_filter.mp hchildMem
          obtain ⟨hchildZip, hchildGroup⟩ := List.mem_filter.mp hchildTop
          have hchildGroup' : child.1.border = -2 := by simpa using hchildGroup
          have hchildIndex := List.mem_zipIdx_iff_getElem?.mp hchildZip
          obtain ⟨childBottomTitle, _, hchildFind0⟩ :=
            componentRun_prepared_group_bottom hgraph hcomp hrun hc hk hready hrecords
              hchildIndex hchildGroup'
          obtain ⟨childOriginal, _, _, _, _, hchildFind'⟩ :=
            candidate_titled_bottom_constraint_source hgraph hk hrecords hchildIndex
              hchildGroup' hchildFind0
          have hchildPair : cg.nodes.zipIdx.find? (fun entry =>
              entry.1.border == 2 && entry.1.decl == child.1.decl) =
              some (childOriginal, childBottomTitle.2) := hchildFind'
          have hpathEq : child.1.clusterPath.dropLast = top.clusterPath := by
            simpa using hchildPath
          have hdirect := ranked_compound_child_interval hrr
            (parent := (top, topIndex)) (parentBottom := bottom) (child := child)
            (childBottom := (childOriginal, childBottomTitle.2))
            (List.mem_zipIdx_iff_getElem?.mpr htop) hgroup hbottom
            hchildZip hchildGroup' hpathEq hchildPair
          obtain ⟨hleftDirect, hrightDirect⟩ := hdirect
          have hleftDirect' : rk rr.ranks topIndex + 1 ≤ rk rr.ranks child.2 := hleftDirect
          have hlength : child.1.clusterPath.length = top.clusterPath.length + 1 := by
            have hne : top.clusterPath ≠ [] := hnonempty topIndex top htop hgroup
            have hchildNonEmpty : child.1.clusterPath ≠ [] := by
              intro hempty
              rw [hempty, List.dropLast_nil] at hpathEq
              exact hne hpathEq.symm
            rw [← hpathEq, List.length_dropLast]
            have hchildLen := List.length_pos_iff.mpr hchildNonEmpty
            omega
          have hboundChild := hbound child.2 child.1 hchildIndex hchildGroup'
          have hpos : 0 < fuel := by omega
          have hfuelChild : maxLen - child.1.clusterPath.length = fuel - 1 := by omega
          have hih := ih (fuel - 1) (by omega) child.2 child.1
            (childOriginal, childBottomTitle.2) hchildIndex hchildGroup' hchildPair hfuelChild
          have hih' : rk rr.ranks child.2 + 1 ≤ rk rr.ranks (childOriginal, childBottomTitle.2).2 :=
            hih
          omega
        | true =>
          exact ranked_empty_group_interval hrr (top := (top, topIndex)) (bottom := bottom)
            (List.mem_zipIdx_iff_getElem?.mpr htop) hgroup hbottom hmemCase hchildCase
  intro topIndex top bottom htop hgroup hbottom
  exact main (maxLen - top.clusterPath.length) topIndex top bottom htop hgroup hbottom rfl

/-! ### Unit D: a nested candidate group's bottom ranks strictly below the outer group's bottom -/

theorem componentRun_nested_bottom_lt_outer_bottom
    {cg : Graph} {rr : RankImpl.RankResult}
    (hrank : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    {parent parentBottom child childBottom : Node × Nat}
    (hparent : parent ∈ cg.nodes.zipIdx) (hparentGroup : parent.1.border = -2)
    (hparentBottom : (cg.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == parent.1.decl) = some parentBottom)
    (hchild : child ∈ cg.nodes.zipIdx) (hchildGroup : child.1.border = -2)
    (hpath : child.1.clusterPath.dropLast = parent.1.clusterPath)
    (hchildBottom : (cg.nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == child.1.decl) = some childBottom) :
    rk rr.ranks childBottom.2 + 1 ≤ rk rr.ranks parentBottom.2 :=
  (ranked_compound_child_interval hrank hparent hparentGroup hparentBottom hchild
    hchildGroup hpath hchildBottom).2

end Elegant.Layered.PipelineImpl

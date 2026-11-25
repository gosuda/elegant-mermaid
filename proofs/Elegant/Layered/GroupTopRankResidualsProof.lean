import Elegant.Layered.GroupAnchorFactsProof
import Elegant.Layered.BottomClearanceNesting
import Elegant.Layered.BottomClearanceExistence
import Elegant.Layered.RouteProxyStart
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.BracketInsideRankFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.CgShape
import Elegant.Layered.PipelineFacts
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.CompoundPathFacts
import Elegant.Layered.Rank
import Elegant.Layered.Labels
import Elegant.Layered.SizingFacts
import Elegant.Layered.Normalize
import Elegant.Layered.Pipeline
import Elegant.Layered.Compound

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! ### Rank residuals behind the group top seam

`GroupTopSubtreeRankProper` (`GroupTopRank.lean`) splits into a candidate-graph
closure (`GroupTopSubtreeRankCg`: every original node whose cluster path
contains a group top's declaration ranks at or below the top) and a derived
closure (`ProperDerivedRank`: the same bound for dummies, side markers, and
title copies).  The combination is `groupTopSubtreeRankProper_of_seams`.

Route for the cg closure: `Compound.constraints` adds a ranking edge from each
group's top to every direct member and to the top of each directly nested
group; ranking respects every constraint edge
(`rankingGraph_constraint_feasible`).  A plain member is therefore one edge
below its top (`ranked_compound_member_interval`); a nested top descends
through its parent chain (`ranked_compound_child_interval` plus
`candidate_parent_top_exists`); a bottom marker is handled through its own
group top (`componentRun_cg_top_of_bottom`) and
`componentRun_group_top_lt_bottom`.

Route for derived nodes: a dummy lies on a chain whose endpoints both contain
the declaration (`componentRun_dummy_path_chain_source` plus
`commonPath_member_both`), so the cg closure bounds the tail and the chain
rank equation lifts it; a side marker shares its group top's cluster path and
sits inside the top/bottom rank interval
(`coordinateGraph_side_rank_bounds`); a title copy shares its top's rank
(`coordinateGraph_title_rank_source`). -/

/-- A list prefix take is a prefix. -/
private theorem take_is_prefix {α : Type} (l : List α) (n : Nat) :
    l.take n <+: l :=
  ⟨l.drop n, by simp⟩

 /-- A prefix is the take of its length. -/
 private theorem prefix_take_eq {α : Type} {p s : List α} (hp : p <+: s) :
     s.take p.length = p := by
   obtain ⟨r, rfl⟩ := hp
   simp

/-- Of two prefixes of one list, the shorter is a prefix of the longer. -/
private theorem prefix_of_common_prefix {α : Type} {p q s : List α}
    (hp : p <+: s) (hq : q <+: s) (hle : p.length ≤ q.length) : p <+: q := by
  obtain ⟨r₁, rfl⟩ := hp
  obtain ⟨r₂, hr⟩ := hq
  have h1 : (p ++ r₁).take p.length = p := prefix_take_eq ⟨r₁, rfl⟩
  have h2 : (q ++ r₂).take p.length = q.take p.length := by
    have hz : p.length - q.length = 0 := by omega
    simp [List.take_append, hz]
  rw [← hr] at h1
  rw [h2] at h1
  rw [← h1]
  exact take_is_prefix q p.length

/-- Mutual prefixes are equal. -/
private theorem prefix_antisymm {α : Type} {p q : List α}
    (h1 : p <+: q) (h2 : q <+: p) : p = q := by
  have e : q.take p.length = p := prefix_take_eq h1
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

/-- A strict prefix is strictly shorter. -/
private theorem prefix_length_lt {α : Type} {p s : List α}
    (hp : p <+: s) (hne : p ≠ s) : p.length < s.length := by
  rcases Nat.lt_or_ge p.length s.length with h | h
  · exact h
  · have h2 : s <+: p :=
      prefix_of_common_prefix ⟨[], by simp⟩ hp h
    exact absurd (prefix_antisymm hp h2) hne

/-- Dropping the last element is a prefix. -/
private theorem dropLast_is_prefix {α : Type} (l : List α) : l.dropLast <+: l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    cases as with
    | nil => exact ⟨[a], rfl⟩
    | cons b bs =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨r, by simpa using congrArg (a :: ·) hr⟩

/-- A cluster path ending in `d` has last element `d`. -/
private theorem cg_path_last {boxes : List ModelBox} {box : ModelBox} {d : Nat}
    {p : List Nat} (h : p = Compound.path boxes box ++ [d]) :
    p.getLast? = some d := by
  rw [h]
  simp

/-- Candidate `-2` node path source in input boxes: the declaration is the
input-box index and the cluster path is the box path with the declaration
appended.  This is the `SceneExecution.group_node_path_source` argument with
the execution replaced by the measured-graph hypothesis. -/
private theorem cg_group_box {P : Params} {inp : Input} {o : Options}
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

/-- Candidate bottom-marker path source in input boxes.  The declaration is
the group-box index and the cluster path is the box path with the declaration
appended. -/
private theorem cg_bottom_box {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hborder : node.border = 2) :
    ∃ box : ModelBox, inp.boxes[node.decl]? = some box ∧
      node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
  obtain ⟨_, ho, hsource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨boxD, hboxD, hroleD, hpathD, _, _⟩ :=
    measuredGraph_bottom_origin hgraph (List.mem_of_getElem? hsource) hborder
  rw [List.getElem?_map] at hboxD
  obtain ⟨orig, horig, hchange⟩ := Option.map_eq_some_iff.mp hboxD
  have hnotfixed : ¬(inp.fixedSizes.any (fun fixed : String × Size =>
      fixed.1 == orig.id) = true) := by
    intro hfixed
    have heq : ({ orig with role := .node } : ModelBox) = boxD := by
      simpa [hfixed] using hchange
    rw [← heq] at hroleD
    simp at hroleD
  have hboxEq : boxD = orig := by
    have hif : (if inp.fixedSizes.any (fun fixed : String × Size =>
        fixed.1 == orig.id) then ({ orig with role := .node } : ModelBox)
        else orig) = orig := ite_eq_right hnotfixed
    simpa [hif] using hchange.symm
  obtain ⟨_, _, hpathMap0⟩ := fixedSizes_path_index inp horig
  have hpathMap : Compound.path (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        ({ box with role := .node } : ModelBox) else box) orig =
      Compound.path inp.boxes orig := by
    simpa [hnotfixed] using hpathMap0
  refine ⟨orig, horig, ?_⟩
  rw [hboxEq] at hpathD
  rw [hpathD, hpathMap]

/-- Scope prefix: a marker whose cluster path contains a group top's
declaration extends that top's cluster path.  The declaration-membership
forces the box ancestor relation through
`Compound.path_ancestor_prefix`. -/
private theorem cg_scope_prefix {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o))
    {tbox mbox : ModelBox} {td md : Nat} {tpath mpath : List Nat}
    (htbox : inp.boxes[td]? = some tbox)
    (htpath : tpath = Compound.path inp.boxes tbox ++ [td])
    (hmbox : inp.boxes[md]? = some mbox)
    (hmpath : mpath = Compound.path inp.boxes mbox ++ [md])
    (hin : mpath.contains td = true) :
    tpath <+: mpath := by
  have hmem : td ∈ mpath := List.contains_iff_mem.mp hin
  rw [hmpath, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · have hpre := Compound.path_ancestor_prefix (inputModel inp o) hwf htbox hmbox hleft
    rw [htpath]
    exact hpre.trans ⟨[md], hmpath.symm⟩
  · have htd : td = md := by
      have h := hright
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact h
    subst htd
    have hbox : mbox = tbox := Option.some.inj (hmbox.symm.trans htbox)
    subst hbox
    rw [htpath, hmpath]
    exact List.prefix_refl _

/-- Same-path group tops share their candidate index: the declaration is the
graph source index (`measuredGraph_group_origin`), so equal declarations give
equal sources and `comp` nodup closes the indices. -/
private theorem cg_top_unique {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {a b : Nat} {na nb : Node}
    (ha : (componentCandidate graph comp candidate).nodes[a]? = some na)
    (hb : (componentCandidate graph comp candidate).nodes[b]? = some nb)
    (hbA : na.border = -2) (hbB : nb.border = -2)
    (hpath : na.clusterPath = nb.clusterPath) : a = b := by
  have hlastA : na.clusterPath.getLast? = some na.decl := by
    obtain ⟨box, hbox, hpathA⟩ := cg_group_box hgraph ha hbA
    exact cg_path_last hpathA
  have hlastB : nb.clusterPath.getLast? = some nb.decl := by
    obtain ⟨box, hbox, hpathB⟩ := cg_group_box hgraph hb hbB
    exact cg_path_last hpathB
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

 /-- Shared run bundle: the ranking result, the labeled proper graph, its key
 and record transports, border readiness, and length alignment.  This repackages
 `componentRun_ranked_source` with the derivations used for
 `componentRun_prepared_titled_source`. -/
 private theorem cg_run_bundle {P : Params} {inp : Input} {o : Options}
     {lines : List (List Measure.Line)} {graph : Graph}
     (hgraph : measuredGraph P inp o lines = .ok graph)
     {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
     {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
       .ok run) :
     ∃ (rr : RankImpl.RankResult) (labeled : Proper),
       rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
         .ok rr ∧
       coordinateGraph P labeled = run.coordinateProper ∧
       NodeKeys (componentCandidate graph comp candidate) labeled ∧
       OrderImpl.BorderConstructionReady (titleReservations (sizeProperPorts P labeled)) ∧
       (∀ (index : Nat) (node : Node),
         (componentCandidate graph comp candidate).nodes[index]? = some node →
           labeled.nodes[index]? = some ⟨node, false, none, false⟩) ∧
       (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
         labeled.rank[index]? = some rank) ∧
       labeled.nodes.length = labeled.rank.length := by
   obtain ⟨rr, normalized, labeled, hrr, hn, hl, hc, _⟩ := componentRun_ranked_source hrun
   have hk := addLabelNodes_keys _ _ _ (normalize_keys hn) hl
   have haligned : labeled.nodes.length = labeled.rank.length := by
     rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
     exact (normalize_node_rank_alignment hn).1
   have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
     (measuredGraph_shape hgraph) candidate
   have hready := titled_border_ready (P := P) hk hshape
     (fun _ _ hnode => componentCandidate_marker_shape hgraph hnode) haligned
   refine ⟨rr, labeled, hrr, hc, hk, hready, ?_, ?_, haligned⟩
   · intro index node hnode
     exact addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
   · intro index rank hrank
     rw [(Labels.addLabelNodes_metadata hl).2.1]
     exact normalize_rank_record hn hrank

 /-- Transitive group-top rank bound: a group top ranks at or below every nested
 group top whose cluster path extends its own.  Strong induction on the
 path-length gap: equal paths force the same index (`cg_top_unique`); a strict
 prefix descends through the direct parent (`candidate_parent_top_exists`) and
 chains the induction hypothesis with the direct child edge
 (`ranked_compound_child_interval`). -/
 private theorem cg_nested_top_rank {P : Params} {inp : Input} {o : Options}
     {lines : List (List Measure.Line)} {graph : Graph}
     (hgraph : measuredGraph P inp o lines = .ok graph)
     (hlines : lines.length = inp.boxes.length)
     (hwf : WellFormed (inputModel inp o))
     (hfp : framedParents inp = true)
     {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
     {rr : RankImpl.RankResult}
     (hrr : rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
       .ok rr) :
     ∀ delta : Nat, ∀ a b : Nat, ∀ na nb : Node,
       (componentCandidate graph comp candidate).nodes[a]? = some na →
       na.border = -2 →
       (componentCandidate graph comp candidate).nodes[b]? = some nb →
       nb.border = -2 →
       na.clusterPath <+: nb.clusterPath →
       nb.clusterPath.length - na.clusterPath.length = delta →
       rk rr.ranks a ≤ rk rr.ranks b := by
   have hparEx := candidate_parent_top_exists hgraph hlines hwf hfp hcomp candidate
   intro delta
   induction delta using Nat.strongRecOn with
   | _ delta ih =>
     intro a b na nb ha hbA hb hbB hpre hdelta
     by_cases heq : na.clusterPath = nb.clusterPath
     · have hab : a = b := cg_top_unique hgraph hcomp ha hb hbA hbB heq
       subst hab
       exact Int.le_refl _
     · have hlt : na.clusterPath.length < nb.clusterPath.length := prefix_length_lt hpre heq
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
         prefix_of_common_prefix hpre (huPath ▸ dropLast_is_prefix nb.clusterPath) hleU
       have hdeltaU : u.1.clusterPath.length - na.clusterPath.length < delta := by omega
       have hIH := ih _ hdeltaU a u.2 na u.1 ha hbA huLookup huBorder hpreU rfl
       obtain ⟨bbot, hbbot⟩ := componentRun_cg_bottom_find hgraph hlines hcomp hb hbB
       obtain ⟨ubot, hubot⟩ := componentRun_cg_bottom_find hgraph hlines hcomp huLookup huBorder
       have hpathUB : nb.clusterPath.dropLast = u.1.clusterPath := huPath.symm
       have hparent : (u.1, u.2) ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
         List.mem_zipIdx_iff_getElem?.mpr huLookup
       have hchild : (nb, b) ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
         List.mem_zipIdx_iff_getElem?.mpr hb
       have hinterv := ranked_compound_child_interval hrr hparent huBorder hubot
         hchild hbB hpathUB hbbot
       have hpleft : ((u.1, u.2)).2 = u.2 := rfl
       have hpright : ((nb, b)).2 = b := rfl
       rw [hpleft, hpright] at hinterv
       omega

 /-- Cg-level rank closure for a group top: every candidate node whose cluster
 path contains the top's declaration ranks at or below the top.  Plain members
 use their direct ranking edge; nested tops descend transitively; bottom
 markers go through their own group top. -/
 theorem groupTopSubtreeRankCg : GroupTopSubtreeRankCg := by
   intro P inp o lines graph hgraph hlines hwf hfp comp hcomp candidate run labels
     orderOptions hrun v nd hnode hborder
   obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks, haligned⟩ :=
     cg_run_bundle hgraph hcomp hrun
   refine ⟨rr, hrr, ?_⟩
   intro j hj hjpath
   have hjnode : (componentCandidate graph comp candidate).nodes[j]? =
       some ((componentCandidate graph comp candidate).nodes.getD j default) := by
     have h1 := List.getElem?_eq_getElem (l := (componentCandidate graph comp candidate).nodes) hj
     have h2 : (componentCandidate graph comp candidate).nodes[j] =
         (componentCandidate graph comp candidate).nodes.getD j default := by
       simp [List.getD_eq_getElem?_getD, hj]
     rw [h2] at h1
     exact h1
   have hshape := (componentCandidate_marker_shape hgraph hjnode).1
   rcases hshape with h0 | hm2 | h2
   · obtain ⟨bot, hbot⟩ := componentRun_cg_bottom_find hgraph hlines hcomp hnode hborder
     have htop : (nd, v) ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
       List.mem_zipIdx_iff_getElem?.mpr hnode
     have hmem : (((componentCandidate graph comp candidate).nodes.getD j default), j) ∈
         (componentCandidate graph comp candidate).nodes.zipIdx :=
       List.mem_zipIdx_iff_getElem?.mpr hjnode
     have hinterv := ranked_compound_member_interval hrr htop hborder hbot hmem h0 hjpath
     have htop2 : ((nd, v)).2 = v := rfl
     have hmem2 : ((componentCandidate graph comp candidate).nodes.getD j default, j).2 = j := rfl
     rw [htop2, hmem2] at hinterv
     omega
   · obtain ⟨boxT, hboxT, hpathT⟩ := cg_group_box hgraph hnode hborder
     obtain ⟨boxJ, hboxJ, hpathJ⟩ := cg_group_box hgraph hjnode hm2
     have hpre : nd.clusterPath <+:
         ((componentCandidate graph comp candidate).nodes.getD j default).clusterPath :=
       cg_scope_prefix hwf hboxT hpathT hboxJ hpathJ hjpath
     exact cg_nested_top_rank hgraph hlines hwf hfp hcomp candidate hrr
       _ v j nd _ hnode hborder hjnode hm2 hpre rfl
   · have hfind := componentCandidate_bottom_find_eq hgraph hcomp hjnode h2
     by_cases hdecl : ((componentCandidate graph comp candidate).nodes.getD j default).decl =
         nd.decl
     · rw [hdecl] at hfind
       obtain ⟨rr2, labeled2, hrr2, hc2, hk2, hrecords2, hranks2, H⟩ :=
         componentRun_group_top_lt_bottom hgraph hcomp hrun
       have hrrEq : rr = rr2 := Except.ok.inj (hrr.symm.trans hrr2)
       subst hrrEq
       have hle := H v nd _ hnode hborder hfind
       have h2eq : ((((componentCandidate graph comp candidate).nodes.getD j default),
           j)).2 = j := rfl
       rw [h2eq] at hle
       omega
     · obtain ⟨boxT, hboxT, hpathT⟩ := cg_group_box hgraph hnode hborder
       obtain ⟨boxM, hboxM, hpathM⟩ := cg_bottom_box hgraph hjnode h2
       have hpre : nd.clusterPath <+:
           ((componentCandidate graph comp candidate).nodes.getD j default).clusterPath :=
         cg_scope_prefix hwf hboxT hpathT hboxM hpathM hjpath
       obtain ⟨t, ht⟩ := componentRun_cg_top_of_bottom hgraph hlines hcomp hjnode h2
       have htPred := List.find?_some ht
       simp only [Bool.and_eq_true, beq_iff_eq] at htPred
       obtain ⟨htBorder, htPath⟩ := htPred
       have htMem : t ∈ (componentCandidate graph comp candidate).nodes.zipIdx :=
         List.mem_of_find?_eq_some ht
       have htLookup : (componentCandidate graph comp candidate).nodes[t.2]? = some t.1 :=
         List.mem_zipIdx_iff_getElem?.mp htMem
       have hpreT : nd.clusterPath <+: t.1.clusterPath := by
         rw [htPath]
         exact hpre
       have htrans := cg_nested_top_rank hgraph hlines hwf hfp hcomp candidate hrr
         _ v t.2 nd t.1 hnode hborder htLookup htBorder hpreT rfl
       have hdeclT : t.1.decl =
           ((componentCandidate graph comp candidate).nodes.getD j default).decl := by
         have hlastT : t.1.clusterPath.getLast? = some t.1.decl := by
           obtain ⟨box, hbox, hpathT'⟩ := cg_group_box hgraph htLookup htBorder
           exact cg_path_last hpathT'
         have hlastM : ((componentCandidate graph comp candidate).nodes.getD j default).clusterPath.getLast? =
             some ((componentCandidate graph comp candidate).nodes.getD j default).decl :=
           cg_path_last hpathM
         have h := congrArg List.getLast? htPath
         rw [hlastT, hlastM] at h
         exact Option.some.inj h
       obtain ⟨tbot, htbot⟩ := componentRun_cg_bottom_find hgraph hlines hcomp htLookup htBorder
       rw [← hdeclT] at hfind
       have htbotEq : tbot =
           (((componentCandidate graph comp candidate).nodes.getD j default), j) :=
         Option.some.inj (htbot.symm.trans hfind)
       obtain ⟨rr2, labeled2, hrr2, hc2, hk2, hrecords2, hranks2, H⟩ :=
         componentRun_group_top_lt_bottom hgraph hcomp hrun
       have hrrEq : rr = rr2 := Except.ok.inj (hrr.symm.trans hrr2)
       subst hrrEq
       have hle := H t.2 t.1 tbot htLookup htBorder htbot
       rw [htbotEq] at hle
       have h2eq : ((((componentCandidate graph comp candidate).nodes.getD j default),
           j)).2 = j := rfl
       rw [h2eq] at hle
       omega

 /-- Proxy widths rewrite only the width: the cluster path survives. -/
 private theorem proxyWidths_path {p q : Proper} {xs xs' : List Int}
     (h : proxyWidths p xs = .ok (q, xs')) {v : Nat} {nd qn : ProperNode}
     (hv : p.nodes[v]? = some nd) (hq : q.nodes[v]? = some qn) :
     qn.node.clusterPath = nd.node.clusterPath := by
   unfold proxyWidths at h
   obtain ⟨updated, hu, hok⟩ := bind_ok h
   obtain ⟨hlen, hidx⟩ := mapM_getElem? _ _ _ hu
   have hok2 : (Except.ok _ : Except LayoutError (Proper × List Int)) =
       Except.ok (q, xs') := hok
   have hqeq : q = { p with nodes := updated.map (·.1) } :=
     (Prod.mk.inj (Except.ok.inj hok2)).1.symm
   have hmem : (p.nodes.zipIdx[v]?) = some (nd, v) := by
     simp [List.getElem?_zipIdx, hv]
   obtain ⟨b, hb1, hb2⟩ := hidx v (nd, v) hmem
   have hqn : q.nodes[v]? = some b.1 := by
     have h0 : (updated.map (·.1))[v]? = some b.1 := by
       simp only [List.getElem?_map, hb2, Option.map_some]
     have h1 : ({ p with nodes := updated.map (·.1) } : Proper).nodes[v]? =
         some b.1 := h0
     rwa [← hqeq] at h1
   have hqnEq : qn = b.1 := Option.some.inj (hq.symm.trans hqn)
   dsimp only at hb1
   by_cases hcond : (nd.node.border == -2 || nd.node.border == 2) = true
   · simp only [hcond, ↓reduceIte] at hb1
     cases hl : nd.node.clusterPath.getLast? with
     | none => simp [hl] at hb1
     | some owner =>
       simp only [hl] at hb1
       obtain ⟨span, hspan, hb1⟩ := bind_ok hb1
       obtain ⟨width, hwidth, hb1⟩ := bind_ok hb1
       by_cases hw0 : width < 0
       · simp only [hw0, ↓reduceIte] at hb1
         simp [bind, Except.bind] at hb1
       · simp only [hw0, ↓reduceIte] at hb1
         obtain ⟨center, hcenter, hb1⟩ := bind_ok hb1
         have hb1' : (Except.ok _ : Except LayoutError (ProperNode × Int)) =
             Except.ok b := hb1
         have hb1'' := Except.ok.inj hb1'
         subst hb1''
         rw [hqnEq]
   · simp only [hcond] at hb1
     have hb1' : (Except.ok (nd, xs.getD v 0) : Except LayoutError (ProperNode × Int)) =
         Except.ok b := hb1
     have hb1'' := Except.ok.inj hb1'
     subst hb1''
     rw [hqnEq]

 /-- Executed proper nodes share their coordinate records: synthetic dropping
 only filters edges, and proxy widths preserve dummy flags, borders, and
 cluster paths. -/
 private theorem proper_coord_record {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRun P cg labels orderOptions = .ok run)
     {i : Nat} {pn : ProperNode}
     (hp : run.proper.nodes[i]? = some pn) :
     ∃ cn, run.coordinateProper.nodes[i]? = some cn ∧ cn.dummy = pn.dummy ∧
       cn.node.border = pn.node.border ∧
       cn.node.clusterPath = pn.node.clusterPath := by
   obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoord, hord, hxs, hproxy, hdrop,
     hr, hrl, hy, hys, hroutes⟩ := componentRun_spec hrun
   have hnodes : run.proper.nodes = q0.nodes := by
     have h := congrArg Proper.nodes hdrop.symm
     simpa [OrderImpl.dropSynthetic] using h
   rw [hnodes] at hp
   have hlen : i < run.coordinateProper.nodes.length := by
     have h1 : i < q0.nodes.length := (List.getElem?_eq_some_iff.mp hp).1
     have h2 := (proxyWidths_rel hproxy).2.2.1
     omega
   have hcn : run.coordinateProper.nodes[i]? =
       some (run.coordinateProper.nodes[i]'hlen) := List.getElem?_eq_getElem hlen
   obtain ⟨qn, hqn, hqdum, hqbord, _⟩ :=
     (proxyWidths_rel hproxy).2.2.2.2.1 i _ hcn
   have hqnEq : qn = pn := Option.some.inj (hqn.symm.trans hp)
   have hpath := proxyWidths_path hproxy hcn hp
   refine ⟨_, hcn, ?_, ?_, ?_⟩
   · rw [← hqnEq]; exact hqdum.symm
   · rw [← hqnEq]; exact hqbord.symm
   · exact hpath.symm

 /-- Executed proper ranks agree with coordinate ranks index-wise. -/
 private theorem proper_rank_eq {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRun P cg labels orderOptions = .ok run) (x : Nat) :
     rk run.proper.rank x = rk run.coordinateProper.rank x := by
   have h : run.proper.rank = run.coordinateProper.rank := by
     obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ :=
       componentRun_spec hrun
     obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hproxy
     rw [← hdrop, OrderImpl.dropSynthetic_rank]
     exact hrankEq
   rw [h]

 /-- From `toNat` order to `Int` order under nonnegativity. -/
 private theorem toNat_le_of_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b)
     (h : a.toNat ≤ b.toNat) : a ≤ b := by
   have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
   have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg hb
   have h3 : (a.toNat : Int) ≤ (b.toNat : Int) := by exact_mod_cast h
   omega

 /-- Side markers sit at or above their group top: the side rank interval
 (`coordinateGraph_side_rank_bounds`) puts the titled top rank below the side
 rank, and the titled top is an original top bounded by `groupTopSubtreeRankCg`. -/
 private theorem side_marker_rank_ge (hcg : GroupTopSubtreeRankCg)
     {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
     {graph : Graph}
     (hgraph : measuredGraph P inp o lines = .ok graph)
     (hlines : lines.length = inp.boxes.length)
     (hwf : WellFormed (inputModel inp o))
     (hfp : framedParents inp = true)
     {comp : List Nat} (hcomp : comp ∈ components graph)
     {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRun P (componentCandidate graph comp candidate) labels
       orderOptions = .ok run)
     {v : Nat} {nd : Node}
     (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some nd)
     (hbordV : nd.border = -2)
     (hvcg : v < (componentCandidate graph comp candidate).nodes.length)
     {i : Nat} (hi : i < run.proper.nodes.length)
     (hcontains : (run.proper.nodes.getD i default).node.clusterPath.contains nd.decl = true)
     (hside : (run.proper.nodes.getD i default).node.border = -1 ∨
       (run.proper.nodes.getD i default).node.border = 1) :
     rk run.proper.rank v ≤ rk run.proper.rank i := by
   have erv : rk run.proper.rank v = rk run.coordinateProper.rank v := proper_rank_eq hrun v
   have eri : rk run.proper.rank i = rk run.coordinateProper.rank i := proper_rank_eq hrun i
   rw [erv, eri]
   obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks⟩ :=
     componentRun_prepared_titled_source hgraph hcomp hrun
   have hpi : run.proper.nodes[i]? = some (run.proper.nodes.getD i default) := by
     simp [List.getD_eq_getElem?_getD, hi]
   obtain ⟨cn, hcn, _, hcbord, hcpath⟩ := proper_coord_record hrun hpi
   have hsideC : cn.node.border = -1 ∨ cn.node.border = 1 := by
     rw [hcbord]; exact hside
   have hncL : (coordinateGraph P labeled).nodes[i]? = some cn := by
     rwa [← hc] at hcn
   obtain ⟨top, htopMem, _, hfindB, hpathEq, hnn, hlo, _⟩ :=
     coordinateGraph_side_rank_bounds hready hncL hsideC
   have htopGet : (titleReservations (sizeProperPorts P labeled)).nodes[top.2]? =
       some top.1 :=
     List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp htopMem).1
   have htopBorder : top.1.node.border = -2 := by
     simpa using (List.mem_filter.mp htopMem).2
   obtain ⟨topOrig, htopCg, htopBorderEq, htopRecord⟩ :=
     titled_marker_source_record hk hrecords htopGet (Or.inl htopBorder)
   have htopPath : top.1.node.clusterPath = topOrig.clusterPath := by
     rw [htopRecord]; exact (titleF_keys _).2.2.1
   have hcnContains : cn.node.clusterPath.contains nd.decl = true := by
     rw [hcpath]; exact hcontains
   have htopContains : top.1.node.clusterPath.contains nd.decl = true := by
     rw [← hpathEq]; exact hcnContains
   have htopOrigContains : topOrig.clusterPath.contains nd.decl = true := by
     rw [← htopPath]; exact htopContains
   have hlt : top.2 < (componentCandidate graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp htopCg).1
   have hgetDTop : (componentCandidate graph comp candidate).nodes.getD top.2 default =
       topOrig := by
     rw [List.getD_eq_getElem?_getD, htopCg, Option.getD_some]
   have hgetDContains : ((componentCandidate graph comp candidate).nodes.getD top.2
       default).clusterPath.contains nd.decl = true := by
     rw [hgetDTop]; exact htopOrigContains
   obtain ⟨rr2, hrr2, hclose⟩ := hcg hgraph hlines hwf hfp hcomp hrun hvGet hbordV
   have hrrEq : rr = rr2 := Except.ok.inj (hrr.symm.trans hrr2)
   subst hrrEq
   have hle : rk rr.ranks v ≤ rk rr.ranks top.2 := hclose top.2 hlt hgetDContains
   have hVcoord : rk run.coordinateProper.rank v = rk rr.ranks v := by
     have h1 := prepared_coordinate_original_rk (P := P) hrr hranks hvcg
     rw [← hc]; exact h1
   have hTtitle : rk (titleReservations (sizeProperPorts P labeled)).rank top.2 =
       rk rr.ranks top.2 :=
     (prepared_titled_original_rk (P := P) hrr hranks hlt).1
   have hBcoord : rk (coordinateGraph P labeled).rank i = rk run.coordinateProper.rank i := by
     rw [hc]
   have hTnn : 0 ≤ rk (titleReservations (sizeProperPorts P labeled)).rank top.2 := by
     rw [hTtitle]; exact rankWithBudget_rk_nonneg hrr top.2
   have hTopLe : rk (titleReservations (sizeProperPorts P labeled)).rank top.2 ≤
       rk (coordinateGraph P labeled).rank i :=
     toNat_le_of_nonneg hTnn hnn hlo
   have hTopCoord : rk rr.ranks top.2 ≤ rk run.coordinateProper.rank i := by
     rw [← hTtitle, ← hBcoord]; exact hTopLe
   rw [hVcoord]
   exact Int.le_trans hle hTopCoord

 /-- Title copies share their anchor top rank
 (`coordinateGraph_title_rank_source`), and the anchor is an original top
 bounded by `groupTopSubtreeRankCg`. -/
 private theorem title_copy_rank_ge (hcg : GroupTopSubtreeRankCg)
     {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
     {graph : Graph}
     (hgraph : measuredGraph P inp o lines = .ok graph)
     (hlines : lines.length = inp.boxes.length)
     (hwf : WellFormed (inputModel inp o))
     (hfp : framedParents inp = true)
     {comp : List Nat} (hcomp : comp ∈ components graph)
     {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRun P (componentCandidate graph comp candidate) labels
       orderOptions = .ok run)
     {v : Nat} {nd : Node}
     (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some nd)
     (hbordV : nd.border = -2)
     (hvcg : v < (componentCandidate graph comp candidate).nodes.length)
     {i : Nat} (hi : i < run.proper.nodes.length)
     (hcontains : (run.proper.nodes.getD i default).node.clusterPath.contains nd.decl = true)
     (hb3 : (run.proper.nodes.getD i default).node.border = 3) :
     rk run.proper.rank v ≤ rk run.proper.rank i := by
   have erv : rk run.proper.rank v = rk run.coordinateProper.rank v := proper_rank_eq hrun v
   have eri : rk run.proper.rank i = rk run.coordinateProper.rank i := proper_rank_eq hrun i
   rw [erv, eri]
   obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks⟩ :=
     componentRun_prepared_titled_source hgraph hcomp hrun
   have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
     (measuredGraph_shape hgraph) candidate
   have haligned : labeled.nodes.length = labeled.rank.length :=
     source_alignment_of_titled hready.2.2.2.1
   have hpi : run.proper.nodes[i]? = some (run.proper.nodes.getD i default) := by
     simp [List.getD_eq_getElem?_getD, hi]
   obtain ⟨cn, hcn, _, hcbord, hcpath⟩ := proper_coord_record hrun hpi
   have hncL : (coordinateGraph P labeled).nodes[i]? = some cn := by
     rwa [← hc] at hcn
   have hb3C : cn.node.border = 3 := by
     rw [hcbord]; exact hb3
   obtain ⟨originalIndex, original, horiginal, hOrigBorder, hOrigReal, _, htitlePath,
       htitleRank⟩ :=
     coordinateGraph_title_rank_source hk hshape haligned hncL hb3C
   have hcnContains : cn.node.clusterPath.contains nd.decl = true := by
     rw [hcpath]; exact hcontains
   have horigContains : original.node.clusterPath.contains nd.decl = true := by
     rw [← htitlePath]; exact hcnContains
   rcases hk originalIndex original horiginal with
     ⟨n, hn, _, hborderN, hpathN⟩ | ⟨hdT, _, _⟩
   · have hnBorder : n.border = -2 := hborderN.symm.trans hOrigBorder
     have hncN : n.clusterPath.contains nd.decl = true := by
       rw [← hpathN]; exact horigContains
     have hlt : originalIndex < (componentCandidate graph comp candidate).nodes.length :=
       (List.getElem?_eq_some_iff.mp hn).1
     have hgetDOrig : (componentCandidate graph comp candidate).nodes.getD originalIndex
         default = n := by
       rw [List.getD_eq_getElem?_getD, hn, Option.getD_some]
     have hgetDContains : ((componentCandidate graph comp candidate).nodes.getD
         originalIndex default).clusterPath.contains nd.decl = true := by
       rw [hgetDOrig]; exact hncN
     obtain ⟨rr2, hrr2, hclose⟩ := hcg hgraph hlines hwf hfp hcomp hrun hvGet hbordV
     have hrrEq : rr = rr2 := Except.ok.inj (hrr.symm.trans hrr2)
     subst hrrEq
     have hle : rk rr.ranks v ≤ rk rr.ranks originalIndex :=
       hclose originalIndex hlt hgetDContains
     have hVcoord : rk run.coordinateProper.rank v = rk rr.ranks v := by
       have h1 := prepared_coordinate_original_rk (P := P) hrr hranks hvcg
       rw [← hc]; exact h1
     have hOcoord : rk run.coordinateProper.rank originalIndex = rk rr.ranks originalIndex := by
       have h1 := prepared_coordinate_original_rk (P := P) hrr hranks hlt
       rw [← hc]; exact h1
     have hrankEq : rk run.coordinateProper.rank i = rk labeled.rank originalIndex := by
       rw [← hc]; exact htitleRank
     have hlabEq : rk labeled.rank originalIndex =
         rk run.coordinateProper.rank originalIndex := by
       rw [← hc]
       have hlabLen : originalIndex < labeled.rank.length := by
         have h1 : originalIndex < labeled.nodes.length :=
           (List.getElem?_eq_some_iff.mp horiginal).1
         omega
       have hlabLook : labeled.rank[originalIndex]? = some labeled.rank[originalIndex] :=
         List.getElem?_eq_getElem hlabLen
       have htitLook := titled_rank_record (P := P) hlabLook
       have hcoordLook := coordinateGraph_titled_rank_record htitLook
       simp only [rk, List.getD_eq_getElem?_getD, hlabLook, hcoordLook,
         Option.getD_some]
     rw [hVcoord, hrankEq, hlabEq, hOcoord]
     exact hle
   · rw [hdT] at hOrigReal
     simp at hOrigReal

 /-- Dummy-only residual of `ProperDerivedRank`: an executed edge-dummy whose
 cluster path carries the group top declaration ranks at or below the top.
 Strictly simpler than the full derived goal: same executed-run premises,
 conclusion restricted to the dummy disjunct. -/
 def GroupTopDummyRankLe : Prop :=
   ∀ {P : Params} {inp : Input} {o : Options}
     {lines : List (List Measure.Line)} {graph : Graph},
     measuredGraph P inp o lines = .ok graph →
     lines.length = inp.boxes.length →
     WellFormed (inputModel inp o) →
     framedParents inp = true →
     ∀ {comp : List Nat}, comp ∈ components graph →
     ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
       {orderOptions : OrderOptions},
     componentRun P (componentCandidate graph comp candidate) labels
       orderOptions = .ok run →
     ∀ {v : Nat} {nd : Node},
     (componentCandidate graph comp candidate).nodes[v]? = some nd →
     nd.border = -2 →
     v < (componentCandidate graph comp candidate).nodes.length →
     ∀ {i : Nat}, i < run.proper.nodes.length →
     (run.proper.nodes.getD i default).node.clusterPath.contains nd.decl = true →
     (run.proper.nodes.getD i default).dummy = true →
     rk run.proper.rank v ≤ rk run.proper.rank i

 /-- Derived closure from its seams: side markers and title copies by the two
 lemmas above; edge dummies by the `GroupTopDummyRankLe` residual. -/
 theorem properDerivedRank_of_seams (hcg : GroupTopSubtreeRankCg)
     (hdummy : GroupTopDummyRankLe) : ProperDerivedRank := by
   intro P inp o lines graph hgraph hlines hwf hfp comp hcomp candidate run labels
     orderOptions hrun v nd hnode hborder hvcg i hi hpath hkind
   rcases hkind with hd | hb1 | hb2 | hb3
   · exact hdummy hgraph hlines hwf hfp hcomp hrun hnode hborder hvcg hi hpath hd
   · exact side_marker_rank_ge hcg hgraph hlines hwf hfp hcomp hrun hnode hborder hvcg
       hi hpath (Or.inl hb1)
   · exact side_marker_rank_ge hcg hgraph hlines hwf hfp hcomp hrun hnode hborder hvcg
       hi hpath (Or.inr hb2)
   · exact title_copy_rank_ge hcg hgraph hlines hwf hfp hcomp hrun hnode hborder hvcg
       hi hpath hb3

 /-- Derived closure with the dummy residual as hypothesis: side markers and
 title copies are proved, dummies stay in `GroupTopDummyRankLe`. -/
 theorem properDerivedRank (hdummy : GroupTopDummyRankLe) : ProperDerivedRank :=
   properDerivedRank_of_seams groupTopSubtreeRankCg hdummy

 /-- Executed top closure with the dummy residual as hypothesis. -/
 theorem groupTopSubtreeRankProper (hdummy : GroupTopDummyRankLe) :
     GroupTopSubtreeRankProper :=
   groupTopSubtreeRankProper_of_seams groupTopSubtreeRankCg
     (properDerivedRank hdummy)

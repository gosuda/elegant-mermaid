import Elegant.Layered.ExactCaptionMembersProof
import Elegant.Layered.ExactFlatC5
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.GroupWidthFacts

set_option autoImplicit false

open Elegant
open Elegant.Layered

namespace Elegant
namespace Layered
namespace PipelineImpl

private theorem xcmf_take_is_prefix {α : Type} (l : List α) (n : Nat) :
    l.take n <+: l :=
  ⟨l.drop n, by simp⟩

private theorem xcmf_prefix_take_eq {α : Type} {p s : List α} (hp : p <+: s) :
    s.take p.length = p := by
  obtain ⟨r, rfl⟩ := hp
  simp

private theorem xcmf_prefix_of_common_prefix {α : Type} {p q s : List α}
    (hp : p <+: s) (hq : q <+: s) (hle : p.length ≤ q.length) : p <+: q := by
  obtain ⟨r₁, rfl⟩ := hp
  obtain ⟨r₂, hr⟩ := hq
  have h1 : (p ++ r₁).take p.length = p := xcmf_prefix_take_eq ⟨r₁, rfl⟩
  have h2 : (q ++ r₂).take p.length = q.take p.length := by
    have hz : p.length - q.length = 0 := by omega
    simp [List.take_append, hz]
  rw [← hr] at h1
  rw [h2] at h1
  rw [← h1]
  exact xcmf_take_is_prefix q p.length

private theorem xcmf_prefix_antisymm {α : Type} {p q : List α}
    (h1 : p <+: q) (h2 : q <+: p) : p = q := by
  have e : q.take p.length = p := xcmf_prefix_take_eq h1
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

private theorem xcmf_prefix_length_lt {α : Type} {p s : List α}
    (hp : p <+: s) (hne : p ≠ s) : p.length < s.length := by
  rcases Nat.lt_or_ge p.length s.length with h | h
  · exact h
  · have h2 : s <+: p := xcmf_prefix_of_common_prefix ⟨[], by simp⟩ hp h
    exact absurd (xcmf_prefix_antisymm hp h2) hne

private theorem xcmf_dropLast_is_prefix {α : Type} (l : List α) : l.dropLast <+: l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    cases as with
    | nil => exact ⟨[a], rfl⟩
    | cons b bs =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨r, by simpa using congrArg (a :: ·) hr⟩

private theorem xcmf_path_last {boxes : List ModelBox} {box : ModelBox} {d : Nat}
    {p : List Nat} (h : p = Compound.path boxes box ++ [d]) :
    p.getLast? = some d := by
  rw [h]
  simp

private theorem xcmf_scope_prefix {inp : Input} {o : Options}
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

private theorem xcmf_node_key_rev {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g g' : Graph}
    (h : exactGraph P exactIds inp o measured g = .ok g')
    {v : Nat} {nd' : Node} (hv : g'.nodes[v]? = some nd') :
    ∃ nd, g.nodes[v]? = some nd ∧ nd'.border = nd.border ∧
      nd'.clusterPath = nd.clusterPath ∧ nd'.decl = nd.decl := by
  have hlen : g'.nodes.length = g.nodes.length := exactGraph_length h
  have hvlt : v < g.nodes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hv).1
    omega
  have hmem : g.nodes[v]? = some g.nodes[v] := List.getElem?_eq_getElem hvlt
  obtain ⟨nd'', hnd'', hb, hc, hd⟩ := exactGraph_node_key h hmem
  have heq : nd'' = nd' := Option.some.inj (hnd''.symm.trans hv)
  subst heq
  exact ⟨g.nodes[v], hmem, hb, hc, hd⟩

private theorem xcmf_top_unique {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat}
    {a b : Nat} {na nb : Node}
    (ha : (componentCandidate graph comp candidate).nodes[a]? = some na)
    (hb : (componentCandidate graph comp candidate).nodes[b]? = some nb)
    (hbA : na.border = -2) (hbB : nb.border = -2)
    (hpath : na.clusterPath = nb.clusterPath) : a = b := by
  have hlastA : na.clusterPath.getLast? = some na.decl := by
    obtain ⟨box, hbox, hpathA⟩ := X_cg_group_box h0 h ha hbA
    exact xcmf_path_last hpathA
  have hlastB : nb.clusterPath.getLast? = some nb.decl := by
    obtain ⟨box, hbox, hpathB⟩ := X_cg_group_box h0 h hb hbB
    exact xcmf_path_last hpathB
  have hdecl : na.decl = nb.decl := by
    have h := congrArg List.getLast? hpath
    rw [hlastA, hlastB] at h
    exact Option.some.inj h
  obtain ⟨aSrc, haSrc, hsa⟩ := componentCandidate_nonplain_source ha (by omega)
  obtain ⟨bSrc, hbSrc, hsb⟩ := componentCandidate_nonplain_source hb (by omega)
  obtain ⟨na0, hna0, hbA0, _hp0, hdA0⟩ := xcmf_node_key_rev h hsa
  obtain ⟨nb0, hnb0, hbB0, _hp1, hdB0⟩ := xcmf_node_key_rev h hsb
  have hbA0' : na0.border = -2 := by rw [← hbA0]; exact hbA
  have hbB0' : nb0.border = -2 := by rw [← hbB0]; exact hbB
  obtain ⟨hdeclA, _, _, _, _⟩ := measuredGraph_group_origin h0 hna0 hbA0'
  obtain ⟨hdeclB, _, _, _, _⟩ := measuredGraph_group_origin h0 hnb0 hbB0'
  have hsrc : aSrc = bSrc := by omega
  exact nodup_map_inj_aux (fun x => x)
    (by simpa using components_nodup graph comp hcomp) haSrc hbSrc hsrc
private theorem xcmf_chain_le {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
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
  intro delta
  induction delta using Nat.strongRecOn with
  | _ delta ih =>
    intro a b na nb ha hbA hb hbB hpre hdelta
    by_cases heq : na.clusterPath = nb.clusterPath
    · have hab : a = b := xcmf_top_unique h0 h hcomp ha hb hbA hbB heq
      subst hab
      exact Int.le_refl _
    · have hlt : na.clusterPath.length < nb.clusterPath.length :=
        xcmf_prefix_length_lt hpre heq
      have hbne : nb.clusterPath ≠ [] :=
        (X_componentCandidate_marker_shape h0 h hb).2 hbB
      have hna_ne : na.clusterPath ≠ [] :=
        (X_componentCandidate_marker_shape h0 h ha).2 hbA
      obtain ⟨u, hu⟩ := X_candidate_parent_top_exists h0 h hlines hwf hfp hcomp candidate
        (x := (nb, b)) (List.mem_zipIdx_iff_getElem?.mpr hb) hbB
        (outerPrefix := na.clusterPath) hpre hlt hna_ne
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
      have hleU : na.clusterPath.length ≤ u.1.clusterPath.length := by omega
      have hpreU : na.clusterPath <+: u.1.clusterPath :=
        xcmf_prefix_of_common_prefix hpre
          (huPath ▸ xcmf_dropLast_is_prefix nb.clusterPath) hleU
      have hdeltaU : u.1.clusterPath.length - na.clusterPath.length < delta := by omega
      have hIH := ih _ hdeltaU a u.2 na u.1 ha hbA huLookup huBorder hpreU rfl
      obtain ⟨bbot, hbbot⟩ := X_componentRun_cg_bottom_find h0 h hlines hcomp hb hbB
      obtain ⟨ubot, hubot⟩ := X_componentRun_cg_bottom_find h0 h hlines hcomp huLookup huBorder
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

private theorem xcmf_chain_strict {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph) (candidate : Nat)
    {rr : RankImpl.RankResult}
    (hrr : rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
      .ok rr)
    {a b : Nat} {na nb : Node}
    (ha : (componentCandidate graph comp candidate).nodes[a]? = some na)
    (hbA : na.border = -2)
    (hb : (componentCandidate graph comp candidate).nodes[b]? = some nb)
    (hbB : nb.border = -2)
    (hne : na.decl ≠ nb.decl)
    (hpre : na.clusterPath <+: nb.clusterPath) :
    rk rr.ranks a + 1 ≤ rk rr.ranks b := by
  have hlastA : na.clusterPath.getLast? = some na.decl := by
    obtain ⟨box, hbox, hpathA⟩ := X_cg_group_box h0 h ha hbA
    exact xcmf_path_last hpathA
  have hlastB : nb.clusterPath.getLast? = some nb.decl := by
    obtain ⟨box, hbox, hpathB⟩ := X_cg_group_box h0 h hb hbB
    exact xcmf_path_last hpathB
  have hnePath : na.clusterPath ≠ nb.clusterPath := by
    intro heq
    apply hne
    have h := congrArg List.getLast? heq
    rw [hlastA, hlastB] at h
    exact Option.some.inj h
  have hlt : na.clusterPath.length < nb.clusterPath.length :=
    xcmf_prefix_length_lt hpre hnePath
  have hbne : nb.clusterPath ≠ [] :=
    (X_componentCandidate_marker_shape h0 h hb).2 hbB
  have hna_ne : na.clusterPath ≠ [] :=
    (X_componentCandidate_marker_shape h0 h ha).2 hbA
  obtain ⟨u, hu⟩ := X_candidate_parent_top_exists h0 h hlines hwf hfp hcomp candidate
    (x := (nb, b)) (List.mem_zipIdx_iff_getElem?.mpr hb) hbB
    (outerPrefix := na.clusterPath) hpre hlt hna_ne
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
  have hleU : na.clusterPath.length ≤ u.1.clusterPath.length := by omega
  have hpreU : na.clusterPath <+: u.1.clusterPath :=
    xcmf_prefix_of_common_prefix hpre
      (huPath ▸ xcmf_dropLast_is_prefix nb.clusterPath) hleU
  have hchain := xcmf_chain_le h0 h hlines hwf hfp hcomp candidate hrr
    _ a u.2 na u.1 ha hbA huLookup huBorder hpreU rfl
  obtain ⟨bbot, hbbot⟩ := X_componentRun_cg_bottom_find h0 h hlines hcomp hb hbB
  obtain ⟨ubot, hubot⟩ := X_componentRun_cg_bottom_find h0 h hlines hcomp huLookup huBorder
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

private theorem xcmw_coordinateGraph_anchor_prefix (P : Params) (exact : List Nat)
    (p : Proper) :
    ∃ extra, (coordinateGraphX P exact p).rank = p.rank ++ extra := by
  obtain ⟨extraRanks, hr⟩ := addClusterBorders_rank_prefix
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  obtain ⟨tail, htitle⟩ : ∃ tail, (titleReservations (sizeProperPortsX P exact p)).rank =
      p.rank ++ tail := by
    unfold titleReservations sizeProperPortsX
    exact ⟨_, rfl⟩
  refine ⟨tail ++ extraRanks, ?_⟩
  change (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).rank = _
  rw [hr, htitle, List.append_assoc]

private theorem xcmw_coordinateGraph_rank_record {P : Params} {exact : List Nat}
    {source : Proper} {index : Nat} {rank : Int}
    (h : source.rank[index]? = some rank) :
    (coordinateGraphX P exact source).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := xcmw_coordinateGraph_anchor_prefix P exact source
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

private theorem xcmw_prepared {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {source : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      source.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (coordinateGraphX P exact source).rank index = rk rr.ranks index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have hcoordinateLookup := xcmw_coordinateGraph_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  simp only [rk, List.getD_eq_getElem?_getD, hcoordinateLookup, hrrLookup, Option.getD_some]

private theorem xcmw_proxy_interval {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner : Nat) (span : FramePorts.Span),
      node.node.clusterPath.getLast? = some owner ∧
      proxySpan run.coordinateProper run.coordinateXs owner index = .ok span ∧
      run.proper.nodes[index]? =
        some { node with node := { node.node with w := span.hi - span.lo } } ∧
      0 ≤ span.hi - span.lo ∧
      RouteImpl.leftOf run.proper run.xs index = span.lo ∧
      RouteImpl.leftOf run.proper run.xs index + RouteImpl.nodeW run.proper index = span.hi := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = q0.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨owner, span, ownerEq, hspan, outputNode, widthNonnegative, left, right⟩ :=
    proxyWidths_proxy_interval hproxy hnode hborder
  refine ⟨owner, span, ownerEq, hspan, ?_, widthNonnegative, ?_, ?_⟩
  · simpa only [nodesEq] using outputNode
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using left
  · simpa only [RouteImpl.leftOf, RouteImpl.nodeW, nodesEq] using right

private theorem xcmw_nonproxy {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

private theorem xcmw_bottom_coordinate {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph) {candidate : Nat} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hgroup : nd.border = 2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = 2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
  obtain ⟨_, labeled, _, hc, _, _, hrecords, _, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hrecords v nd hnode
  have hmarker := X_coordinateGraph_marker_record (P := P) (exact := exact) hrec
    (Or.inr hgroup) rfl
  rw [hc] at hmarker
  have hb : (clearF (titleF ⟨nd, false, none, false⟩)).node.border = 2 := by
    have h1 := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [h1, (titleF_keys _).2.1]
    exact hgroup
  have hd : (clearF (titleF ⟨nd, false, none, false⟩)).dummy = false :=
    (clearF_keys _).1.trans (titleF_keys _).1
  have hp : (clearF (titleF ⟨nd, false, none, false⟩)).node.clusterPath = nd.clusterPath :=
    (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
  have hh : (clearF (titleF ⟨nd, false, none, false⟩)).node.h = 0 :=
    (clearF_keys _).2.2.2.trans
      ((titleF_keys ⟨nd, false, none, false⟩).2.2.2 (Or.inr hgroup))
  exact ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, hb, hd, hp, hh⟩

private theorem xcmw_bottom_proper {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = 2) (hcoordH : coord.node.h = 0) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath ∧
      RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨owner, span, _, _, hproper, _, _⟩ :=
    xcmw_proxy_interval hrun hcoord (Or.inr hb)
  have hh : RouteImpl.nodeH run.proper v = 0 := by
    simp only [RouteImpl.nodeH, hproper]
    exact hcoordH
  exact ⟨_, hproper, rfl, hh⟩

private theorem xcmw_bottom_path {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hborder : nd.border = 2) :
    nd.clusterPath.getLast? = some nd.decl ∧ nd.clusterPath.contains nd.decl = true := by
  obtain ⟨box, hbox, hpath⟩ := X_cg_bottom_box h0 h hnode hborder
  exact ⟨by rw [hpath]; simp, by rw [hpath]; simp⟩

private theorem xcmw_foldl_minY_le (rects : List Rect) (b : Bounds) (lo : Int)
    (hb : lo ≤ b.minY) (hall : ∀ r ∈ rects, lo ≤ r.y) :
    lo ≤ ((rects.foldl fun b r =>
      ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
        max b.bottom (r.y + r.h)⟩) b).minY := by
  induction rects generalizing b with
  | nil => simpa using hb
  | cons first rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · show lo ≤ min b.minY first.y
      have h1 := hb
      have h2 := hall first (by simp)
      omega
    · intro r hr
      exact hall r (List.mem_cons_of_mem _ hr)

private theorem xcmw_minY_of_all_le (rects : List Rect) (lo : Int)
    (hall : ∀ r ∈ rects, lo ≤ r.y) (hne : rects ≠ []) :
    lo ≤ (boundsOf rects []).minY := by
  cases rects with
  | nil => exact absurd rfl hne
  | cons first rest =>
    unfold boundsOf
    dsimp only
    exact xcmw_foldl_minY_le (first :: rest) _ lo (hall first (by simp)) hall

private theorem xcmw_group_final_side {P : Params} {inp : Input} {o : Options}
    {exactIds : List String} {lines : List (List Measure.Line)}
    {graph0 graph : Graph} {measured : List MeasuredLabel}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX P exact (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ (sideIndex : Nat) (side : ProperNode),
      run.proper.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      side.node.clusterPath.getLast? = some node.decl := by
  obtain ⟨_, labeled, _, _, hc, _, _, hrecords, _, _, _⟩ :=
    X_group_bottom_source h0 h hcomp hrun hnode hgroup
  let proxy := clearF (titleF ⟨node, false, none, false⟩)
  have hproxy : run.coordinateProper.nodes[index]? = some proxy := by
    rw [← hc]
    exact X_coordinateGraph_marker_record (hrecords index node hnode) (Or.inl hgroup) rfl
  have hproxyBorder : proxy.node.border = -2 :=
    (clearF_keys _).2.1.trans ((titleF_keys _).2.1.trans hgroup)
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, _⟩ :=
    X_proxy_side_source hrun hproxy (Or.inl hproxyBorder)
  obtain ⟨_, _, hpath⟩ := X_cg_group_box h0 h hnode hgroup
  have hproxyLast : proxy.node.clusterPath.getLast? = some node.decl := by
    change (clearF (titleF ⟨node, false, none, false⟩)).node.clusterPath.getLast? = _
    rw [(clearF_keys _).2.2.1, (titleF_keys _).2.2.1]
    simp [hpath]
  have hsideProper : run.proper.nodes[sideIndex]? = some side :=
    (xcmw_nonproxy hrun hside (by intro hc; rcases hsideBorder with h | h <;> rcases hc with h2 | h2 <;> omega)).1
  exact ⟨sideIndex, side, hsideProper, hsideBorder,
    hsideOwner.trans (howner.symm.trans hproxyLast)⟩

/-- Per-execution descendant-chain residual: the same statement as
`XC_DescChainX` with the two admission facts as local premises on the
executed run (`WellFormed`, `framedParents`), matching the shapes the plain
chain lemmas need. No global quantification over all inputs. -/
def XC_DescChainXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {a b : Nat} {na nb : Node},
      (componentCandidate execution.graph comp candidate).nodes[a]? = some na →
      na.border = -2 →
      (componentCandidate execution.graph comp candidate).nodes[b]? = some nb →
      nb.border = -2 →
      na.decl ≠ nb.decl →
      nb.clusterPath.contains na.decl = true →
      ∃ rr : RankImpl.RankResult,
        rankWithBudget (Compound.rankingGraph
          (componentCandidate execution.graph comp candidate)) = .ok rr ∧
        rk rr.ranks a + 1 ≤ rk rr.ranks b

/-- Per-execution descendant chain over exact runs, from local admission. -/
theorem XC_descChainXW_holds (exactIds : List String) : XC_DescChainXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  intro a b na nb ha hbA hb hbB hne hpath
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  obtain ⟨tbox, hboxT, hpathT⟩ :=
    X_cg_group_box execution.graph0_eq execution.graph_eq ha hbA
  obtain ⟨fbox, hboxF, hpathF⟩ :=
    X_cg_group_box execution.graph0_eq execution.graph_eq hb hbB
  have hpre : na.clusterPath <+: nb.clusterPath :=
    xcmf_scope_prefix hwf hboxT hpathT hboxF hpathF hpath
  obtain ⟨rr, _, hrr, _, _, _, _, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  exact ⟨rr, hrr, xcmf_chain_strict execution.graph0_eq execution.graph_eq
    hlines hwf hfp hcomp candidate hrr ha hbA hb hbB hne hpre⟩


/-- Per-execution child-top residual: the same statement as `XC_ChildTopX`
with the two admission facts as local premises on the executed run. -/
def XC_ChildTopXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {c : Nat} {nd : Node},
      (componentCandidate execution.graph comp candidate).nodes[c]? = some nd →
      nd.border = -2 →
      ChildTopRankLe (componentCandidate execution.graph comp candidate) run c

/-- Per-execution child-top rank bound over exact runs, from local admission. -/
theorem XC_childTopXW_holds (exactIds : List String) : XC_ChildTopXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  intro c nd hnode hborder
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  have hclt : c < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hgetDc : (componentCandidate execution.graph comp candidate).nodes.getD c default = nd := by
    simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  unfold ChildTopRankLe
  intro q hq hcontains
  have hqlook : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp hq
  have hqlen : q.2 < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hqlook).1
  have hgetD : run.proper.nodes.getD q.2 default = q.1 := by
    simp only [List.getD_eq_getElem?_getD, hqlook, Option.getD_some]
  have hpath : (run.proper.nodes.getD q.2 default).node.clusterPath.contains nd.decl = true := by
    rw [hgetD]
    have h2 : (componentCandidate execution.graph comp candidate).nodes.getD c default = nd :=
      hgetDc
    rw [h2] at hcontains
    exact hcontains
  exact (x_topRank_holds exactIds) execution.graph0_eq execution.graph_eq hlines hwf hfp
    hcomp hrun hnode hborder hclt hqlen hpath

/-- Per-execution descendant case: the same statement as `XC_MemberDescX`
with the two admission facts as local premises on the executed run. -/
def XC_MemberDescXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    CaptionMemberDescDisjoint execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp

/-- Descendant case over exact runs from per-execution admission: replay of
`XC_memberDescX_holds`, feeding the local premises to the W chain/child facts. -/
theorem XC_memberDescXW_holds (exactIds : List String)
    (hcap : XC_CapBandX exactIds) : XC_MemberDescXW exactIds := by
  intro inp o res execution hwf hfp comp hcomp candidate run orderOptions hrun
  intro i stored0 tNode hmem hnode hborder pos fNode g0 hfn hne hpath hnonplain hframe
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  have hindexLt : i < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hposLt : pos < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hfn).1
  obtain ⟨rr, _, hrr, hc, _, _, _, hranks, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  have eTop : rk run.coordinateProper.rank i = rk rr.ranks i := by
    have h2 := xcmw_prepared (P := execution.params) (exact := exactDecls exactIds inp)
      hrr hranks hindexLt
    rw [hc] at h2
    exact h2
  have rEqT := X_proper_rank_eq_local hrun i
  have rEqM := X_proper_rank_eq_local hrun pos
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, _⟩ := componentRunX_spec hrun
  have hindexLen : i < run.proper.nodes.length :=
    componentRunX_original_nodes_covered hrun i hindexLt
  have hposLen : pos < run.proper.nodes.length :=
    componentRunX_original_nodes_covered hrun pos hposLt
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
  obtain ⟨ltT, hlyT, _, hnnT⟩ := hcov i hindexLen
  rw [rEqT] at hlyT hnnT
  have hcap0 := hcap execution hcomp hrun i stored0 tNode hmem hnode hborder
  have hltTget : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = ltT := by
    simp only [List.getD_eq_getElem?_getD, hlyT, Option.getD_some]
  rw [hltTget] at hcap0
  have hmemberGet : (componentCandidate execution.graph comp candidate).nodes.getD pos
      default = fNode := by
    simp only [List.getD_eq_getElem?_getD, hfn, Option.getD_some]
  have hRB := (X_ReserveBands_holds exactIds) hrun
  obtain ⟨ltM, hlyM, _, hnnM⟩ := hcov pos hposLen
  have hnnM0 : 0 ≤ rk run.proper.rank pos := hnnM
  rw [rEqM] at hlyM hnnM
  by_cases hfb : fNode.border = -2
  · obtain ⟨rrC, hrrC, hchainLe⟩ :=
      (XC_descChainXW_holds exactIds) execution hwf hfp hcomp hrun
        hnode hborder hfn hfb hne hpath
    have hrrEq : rrC = rr := Except.ok.inj (hrrC.symm.trans hrr)
    rw [hrrEq] at hchainLe
    have ePos : rk run.coordinateProper.rank pos = rk rr.ranks pos := by
      have h2 := xcmw_prepared (P := execution.params) (exact := exactDecls exactIds inp)
        hrr hranks hposLt
      rw [hc] at h2
      exact h2
    have hltTM : (rk run.coordinateProper.rank i).toNat <
        (rk run.coordinateProper.rank pos).toNat := by
      have h1 := eTop
      have h2 := ePos
      have h3 : rk rr.ranks i + 1 ≤ rk rr.ranks pos := hchainLe
      have h4 := hnnT
      have h5 := hnnM
      omega
    have hbandTM := hRB.2 _ _ _ _ hltTM hlyT hlyM
    have htopLe := (XC_childTopXW_holds exactIds) execution hwf hfp hcomp hrun hfn hfb
    unfold ChildTopRankLe at htopLe
    rw [hmemberGet] at htopLe
    obtain ⟨sideIndex, side, hside, _, howner⟩ :=
      xcmw_group_final_side execution.graph0_eq execution.graph_eq hcomp hrun hfn hfb
    let descRects := run.proper.nodes.zipIdx.filterMap fun q =>
      if q.1.node.clusterPath.contains fNode.decl then
        some (Labels.rectAt run.proper run.xs run.ys q.2)
      else none
    have hsideMem : Labels.rectAt run.proper run.xs run.ys sideIndex ∈ descRects := by
      apply List.mem_filterMap.mpr
      refine ⟨(side, sideIndex), List.mem_zipIdx_iff_getElem?.mpr hside, ?_⟩
      have hmemSide : fNode.decl ∈ side.node.clusterPath := List.mem_of_getLast? howner
      simp [hmemSide]
    have hneDesc : descRects ≠ [] := by
      intro hempty
      rw [hempty] at hsideMem
      exact List.not_mem_nil hsideMem
    have hmin : run.top.getD (rk run.coordinateProper.rank pos).toNat 0 ≤
        (boundsOf descRects []).minY := by
      refine xcmw_minY_of_all_le _ _ ?_ hneDesc
      intro r hr
      obtain ⟨entry, hentry, heq⟩ := List.mem_filterMap.mp hr
      split at heq
      · rename_i hcontains
        have hrectEq := Option.some.inj heq
        rw [← hrectEq]
        have hle : rk run.proper.rank pos ≤ rk run.proper.rank entry.2 :=
          htopLe entry hentry hcontains
        have hqLen : entry.2 < run.proper.nodes.length :=
          (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hentry)).1
        have hqCoordLen : entry.2 < run.coordinateProper.nodes.length := by
          obtain ⟨_, _, _, q0E, _, _, _, _, _, hproxyE, hdropE, _, _, _⟩ :=
            componentRunX_spec hrun
          obtain ⟨_, _, hqlenE, _, _, _⟩ := proxyWidths_rel hproxyE
          have hnodesE : run.proper.nodes = q0E.nodes := by rw [← hdropE]; rfl
          have h1 : entry.2 < q0E.nodes.length := by rw [← hnodesE]; exact hqLen
          omega
        have rEqE := X_proper_rank_eq_local hrun entry.2
        have hleC : rk run.coordinateProper.rank pos ≤
            rk run.coordinateProper.rank entry.2 := by
          rw [← rEqM, ← rEqE]; exact hle
        obtain ⟨ltQ, hlyQ, hmemQ, hnnQ⟩ := hcov entry.2 hqLen
        rw [rEqE] at hlyQ
        have hnnQc : 0 ≤ rk run.coordinateProper.rank entry.2 := by
          rw [← rEqE]; exact hnnQ
        have hmonoQ : run.top.getD (rk run.coordinateProper.rank pos).toNat 0 ≤
            run.top.getD (rk run.coordinateProper.rank entry.2).toNat 0 := by
          by_cases heqR : (rk run.coordinateProper.rank pos).toNat =
              (rk run.coordinateProper.rank entry.2).toNat
          · rw [heqR]; exact Int.le_refl _
          · have hltQ : (rk run.coordinateProper.rank pos).toNat <
                (rk run.coordinateProper.rank entry.2).toNat := by
              have h1 := hleC
              have h2 := hnnQc
              have h3 : 0 ≤ rk run.coordinateProper.rank pos := by
                rw [← rEqM]; exact hnnM0
              omega
            have hle2 := hRB.2 _ _ _ _ hltQ hlyM hlyQ
            have hHnn : 0 ≤ CoordsImpl.layerHeight run.coordinateProper ltM :=
              CoordsImpl.layerHeight_nonneg _ _
            omega
        have hrkQ : rk run.coordinateProper.rank entry.2 =
            ((rk run.coordinateProper.rank entry.2).toNat : Int) := by
          have h := Int.toNat_of_nonneg hnnQc
          exact h.symm
        have hbandLoQ := hRB.1 _ _ _ hlyQ hmemQ hqCoordLen hrkQ
        have hYq : (Labels.rectAt run.proper run.xs run.ys entry.2).y =
            run.ys.getD entry.2 0 := rfl
        rw [hYq]
        have h1 := hmonoQ
        have h2 := hbandLoQ.1
        omega
      · cases heq
    have hframeY : g0.y = (boundsOf descRects []).minY := by
      rw [← hframe]
      simp only [descRects, frameRect, hmemberGet, hfb,
        show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rw [← hframeY] at hmin
    unfold Disjoint
    intro hcon
    obtain ⟨-, hy⟩ := hcon
    omega
  · have hb2 : fNode.border = 2 := by
      have hshapeB := (X_componentCandidate_marker_shape execution.graph0_eq
        execution.graph_eq hfn).1
      rcases hshapeB with h0 | hm2 | h2
      · exact absurd h0 hnonplain
      · exact absurd hm2 hfb
      · exact h2
    obtain ⟨t, ht⟩ := X_componentRun_cg_top_of_bottom execution.graph0_eq
      execution.graph_eq hlines hcomp hfn hb2
    have htPred := List.find?_some ht
    simp only [Bool.and_eq_true, beq_iff_eq] at htPred
    obtain ⟨htBorder, htPath⟩ := htPred
    have htMem : t ∈ (componentCandidate execution.graph comp candidate).nodes.zipIdx :=
      List.mem_of_find?_eq_some ht
    have htLookup : (componentCandidate execution.graph comp candidate).nodes[t.2]? =
        some t.1 := List.mem_zipIdx_iff_getElem?.mp htMem
    have hlastT : t.1.clusterPath.getLast? = some t.1.decl := by
      obtain ⟨_, _, hpathT⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq
        htLookup htBorder
      rw [hpathT]; simp
    have hlastF : fNode.clusterPath.getLast? = some fNode.decl :=
      (xcmw_bottom_path execution.graph0_eq execution.graph_eq hfn hb2).1
    have htDecl : t.1.decl = fNode.decl := by
      have hget : t.1.clusterPath.getLast? = fNode.clusterPath.getLast? :=
        congrArg List.getLast? htPath
      rw [hlastT, hlastF] at hget
      exact Option.some.inj hget
    have hneT : tNode.decl ≠ t.1.decl := by
      rw [htDecl]
      exact hne
    have hcontainsT : t.1.clusterPath.contains tNode.decl = true := by
      rw [htPath]
      exact hpath
    have htLt : t.2 < (componentCandidate execution.graph comp candidate).nodes.length :=
      (List.getElem?_eq_some_iff.mp htLookup).1
    obtain ⟨rrT, hrrT, hchainTLe⟩ :=
      (XC_descChainXW_holds exactIds) execution hwf hfp hcomp hrun
        hnode hborder htLookup htBorder hneT hcontainsT
    have hrrTEq : rrT = rr := Except.ok.inj (hrrT.symm.trans hrr)
    rw [hrrTEq] at hchainTLe
    have etT : rk run.coordinateProper.rank t.2 = rk rr.ranks t.2 := by
      have h2 := xcmw_prepared (P := execution.params) (exact := exactDecls exactIds inp)
        hrr hranks htLt
      rw [hc] at h2
      exact h2
    have rEqN := X_proper_rank_eq_local hrun t.2
    have htLen : t.2 < run.proper.nodes.length :=
      componentRunX_original_nodes_covered hrun t.2 htLt
    obtain ⟨ltN, hlyN, _, hnnN⟩ := hcov t.2 htLen
    rw [rEqN] at hlyN hnnN
    have hltTN : (rk run.coordinateProper.rank i).toNat <
        (rk run.coordinateProper.rank t.2).toNat := by
      have h1 := eTop
      have h2 := etT
      have h3 : rk rr.ranks i + 1 ≤ rk rr.ranks t.2 := hchainTLe
      have h4 := hnnT
      have h5 := hnnN
      omega
    have hbandTN := hRB.2 _ _ _ _ hltTN hlyT hlyN
    obtain ⟨coord, hcoord, hcoordB, _, hcoordP, hcoordH⟩ :=
      xcmw_bottom_coordinate execution.graph0_eq execution.graph_eq hcomp hrun hfn hb2
    obtain ⟨bprop, hbprop, hbpropP, _⟩ :=
      xcmw_bottom_proper hrun hcoord hcoordB hcoordH
    have hbproperD : run.proper.nodes.getD pos default = bprop := by
      simp only [List.getD_eq_getElem?_getD, hbprop, Option.getD_some]
    have hcontainsP : (run.proper.nodes.getD pos default).node.clusterPath.contains
        t.1.decl = true := by
      rw [hbproperD, hbpropP, hcoordP, htDecl]
      exact (xcmw_bottom_path execution.graph0_eq execution.graph_eq hfn hb2).2
    have htGet : (componentCandidate execution.graph comp candidate).nodes.getD t.2
        default = t.1 := by
      simp only [List.getD_eq_getElem?_getD, htLookup, Option.getD_some]
    have hcloseLe : rk run.proper.rank t.2 ≤ rk run.proper.rank pos := by
      have hq2 : (bprop, pos) ∈ run.proper.nodes.zipIdx :=
        List.mk_mem_zipIdx_iff_getElem?.mpr hbprop
      have hq3 : (run.proper.nodes.getD pos default, pos) ∈ run.proper.nodes.zipIdx := by
        rw [hbproperD]; exact hq2
      have hcont : (run.proper.nodes.getD pos default).node.clusterPath.contains
          t.1.decl = true := hcontainsP
      have hclose := (XC_childTopXW_holds exactIds) execution hwf hfp hcomp hrun
        htLookup htBorder
      unfold ChildTopRankLe at hclose
      rw [htGet] at hclose
      exact hclose _ hq3 hcont
    obtain ⟨lP0B, hlyP0B, _, hnnP0B⟩ := hcov t.2 htLen
    obtain ⟨lQ0B, hlyQ0B, hmemQ0B, hnnQ0B⟩ := hcov pos hposLen
    rw [rEqN] at hlyP0B hnnP0B
    rw [rEqM] at hlyQ0B hnnQ0B
    have hcloseLeC : rk run.coordinateProper.rank t.2 ≤
        rk run.coordinateProper.rank pos := by
      rw [← rEqN, ← rEqM]; exact hcloseLe
    have hmono : run.top.getD (rk run.coordinateProper.rank t.2).toNat 0 ≤
        run.top.getD (rk run.coordinateProper.rank pos).toNat 0 := by
      by_cases heqR : (rk run.coordinateProper.rank t.2).toNat =
          (rk run.coordinateProper.rank pos).toNat
      · rw [heqR]; exact Int.le_refl _
      · have hltQ : (rk run.coordinateProper.rank t.2).toNat <
            (rk run.coordinateProper.rank pos).toNat := by
          have h1 := hcloseLeC
          have h2 := hnnP0B
          have h3 := hnnQ0B
          omega
        have hle2 := hRB.2 _ _ _ _ hltQ hlyP0B hlyQ0B
        have hHnn : 0 ≤ CoordsImpl.layerHeight run.coordinateProper lP0B :=
          CoordsImpl.layerHeight_nonneg _ _
        omega
    have hcoordLenM : pos < run.coordinateProper.nodes.length := by
      obtain ⟨_, _, _, q0M, _, _, _, _, _, hproxyM, hdropM, _, _, _⟩ :=
        componentRunX_spec hrun
      obtain ⟨_, _, hqlenM, _, _, _⟩ := proxyWidths_rel hproxyM
      have hnodesM : run.proper.nodes = q0M.nodes := by rw [← hdropM]; rfl
      have h1 : pos < q0M.nodes.length := by rw [← hnodesM]; exact hposLen
      omega
    have hrkMnn : 0 ≤ rk run.coordinateProper.rank pos := hnnQ0B
    have hrkM : rk run.coordinateProper.rank pos =
        ((rk run.coordinateProper.rank pos).toNat : Int) := by
      have h := Int.toNat_of_nonneg hrkMnn
      exact h.symm
    have hbandLo := hRB.1 _ _ _ hlyQ0B hmemQ0B hcoordLenM hrkM
    have hb : (fNode.border != -2) = true := by
      simp only [bne_iff_ne]
      exact hfb
    have hfr : frameRect execution.params (componentCandidate execution.graph comp candidate)
        run pos =
        nodeRect (componentCandidate execution.graph comp candidate) run pos := by
      unfold frameRect
      simp only [hmemberGet, hb, ↓reduceIte]
    have hgy : (nodeRect (componentCandidate execution.graph comp candidate) run pos).y =
        run.ys.getD pos 0 := rfl
    have hbelow : (transportCaption execution.params o execution.lines comp i stored0).y +
        (transportCaption execution.params o execution.lines comp i stored0).h ≤
        run.ys.getD pos 0 := by
      have h1 := hcap0
      have h2 := hbandTN
      have h3 := hmono
      have h4 := hbandLo.1
      omega
    unfold Disjoint
    intro hcon
    obtain ⟨-, hy⟩ := hcon
    rw [← hframe, hfr, hgy] at hy
    omega

end PipelineImpl
end Layered
end Elegant

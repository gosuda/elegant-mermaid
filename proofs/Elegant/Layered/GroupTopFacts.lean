import Elegant.Layered.GroupRouteAttachment

set_option autoImplicit false

/-! ### Group top endpoint facts (C5, measured candidate graphs)

`GroupTopEndpointFactsCandidate` is discharged conjunct by conjunct.  The first
six conjuncts of `GroupTopEndpointData` are bookkeeping transports through
`componentRun_ranked_node_records`, `coordinateGraph_marker_record`,
`componentRun_proxy_interval`, and `componentRun_original_nodes_covered`; the
seventh is the member routing bound `hlow`, reduced through
`componentRun_executed_ys_ge_top_band` to a rank inequality over the cluster
subtree; the last two are `group_top_frame_facts`. -/

namespace Elegant.Layered.PipelineImpl

/-- A `border = -2` graph node index is in bounds and its `getD` lookup is a
real `getElem?` lookup. -/
private theorem group_top_index {cg : Graph} {v : Nat}
    (hcb : (cg.nodes.getD v default).border = -2) :
    v < cg.nodes.length ∧ cg.nodes[v]? = some (cg.nodes.getD v default) := by
  by_cases hlt : v < cg.nodes.length
  · have hg : cg.nodes[v]? = some (cg.nodes.getD v default) := by
      rw [List.getD_eq_getElem?_getD]
      simp [List.getElem?_eq_getElem hlt]
    exact ⟨hlt, hg⟩
  · exfalso
    have hget : cg.nodes[v]? = none := List.getElem?_eq_none (by omega)
    rw [List.getD_eq_getElem?_getD, hget, Option.getD_none] at hcb
    have hz : (default : Node).border = 0 := rfl
    rw [hz] at hcb
    omega

/-- The candidate `-2` node is a measured-graph group marker: its declaration is
its source index and its cluster path ends in that declaration. -/
private theorem group_top_decl_path {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hgroup : nd.border = -2) :
    nd.clusterPath.getLast? = some nd.decl ∧ nd.clusterPath.contains nd.decl = true := by
  obtain ⟨original, horiginal, hsource⟩ :=
    componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨hdecl, box, hbox, hrole, hpath⟩ :=
    measuredGraph_group_origin hgraph hsource hgroup
  have hlast : nd.clusterPath.getLast? = some nd.decl := by
    rw [hpath]
    simp
  exact ⟨hlast, by rw [hpath]; simp⟩

/-- The coordinate-graph record of a `-2` graph node: the titled, cleared
marker at the same index. -/
private theorem group_top_coordinate_record {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : cg.nodes[v]? = some nd) (hgroup : nd.border = -2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = -2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath := by
  obtain ⟨_, labeled, _, hc, _, hnodeRec, _⟩ := componentRun_ranked_node_records hrun
  have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hnodeRec v nd hnode
  have hmarker := coordinateGraph_marker_record (P := P) hrec (Or.inl hgroup) rfl
  rw [hc] at hmarker
  refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_⟩
  · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [hb, (titleF_keys _).2.1]
    exact hgroup
  · exact (clearF_keys _).1.trans (titleF_keys _).1
  · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1

/-- The executed record of the `-2` top proxy keeps the coordinate record's
cluster path; only the width is rewritten by `proxyWidths`. -/
private theorem group_top_proper_clusterPath {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = -2) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath := by
  obtain ⟨_, span, _, _, hproper, _, _⟩ :=
    componentRun_proxy_interval hrun hcoord (Or.inl hb)
  exact ⟨{ coord with node := { coord.node with w := span.hi - span.lo } }, hproper, rfl⟩

/-- The executed `run.proper` rank of every graph-index node equals the rank
record rank: the coordinate rank extends the rank record, and neither proxy
widths nor synthetic dropping touch the rank list. -/
private theorem group_top_rank_eq_coordinate {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (i : Nat) :
    rk run.proper.rank i = rk run.coordinateProper.rank i := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ := componentRun_spec hrun
  rw [← hdrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hproxy).2.1]

/-- The member routing bound for a `-2` top proxy: every executed node whose
cluster path contains the proxy's declaration is routed at or below the
proxy's band top.  `hrank` is the open seam `GroupTopSubtreeRankProper`
(`GroupTopRank.lean`) at this run and group top. -/
private theorem group_top_low_band
    {P : Params}
    {graph : Graph} {comp : List Nat}
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hcb : nd.border = -2)
    (hvcg : v < (componentCandidate graph comp candidate).nodes.length)
    (hrank : ∀ {i : Nat}, i < run.proper.nodes.length →
      (run.proper.nodes.getD i default).node.clusterPath.contains nd.decl = true →
      rk run.proper.rank v ≤ rk run.proper.rank i)
    (q : ProperNode × Nat) (hq : q ∈ run.proper.nodes.zipIdx)
    (hin : q.1.node.clusterPath.contains nd.decl = true) :
    run.ys.getD v 0 ≤ run.ys.getD q.2 0 := by
  have hqget : run.proper.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  have hqi : q.2 < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hqget).1
  have hqD : run.proper.nodes.getD q.2 default = q.1 := by
    rw [List.getD_eq_getElem?_getD, hqget, Option.getD_some]
  have hrk := hrank hqi (by rw [hqD]; exact hin)
  exact componentRun_executed_ys_ge_top_band hrun hnode hcb hvcg hqi hrk

/-- The candidate-graph form of the group-endpoint facts, one lemma per
conjunct of `GroupTopEndpointData`.  `hrsub` is the open seam
`GroupTopSubtreeRankProper` (`GroupTopRank.lean`) at this run and group top. -/
theorem groupTopEndpointFactsCandidate {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat}
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v : Nat}
    (hcb : ((componentCandidate graph comp candidate).nodes.getD v default).border =
      -2)
    (hrsub : ∀ {i : Nat}, i < run.proper.nodes.length →
      (run.proper.nodes.getD i default).node.clusterPath.contains
        ((componentCandidate graph comp candidate).nodes.getD v default).decl = true →
      rk run.proper.rank v ≤ rk run.proper.rank i) :
    GroupTopEndpointData (componentCandidate graph comp candidate) run v := by
  obtain ⟨hvcg, hnodeCg⟩ := group_top_index hcb
  have hdeclpath := group_top_decl_path hgraph hnodeCg hcb
  obtain ⟨coord, hcoord, hcoordBorder, _, hcoordPath⟩ :=
    group_top_coordinate_record hrun hnodeCg hcb
  obtain ⟨_, span, _, _, hproper, _, _⟩ :=
    componentRun_proxy_interval hrun hcoord (Or.inl hcoordBorder)
  have hcoordD : run.coordinateProper.nodes.getD v default = coord := by
    rw [List.getD_eq_getElem?_getD, hcoord, Option.getD_some]
  have hproperD : run.proper.nodes.getD v default =
      { coord with node := { coord.node with w := span.hi - span.lo } } := by
    rw [List.getD_eq_getElem?_getD, hproper, Option.getD_some]
  have hnodeCoord : run.coordinateProper.nodes[v]? =
      some (run.coordinateProper.nodes.getD v default) := by
    rw [hcoordD]
    exact hcoord
  have hv : v < run.proper.nodes.length := componentRun_original_nodes_covered hrun v hvcg
  have hframe := group_top_frame_facts hrun hnodeCoord
    (by rw [hcoordD]; exact hcoordBorder)
  refine ⟨hcb, hnodeCoord, ?_, ?_, ?_, hv, ?_, ?_, ?_⟩
  · rw [hcoordD]
    exact hcoordBorder
  · rw [hcoordD, hcoordPath]
    exact hdeclpath.1
  · rw [hproperD]
    show ({ coord with node := { coord.node with w := span.hi - span.lo } } : ProperNode).node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD v default).decl = true
    rw [hcoordPath]
    exact hdeclpath.2
  · intro q hq hin
    exact group_top_low_band hrun hnodeCg hcb hvcg hrsub q hq hin
  · exact hframe.1
  · exact hframe.2

end Elegant.Layered.PipelineImpl

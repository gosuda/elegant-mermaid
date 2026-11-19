import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.CompoundPathFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ExactMemberInFrame

set_option autoImplicit false

namespace Elegant
namespace Layered
open CoordsImpl
namespace PipelineImpl

 /-! Exact-run frame-nesting core: replay of the `GroupWidthFacts`
containment chain for `componentRunX`. The exact pipeline shares ranking,
ordering, borders, and coordinates with the plain pipeline; it changes node
sizes (`exactGraph`), port widening (`sizeProperPortsX`), and rank shifts
(`reserveExactRanks`). Sizes enter only through width lower bounds and
nonnegativity, which the exact run's own equations supply; rank shifts enter
only through `ys`/`top`, which the hull arguments below never use
quantitatively (`boundsOf` covers the shifted rectangles by construction).
Every lemma below mirrors its plain counterpart with `componentRunX_spec`
and the `sizeProperPortsX` key facts. -/

/-- Exact lines cover every input box. -/
private theorem X_lines_len {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  exact ((mapM_getElem? _ _ _ h).1).trans List.length_zipIdx

private def X_proj (n : Node) : Nat × Int × List Nat := (n.decl, n.border, n.clusterPath)

private theorem X_projMap {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    List.map X_proj execution.graph.nodes =
      List.map X_proj execution.graph0.nodes := by
  have hlen : execution.graph.nodes.length = execution.graph0.nodes.length :=
    exactGraph_length execution.graph_eq
  apply List.ext_getElem?
  intro v
  rw [List.getElem?_map, List.getElem?_map]
  cases h0 : execution.graph0.nodes[v]? with
  | none =>
    have hnone : execution.graph.nodes[v]? = none := by
      rw [List.getElem?_eq_none_iff] at h0 ⊢
      omega
    rw [hnone]
  | some nd0 =>
    obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key execution.graph_eq h0
    rw [hnd']
    simp only [Option.map_some, X_proj, hnb, hnap, hnd]

/-- Every exact-graph node comes from the measured-graph node at the same
index with the same key fields. -/
private theorem X_revKey {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {v : Nat} {nd : Node} (h : execution.graph.nodes[v]? = some nd) :
    ∃ nd0, execution.graph0.nodes[v]? = some nd0 ∧ nd0.decl = nd.decl ∧
      nd0.border = nd.border ∧ nd0.clusterPath = nd.clusterPath := by
  have hmap := X_projMap execution
  have h1 : (List.map X_proj execution.graph.nodes)[v]? = some (X_proj nd) := by
    simp only [List.getElem?_map, h, Option.map_some]
  rw [hmap] at h1
  rw [List.getElem?_map] at h1
  obtain ⟨nd0, hnd0, hproj⟩ := Option.map_eq_some_iff.mp h1
  simp only [X_proj, Prod.mk.injEq] at hproj
  exact ⟨nd0, hnd0, hproj.1, hproj.2.1, hproj.2.2⟩

/-- Exact-graph border classification transfers to the measured graph. -/
private theorem X_borderSplit {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} (hkeyLen : key < inp.boxes.length)
    {member : Node} (hmemberGraph : execution.graph.nodes[key]? = some member) :
    ∃ member0, execution.graph0.nodes[key]? = some member0 ∧
      member0.border = member.border ∧ member0.decl = member.decl ∧
      member0.clusterPath = member.clusterPath ∧
      (member.border = 0 ∨ member.border = -2) := by
  obtain ⟨member0, hmember0, hdecl, hborder, hpath⟩ := X_revKey execution hmemberGraph
  have h0 : member0.border = 0 ∨ member0.border = -2 := by
    obtain ⟨nodes, edges, titles, hprepared, hnodeLen, hmetadata⟩ :=
      measuredGraph_prepared_source execution.graph0_eq
    have hkeyNodes : key < nodes.length := by
      rw [hnodeLen, X_lines_len execution]
      exact hkeyLen
    rw [hprepared] at hmember0
    have hdemoted : (inp.boxes.map (fun source : ModelBox =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
          { source with role := .node } else source))[key]? =
        some ((fun source : ModelBox =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
          { source with role := .node } else source) inp.boxes[key]) := by
      simp only [List.getElem?_map, List.getElem?_eq_getElem hkeyLen, Option.map_some]
    by_cases hng : ((fun source : ModelBox =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
          { source with role := .node } else source) inp.boxes[key]).role = .group
    · rw [Compound.prepare_group_title_record _ _ _ ⟨nodes, edges, execution.params.slot⟩
        hkeyNodes hdemoted hng] at hmember0
      refine Or.inr ?_
      have hb := congrArg Node.border (Option.some.inj hmember0)
      simpa using hb.symm
    · rw [Compound.prepare_plain_node_record _ _ _ ⟨nodes, edges, execution.params.slot⟩
        hkeyNodes hdemoted hng] at hmember0
      refine Or.inl ?_
      have hsrc := hmetadata key nodes[key] (List.getElem?_eq_getElem hkeyNodes)
      have hb : member0.border = nodes[key].border :=
        (congrArg Node.border (Option.some.inj hmember0)).symm
      rw [hb]
      exact hsrc.2
  rcases h0 with h0 | h0
  · exact ⟨member0, hmember0, hborder, hdecl, hpath, Or.inl (hborder.symm.trans h0)⟩
  · exact ⟨member0, hmember0, hborder, hdecl, hpath, Or.inr (hborder.symm.trans h0)⟩

 /-- Plain measured-graph nodes resolve to input boxes over original boxes. -/
 private theorem X_plainPath {exactIds : List String} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
     {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
     (hplain : node.border = 0) :
     ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
       node.clusterPath = Compound.path inp.boxes box := by
  have hlineLength : execution.lines.length = inp.boxes.length := X_lines_len execution
  obtain ⟨nodes, edges, titles, hprepared, hnodeLength, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hpreparedNode := hnode
  rw [hprepared] at hpreparedNode
  have hi : index < nodes.length := by
    by_cases hi : index < nodes.length
    · exact hi
    · have hb := Compound.prepare_bottom_of_index _ _ _ _ index (by dsimp only; omega)
        hpreparedNode
      omega
  have hibox : index < inp.boxes.length := by omega
  let box := inp.boxes[index]'hibox
  have hbox : inp.boxes[index]? = some box := List.getElem?_eq_getElem hibox
  obtain ⟨_, hchangedBox, hpathMap⟩ := fixedSizes_path_index inp hbox
  obtain ⟨hdecl, hpath⟩ :=
    prepare_plain_path_origin _ _ _ _ hmetadata hpreparedNode hplain hchangedBox
  exact ⟨box, hbox, hdecl, hpath.trans hpathMap⟩
 private theorem X_ranked_source {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (h : componentRunX P exact cg labels orderOptions = .ok run) :
     ∃ (rr : RankImpl.RankResult) (normalized labeled : Proper),
       rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧
       normalize cg rr.ranks = .ok normalized ∧
       Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled ∧
       coordinateGraphX P exact labeled = run.coordinateProper ∧
       ∀ edge ∈ (Compound.rankingGraph cg).edges,
         edge.minLen ≤ rk rr.ranks edge.head - rk rr.ranks edge.tail := by
   unfold componentRunX at h
   obtain ⟨rr, hrr, h⟩ := bind_ok h
   obtain ⟨normalized, hn, h⟩ := bind_ok h
   obtain ⟨labeled, hl, h⟩ := bind_ok h
   obtain ⟨ord, _, h⟩ := bind_ok h
   obtain ⟨xs, _, h⟩ := bind_ok h
   obtain ⟨routed, _, h⟩ := bind_ok h
   obtain ⟨lanes, _, h⟩ := bind_ok h
   obtain ⟨yt, _, h⟩ := bind_ok h
   obtain ⟨shifted, _, h⟩ := bind_ok h
   obtain ⟨routes, _, h⟩ := bind_ok h
   have heq := Except.ok.inj h
   subst run
   refine ⟨rr, normalized, labeled, hrr, hn, hl, rfl, ?_⟩
   apply rank_feasible (Compound.rankingGraph cg) rr.ranks
   simp only [RankImpl.rank, hrr]

/-- Group-top measured-graph nodes resolve to input boxes. -/
private theorem X_groupPath {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ box : ModelBox, inp.boxes[index]? = some box ∧ node.decl = index ∧
      node.clusterPath = Compound.path inp.boxes box ++ [index] := by
  obtain ⟨hdecl, effective, heffective, _, hpath⟩ :=
    measuredGraph_group_origin execution.graph0_eq hnode hgroup
  rw [hdecl, List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  refine ⟨box, hbox, hdecl, ?_⟩
  rw [← hchange] at hpath
  rw [hpathMap, hdecl] at hpath
  exact hpath

/-- Bottom-marker measured-graph nodes resolve to input boxes. -/
private theorem X_bottomPath {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {index : Nat} {node : Node} (hnode : execution.graph0.nodes[index]? = some node)
    (hborder : node.border = 2) :
    ∃ box : ModelBox, inp.boxes[node.decl]? = some box ∧
      node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
  obtain ⟨effective, heffective, _, hpath, _, _⟩ :=
    measuredGraph_bottom_origin execution.graph0_eq (List.mem_of_getElem? hnode) hborder
  rw [List.getElem?_map] at heffective
  obtain ⟨box, hbox, hchange⟩ := Option.map_eq_some_iff.mp heffective
  obtain ⟨_, _, hpathMap⟩ := fixedSizes_path_index inp hbox
  refine ⟨box, hbox, ?_⟩
  rw [← hchange] at hpath
  rw [hpathMap] at hpath
  exact hpath

 /-- `sizeProperPortsX` preserves the node count. -/
 private theorem X_sized_length (P : Params) (exact : List Nat) (p : Proper) :
     (sizeProperPortsX P exact p).nodes.length = p.nodes.length := by
   unfold sizeProperPortsX
   simp

 /-- Titled reservations preserve node/rank alignment for exact sizing. -/
 private theorem X_titled_alignment (P : Params) (exact : List Nat) {source : Proper}
     (h : source.nodes.length = source.rank.length) :
     (titleReservations (sizeProperPortsX P exact source)).nodes.length =
       (titleReservations (sizeProperPortsX P exact source)).rank.length := by
   rw [titleReservations_nodes]
   simp only [List.length_append, List.length_map, X_sized_length]
   have hrank : (titleReservations (sizeProperPortsX P exact source)).rank =
       source.rank ++ (titleNodes (sizeProperPortsX P exact source)).map
         (fun entry => rk source.rank entry.2) := by
     unfold titleReservations titleNodes sizeProperPortsX
     rfl
   rw [hrank]
   simp only [List.length_append, List.length_map]
   omega

/-- Exact-run coordinate source alignment. -/
private theorem X_coordinate_alignment {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ labeled : Proper, coordinateGraphX P exact labeled = run.coordinateProper ∧
      NodeKeys cg labeled ∧ labeled.nodes.length = labeled.rank.length ∧
      (titleReservations (sizeProperPortsX P exact labeled)).nodes.length =
        (titleReservations (sizeProperPortsX P exact labeled)).rank.length := by
  obtain ⟨_, normalized, labeled, _, hn, hl, hc, _⟩ := X_ranked_source h
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  exact ⟨labeled, hc, addLabelNodes_keys _ _ _ (normalize_keys hn) hl,
    haligned, X_titled_alignment P exact haligned⟩

 /-- Exact-sized nodes preserve dummy, border, and cluster path. -/
 private theorem X_sized_origin (P : Params) (exact : List Nat) (source : Proper)
     {index : Nat} {node : ProperNode}
     (hnode : (sizeProperPortsX P exact source).nodes[index]? = some node) :
     ∃ original : ProperNode, source.nodes[index]? = some original ∧
       node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
       node.node.clusterPath = original.node.clusterPath := by
   have hkey := sizeProperPortsX_key P exact source index
   rw [hnode] at hkey
   cases horiginal : source.nodes[index]? with
   | none => simp [horiginal] at hkey
   | some original =>
       simp only [horiginal, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
       exact ⟨original, rfl, hkey⟩

 /-- Exact titled nodes come from source nodes or title entries. -/
 private theorem X_titled_origin {cg : Graph} {P : Params} {exact : List Nat} {source : Proper}
     (hkeys : NodeKeys cg source) {index : Nat} {node : ProperNode}
     (hnode : (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some node) :
     (∃ original : ProperNode, source.nodes[index]? = some original ∧
       node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
       node.node.clusterPath = original.node.clusterPath) ∨
     (node.dummy = false ∧ node.node.border = 3) := by
   rw [titleReservations_nodes] at hnode
   by_cases hi : index < (sizeProperPortsX P exact source).nodes.length
   · rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),
       List.getElem?_map] at hnode
     obtain ⟨sized, hsized, heq⟩ := Option.map_eq_some_iff.mp hnode
     obtain ⟨original, horiginal, hd, hb, hp⟩ :=
       X_sized_origin P exact source hsized
     have ht := titleF_keys sized
     rw [heq] at ht
     exact Or.inl ⟨original, horiginal, ht.1.trans hd,
       ht.2.1.trans hb, ht.2.2.1.trans hp⟩
   · rw [List.getElem?_append_right (by
       simpa only [List.length_map] using Nat.le_of_not_gt hi),
       List.getElem?_map] at hnode
     obtain ⟨entry, hentry, heq⟩ := Option.map_eq_some_iff.mp hnode
     obtain ⟨hsized, hborder⟩ := titleNodes_spec hentry
     obtain ⟨original, horiginal, hd, hb, _⟩ :=
       X_sized_origin P exact source hsized
     have hreal : original.dummy = false := by
       rcases hkeys entry.2 original horiginal with
         ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
       · exact hreal
       · rw [hplain] at hb
         omega
     right
     rw [← heq]
     exact ⟨hd.trans hreal, rfl⟩

 /-- Exact marker record for non-plain source nodes. -/
 private theorem X_titled_marker_record {P : Params} {exact : List Nat} {source : Proper}
     {index : Nat} {node : ProperNode} (hnode : source.nodes[index]? = some node)
     (hborder : node.node.border = -2 ∨ node.node.border = 2) :
     (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some (titleF node) := by
   have hnonplain : node.node.border ≠ 0 := by
     rcases hborder with hborder | hborder <;> omega
   have hsized : (sizeProperPortsX P exact source).nodes[index]? = some node := by
     unfold sizeProperPortsX
     simp only [List.getElem?_map, List.getElem?_zipIdx, hnode, Option.map_some,
       Nat.zero_add]
     simp [hnonplain]
   rw [titleReservations_nodes, List.getElem?_append_left (by
     simp only [List.length_map, X_sized_length]
     exact (List.getElem?_eq_some_iff.mp hnode).1)]
   simp only [List.getElem?_map, hsized, Option.map_some]

 /-- Exact titled markers come from candidate graph nodes. -/
 private theorem X_titled_marker_source_record {cg : Graph} {P : Params} {exact : List Nat}
     {source : Proper}
     (hkeys : NodeKeys cg source)
     (hrecords : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
       source.nodes[index]? = some ⟨node, false, none, false⟩)
     {index : Nat} {marker : ProperNode}
     (hmarker : (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some marker)
     (hborder : marker.node.border = -2 ∨ marker.node.border = 2) :
     ∃ original : Node, cg.nodes[index]? = some original ∧
       marker.node.border = original.border ∧
       marker = titleF ⟨original, false, none, false⟩ := by
  rcases X_titled_origin hkeys hmarker with
    ⟨before, hbefore, _, hb, _⟩ | ⟨_, hb⟩
  · rcases hkeys index before hbefore with
      ⟨original, horiginal, _, hsourceBorder, _⟩ | ⟨_, hplain, _⟩
    · have hborderOriginal : original.border = -2 ∨ original.border = 2 := by
        rcases hborder with hborder | hborder <;> omega
      have hforward := X_titled_marker_record (P := P) (exact := exact)
        (hrecords index original horiginal) hborderOriginal
      exact ⟨original, horiginal, hb.trans hsourceBorder,
        Option.some.inj (hmarker.symm.trans hforward)⟩
    · rcases hborder with hborder | hborder <;> omega
  · rcases hborder with hborder | hborder <;> omega
 private theorem X_titled_rank_prefix (P : Params) (exact : List Nat) (source : Proper) :
     ∃ extra, (titleReservations (sizeProperPortsX P exact source)).rank =
       source.rank ++ extra := by
   unfold titleReservations sizeProperPortsX
   exact ⟨_, rfl⟩

 /-- Exact titled rank prefix. -/
 private theorem X_titled_rank_record {P : Params} {exact : List Nat} {source : Proper}
     {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
     (titleReservations (sizeProperPortsX P exact source)).rank[index]? = some rank := by
   obtain ⟨extra, heq⟩ := X_titled_rank_prefix P exact source
   rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
   exact h

 private theorem X_coordinate_anchor_prefix (P : Params) (exact : List Nat) (source : Proper) :
     (∃ extra, (coordinateGraphX P exact source).nodes.map ProperNode.edge =
       source.nodes.map ProperNode.edge ++ extra) ∧
     (∃ extra, (coordinateGraphX P exact source).rank = source.rank ++ extra) := by
   have mapped : ∀ (nodes : List ProperNode) (f : ProperNode → ProperNode),
       (∀ n, (f n).edge = n.edge) →
       (nodes.map f).map ProperNode.edge = nodes.map ProperNode.edge := by
     intro nodes f hf
     simp only [List.map_map]
     apply congrArg (fun g => nodes.map g)
     funext n
     exact hf n
   have indexed : ∀ (nodes : List ProperNode) (f : ProperNode × Nat → ProperNode),
       (∀ n, (f n).edge = n.1.edge) →
       (nodes.zipIdx.map f).map ProperNode.edge = nodes.map ProperNode.edge := by
     intro nodes f hf
     calc
       (nodes.zipIdx.map f).map ProperNode.edge =
           (nodes.zipIdx.map Prod.fst).map ProperNode.edge := by
         simp only [List.map_map]
         apply congrArg (fun g => nodes.zipIdx.map g)
         funext n
         exact hf n
       _ = nodes.map ProperNode.edge := by rw [List.zipIdx_map_fst]
   have hs : (sizeProperPortsX P exact source).nodes.map ProperNode.edge =
       source.nodes.map ProperNode.edge := by
     unfold sizeProperPortsX
     apply indexed
     intro n
     split <;> rfl
   have ht : ∀ nodes : List ProperNode,
       (nodes.map titleF).map ProperNode.edge = nodes.map ProperNode.edge := by
     intro nodes
     apply mapped
     intro n
     unfold titleF
     split <;> rfl
   have hc : ∀ q : Proper,
       (clearProxyExtents q).nodes.map ProperNode.edge = q.nodes.map ProperNode.edge := by
     intro q
     rw [clearProxyExtents_nodes]
     apply mapped
     intro n
     unfold clearF
     split <;> rfl
   have hm : ∀ q : Proper,
       (materializeDummyPaths q).nodes.map ProperNode.edge = q.nodes.map ProperNode.edge := by
     intro q
     unfold materializeDummyPaths
     apply indexed
     intro n
     split <;> rfl
   obtain ⟨extraNodes, hn, _⟩ := addClusterBorders_extra
     (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW
   constructor
   · unfold coordinateGraphX
     rw [hm, hc, hn, List.map_append, titleReservations_nodes, List.map_append, ht, hs]
     refine ⟨((titleNodes (sizeProperPortsX P exact source)).map copyF).map ProperNode.edge ++
       extraNodes.map ProperNode.edge, ?_⟩
     rw [List.append_assoc]
   · obtain ⟨extraRanks, hr⟩ := addClusterBorders_rank_prefix
       (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW
     have htitle : ∃ tail, (titleReservations (sizeProperPortsX P exact source)).rank =
         source.rank ++ tail :=
       ⟨_, rfl⟩
     obtain ⟨tail, htitle⟩ := htitle
     refine ⟨tail ++ extraRanks, ?_⟩
     change (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).rank = _
     rw [hr, htitle, List.append_assoc]

 /-- Exact coordinate rank prefix records. -/
 private theorem X_coordinate_rank_record {P : Params} {exact : List Nat} {source : Proper}
     {index : Nat} {rank : Int} (h : source.rank[index]? = some rank) :
    (coordinateGraphX P exact source).rank[index]? = some rank := by
  obtain ⟨extra, heq⟩ := (X_coordinate_anchor_prefix P exact source).2
  rw [heq, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h




 /-- Exact sided nodes transfer through the coordinate construction. -/
 private theorem X_side_record {P : Params} {exact : List Nat} {source : Proper}
     {index : Nat} {node : ProperNode}
     (hnode : (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).nodes[index]? =
         some node)
     (hdummy : node.dummy = false)
     (hborder : node.node.border = -1 ∨ node.node.border = 1) :
     (coordinateGraphX P exact source).nodes[index]? = some node := by
   have hnotProxy :
       (node.node.border == -2 || node.node.border == 2) = false := by
     rcases hborder with hborder | hborder <;> simp [hborder]
   have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
         some node := by
     simp only [clearProxyExtents, List.getElem?_map, hnode, Option.map_some]
     simp only [hnotProxy, Bool.false_eq_true, ↓reduceIte]
   unfold coordinateGraphX materializeDummyPaths
   simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some,
     Nat.zero_add, hdummy, Bool.false_eq_true, ↓reduceIte]

 /-- Exact marker nodes transfer through the coordinate construction. -/
 private theorem X_marker_record {P : Params} {exact : List Nat} {source : Proper}
     {index : Nat} {node : ProperNode} (hnode : source.nodes[index]? = some node)
     (hborder : node.node.border = -2 ∨ node.node.border = 2)
     (hdummy : node.dummy = false) :
     (coordinateGraphX P exact source).nodes[index]? = some (clearF (titleF node)) := by
   have htitled := X_titled_marker_record (P := P) (exact := exact) hnode hborder
   obtain ⟨extra, hextension, _⟩ := addClusterBorders_extra
     (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW
   have hbordered : (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).nodes[index]? =
         some (titleF node) := by
     rw [hextension, List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitled).1]
     exact htitled
   have hcleared : (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
         some (clearF (titleF node)) := by
     rw [clearProxyExtents_nodes, List.getElem?_map, hbordered]
     rfl
   have hreal : (clearF (titleF node)).dummy = false :=
     (clearF_keys _).1.trans ((titleF_keys node).1.trans hdummy)
   unfold coordinateGraphX materializeDummyPaths
   simp only [List.getElem?_map, List.getElem?_zipIdx, hcleared, Option.map_some,
     Nat.zero_add, hreal, Bool.false_eq_true, ↓reduceIte]

 /-- Exact port sizing can widen a plain anchor but never shrinks it. -/
 private theorem X_plain_anchor_dims (P : Params) {exact : List Nat} {p : Proper}
     {i : Nat} {nd : ProperNode} (hp : p.nodes[i]? = some nd)
     (hb : nd.node.border = 0) :
     ∃ out, (coordinateGraphX P exact p).nodes[i]? = some out ∧
       out.edge = nd.edge ∧ out.node.border = 0 ∧
       nd.node.w ≤ out.node.w ∧ out.node.h = nd.node.h := by
   obtain ⟨sized, hs, he, hb', hw, hh⟩ :
       ∃ sized, (sizeProperPortsX P exact p).nodes[i]? = some sized ∧
         sized.edge = nd.edge ∧ sized.node.border = 0 ∧
         nd.node.w ≤ sized.node.w ∧ sized.node.h = nd.node.h := by
     unfold sizeProperPortsX
     simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
     split
     · exact ⟨nd, rfl, rfl, hb, Int.le_refl _, rfl⟩
     · refine ⟨_, rfl, rfl, hb, ?_, rfl⟩
       exact Int.le_max_left _ _
   have hi := (List.getElem?_eq_some_iff.mp hs).1
   have htitle : (titleReservations (sizeProperPortsX P exact p)).nodes[i]? = some sized := by
     rw [titleReservations_nodes,
       List.getElem?_append_left (by simpa only [List.length_map] using hi)]
     simp [List.getElem?_map, hs, titleF, hb']
   obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
     (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
   have hplaced : (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]? = some sized := by
     rw [hborder,
       List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
     exact htitle
   have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[i]? =
         some sized := by
     rw [clearProxyExtents_nodes]
     simp [List.getElem?_map, hplaced, clearF, hb']
   unfold coordinateGraphX materializeDummyPaths
   simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
   split <;> exact ⟨_, rfl, he, hb', hw, hh⟩

 /-- Exact plain nodes transfer from coordinate to proper runs. -/
 private theorem X_plain_node_dims {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (h : componentRunX P exact cg labels orderOptions = .ok run)
     {i : Nat} {nd : ProperNode}
     (hnode : run.coordinateProper.nodes[i]? = some nd)
     (hborder : nd.node.border = 0) :
     run.proper.nodes[i]? = some nd := by
   obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
   have hprojected := proxyWidths_plain_node hproxy hnode hborder
   rw [← hdrop]
   exact hprojected

 /-- Exact border nodes transfer without proxy changes. -/
 private theorem X_final_border_source {P : Params} {exact : List Nat} {cg : Graph}
     {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (h : componentRunX P exact cg labels orderOptions = .ok run)
     {index : Nat} {node : ProperNode}
     (hnode : run.proper.nodes[index]? = some node)
     (hborder : node.node.border = -1 ∨ node.node.border = 1) :
     run.coordinateProper.nodes[index]? = some node ∧
       run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  obtain ⟨_, _, hlength, _, hrecords, hunchanged⟩ := proxyWidths_rel hproxy
  have hrouted : q0.nodes[index]? = some node := by
    rw [← hdrop] at hnode
    exact hnode
  have hbound : index < run.coordinateProper.nodes.length := by
    have hn := (List.getElem?_eq_some_iff.mp hrouted).1
    omega
  have hsource : run.coordinateProper.nodes[index]? =
      some run.coordinateProper.nodes[index] := List.getElem?_eq_getElem hbound
  obtain ⟨updated, hupdated, _, hborderEq, _⟩ := hrecords index _ hsource
  have hupdatedEq : updated = node := Option.some.inj (hupdated.symm.trans hrouted)
  have hsourceBorder : (run.coordinateProper.nodes[index]).node.border = node.node.border :=
    hborderEq.symm.trans (congrArg (fun value : ProperNode => value.node.border) hupdatedEq)
  have hnotProxy : ¬ ((run.coordinateProper.nodes[index]).node.border = -2 ∨
      (run.coordinateProper.nodes[index]).node.border = 2) := by
    rw [hsourceBorder]
    rcases hborder with hb | hb <;> omega
  obtain ⟨hexact, hx⟩ := hunchanged index _ hsource hnotProxy
  have heq : run.coordinateProper.nodes[index] = node :=
    Option.some.inj (hexact.symm.trans hrouted)
  refine ⟨hsource.trans (congrArg some heq), ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]
 /-- Exact side nodes come from bordered source nodes. -/
 private theorem X_side_original {P : Params} {exact : List Nat} {source : Proper}
     (hready : OrderImpl.BorderConstructionReady
       (titleReservations (sizeProperPortsX P exact source)))
     {index : Nat} {side : ProperNode}
     (hside : (coordinateGraphX P exact source).nodes[index]? = some side)
     (hborder : side.node.border = -1 ∨ side.node.border = 1) :
     (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact source))
         P.clusterBorderW).nodes[index]? = some side := by
   have hwf : OrderImpl.BordersWellFormed (coordinateGraphX P exact source) := by
     unfold coordinateGraphX
     exact materializeDummyPaths_bordersWellFormed
       (clearProxyExtents_bordersWellFormed
         (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))
   have hreal : side.dummy = false := by
     cases hd : side.dummy with
     | false => rfl
     | true =>
         have hz := hwf.2.2 index side hside hd
         rcases hborder with hborder | hborder <;> omega
   obtain ⟨cleared, hcleared, hd, _, _, heq⟩ :=
     materialize_lookup (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)) hside
   have hclearedReal : cleared.dummy = false := hd.symm.trans hreal
   have hsame : side = cleared := heq hclearedReal
   have hclearLookup : (clearProxyExtents (OrderImpl.addClusterBorders
       (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
         some side := by
     rw [hsame]
     exact hcleared
   rw [clearProxyExtents_nodes, List.getElem?_map] at hclearLookup
   obtain ⟨original, horiginal, hclearEq⟩ := Option.map_eq_some_iff.mp hclearLookup
   have hb : side.node.border = original.node.border := by
     rw [← hclearEq]
     exact (clearF_keys original).2.1
   have hoside : original.node.border = -1 ∨ original.node.border = 1 := by
     rwa [hb] at hborder
   have hclearId : clearF original = original := by
     unfold clearF
     rcases hoside with hoside | hoside <;> simp [hoside]
   exact horiginal.trans (congrArg some (hclearId.symm.trans hclearEq))

 /-- Exact titled border readiness. -/
 private theorem X_titled_ready {cg : Graph} {P : Params} {exact : List Nat} {source : Proper}
     (hkeys : NodeKeys cg source) (hshape : CgShape cg)
     (hmarkers : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
       (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
         (node.border = -2 → node.clusterPath ≠ []))
     (haligned : source.nodes.length = source.rank.length) :
     OrderImpl.BorderConstructionReady
       (titleReservations (sizeProperPortsX P exact source)) := by
  refine ⟨?_, ?_, ?_, X_titled_alignment P exact haligned, ?_⟩
  · intro node hnode
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases X_titled_origin hkeys hindex with ⟨original, horiginal, _, hb, _⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with ⟨before, hbefore, _, hborder, _⟩ | ⟨_, hborder, _⟩
      · have hc := (hmarkers index before hbefore).1
        rw [hb, hborder]
        rcases hc with hc | hc | hc <;> omega
      · rw [hb, hborder]
        exact ⟨by decide, by decide⟩
    · rw [hb]
      exact ⟨by decide, by decide⟩
  · intro node hnode hgroup
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases X_titled_origin hkeys hindex with ⟨original, horiginal, _, hb, hp⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with ⟨before, hbefore, _, hborder, hpath⟩ | ⟨_, hborder, _⟩
      · have hbeforeGroup : before.border = -2 := by omega
        rw [hp, hpath]
        exact (hmarkers index before hbefore).2 hbeforeGroup
      · omega
    · omega
  · intro a b na nb ha hb hgroupA hgroupB hpath
    rcases X_titled_origin hkeys ha with ⟨oa, hoa, _, hba, hpa⟩ | ⟨_, hba⟩
    · rcases X_titled_origin hkeys hb with ⟨ob, hob, _, hbb, hpb⟩ | ⟨_, hbb⟩
      · apply labeled_topUnique hkeys hshape hoa hob
        · omega
        · omega
        · rw [← hpa, ← hpb]
          exact hpath
      · omega
    · omega
  · intro node hnode hdummy
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases X_titled_origin hkeys hindex with ⟨original, horiginal, hd, hb, _⟩ | ⟨hd, _⟩
    · rcases hkeys index original horiginal with ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · rw [hreal] at hd
        rw [hd] at hdummy
        cases hdummy
      · exact hb.trans hplain
    · rw [hd] at hdummy
      cases hdummy

 /-- Exact candidate markers have valid shapes. -/
 private theorem X_marker_shape {exactIds : List String} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
     {comp : List Nat} {candidate index : Nat} {node : Node}
     (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node) :
     (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
       (node.border = -2 → node.clusterPath ≠ []) := by
  by_cases hplain : node.border = 0
  · exact ⟨Or.inl hplain, fun hgroup => by omega⟩
  · obtain ⟨_, _, hsource⟩ := componentCandidate_nonplain_source hnode hplain
    obtain ⟨member0, hmember0, _, hborder, hpath⟩ := X_revKey execution hsource
    obtain ⟨hdisj, hne⟩ := measuredGraph_marker_shape execution.graph0_eq hmember0
    refine ⟨?_, ?_⟩
    · rcases hdisj with h0 | h2 | h2
      · exact Or.inl (hborder.symm.trans h0)
      · exact Or.inr (Or.inl (hborder.symm.trans h2))
      · exact Or.inr (Or.inr (hborder.symm.trans h2))
    · intro hgroup
      have h0 : member0.border = -2 := hborder.trans hgroup
      rw [← hpath]
      exact hne h0


 /-- Exact border records transfer coordinates unchanged. -/
 private theorem X_border_record {P : Params} {exact : List Nat} {cg : Graph}
     {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (h : componentRunX P exact cg labels orderOptions = .ok run)
     {v : Nat} {node : ProperNode}
     (hv : run.coordinateProper.nodes[v]? = some node)
     (hborder : node.node.border = -1 ∨ node.node.border = 1) :
     run.proper.nodes[v]? = some node ∧
       run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
   obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
   have hnotProxy : ¬ (node.node.border = -2 ∨ node.node.border = 2) := by
     rcases hborder with hborder | hborder <;> omega
   obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v node hv hnotProxy
   refine ⟨?_, ?_⟩
   · rw [← hdrop]
     exact hnode
   · simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- Exact port sizing preserves node origin. -/
private theorem X_sizeProperPorts_node_origin (P : Params) (exact : List Nat)
    (source : Proper)
    {index : Nat} {node : ProperNode}
    (hnode : (sizeProperPortsX P exact source).nodes[index]? = some node) :
    ∃ original : ProperNode, source.nodes[index]? = some original ∧
      node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
      node.node.clusterPath = original.node.clusterPath := by
  have hkey := sizeProperPortsX_key P exact source index
  rw [hnode] at hkey
  cases horiginal : source.nodes[index]? with
  | none => simp [horiginal] at hkey
  | some original =>
      simp only [horiginal, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
      exact ⟨original, rfl, hkey⟩

/-- Exact titled reservations determine source alignment. -/
private theorem X_source_alignment_of_titled (P : Params) (exact : List Nat)
    {source : Proper}
    (h : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length) :
    source.nodes.length = source.rank.length := by
  rw [titleReservations_nodes] at h
  simp only [List.length_append, List.length_map, X_sized_length] at h
  have hrank : (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ (titleNodes (sizeProperPortsX P exact source)).map
        (fun entry => rk source.rank entry.2) := by
    unfold titleReservations titleNodes sizeProperPortsX
    rfl
  rw [hrank] at h
  simp only [List.length_append, List.length_map] at h
  omega

/-- The exact graph is shape-well-formed whenever the measured graph is. -/
private theorem X_cgShape {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    CgShape execution.graph := by
  have hshape := measuredGraph_shape execution.graph0_eq
  refine ⟨?_, ?_⟩
  · intro a b na nb ha hb h1 h2 hp
    obtain ⟨na0, ha0, _, hb1, hp1⟩ := X_revKey execution ha
    obtain ⟨nb0, hb0, _, hb2, hp2⟩ := X_revKey execution hb
    exact hshape.1 a b na0 nb0 ha0 hb0 (by rw [hb1]; exact h1) (by rw [hb2]; exact h2)
      (by rw [hp1, hp2]; exact hp)
  · intro n hn
    obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hn
    obtain ⟨n0, h0, _, hb, _⟩ := X_revKey execution hv
    have h3 := hshape.2 n0 (List.mem_of_getElem? h0)
    rw [hb] at h3
    exact h3

/-- Exact titled border readiness. -/
private theorem X_titled_border_ready {cg : Graph} {P : Params} {exact : List Nat}
    {source : Proper}
    (hkeys : NodeKeys cg source) (hshape : CgShape cg)
    (hmarkers : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []))
    (haligned : source.nodes.length = source.rank.length) :
    OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact source)) := by
  refine ⟨?_, ?_, ?_, X_titled_alignment P _ haligned, ?_⟩
  · intro node hnode
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases X_titled_origin hkeys hindex with
      ⟨original, horiginal, _, hb, _⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with
        ⟨before, hbefore, _, hborder, _⟩ | ⟨_, hborder, _⟩
      · have hc := (hmarkers index before hbefore).1
        rw [hb, hborder]
        rcases hc with hc | hc | hc <;> omega
      · rw [hb, hborder]
        exact ⟨by decide, by decide⟩
    · rw [hb]
      exact ⟨by decide, by decide⟩
  · intro node hnode hgroup
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases X_titled_origin hkeys hindex with
      ⟨original, horiginal, _, hb, hp⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with
        ⟨before, hbefore, _, hborder, hpath⟩ | ⟨_, hborder, _⟩
      · have hbeforeGroup : before.border = -2 := by omega
        rw [hp, hpath]
        exact (hmarkers index before hbefore).2 hbeforeGroup
      · omega
    · omega
  · intro a b na nb ha hb hgroupA hgroupB hpath
    rcases X_titled_origin hkeys ha with
      ⟨oa, hoa, _, hba, hpa⟩ | ⟨_, hba⟩
    · rcases X_titled_origin hkeys hb with
        ⟨ob, hob, _, hbb, hpb⟩ | ⟨_, hbb⟩
      · apply labeled_topUnique hkeys hshape hoa hob
        · omega
        · omega
        · rw [← hpa, ← hpb]
          exact hpath
      · omega
    · omega
  · intro node hnode hdummy
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases X_titled_origin hkeys hindex with
      ⟨original, horiginal, hd, hb, _⟩ | ⟨hd, _⟩
    · rcases hkeys index original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · rw [hreal] at hd
        rw [hd] at hdummy
        cases hdummy
      · exact hb.trans hplain
    · rw [hd] at hdummy
      cases hdummy

/-- Exact prepared titled source. -/
private theorem X_prepared_titled_source {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper),
      rankWithBudget (Compound.rankingGraph
        (componentCandidate execution.graph comp candidate)) = .ok rr ∧
      coordinateGraphX execution.params (exactDecls exactIds inp) labeled =
        run.coordinateProper ∧
      NodeKeys (componentCandidate execution.graph comp candidate) labeled ∧
      OrderImpl.BorderConstructionReady (titleReservations
        (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)) ∧
      (∀ (index : Nat) (node : Node),
        (componentCandidate execution.graph comp candidate).nodes[index]? = some node →
          labeled.nodes[index]? = some ⟨node, false, none, false⟩) ∧
      (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
        labeled.rank[index]? = some rank) := by
  obtain ⟨rr, normalized, labeled, hrr, hn, hl, hc, _⟩ := X_ranked_source hrun
  have hk := addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (X_cgShape execution) candidate
  have hready := X_titled_border_ready (P := execution.params)
    (exact := exactDecls exactIds inp) hk hshape
    (fun _ _ hnode => X_marker_shape execution hnode) haligned
  refine ⟨rr, labeled, hrr, hc, hk, hready, ?_, ?_⟩
  · intro index node hnode
    exact addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  · intro index rank hrank
    rw [(Labels.addLabelNodes_metadata hl).2.1]
    exact normalize_rank_record hn hrank
/-- Exact candidate group paths match declarations. -/
private theorem X_group_path_iff_decl {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate firstIndex secondIndex : Nat} {first second : Node}
    (hfirst : (componentCandidate execution.graph comp candidate).nodes[firstIndex]? =
      some first)
    (hsecond : (componentCandidate execution.graph comp candidate).nodes[secondIndex]? =
      some second)
    (hfirstBorder : first.border = -2) (hsecondBorder : second.border = -2) :
    first.clusterPath = second.clusterPath ↔ first.decl = second.decl := by
  obtain ⟨_, _, hfirstSource⟩ := componentCandidate_nonplain_source hfirst (by omega)
  obtain ⟨_, _, hsecondSource⟩ := componentCandidate_nonplain_source hsecond (by omega)
  obtain ⟨first0, hfirst0, hfirstDecl, hfirstBorder0, hfirstPath⟩ :=
    X_revKey execution hfirstSource
  obtain ⟨second0, hsecond0, hsecondDecl, hsecondBorder0, hsecondPath⟩ :=
    X_revKey execution hsecondSource
  have hfirstGroup : first0.border = -2 := hfirstBorder0.trans hfirstBorder
  have hsecondGroup : second0.border = -2 := hsecondBorder0.trans hsecondBorder
  obtain ⟨_, firstBox, hfirstBox, _, hfirstOrigin⟩ :=
    measuredGraph_group_origin execution.graph0_eq hfirst0 hfirstGroup
  obtain ⟨_, secondBox, hsecondBox, _, hsecondOrigin⟩ :=
    measuredGraph_group_origin execution.graph0_eq hsecond0 hsecondGroup
  constructor
  · intro hp
    have hlast := congrArg List.getLast? hp
    have hdecl : first0.decl = second0.decl := by
      simpa [← hfirstPath, ← hsecondPath, hfirstOrigin, hsecondOrigin] using hlast
    rw [← hfirstDecl, ← hsecondDecl]
    exact hdecl
  · intro hd
    have hdecl : first0.decl = second0.decl := by
      rw [hfirstDecl, hsecondDecl]
      exact hd
    rw [hdecl] at hfirstBox hfirstOrigin
    have hbox : firstBox = secondBox := Option.some.inj (hfirstBox.symm.trans hsecondBox)
    rw [← hfirstPath, ← hsecondPath, hfirstOrigin, hsecondOrigin, hbox]


/-- Exact titled group owners are unique. -/
private theorem X_titled_group_owner_unique {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat}
    {source : Proper}
    (hkeys : NodeKeys (componentCandidate execution.graph comp candidate) source)
    (hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate execution.graph comp candidate).nodes[index]? = some node →
        source.nodes[index]? = some ⟨node, false, none, false⟩)
    {a b : Nat} {first second : ProperNode}
    (hfirst : (titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) source)).nodes[a]? = some first)
    (hsecond : (titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) source)).nodes[b]? = some second)
    (hfirstBorder : first.node.border = -2) (hsecondBorder : second.node.border = -2)
    (howner : first.node.clusterPath.getLast? = second.node.clusterPath.getLast?) :
    a = b := by
  obtain ⟨oa, hoa, hba, hea⟩ :=
    X_titled_marker_source_record hkeys hrecords hfirst (Or.inl hfirstBorder)
  obtain ⟨ob, hob, hbb, heb⟩ :=
    X_titled_marker_source_record hkeys hrecords hsecond (Or.inl hsecondBorder)
  have hgroupA : oa.border = -2 := hba.symm.trans hfirstBorder
  have hgroupB : ob.border = -2 := hbb.symm.trans hsecondBorder
  obtain ⟨_, _, hoaSource⟩ := componentCandidate_nonplain_source hoa (by omega)
  obtain ⟨_, _, hobSource⟩ := componentCandidate_nonplain_source hob (by omega)
  obtain ⟨oa0, ha0, hdA0, hbA0, hpA0⟩ := X_revKey execution hoaSource
  obtain ⟨ob0, hb0, hdB0, hbB0, hpB0⟩ := X_revKey execution hobSource
  have hgroupA0 : oa0.border = -2 := hbA0.trans hgroupA
  have hgroupB0 : ob0.border = -2 := hbB0.trans hgroupB
  obtain ⟨_, boxA, _, _, hpathA⟩ :=
    measuredGraph_group_origin execution.graph0_eq ha0 hgroupA0
  obtain ⟨_, boxB, _, _, hpathB⟩ :=
    measuredGraph_group_origin execution.graph0_eq hb0 hgroupB0
  have hlastA : first.node.clusterPath.getLast? = some oa.decl := by
    rw [hea, (titleF_keys _).2.2.1, ← hpA0, hpathA]
    simp [hdA0]
  have hlastB : second.node.clusterPath.getLast? = some ob.decl := by
    rw [heb, (titleF_keys _).2.2.1, ← hpB0, hpathB]
    simp [hdB0]
  have hdecl : oa.decl = ob.decl := by
    rw [hlastA, hlastB] at howner
    exact Option.some.inj howner
  have hpath := (X_group_path_iff_decl execution hoa hob
    hgroupA hgroupB).mpr hdecl
  exact (componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (X_cgShape execution) candidate).1 a b oa ob hoa hob hgroupA hgroupB hpath

/-- Exact group-bottom paths match declarations. -/
private theorem X_group_bottom_path_iff_decl {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {index : Nat} {top bottom : Node} (htop : execution.graph.nodes[index]? = some top)
    (hgroup : top.border = -2) (hbottom : bottom ∈ execution.graph.nodes)
    (hbottomBorder : bottom.border = 2) :
    bottom.clusterPath = top.clusterPath ↔ bottom.decl = top.decl := by
  obtain ⟨top0, htop0, hdTop, hbTop, hpTop⟩ := X_revKey execution htop
  obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hbottom
  obtain ⟨bottom0, hbottom0, hdBottom, hbBottom, hpBottom⟩ := X_revKey execution hbi
  have hgroup0 : top0.border = -2 := hbTop.trans hgroup
  have hborder0 : bottom0.border = 2 := hbBottom.trans hbottomBorder
  have hkey := measuredGraph_group_bottom_path_iff_decl execution.graph0_eq htop0
    hgroup0 (List.mem_of_getElem? hbottom0) hborder0
  rw [← hpBottom, ← hpTop, ← hdBottom, ← hdTop]
  exact hkey

/-- Exact candidate bottom lookup by path agrees with lookup by declaration. -/
private theorem X_bottom_lookup_keys {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate index : Nat} {top : Node}
    (htop : (componentCandidate execution.graph comp candidate).nodes[index]? = some top)
    (hgroup : top.border = -2) :
    ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.clusterPath == top.clusterPath) =
    ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.decl == top.decl) := by
  obtain ⟨_, _, htopSource⟩ := componentCandidate_nonplain_source htop (by omega)
  apply RankImpl.find?_congr'
  intro entry hentry
  by_cases hb : entry.1.border = 2
  · have hentryLookup := List.mem_zipIdx_iff_getElem?.mp hentry
    obtain ⟨_, _, hbottomSource⟩ :=
      componentCandidate_nonplain_source hentryLookup (by omega)
    have hkey := X_group_bottom_path_iff_decl execution htopSource hgroup
      (List.mem_of_getElem? hbottomSource) hb
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun h => ⟨h.1, hkey.mp h.2⟩, fun h => ⟨h.1, hkey.mpr h.2⟩⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun h => (hb h.1).elim, fun h => (hb h.1).elim⟩

/-- Exact bordered-graph node classification. -/
private theorem X_coordinateGraph0_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.clusterPath = m.node.clusterPath ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = q.1.node.clusterPath) := by
  rw [clearProxyExtents_nodes] at h
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  rw [hx] at h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hl, rfl⟩ := h
  have hlen := X_sized_length P exact p
  obtain ⟨c1, c2, c3, c4⟩ := clearF_keys m
  by_cases hv1 : v < (titleReservations (sizeProperPortsX P exact p)).nodes.length
  · rw [List.getElem?_append_left hv1] at hl
    rw [titleReservations_nodes] at hl hv1
    by_cases hv2 : v < (sizeProperPortsX P exact p).nodes.length
    · rw [List.getElem?_append_left (by simpa using hv2)] at hl
      left
      cases hs : (sizeProperPortsX P exact p).nodes[v]? with
      | none => simp [List.getElem?_map, hs] at hl
      | some s =>
        simp only [List.getElem?_map, hs, Option.map_some, Option.some.injEq] at hl
        subst hl
        have hk := sizeProperPortsX_key P exact p v
        rw [hs] at hk
        cases hp : p.nodes[v]? with
        | none => simp [hp] at hk
        | some mp =>
          simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨hd, hb, hpth⟩ := hk
          obtain ⟨t1, t2, t3, t4⟩ := titleF_keys s
          refine ⟨mp, rfl, ?_, ?_, ?_, ?_⟩
          · rw [c1, t1, hd]
          · rw [c2, t2, hb]
          · rw [c3, t3, hpth]
          · intro hbd
            rw [c4]
            exact t4 (by rw [← t2, ← c2]; exact hbd)
    · right; right
      rw [List.getElem?_append_right (by simpa [hlen] using hv2)] at hl
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hl
      obtain ⟨q, hq, rfl⟩ := hl
      refine ⟨v - (sizeProperPortsX P exact p).nodes.length, q, ?_, by omega, ?_, ?_, ?_⟩
      · simpa [hlen] using hq
      · rw [c1]; rfl
      · rw [c2]; rfl
      · rw [c3]; rfl
  · rw [List.getElem?_append_right (by omega)] at hl
    right; left
    obtain ⟨e1, e2⟩ := hall m (List.mem_of_getElem? hl)
    refine ⟨(clearF_keys m).1.trans e1, ?_⟩
    rw [(clearF_keys m).2.1]
    exact e2

/-- Exact coordinate-graph node classification. -/
private theorem X_coordinateGraph_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphX P exact p).nodes[v]? = some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      (m.dummy = false → nd.node.clusterPath = m.node.clusterPath) ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      (q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath)) := by
  unfold coordinateGraphX at h
  obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup _ h
  rcases X_coordinateGraph0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
    ⟨i, q, hq, hv, h1, h2, h3⟩
  · refine Or.inl ⟨m, hm, hd.trans h1, hb.trans h2, fun hf => ?_, fun hbd => ?_⟩
    · have : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd this]
      exact h3
    · rw [hh]
      exact h4 (by rw [← hb]; exact hbd)
  · exact Or.inr (Or.inl ⟨by rw [hd]; exact h1, by rw [hb]; exact h2⟩)
  · refine Or.inr (Or.inr ⟨i, q, hq, hv, hd.trans h1, hb.trans h2, fun hf => ?_⟩)
    have : m1.dummy = false := by rw [h1]; exact hf
    rw [hnd this]
    exact h3

/-- Exact coordinate titles are unique per cluster path. -/
private theorem X_pc_title_unique {cg : Graph} {P : Params} {exact : List Nat}
    {labeled : Proper} (hK : NodeKeys cg labeled)
    (hS : CgShape cg) {a b : Nat} {na nb : ProperNode}
    (ha : (coordinateGraphX P exact labeled).nodes[a]? = some na)
    (hb : (coordinateGraphX P exact labeled).nodes[b]? = some nb)
    (h1 : na.node.border = 3) (h2 : nb.node.border = 3)
    (hp : na.node.clusterPath = nb.node.clusterPath) : a = b := by
  have key : ∀ {v : Nat} {nd : ProperNode},
      (coordinateGraphX P exact labeled).nodes[v]? = some nd →
      nd.node.border = 3 →
      ∃ (i : Nat) (q : ProperNode × Nat),
        (titleNodes (sizeProperPortsX P exact labeled))[i]? = some q ∧
        v = labeled.nodes.length + i ∧ nd.node.clusterPath = q.1.node.clusterPath := by
    intro v nd h hb3
    rcases X_coordinateGraph_lookup P exact labeled h with ⟨m, hm, _, h1, _, _⟩ | ⟨_, h1⟩ |
      ⟨i, q, hq, hv, hqd, _, h4⟩
    · rcases hK v m hm with ⟨n, hn, _, hb, _⟩ | ⟨_, hb, _⟩
      · exact absurd (by rw [← hb, ← h1]; exact hb3) (hS.2 n (List.mem_of_getElem? hn))
      · rw [hb] at h1; omega
    · omega
    · obtain ⟨hs, hbq⟩ := titleNodes_spec hq
      have hk := sizeProperPortsX_key P exact labeled q.2
      rw [hs] at hk
      cases hp : labeled.nodes[q.2]? with
      | none => simp [hp] at hk
      | some mp =>
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hk1, hk2, _⟩ := hk
        rcases hK q.2 mp hp with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
        · exact ⟨i, q, hq, hv, h4 (by rw [hk1]; exact hmd)⟩
        · rw [hk2] at hbq
          rw [hb'] at hbq
          exact absurd hbq (by decide)
  obtain ⟨i, qi, hqi, hvi, hpi⟩ := key ha h1
  obtain ⟨j, qj, hqj, hvj, hpj⟩ := key hb h2
  obtain ⟨hsi, hbi⟩ := titleNodes_spec hqi
  obtain ⟨hsj, hbj⟩ := titleNodes_spec hqj
  have kI := sizeProperPortsX_key P exact labeled qi.2
  have kJ := sizeProperPortsX_key P exact labeled qj.2
  rw [hsi] at kI
  rw [hsj] at kJ
  cases hli : labeled.nodes[qi.2]? with
  | none => simp [hli] at kI
  | some mi =>
    cases hlj : labeled.nodes[qj.2]? with
    | none => simp [hlj] at kJ
    | some mj =>
      simp only [hli, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kI
      simp only [hlj, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kJ
      have hidx : qi.2 = qj.2 :=
        labeled_topUnique hK hS hli hlj (by rw [← kI.2.1]; exact hbi)
          (by rw [← kJ.2.1]; exact hbj)
          (by rw [← kI.2.2, ← kJ.2.2, ← hpi, ← hpj]; exact hp)
      have hij : i = j :=
        nodup_map_inj_aux (·.2) (titleNodes_snd_nodup _) hqi hqj hidx
      rw [hvi, hvj, hij]

/-- Exact coordinate side-rank pairs. -/
private theorem X_coordinate_rank_pair (P : Params) (exact : List Nat)
    (source : Proper)
    (haligned : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length)
    {top bottom : ProperNode × Nat}
    (htop : top ∈ (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx)
    (hborder : top.1.node.border = -2)
    (hbottom : ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom)
    {rank : Nat}
    (hlo : (rk (titleReservations (sizeProperPortsX P exact source)).rank top.2).toNat ≤
      rank)
    (hhi : rank ≤
      (rk (titleReservations (sizeProperPortsX P exact source)).rank bottom.2).toNat) :
    ∃ left right : Nat,
      (coordinateGraphX P exact source).nodes[left]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := -1 }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).nodes[right]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := 1
                loopExtent := top.1.node.loopExtent }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).rank[left]? = some (rank : Int) ∧
      (coordinateGraphX P exact source).rank[right]? = some (rank : Int) := by
  obtain ⟨left, right, hl, hr, hrl, hrr⟩ :=
    addClusterBorders_rank_pair (titleReservations (sizeProperPortsX P exact source))
      P.clusterBorderW haligned htop hborder hbottom hlo hhi
  refine ⟨left, right, X_side_record hl rfl (Or.inl rfl),
    X_side_record hr rfl (Or.inr rfl), ?_, ?_⟩
  · exact hrl
  · exact hrr

/-- Exact runs expose proxy side nodes. -/
private theorem X_proxy_side_source {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    ∃ (owner sideIndex : Nat) (side : ProperNode),
      node.node.clusterPath.getLast? = some owner ∧
      run.coordinateProper.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      side.node.clusterPath.getLast? = some owner ∧
      rk run.coordinateProper.rank sideIndex = rk run.coordinateProper.rank index := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _⟩ := componentRunX_spec h
  obtain ⟨owner, span, howner, hspan⟩ :=
    proxyWidths_proxy_span_source hproxy hnode hborder
  obtain ⟨sideIndex, side, hside, hsideBorder, hsideOwner, hsideRank⟩ :=
    proxySpan_side_source hspan
  exact ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, hsideRank⟩

/-- Exact prepared group bottom markers. -/
private theorem X_prepared_group_bottom {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) {labeled : Proper}
    (hc : coordinateGraphX execution.params (exactDecls exactIds inp) labeled =
      run.coordinateProper)
    (hk : NodeKeys (componentCandidate execution.graph comp candidate) labeled)
    (hready : OrderImpl.BorderConstructionReady (titleReservations
      (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)))
    (hrecords : ∀ (key : Nat) (original : Node),
      (componentCandidate execution.graph comp candidate).nodes[key]? = some original →
        labeled.nodes[key]? = some ⟨original, false, none, false⟩)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ bottom : ProperNode × Nat,
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[index]? =
        some (titleF ⟨node, false, none, false⟩) ∧
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 && entry.1.node.clusterPath == node.clusterPath) =
          some bottom := by
  let requested : ProperNode := titleF ⟨node, false, none, false⟩
  let proxy : ProperNode := clearF requested
  have hrequested : (titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) labeled)).nodes[index]? =
      some requested := X_titled_marker_record (hrecords index node hnode) (Or.inl hgroup)
  have hrequestedBorder : requested.node.border = -2 :=
    (titleF_keys _).2.1.trans hgroup
  have hproxyBorder : proxy.node.border = -2 :=
    (clearF_keys requested).2.1.trans hrequestedBorder
  have hproxy : run.coordinateProper.nodes[index]? = some proxy := by
    rw [← hc]
    exact X_marker_record (hrecords index node hnode) (Or.inl hgroup) rfl
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, _⟩ :=
    X_proxy_side_source hrun hproxy (Or.inl hproxyBorder)
  have hsideCoordinate : (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).nodes[sideIndex]? = some side := by
    rw [hc]
    exact hside
  have hsideOriginal := X_side_original hready hsideCoordinate hsideBorder
  obtain ⟨anchor, hanchor, bottom, hbottom, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? hsideOriginal)
      hsideBorder
  obtain ⟨hanchorMember, hanchorCondition⟩ := List.mem_filter.mp hanchor
  have hanchorLookup := List.mem_zipIdx_iff_getElem?.mp hanchorMember
  have hanchorBorder : anchor.1.node.border = -2 := by simpa using hanchorCondition
  have hownerEq : anchor.1.node.clusterPath.getLast? =
      requested.node.clusterPath.getLast? := by
    rw [← hpath, ← (clearF_keys requested).2.2.1]
    exact hsideOwner.trans howner.symm
  have hindex := X_titled_group_owner_unique execution hcomp hk hrecords
    hanchorLookup hrequested hanchorBorder hrequestedBorder hownerEq
  have hrequestedAtAnchor :
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[anchor.2]? = some requested := by
    rw [hindex]
    exact hrequested
  have hanchorEq : anchor.1 = requested :=
    Option.some.inj (hanchorLookup.symm.trans hrequestedAtAnchor)
  refine ⟨bottom, hrequested, ?_⟩
  rw [hanchorEq] at hbottom
  simpa only [requested, titleF, hgroup, beq_self_eq_true, Bool.true_or,
    ↓reduceIte] using hbottom

/-- Exact group bottom sources. -/
private theorem X_group_bottom_source {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper) (bottom : ProperNode × Nat),
      rankWithBudget (Compound.rankingGraph
        (componentCandidate execution.graph comp candidate)) = .ok rr ∧
      coordinateGraphX execution.params (exactDecls exactIds inp) labeled =
        run.coordinateProper ∧
      NodeKeys (componentCandidate execution.graph comp candidate) labeled ∧
      OrderImpl.BorderConstructionReady (titleReservations
        (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)) ∧
      (∀ (key : Nat) (original : Node),
        (componentCandidate execution.graph comp candidate).nodes[key]? = some original →
          labeled.nodes[key]? = some ⟨original, false, none, false⟩) ∧
      (∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
        labeled.rank[key]? = some rank) ∧
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[index]? =
        some (titleF ⟨node, false, none, false⟩) ∧
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 && entry.1.node.clusterPath == node.clusterPath) =
          some bottom := by
  obtain ⟨rr, labeled, hrr, hc, hk, hready, hrecords, hranks⟩ :=
    X_prepared_titled_source execution hcomp hrun
  obtain ⟨bottom, htitled, hbottom⟩ :=
    X_prepared_group_bottom execution hcomp hrun hc hk hready hrecords hnode hgroup
  exact ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitled, hbottom⟩

/-- Exact titled bottom markers resolve to candidate bottom nodes. -/
private theorem X_bottom_find_source {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate : Nat} {source : Proper}
    (hkeys : NodeKeys (componentCandidate execution.graph comp candidate) source)
    (hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate execution.graph comp candidate).nodes[index]? = some node →
        source.nodes[index]? = some ⟨node, false, none, false⟩)
    {path : List Nat} {bottom : ProperNode × Nat}
    (hfind : ((titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == path) = some bottom) :
    ∃ original : Node,
      (componentCandidate execution.graph comp candidate).nodes[bottom.2]? =
        some original ∧
      original.border = 2 ∧ original.clusterPath = path ∧
      bottom.1 = titleF ⟨original, false, none, false⟩ ∧
      ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.clusterPath == path) =
          some (original, bottom.2) := by
  have hbottomLookup := List.mem_zipIdx_iff_getElem?.mp
    (List.mem_of_find?_eq_some hfind)
  have hpredicate := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hpredicate
  obtain ⟨original, horiginal, hborder, hrecord⟩ :=
    X_titled_marker_source_record hkeys hrecords hbottomLookup (Or.inr hpredicate.1)
  have horiginalBorder : original.border = 2 := hborder.symm.trans hpredicate.1
  have horiginalPath : original.clusterPath = path := by
    simpa [hrecord, titleF, horiginalBorder] using hpredicate.2
  refine ⟨original, horiginal, horiginalBorder, horiginalPath, hrecord, ?_⟩
  obtain ⟨_, position, hposition, hpositionRecord, hbefore⟩ :=
    List.find?_eq_some_iff_getElem.mp hfind
  have hpositionIndex : position = bottom.2 := by
    simpa only [List.getElem_zipIdx, Nat.zero_add] using
      congrArg Prod.snd hpositionRecord
  have hsourceZip : (componentCandidate execution.graph comp candidate).nodes.zipIdx[bottom.2]? =
      some (original, bottom.2) := by
    simp only [List.getElem?_zipIdx, horiginal, Option.map_some, Nat.zero_add]
  obtain ⟨hsourceBound, hsourceRecord⟩ := List.getElem?_eq_some_iff.mp hsourceZip
  apply List.find?_eq_some_iff_getElem.mpr
  refine ⟨by simp [horiginalBorder, horiginalPath], bottom.2, hsourceBound,
    hsourceRecord, ?_⟩
  intro earlier hearlier
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
  apply Bool.eq_false_iff.mpr
  intro hmatch
  have hearlierSource : earlier < (componentCandidate execution.graph comp candidate).nodes.length := by
    have hlen : (componentCandidate execution.graph comp candidate).nodes.length =
        (componentCandidate execution.graph comp candidate).nodes.zipIdx.length := by
      simp only [List.length_zipIdx]
    omega
  let previous := (componentCandidate execution.graph comp candidate).nodes[earlier]'hearlierSource
  have hprevious : (componentCandidate execution.graph comp candidate).nodes[earlier]? =
      some previous := List.getElem?_eq_getElem hearlierSource
  have hpreviousMatch : previous.border = 2 ∧ previous.clusterPath = path := by
    simpa only [List.getElem_zipIdx, Nat.zero_add, Bool.and_eq_true, beq_iff_eq] using hmatch
  have hforward := X_titled_marker_record (P := execution.params)
    (exact := exactDecls exactIds inp)
    (hrecords earlier previous hprevious) (Or.inr hpreviousMatch.1)
  have hprior := hbefore earlier (by omega)
  have htargetZip :
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) source)).nodes.zipIdx[earlier]? =
        some (titleF ⟨previous, false, none, false⟩, earlier) := by
    simp only [List.getElem?_zipIdx, hforward, Option.map_some, Nat.zero_add]
  rw [(List.getElem?_eq_some_iff.mp htargetZip).2] at hprior
  simp [titleF, hpreviousMatch.1, hpreviousMatch.2] at hprior

/-- Exact candidate bottom constraints resolve by declaration. -/
private theorem X_bottom_constraint_source {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate index : Nat} {source : Proper} {node : Node}
    (hkeys : NodeKeys (componentCandidate execution.graph comp candidate) source)
    (hrecords : ∀ (key : Nat) (original : Node),
      (componentCandidate execution.graph comp candidate).nodes[key]? = some original →
        source.nodes[key]? = some ⟨original, false, none, false⟩)
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) {bottom : ProperNode × Nat}
    (hfind : ((titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == node.clusterPath) = some bottom) :
    ∃ original : Node,
      (componentCandidate execution.graph comp candidate).nodes[bottom.2]? = some original ∧
      original.border = 2 ∧ original.clusterPath = node.clusterPath ∧
      bottom.1 = titleF ⟨original, false, none, false⟩ ∧
      ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == node.decl) = some (original, bottom.2) := by
  obtain ⟨original, horiginal, hborder, hpath, hrecord, hsourceFind⟩ :=
    X_bottom_find_source execution hkeys hrecords hfind
  refine ⟨original, horiginal, hborder, hpath, hrecord, ?_⟩
  rw [← X_bottom_lookup_keys execution hnode hgroup]
  exact hsourceFind

/-- Exact titled nodes preserve the executed rank. -/
private theorem X_titled_original_rk {P : Params} {exact : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {source : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
      source.rank[key]? = some rank)
    {index : Nat} (hindex : index < cg.nodes.length) :
    rk (titleReservations (sizeProperPortsX P exact source)).rank index =
      rk rr.ranks index ∧
      0 ≤ rk (titleReservations (sizeProperPortsX P exact source)).rank index := by
  obtain ⟨_, _, hinvariant, _⟩ := RankImpl.rank_spec
    (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlength : rr.ranks.length = cg.nodes.length := hinvariant.1
  have hirank : index < rr.ranks.length := by omega
  have hrrLookup : rr.ranks[index]? = some rr.ranks[index] :=
    List.getElem?_eq_getElem hirank
  have htitledLookup := X_titled_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  have heq : rk (titleReservations (sizeProperPortsX P exact source)).rank index =
      rk rr.ranks index := by
    simp only [rk, List.getD_eq_getElem?_getD, htitledLookup, hrrLookup, Option.getD_some]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact rankWithBudget_rk_nonneg hrr index

/-- Exact coordinate nodes preserve the executed rank. -/
private theorem X_coordinate_original_rk {P : Params} {exact : List Nat} {cg : Graph}
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
  have hcoordinateLookup := X_coordinate_rank_record (P := P) (exact := exact)
    (hranks index rr.ranks[index] hrrLookup)
  simp only [rk, List.getD_eq_getElem?_getD, hcoordinateLookup, hrrLookup, Option.getD_some]

/-- Exact group side borders for a member rank. -/
private theorem X_group_member_borders {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0) (hinside : member.clusterPath.contains node.decl = true) :
    ∃ left right : Nat,
      run.coordinateProper.nodes[left]? =
        some (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
          execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? =
        some (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, index)
          execution.params.clusterBorderW) ∧
      rk run.coordinateProper.rank left = rk run.coordinateProper.rank memberIndex ∧
      rk run.coordinateProper.rank right = rk run.coordinateProper.rank memberIndex := by
  obtain ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitled, hbottom⟩ :=
    X_group_bottom_source execution hcomp hrun hnode hgroup
  obtain ⟨originalBottom, horiginalBottom, _, _, _, hconstraintBottom⟩ :=
    X_bottom_constraint_source execution hk hrecords hnode hgroup hbottom
  have hinterval := ranked_compound_member_interval hrr
    (List.mk_mem_zipIdx_iff_getElem?.mpr hnode) hgroup hconstraintBottom
    (List.mk_mem_zipIdx_iff_getElem?.mpr hmember) hplain hinside
  have htopRank := X_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hnode).1
  have hmemberRank := X_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hmember).1
  have hbottomRank := X_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp horiginalBottom).1
  have hnonnegative := rankWithBudget_rk_nonneg hrr memberIndex
  have htopBorder : (titleF ⟨node, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hgroup
  have hbottomForTop :
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == (titleF ⟨node, false, none, false⟩).node.clusterPath) =
        some bottom := by
    simpa [titleF, hgroup] using hbottom
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    X_coordinate_rank_pair execution.params (exactDecls exactIds inp) labeled
      hready.2.2.2.1
      (List.mk_mem_zipIdx_iff_getElem?.mpr htitled) htopBorder hbottomForTop
      (rank := (rk rr.ranks memberIndex).toNat)
      (by
        dsimp only at hinterval htopRank hmemberRank hbottomRank ⊢
        omega)
      (by
        dsimp only at hinterval htopRank hmemberRank hbottomRank ⊢
        omega)
  have hmemberCoordinate := X_coordinate_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hmember).1
  have hnatcast : ((rk rr.ranks memberIndex).toNat : Int) = rk rr.ranks memberIndex := by
    omega
  have hleftValue : rk (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).rank left = rk rr.ranks memberIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hleftRank, Option.getD_some] using hnatcast
  have hrightValue : rk (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).rank right = rk rr.ranks memberIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hrightRank, Option.getD_some] using hnatcast
  rw [← hc]
  exact ⟨left, right, hleft, hright, hleftValue.trans hmemberCoordinate.symm,
    hrightValue.trans hmemberCoordinate.symm⟩

/-- Exact requested group ranges cover the member rank. -/
private theorem X_requested_group_range {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) {labeled : Proper}
    (hc : coordinateGraphX execution.params (exactDecls exactIds inp) labeled =
      run.coordinateProper)
    (hk : NodeKeys (componentCandidate execution.graph comp candidate) labeled)
    (hready : OrderImpl.BorderConstructionReady (titleReservations
      (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)))
    (hrecords : ∀ (key : Nat) (original : Node),
      (componentCandidate execution.graph comp candidate).nodes[key]? = some original →
        labeled.nodes[key]? = some ⟨original, false, none, false⟩)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) {bottom : ProperNode × Nat}
    (hbottom : ((titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
      entry.1.node.border == 2 && entry.1.node.clusterPath == node.clusterPath) =
        some bottom) :
    (rk (titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) labeled)).rank index).toNat ≤
      (rk (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).rank bottom.2).toNat := by
  let requested : ProperNode := titleF ⟨node, false, none, false⟩
  let proxy : ProperNode := clearF requested
  have htitled : (titleReservations (sizeProperPortsX execution.params
      (exactDecls exactIds inp) labeled)).nodes[index]? =
      some requested := X_titled_marker_record (hrecords index node hnode) (Or.inl hgroup)
  have htitledBorder : requested.node.border = -2 := (titleF_keys _).2.1.trans hgroup
  have hproxyBorder : proxy.node.border = -2 :=
    (clearF_keys requested).2.1.trans htitledBorder
  have hproxy : run.coordinateProper.nodes[index]? = some proxy := by
    rw [← hc]
    exact X_marker_record (hrecords index node hnode) (Or.inl hgroup) rfl
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, _⟩ :=
    X_proxy_side_source hrun hproxy (Or.inl hproxyBorder)
  have hcoordinate : (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).nodes[sideIndex]? = some side := by
    rw [hc]
    exact hside
  have hsource := X_side_original hready hcoordinate hsideBorder
  obtain ⟨anchor, hanchor, generatedBottom, hfind, hpath, hrange⟩ :=
    addClusterBorders_side_range_source _ _ hready (List.mem_of_getElem? hsource)
      hsideBorder
  obtain ⟨hanchorMember, hanchorCondition⟩ := List.mem_filter.mp hanchor
  have hanchorLookup := List.mem_zipIdx_iff_getElem?.mp hanchorMember
  have hanchorBorder : anchor.1.node.border = -2 := by simpa using hanchorCondition
  have hownerEq : anchor.1.node.clusterPath.getLast? =
      requested.node.clusterPath.getLast? := by
    rw [← hpath, ← (clearF_keys requested).2.2.1]
    exact hsideOwner.trans howner.symm
  have hindex := X_titled_group_owner_unique execution hcomp hk hrecords
    hanchorLookup htitled hanchorBorder htitledBorder hownerEq
  have hrequestedAtAnchor :
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[anchor.2]? = some requested := by
    rw [hindex]
    exact htitled
  have hanchorEq : anchor.1 = requested :=
    Option.some.inj (hanchorLookup.symm.trans hrequestedAtAnchor)
  rw [hanchorEq] at hfind
  have hfindForNode :
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == node.clusterPath) =
          some generatedBottom := by
    simpa only [requested, titleF, hgroup, beq_self_eq_true, Bool.true_or,
      ↓reduceIte] using hfind
  have hbottomEq : generatedBottom = bottom :=
    Option.some.inj (hfindForNode.symm.trans hbottom)
  rw [hindex, hbottomEq] at hrange
  exact hrange
/-- Exact original plain nodes transfer to the proper run. -/
private theorem X_original_plain_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      run.proper.nodes[index]? = some actual ∧
      actual.dummy = false ∧ actual.node.border = 0 ∧
      actual.node.clusterPath = node.clusterPath ∧ actual.edge = none ∧
      node.w ≤ actual.node.w ∧ actual.node.h = node.h ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, normalized, labeled, _, hn, hl, hc, _⟩ := X_ranked_source hrun
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨actual, hactual, hedge, hborder, hwidth, hheight⟩ :=
    X_plain_anchor_dims P hsource hplain
  have hmetadata : actual.dummy = false ∧ actual.node.clusterPath = node.clusterPath := by
    rcases X_coordinateGraph_lookup P exact labeled hactual with
      ⟨original, horiginal, hd, _, hp, _⟩ | ⟨_, hside⟩ |
        ⟨_, _, _, _, _, hb3, _⟩
    · have heq : original = ⟨node, false, none, false⟩ :=
        Option.some.inj (horiginal.symm.trans hsource)
      subst original
      exact ⟨hd, hp rfl⟩
    · rcases hside with hside | hside <;> omega
    · omega
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hc]
    exact hactual
  have hproper := X_plain_node_dims hrun hcoordinate hborder
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _, _, _, _⟩ := componentRunX_spec hrun
  have hx := ((proxyWidths_rel hproxy).2.2.2.2.2 index actual hcoordinate
    (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hmetadata.1, hborder, hmetadata.2,
    hedge, hwidth, hheight, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- Exact coordinate side-rank bounds. -/
private theorem X_coordinate_side_rank_bounds (P : Params) (exact : List Nat)
    {source : Proper}
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact source)))
    {index : Nat} {node : ProperNode}
    (hnode : (coordinateGraphX P exact source).nodes[index]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    ∃ top ∈ (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.filter
        (fun entry => entry.1.node.border == -2),
      ∃ bottom : ProperNode × Nat,
        ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
          fun entry =>
          entry.1.node.border == 2 &&
            entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
        node.node.clusterPath = top.1.node.clusterPath ∧
        0 ≤ rk (coordinateGraphX P exact source).rank index ∧
        (rk (titleReservations (sizeProperPortsX P exact source)).rank top.2).toNat ≤
          (rk (coordinateGraphX P exact source).rank index).toNat ∧
        (rk (coordinateGraphX P exact source).rank index).toNat ≤
          (rk (titleReservations (sizeProperPortsX P exact source)).rank bottom.2).toNat := by
  have horiginal := X_side_original hready hnode hside
  exact addClusterBorders_side_rank_bounds _ _ hready horiginal hside

/-- Exact runs are border-well-formed. -/
private theorem X_bordersWellFormed {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    OrderImpl.BordersWellFormed run.coordinateProper := by
  obtain ⟨_, labeled, _, hc, _, hready, _, _⟩ :=
    X_prepared_titled_source execution hcomp hrun
  rw [← hc]
  unfold coordinateGraphX
  apply materializeDummyPaths_bordersWellFormed
  apply clearProxyExtents_bordersWellFormed
  exact OrderImpl.addClusterBorders_bordersWellFormed _ _ hready


/-- Exact runs separate cluster layers. -/
private theorem X_cluster_separated {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∀ layer ∈ run.layers, ∀ i a b,
      layer[i]? = some a → layer[i + 1]? = some b →
      clusterSep P.nodeGap P.clusterPad run.coordinateProper a b ≤
        run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec h
  exact cluster_balance_separated hcross

/-- Exact runs separate cluster gaps. -/
private theorem X_cluster_gap_separated {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∀ layer ∈ run.layers, ∀ i a b,
      layer[i]? = some a → layer[i + 1]? = some b →
      clusterGap P.nodeGap P.clusterPad run.coordinateProper a b ≤
        run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec h
  obtain ⟨_, _, _, hs, _⟩ := crossCoordsClusterWith_spec hcross
  intro layer hl i a b ha hb
  have hsep := X_cluster_separated h layer hl i a b ha hb
  have hwa := nodeW_nonneg hs a
  have hwb := nodeW_nonneg hs b
  unfold clusterSep coordSep at hsep
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide),
    Int.fdiv_eq_ediv_of_nonneg _ (by decide)] at hsep
  omega

/-- Exact border-member gaps respect the cluster pad. -/
private theorem X_border_member_gap {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {layer : List Nat} (hl : layer ∈ run.layers) {i a b : Nat}
    (ha : layer[i]? = some a) (hb : layer[i + 1]? = some b)
    (hm : borderMember run.coordinateProper a b = true) :
    P.clusterPad ≤ run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  have hgap := X_cluster_gap_separated h layer hl i a b ha hb
  simpa only [clusterGap, hm, ite_true] using hgap

/-- Exact double border-member gaps. -/
private theorem X_two_border_member_gaps {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {layer : List Nat} (hl : layer ∈ run.layers) {i a member b : Nat}
    (ha : layer[i]? = some a)
    (hm : layer[i + 1]? = some member)
    (hb : layer[(i + 1) + 1]? = some b)
    (ham : borderMember run.coordinateProper a member = true)
    (hmb : borderMember run.coordinateProper member b = true) :
    2 * P.clusterPad ≤
      run.coordinateXs.getD b 0 - run.coordinateXs.getD a 0 := by
  have hleft := X_border_member_gap h hl ha hm ham
  have hright := X_border_member_gap h hl hm hb hmb
  omega

/-- Exact layer steps never go backward. -/
private theorem X_layer_step_nonnegative {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {layer : List Nat} (hl : layer ∈ run.layers) {i a b : Nat}
    (ha : layer[i]? = some a) (hb : layer[i + 1]? = some b) :
    run.coordinateXs.getD a 0 ≤ run.coordinateXs.getD b 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec h
  obtain ⟨hng, hcp, _⟩ := crossCoordsClusterWith_spec hcross
  have hgap := X_cluster_gap_separated h layer hl i a b ha hb
  have hnonneg :
      0 ≤ clusterGap P.nodeGap P.clusterPad run.coordinateProper a b := by
    unfold clusterGap
    split
    · omega
    · split <;> omega
  omega

/-- Exact layers are ordered left to right. -/
private theorem X_layer_ordered {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {layer : List Nat} (hl : layer ∈ run.layers) {i j a b : Nat}
    (hij : i ≤ j) (ha : layer[i]? = some a) (hb : layer[j]? = some b) :
    run.coordinateXs.getD a 0 ≤ run.coordinateXs.getD b 0 := by
  obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction distance generalizing b with
  | zero =>
      simp only [Nat.add_zero] at hb
      have hab : a = b := Option.some.inj (ha.symm.trans hb)
      subst b
      exact Int.le_refl _
  | succ distance ih =>
      have hlast : i + distance + 1 < layer.length :=
        (List.getElem?_eq_some_iff.mp hb).1
      have hindex : i + distance < layer.length := by omega
      have hmiddle : layer[i + distance]? = some (layer[i + distance]'hindex) :=
        List.getElem?_eq_getElem hindex
      have hprefix := ih (by omega) hmiddle
      have hstep := X_layer_step_nonnegative h hl hmiddle
        (show layer[(i + distance) + 1]? = some b from hb)
      exact Int.le_trans hprefix hstep

/-- Exact distant border-member gaps. -/
private theorem X_two_border_member_gaps_with_intervening
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {layer : List Nat} (hl : layer ∈ run.layers)
    {i j left first last right : Nat}
    (hij : i + 1 ≤ j)
    (hleft : layer[i]? = some left)
    (hfirst : layer[i + 1]? = some first)
    (hlast : layer[j]? = some last)
    (hright : layer[j + 1]? = some right)
    (hleftMember : borderMember run.coordinateProper left first = true)
    (hrightMember : borderMember run.coordinateProper last right = true) :
    2 * P.clusterPad ≤
      run.coordinateXs.getD right 0 - run.coordinateXs.getD left 0 := by
  have hleftGap := X_border_member_gap h hl hleft hfirst hleftMember
  have hrightGap := X_border_member_gap h hl hlast hright hrightMember
  have hmiddle := X_layer_ordered h hl hij hfirst hlast
  omega

/-- Exact border hulls cover the layer gap. -/
private theorem X_border_hull_width {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {group : Nat} (hgroup : (cg.nodes.getD group default).border = -2)
    {layer : List Nat} (hl : layer ∈ run.layers)
    {i j left first last right : Nat} {leftNode rightNode : ProperNode}
    (hij : i + 1 ≤ j)
    (hleft : layer[i]? = some left)
    (hfirst : layer[i + 1]? = some first)
    (hlast : layer[j]? = some last)
    (hright : layer[j + 1]? = some right)
    (hleftMember : borderMember run.coordinateProper left first = true)
    (hrightMember : borderMember run.coordinateProper last right = true)
    (hleftNode : run.coordinateProper.nodes[left]? = some leftNode)
    (hrightNode : run.coordinateProper.nodes[right]? = some rightNode)
    (hleftBorder : leftNode.node.border = -1)
    (hrightBorder : rightNode.node.border = 1)
    (hleftOwner : leftNode.node.clusterPath.getLast? =
      some (cg.nodes.getD group default).decl)
    (hrightOwner : rightNode.node.clusterPath.getLast? =
      some (cg.nodes.getD group default).decl) :
    2 * P.clusterPad ≤ (frameRect P cg run group).w := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec h
  obtain ⟨_, _, _, hs, _⟩ := crossCoordsClusterWith_spec hcross
  have hleftWidth : 0 ≤ leftNode.node.w :=
    (sizesNonneg_lookup hs left leftNode hleftNode).1
  have hrightWidth : 0 ≤ rightNode.node.w :=
    (sizesNonneg_lookup hs right rightNode hrightNode).1
  obtain ⟨hleftFinal, hleftX⟩ :=
    X_border_record h hleftNode (Or.inl hleftBorder)
  obtain ⟨hrightFinal, hrightX⟩ :=
    X_border_record h hrightNode (Or.inr hrightBorder)
  let borders := run.proper.nodes.zipIdx.filterMap fun q =>
    if (q.1.node.border == -1 || q.1.node.border == 1) &&
        q.1.node.clusterPath.getLast? == some (cg.nodes.getD group default).decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none
  have hleftMem : Labels.rectAt run.proper run.xs run.ys left ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(leftNode, left), List.mk_mem_zipIdx_iff_getElem?.mpr hleftFinal, ?_⟩
    simp [hleftBorder, hleftOwner]
  have hrightMem : Labels.rectAt run.proper run.xs run.ys right ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(rightNode, right), List.mk_mem_zipIdx_iff_getElem?.mpr hrightFinal, ?_⟩
    simp [hrightBorder, hrightOwner]
  have hlo := boundsOf_minX_le_rect_x borders []
    (Labels.rectAt run.proper run.xs run.ys left) hleftMem
  have hhi := rect_right_le_boundsOf_right borders []
    (Labels.rectAt run.proper run.xs run.ys right) hrightMem
  have hgap := X_two_border_member_gaps_with_intervening h hl hij
    hleft hfirst hlast hright hleftMember hrightMember
  simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
    hleftFinal, hrightFinal, hleftX, hrightX] at hlo hhi
  have hleftHalf : 0 ≤ Int.fdiv leftNode.node.w 2 :=
    Int.fdiv_nonneg hleftWidth (by decide)
  have hrightHalf : Int.fdiv rightNode.node.w 2 ≤ rightNode.node.w := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    omega
  change (cg.nodes[group]?.getD default).border = -2 at hgroup
  have hwidth : (frameRect P cg run group).w =
      (boundsOf borders []).right - (boundsOf borders []).minX := by
    simp [frameRect, hgroup, borders]
  rw [hwidth]
  omega

/-- Exact member paths extend the group path. -/
private theorem X_member_path_prefix {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? =
      some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0)
    (hinside : member.clusterPath.contains node.decl = true) :
    node.clusterPath <+: member.clusterPath := by
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨group0, hgroup0, hdG, hbG, hpG⟩ := X_revKey execution hgroupSource
  have hnonempty : member.clusterPath ≠ [] := by
    intro hempty
    simp [hempty] at hinside
  obtain ⟨_, _, hmemberSource⟩ :=
    componentCandidate_nonempty_path_source hmember hnonempty
  obtain ⟨member0, hmember0, _hmemberDeclM, hbM, hpM⟩ := X_revKey execution hmemberSource
  obtain ⟨groupBox, hgroupBox, hgroupDecl, hgroupPath⟩ :=
    X_groupPath execution hgroup0 (hbG.trans hgroup)
  obtain ⟨memberBox, hmemberBox, hmemberDecl, hmemberPath⟩ :=
    X_plainPath execution hmember0 (hbM.trans hplain)
  have hin : group0.decl ∈ Compound.path inp.boxes memberBox := by
    have h := hinside
    rw [← hpM, hmemberPath, List.contains_iff_mem] at h
    rwa [← hdG] at h
  have hg : (inputModel inp o).boxes[group0.decl]? = some groupBox := by
    rw [hgroupDecl]
    exact hgroupBox
  have hm : (inputModel inp o).boxes[member0.decl]? = some memberBox := by
    rw [hmemberDecl]
    exact hmemberBox
  have hprefix := Compound.path_ancestor_prefix (inputModel inp o) hwf hg hm hin
  rw [← hpG, hgroupPath, ← hgroupDecl, ← hpM, hmemberPath]
  exact hprefix

/-- Exact member bracket. -/
private theorem X_member_bracket {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? =
      some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0)
    (hinside : member.clusterPath.contains node.decl = true) :
    ∃ (actual : ProperNode) (ord : OrderResult) (left right : Nat),
      orderWithBudget run.coordinateProper orderOptions = .ok ord ∧ ord.layers = run.layers ∧
      run.coordinateProper.nodes[memberIndex]? = some actual ∧
      run.proper.nodes[memberIndex]? = some actual ∧
      actual.dummy = false ∧ actual.node.border = 0 ∧
      actual.node.clusterPath = member.clusterPath ∧
      run.xs.getD memberIndex 0 = run.coordinateXs.getD memberIndex 0 ∧
      run.coordinateProper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      ExecutedBorderOrder.Bracket run.coordinateProper ord left memberIndex right := by
  have hprefix := X_member_path_prefix execution hwf hnode hgroup hmember hplain hinside
  obtain ⟨actual, hcoordinate, hproper, hreal, hactualPlain, hactualPath,
    _, _, _, hx⟩ := X_original_plain_record hrun hmember hplain
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    X_group_member_borders execution hcomp hrun hnode hgroup hmember hplain hinside
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  have hwformed := X_bordersWellFormed execution hcomp hrun
  have hleftLay : OrderImpl.lay run.coordinateProper left =
      OrderImpl.lay run.coordinateProper memberIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hleftRank
  have hrightLay : OrderImpl.lay run.coordinateProper right =
      OrderImpl.lay run.coordinateProper memberIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hrightRank
  have hsidePrefix :
      (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
        execution.params.clusterBorderW).node.clusterPath <+: actual.node.clusterPath := by
    change (titleF ⟨node, false, none, false⟩).node.clusterPath <+: actual.node.clusterPath
    rw [(titleF_keys _).2.2.1, hactualPath]
    exact hprefix
  have hleftNe : left ≠ memberIndex := by
    intro heq
    rw [heq] at hleft
    have hn := Option.some.inj (hleft.symm.trans hcoordinate)
    have hb := congrArg (fun value : ProperNode => value.node.border) hn
    change (-1 : Int) = actual.node.border at hb
    omega
  have hrightNe : right ≠ memberIndex := by
    intro heq
    rw [heq] at hright
    have hn := Option.some.inj (hright.symm.trans hcoordinate)
    have hb := congrArg (fun value : ProperNode => value.node.border) hn
    change (1 : Int) = actual.node.border at hb
    omega
  refine ⟨actual, ord, left, right, horder, hlayers, hcoordinate, hproper, hreal,
    hactualPlain, hactualPath, hx, hleft, hright, ?_⟩
  exact ExecutedBorderOrder.bracket run.coordinateProper orderOptions ord horder hwformed
    left memberIndex right _ actual _ hleft hcoordinate hright hleftLay hrightLay
    rfl rfl rfl hreal rfl hsidePrefix hsidePrefix hleftNe hrightNe

/-- Exact member border intervals cover the member. -/
private theorem X_member_border_interval {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? =
      some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0)
    (hinside : member.clusterPath.contains node.decl = true) :
    ∃ (actual : ProperNode) (left right : Nat),
      run.proper.nodes[memberIndex]? = some actual ∧
      actual.node.clusterPath = member.clusterPath ∧
      run.proper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      run.proper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
      (Labels.rectAt run.proper run.xs run.ys left).x ≤
        (Labels.rectAt run.proper run.xs run.ys memberIndex).x ∧
      (Labels.rectAt run.proper run.xs run.ys memberIndex).x +
          (Labels.rectAt run.proper run.xs run.ys memberIndex).w ≤
        (Labels.rectAt run.proper run.xs run.ys right).x +
          (Labels.rectAt run.proper run.xs run.ys right).w := by
  obtain ⟨actual, ord, left, right, _, hlayers, hcoordinate, hproper, _, hactualPlain,
    hactualPath, hx, hleft, hright, hbracket⟩ :=
    X_member_bracket execution hwf hcomp hrun hnode hgroup hmember hplain hinside
  obtain ⟨li, mi, ri, hli, hmi, hri, hlt, htr⟩ := hbracket.positions
  rw [hlayers] at hli hmi hri
  have hlayer := hbracket.layer_mem
  rw [hlayers] at hlayer
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨labeled, hc, hk, _, _⟩ := X_coordinate_alignment hrun
  have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (X_cgShape execution) candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact X_pc_title_unique hk hshape (by rw [hc]; exact ha) (by rw [hc]; exact hb)
      hba hbb hp
  have hleftSep := cluster_all_pairs_separated hcross hunique _ hlayer
    li mi left memberIndex _ _ hlt hli hmi hleft hcoordinate
    (by change (-1 : Int) ≠ -2; decide) (by change (-1 : Int) ≠ 2; decide)
    (by rw [hactualPlain]; decide) (by rw [hactualPlain]; decide)
  have hrightSep := cluster_all_pairs_separated hcross hunique _ hlayer
    mi ri memberIndex right _ _ htr hmi hri hcoordinate hright
    (by rw [hactualPlain]; decide) (by rw [hactualPlain]; decide)
    (by change (1 : Int) ≠ -2; decide) (by change (1 : Int) ≠ 2; decide)
  obtain ⟨hleftFinal, hleftX⟩ := X_border_record hrun hleft (Or.inl rfl)
  obtain ⟨hrightFinal, hrightX⟩ := X_border_record hrun hright (Or.inr rfl)
  have hactualWidth := (sizesNonneg_lookup hsizes memberIndex actual hcoordinate).1
  have hleftWidth := (sizesNonneg_lookup hsizes left _ hleft).1
  have hrightWidth := (sizesNonneg_lookup hsizes right _ hright).1
  have hactualLoops : 0 ≤ (actual.node.loopExtent : Int) := Int.natCast_nonneg _
  have hgroupLoops : 0 ≤ (node.loopExtent : Int) := Int.natCast_nonneg _
  have hgap : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by omega
  change 0 ≤ execution.params.clusterBorderW at hleftWidth hrightWidth
  refine ⟨actual, left, right, hproper, hactualPath, hleftFinal, hrightFinal, ?_, ?_⟩
  · simp only [coordSep, CoordsImpl.nodeW, hleft, hcoordinate, OrderImpl.borderLeft] at hleftSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hleftFinal, hproper, hleftX, hx, OrderImpl.borderLeft]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hleftSep ⊢
    omega
  · simp only [coordSep, CoordsImpl.nodeW, hcoordinate, hright, OrderImpl.borderRight,
      titleF, hgroup, beq_self_eq_true, Bool.true_or, ↓reduceIte] at hrightSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hproper, hrightFinal, hx, hrightX, OrderImpl.borderRight]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hrightSep ⊢
    omega

/-- Exact member frames lie in the parent group frame. -/
private theorem X_member_contained {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index memberIndex : Nat} {node member : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? =
      some node)
    (hgroup : node.border = -2)
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
      some member)
    (hplain : member.border = 0)
    (hinside : member.clusterPath.contains node.decl = true) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run index).Contained
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run memberIndex) := by
  let cg := componentCandidate execution.graph comp candidate
  obtain ⟨actual, left, right, hproper, hactualPath, hleft, hright, hleftInterval,
    hrightInterval⟩ :=
    X_member_border_interval execution hwf hcomp hrun hnode hgroup hmember hplain hinside
  have hgroupGet : cg.nodes.getD index default = node := by
    simp only [cg, List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨group0, hgroup0, hdG, hbG, hpG⟩ := X_revKey execution hgroupSource
  obtain ⟨box, _, hdeclG, hpath0⟩ := X_groupPath execution hgroup0 (hbG.trans hgroup)
  have hgroupPath : node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
    rw [← hpG, hpath0, ← hdeclG, hdG]
  have hframeGroup : (cg.nodes.getD index default).border = -2 := by
    rw [hgroupGet]
    exact hgroup
  have hleftPath : (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
      execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++ [(cg.nodes.getD index default).decl] := by
    change (titleF ⟨node, false, none, false⟩).node.clusterPath = _
    rw [(titleF_keys _).2.2.1, hgroupGet]
    exact hgroupPath
  have hrightPath : (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, index)
      execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++ [(cg.nodes.getD index default).decl] := by
    change (titleF ⟨node, false, none, false⟩).node.clusterPath = _
    exact hleftPath
  have hleftContained := frameRect_side_marker_contained (P := execution.params) (cg := cg)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hleft) (Or.inl rfl) hleftPath
  have hrightContained := frameRect_side_marker_contained (P := execution.params) (cg := cg)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hright) (Or.inr rfl) hrightPath
  have hscope : actual.node.clusterPath.contains (cg.nodes.getD index default).decl = true := by
    rw [hgroupGet, hactualPath]
    exact hinside
  have hvertical := frameRect_member_vertical (P := execution.params) (cg := cg)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hproper) hscope
  have hcontained : (frameRect execution.params cg run index).Contained
      (Labels.rectAt run.proper run.xs run.ys memberIndex) := by
    unfold Rect.Contained at hleftContained hrightContained ⊢
    exact ⟨Int.le_trans hleftContained.1 hleftInterval,
      Int.le_trans hrightInterval hrightContained.2.1, hvertical.1, hvertical.2⟩
  have hmemberGet : cg.nodes.getD memberIndex default = member := by
    simp only [cg, List.getD_eq_getElem?_getD, hmember, Option.getD_some]
  have hmemberFrame : frameRect execution.params cg run memberIndex =
      Labels.rectAt run.proper run.xs run.ys memberIndex := by
    unfold frameRect
    rw [hmemberGet]
    simp only [hplain, show ((0 : Int) != -2) = true from rfl, ↓reduceIte]
    unfold nodeRect Labels.rectAt Labels.labelRect RouteImpl.xAt RouteImpl.yAt
      RouteImpl.nodeW RouteImpl.nodeH
    simp only [List.getD_eq_getElem?_getD, hproper, Option.getD_some]
  rw [hmemberFrame]
  exact hcontained

/-- Exact direct group paths drop the last element. -/
private theorem X_direct_group_path {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    child.clusterPath.dropLast = parent.clusterPath := by
  obtain ⟨_, _, hparentSource⟩ := componentCandidate_nonplain_source hparent (by omega)
  obtain ⟨parent0, hparent0, hdP, hbP, hpP⟩ := X_revKey execution hparentSource
  obtain ⟨_, _, hchildSource⟩ := componentCandidate_nonplain_source hchild (by omega)
  obtain ⟨child0, hchild0, hdC, hbC, hpC⟩ := X_revKey execution hchildSource
  obtain ⟨parentOriginal, hparentOriginal, hparentDecl, hparentPath⟩ :=
    X_groupPath execution hparent0 (hbP.trans hparentGroup)
  obtain ⟨childOriginal, hchildOriginal, hchildDecl, hchildPath⟩ :=
    X_groupPath execution hchild0 (hbC.trans hchildGroup)
  have hparentEq : parentOriginal = parentBox := by
    rw [← hparentDecl, hdP] at hparentOriginal
    exact Option.some.inj (hparentOriginal.symm.trans hparentBox)
  have hchildEq : childOriginal = childBox := by
    rw [← hchildDecl, hdC] at hchildOriginal
    exact Option.some.inj (hchildOriginal.symm.trans hchildBox)
  have himmediate := Compound.path_of_parent (inputModel inp o) hwf
    hparentBox hchildBox hparentRef hne
  have hparentPathEq : parent.clusterPath = Compound.path inp.boxes parentBox ++ [parent.decl] := by
    rw [← hpP, hparentPath, ← hparentDecl, hdP, hparentEq]
  have hchildPathEq : child.clusterPath = Compound.path inp.boxes childBox ++ [child.decl] := by
    rw [← hpC, hchildPath, ← hchildDecl, hdC, hchildEq]
  calc
    child.clusterPath.dropLast = Compound.path inp.boxes childBox := by
      rw [hchildPathEq, List.dropLast_concat]
    _ = Compound.path inp.boxes parentBox ++ [parent.decl] := himmediate
    _ = parent.clusterPath := hparentPathEq.symm

/-- Exact direct group rank intervals. -/
private theorem X_direct_group_rank_interval {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    ∃ (rr : RankImpl.RankResult) (parentBottom childBottom : Node)
      (parentBottomIndex childBottomIndex : Nat),
      rankWithBudget (Compound.rankingGraph
        (componentCandidate execution.graph comp candidate)) = .ok rr ∧
      (componentCandidate execution.graph comp candidate).nodes[parentBottomIndex]? =
        some parentBottom ∧
      (componentCandidate execution.graph comp candidate).nodes[childBottomIndex]? =
        some childBottom ∧
      ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == parent.decl) =
          some (parentBottom, parentBottomIndex) ∧
      ((componentCandidate execution.graph comp candidate).nodes.zipIdx.find? fun entry =>
        entry.1.border == 2 && entry.1.decl == child.decl) =
          some (childBottom, childBottomIndex) ∧
      rk rr.ranks parentIndex + 1 ≤ rk rr.ranks childIndex ∧
      rk rr.ranks childBottomIndex + 1 ≤ rk rr.ranks parentBottomIndex := by
  obtain ⟨rr, parentLabeled, parentMarker, hrr, _, parentKeys, _, parentRecords,
    _, _, parentFind⟩ := X_group_bottom_source execution hcomp hrun hparent hparentGroup
  obtain ⟨parentBottom, hparentBottom, _, _, _, hparentFind⟩ :=
    X_bottom_constraint_source execution parentKeys parentRecords
      hparent hparentGroup parentFind
  obtain ⟨_, childLabeled, childMarker, _, _, childKeys, _, childRecords,
    _, _, childFind⟩ := X_group_bottom_source execution hcomp hrun hchild hchildGroup
  obtain ⟨childBottom, hchildBottom, _, _, _, hchildFind⟩ :=
    X_bottom_constraint_source execution childKeys childRecords
      hchild hchildGroup childFind
  have hpath := X_direct_group_path execution hwf hparent hparentGroup
    hchild hchildGroup hparentBox hchildBox hparentRef hne
  have hinterval := ranked_compound_child_interval hrr
    (List.mk_mem_zipIdx_iff_getElem?.mpr hparent) hparentGroup hparentFind
    (List.mk_mem_zipIdx_iff_getElem?.mpr hchild) hchildGroup hpath hchildFind
  refine ⟨rr, parentBottom, childBottom, parentMarker.2, childMarker.2, hrr,
    hparentBottom, hchildBottom, hparentFind, hchildFind, ?_⟩
  exact hinterval


/-- Exact group side-rank bounds. -/
private theorem X_group_side_rank_bounds {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2)
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some node.decl) :
    ∃ (rr : RankImpl.RankResult) (labeled : Proper) (bottom : ProperNode × Nat),
      rankWithBudget (Compound.rankingGraph
        (componentCandidate execution.graph comp candidate)) = .ok rr ∧
      coordinateGraphX execution.params (exactDecls exactIds inp) labeled =
        run.coordinateProper ∧
      NodeKeys (componentCandidate execution.graph comp candidate) labeled ∧
      OrderImpl.BorderConstructionReady (titleReservations
        (sizeProperPortsX execution.params (exactDecls exactIds inp) labeled)) ∧
      (∀ (key : Nat) (original : Node),
        (componentCandidate execution.graph comp candidate).nodes[key]? = some original →
          labeled.nodes[key]? = some ⟨original, false, none, false⟩) ∧
      (∀ (key : Nat) (rank : Int), rr.ranks[key]? = some rank →
        labeled.rank[key]? = some rank) ∧
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[index]? =
        some (titleF ⟨node, false, none, false⟩) ∧
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
        fun entry => entry.1.node.border == 2 &&
          entry.1.node.clusterPath == node.clusterPath) = some bottom ∧
      side.node.clusterPath = node.clusterPath ∧
      0 ≤ rk run.coordinateProper.rank sideIndex ∧
      (rk (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).rank index).toNat ≤
        (rk run.coordinateProper.rank sideIndex).toNat ∧
      (rk run.coordinateProper.rank sideIndex).toNat ≤
        (rk (titleReservations (sizeProperPortsX execution.params
          (exactDecls exactIds inp) labeled)).rank bottom.2).toNat := by
  obtain ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks,
    htitled, hbottom⟩ :=
    X_group_bottom_source execution hcomp hrun hnode hgroup
  have hcoordinate : (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).nodes[sideIndex]? =
      some side := by
    rw [hc]
    exact hside
  obtain ⟨anchor, hanchor, generatedBottom, hfind, hpath, hnonneg, hlo, hhi⟩ :=
    X_coordinate_side_rank_bounds execution.params (exactDecls exactIds inp) hready
      hcoordinate hsideBorder
  obtain ⟨hanchorMember, hanchorCondition⟩ := List.mem_filter.mp hanchor
  have hanchorLookup := List.mem_zipIdx_iff_getElem?.mp hanchorMember
  have hanchorBorder : anchor.1.node.border = -2 := by simpa using hanchorCondition
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨group0, hgroup0, hdG, hbG, hpG⟩ := X_revKey execution hgroupSource
  obtain ⟨box, hbox0, hdeclG, hpathG⟩ := X_groupPath execution hgroup0 (hbG.trans hgroup)
  have hlast : node.clusterPath.getLast? = some node.decl := by
    rw [← hpG, hpathG]
    simp [← hdeclG, hdG]
  have hownerEq : anchor.1.node.clusterPath.getLast? =
      (titleF ⟨node, false, none, false⟩).node.clusterPath.getLast? := by
    rw [← hpath, (titleF_keys _).2.2.1]
    exact howner.trans hlast.symm
  have htitledBorder : (titleF ⟨node, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hgroup
  have hindex := X_titled_group_owner_unique execution hcomp hk hrecords
    hanchorLookup htitled hanchorBorder htitledBorder hownerEq
  have hrequestedAtAnchor :
      (titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes[anchor.2]? =
      some (titleF ⟨node, false, none, false⟩) := by
    rw [hindex]
    exact htitled
  have hanchorEq : anchor.1 = titleF ⟨node, false, none, false⟩ :=
    Option.some.inj (hanchorLookup.symm.trans hrequestedAtAnchor)
  rw [hanchorEq, (titleF_keys _).2.2.1] at hfind hpath
  have hbottomEq : generatedBottom = bottom :=
    Option.some.inj (hfind.symm.trans hbottom)
  rw [hindex] at hlo
  rw [hbottomEq] at hhi
  rw [hc] at hnonneg hlo hhi
  exact ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks,
    htitled, hbottom, hpath, hnonneg, hlo, hhi⟩

/-- Exact child side-parent borders. -/
private theorem X_child_side_parent_borders {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some child.decl) :
    ∃ left right : Nat,
      run.coordinateProper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      rk run.coordinateProper.rank left = rk run.coordinateProper.rank sideIndex ∧
      rk run.coordinateProper.rank right = rk run.coordinateProper.rank sideIndex := by
  obtain ⟨rr, labeled, childBottom, hrr, hc, hk, hready, hrecords, hranks,
    _, hchildBottom, _, hnonneg, hlo, hhi⟩ :=
    X_group_side_rank_bounds execution hcomp hrun hchild hchildGroup
      hside hsideBorder howner
  obtain ⟨parentBottom, hparentTitled, hparentBottom⟩ :=
    X_prepared_group_bottom execution hcomp hrun hc hk hready
      hrecords hparent hparentGroup
  obtain ⟨parentOriginalBottom, hparentOriginalBottom, _, _, _, hparentFind⟩ :=
    X_bottom_constraint_source execution hk hrecords
      hparent hparentGroup hparentBottom
  obtain ⟨childOriginalBottom, hchildOriginalBottom, _, _, _, hchildFind⟩ :=
    X_bottom_constraint_source execution hk hrecords
      hchild hchildGroup hchildBottom
  have hpath := X_direct_group_path execution hwf hparent hparentGroup
    hchild hchildGroup hparentBox hchildBox hparentRef hne
  have hinterval := ranked_compound_child_interval hrr
    (List.mk_mem_zipIdx_iff_getElem?.mpr hparent) hparentGroup hparentFind
    (List.mk_mem_zipIdx_iff_getElem?.mpr hchild) hchildGroup hpath hchildFind
  have hparentRank := X_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hparent).1
  have hchildRank := X_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hchild).1
  have hparentBottomRank := X_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hparentOriginalBottom).1
  have hchildBottomRank := X_titled_original_rk (P := execution.params)
    (exact := exactDecls exactIds inp) hrr hranks
    (List.getElem?_eq_some_iff.mp hchildOriginalBottom).1
  have htopBorder : (titleF ⟨parent, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hparentGroup
  have hbottomForTop :
      ((titleReservations (sizeProperPortsX execution.params
        (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
        fun entry => entry.1.node.border == 2 &&
          entry.1.node.clusterPath == (titleF ⟨parent, false, none, false⟩).node.clusterPath) =
            some parentBottom := by
    simpa only [(titleF_keys _).2.2.1] using hparentBottom
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    X_coordinate_rank_pair execution.params (exactDecls exactIds inp) labeled
      hready.2.2.2.1
      (List.mk_mem_zipIdx_iff_getElem?.mpr hparentTitled) htopBorder hbottomForTop
      (rank := (rk run.coordinateProper.rank sideIndex).toNat)
      (by
        dsimp only at hinterval hparentRank hchildRank hparentBottomRank hchildBottomRank ⊢
        omega)
      (by
        dsimp only at hinterval hparentRank hchildRank hparentBottomRank hchildBottomRank ⊢
        omega)
  have hnatcast : ((rk run.coordinateProper.rank sideIndex).toNat : Int) =
      rk run.coordinateProper.rank sideIndex := by omega
  have hleftValue : rk (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).rank left =
      rk run.coordinateProper.rank sideIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hleftRank, Option.getD_some] using hnatcast
  have hrightValue : rk (coordinateGraphX execution.params
      (exactDecls exactIds inp) labeled).rank right =
      rk run.coordinateProper.rank sideIndex := by
    simpa only [rk, List.getD_eq_getElem?_getD, hrightRank, Option.getD_some] using hnatcast
  rw [hc] at hleft hright hleftValue hrightValue
  exact ⟨left, right, hleft, hright, hleftValue, hrightValue⟩

/-- Exact child side-parent bracket. -/
private theorem X_child_side_parent_bracket {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some child.decl) :
    ∃ (ord : OrderResult) (left right : Nat),
      orderWithBudget run.coordinateProper orderOptions = .ok ord ∧
      ord.layers = run.layers ∧ side.dummy = false ∧
      side.node.clusterPath = child.clusterPath ∧
      run.coordinateProper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      run.coordinateProper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      ExecutedBorderOrder.Bracket run.coordinateProper ord left sideIndex right := by
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    X_child_side_parent_borders execution hwf hcomp hrun hparent hparentGroup
      hchild hchildGroup hparentBox hchildBox hparentRef hne hside hsideBorder howner
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsidePath, _, _, _⟩ :=
    X_group_side_rank_bounds execution hcomp hrun hchild hchildGroup
      hside hsideBorder howner
  have hdirect := X_direct_group_path execution hwf hparent hparentGroup
    hchild hchildGroup hparentBox hchildBox hparentRef hne
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  have hwformed := X_bordersWellFormed execution hcomp hrun
  have hreal : side.dummy = false := by
    cases hd : side.dummy with
    | false => rfl
    | true =>
      have hz := hwformed.2.2 sideIndex side hside hd
      rcases hsideBorder with hb | hb <;> omega
  have hnonempty := hwformed.1 sideIndex side hside hsideBorder
  rw [hsidePath] at hnonempty
  have hpositive := List.length_pos_iff.mpr hnonempty
  have hpathNe : parent.clusterPath ≠ child.clusterPath := by
    intro heq
    have hlength := congrArg List.length hdirect
    rw [List.length_dropLast, heq] at hlength
    omega
  have hprefix : parent.clusterPath <+: side.node.clusterPath := by
    rw [hsidePath, ← hdirect]
    exact List.dropLast_prefix _
  have hsidePrefix :
      (OrderImpl.borderLeft (titleF ⟨parent, false, none, false⟩, parentIndex)
        execution.params.clusterBorderW).node.clusterPath <+: side.node.clusterPath := by
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath <+: side.node.clusterPath
    rw [(titleF_keys _).2.2.1]
    exact hprefix
  have hleftLay : OrderImpl.lay run.coordinateProper left =
      OrderImpl.lay run.coordinateProper sideIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hleftRank
  have hrightLay : OrderImpl.lay run.coordinateProper right =
      OrderImpl.lay run.coordinateProper sideIndex := by
    simpa only [OrderImpl.lay] using congrArg Int.toNat hrightRank
  have hleftNe : left ≠ sideIndex := by
    intro heq
    rw [heq] at hleft
    have hn := Option.some.inj (hleft.symm.trans hside)
    have hp := congrArg (fun value : ProperNode => value.node.clusterPath) hn
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath = side.node.clusterPath at hp
    rw [(titleF_keys _).2.2.1, hsidePath] at hp
    exact hpathNe hp
  have hrightNe : right ≠ sideIndex := by
    intro heq
    rw [heq] at hright
    have hn := Option.some.inj (hright.symm.trans hside)
    have hp := congrArg (fun value : ProperNode => value.node.clusterPath) hn
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath = side.node.clusterPath at hp
    rw [(titleF_keys _).2.2.1, hsidePath] at hp
    exact hpathNe hp
  refine ⟨ord, left, right, horder, hlayers, hreal, hsidePath, hleft, hright, ?_⟩
  exact ExecutedBorderOrder.bracket run.coordinateProper orderOptions ord horder hwformed
    left sideIndex right _ side _ hleft hside hright hleftLay hrightLay
    rfl rfl rfl hreal rfl hsidePrefix hsidePrefix hleftNe hrightNe

/-- Exact child side-parent border interval. -/
private theorem X_child_side_parent_border_interval {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.coordinateProper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some child.decl) :
    ∃ left right : Nat,
      run.proper.nodes[sideIndex]? = some side ∧
      run.proper.nodes[left]? = some (OrderImpl.borderLeft
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      run.proper.nodes[right]? = some (OrderImpl.borderRight
        (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
      (Labels.rectAt run.proper run.xs run.ys left).x ≤
        (Labels.rectAt run.proper run.xs run.ys sideIndex).x ∧
      (Labels.rectAt run.proper run.xs run.ys sideIndex).x +
          (Labels.rectAt run.proper run.xs run.ys sideIndex).w ≤
        (Labels.rectAt run.proper run.xs run.ys right).x +
          (Labels.rectAt run.proper run.xs run.ys right).w := by
  obtain ⟨ord, left, right, _, hlayers, _, _, hleft, hright, hbracket⟩ :=
    X_child_side_parent_bracket execution hwf hcomp hrun hparent hparentGroup
      hchild hchildGroup hparentBox hchildBox hparentRef hne hside hsideBorder howner
  obtain ⟨li, mi, ri, hli, hmi, hri, hlt, htr⟩ := hbracket.positions
  rw [hlayers] at hli hmi hri
  have hlayer := hbracket.layer_mem
  rw [hlayers] at hlayer
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨labeled, hc, hk, _, _⟩ := X_coordinate_alignment hrun
  have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (X_cgShape execution) candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact X_pc_title_unique hk hshape (by rw [hc]; exact ha) (by rw [hc]; exact hb)
      hba hbb hp
  have hsideNotTop : side.node.border ≠ -2 := by
    rcases hsideBorder with hb | hb <;> omega
  have hsideNotBottom : side.node.border ≠ 2 := by
    rcases hsideBorder with hb | hb <;> omega
  have hleftSep := cluster_all_pairs_separated hcross hunique _ hlayer
    li mi left sideIndex _ _ hlt hli hmi hleft hside
    (by change (-1 : Int) ≠ -2; decide) (by change (-1 : Int) ≠ 2; decide)
    hsideNotTop hsideNotBottom
  have hrightSep := cluster_all_pairs_separated hcross hunique _ hlayer
    mi ri sideIndex right _ _ htr hmi hri hside hright
    hsideNotTop hsideNotBottom
    (by change (1 : Int) ≠ -2; decide) (by change (1 : Int) ≠ 2; decide)
  obtain ⟨hleftFinal, hleftX⟩ := X_border_record hrun hleft (Or.inl rfl)
  obtain ⟨hrightFinal, hrightX⟩ := X_border_record hrun hright (Or.inr rfl)
  obtain ⟨hsideFinal, hsideX⟩ := X_border_record hrun hside hsideBorder
  have hsideWidth := (sizesNonneg_lookup hsizes sideIndex side hside).1
  have hleftWidth := (sizesNonneg_lookup hsizes left _ hleft).1
  have hrightWidth := (sizesNonneg_lookup hsizes right _ hright).1
  have hsideLoops : 0 ≤ (side.node.loopExtent : Int) := Int.natCast_nonneg _
  have hparentLoops : 0 ≤ (parent.loopExtent : Int) := Int.natCast_nonneg _
  have hgap : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by omega
  change 0 ≤ execution.params.clusterBorderW at hleftWidth hrightWidth
  refine ⟨left, right, hsideFinal, hleftFinal, hrightFinal, ?_, ?_⟩
  · simp only [coordSep, CoordsImpl.nodeW, hleft, hside, OrderImpl.borderLeft] at hleftSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hleftFinal, hsideFinal, hleftX, hsideX, OrderImpl.borderLeft]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hleftSep ⊢
    omega
  · simp only [coordSep, CoordsImpl.nodeW, hside, hright, OrderImpl.borderRight,
      titleF, hparentGroup, beq_self_eq_true, Bool.true_or, ↓reduceIte] at hrightSep
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hsideFinal, hrightFinal, hsideX, hrightX, OrderImpl.borderRight]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hrightSep ⊢
    omega

/-- Exact child side-parent horizontal containment. -/
private theorem X_child_side_parent_horizontal {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
    {sideIndex : Nat} {side : ProperNode}
    (hside : run.proper.nodes[sideIndex]? = some side)
    (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
    (howner : side.node.clusterPath.getLast? = some child.decl) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run parentIndex).x ≤ (Labels.rectAt run.proper run.xs run.ys sideIndex).x ∧
    (Labels.rectAt run.proper run.xs run.ys sideIndex).x +
        (Labels.rectAt run.proper run.xs run.ys sideIndex).w ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).x +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).w := by
  have hcoordinate := (X_final_border_source hrun hside hsideBorder).1
  obtain ⟨left, right, _, hleft, hright, hlo, hhi⟩ :=
    X_child_side_parent_border_interval execution hwf hcomp hrun hparent hparentGroup
      hchild hchildGroup hparentBox hchildBox hparentRef hne hcoordinate hsideBorder howner
  let cg := componentCandidate execution.graph comp candidate
  have hparentGet : cg.nodes.getD parentIndex default = parent := by
    simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
  have hframeGroup : (cg.nodes.getD parentIndex default).border = -2 := by
    rw [hparentGet]
    exact hparentGroup
  obtain ⟨_, _, hparentSource⟩ := componentCandidate_nonplain_source hparent (by omega)
  obtain ⟨parent0, hparent0, hdP, hbP, hpP⟩ := X_revKey execution hparentSource
  obtain ⟨box, _, hdeclP, hpathP⟩ := X_groupPath execution hparent0 (hbP.trans hparentGroup)
  have hleftPath : (OrderImpl.borderLeft
      (titleF ⟨parent, false, none, false⟩, parentIndex)
      execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++ [(cg.nodes.getD parentIndex default).decl] := by
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath = _
    rw [(titleF_keys _).2.2.1, hparentGet]
    have hpg : parent.clusterPath = Compound.path inp.boxes box ++ [parent.decl] := by
      rw [← hpP, hpathP, ← hdeclP, hdP]
    simpa only [hparentGet] using hpg
  have hrightPath : (OrderImpl.borderRight
      (titleF ⟨parent, false, none, false⟩, parentIndex)
      execution.params.clusterBorderW).node.clusterPath =
        Compound.path inp.boxes box ++ [(cg.nodes.getD parentIndex default).decl] := by
    change (titleF ⟨parent, false, none, false⟩).node.clusterPath = _
    exact hleftPath
  have hleftContained := frameRect_side_marker_contained (P := execution.params)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hleft) (Or.inl rfl) hleftPath
  have hrightContained := frameRect_side_marker_contained (P := execution.params)
    hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hright) (Or.inr rfl) hrightPath
  exact ⟨Int.le_trans hleftContained.1 hlo, Int.le_trans hhi hrightContained.2.1⟩

/-- Exact groups expose a final side node. -/
private theorem X_group_final_side {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
    (hgroup : node.border = -2) :
    ∃ (sideIndex : Nat) (side : ProperNode),
      run.proper.nodes[sideIndex]? = some side ∧
      (side.node.border = -1 ∨ side.node.border = 1) ∧
      side.node.clusterPath.getLast? = some node.decl := by
  obtain ⟨_, labeled, _, _, hc, _, _, hrecords, _, _, _⟩ :=
    X_group_bottom_source execution hcomp hrun hnode hgroup
  let proxy := clearF (titleF ⟨node, false, none, false⟩)
  have hproxy : run.coordinateProper.nodes[index]? = some proxy := by
    rw [← hc]
    exact X_marker_record (hrecords index node hnode) (Or.inl hgroup) rfl
  have hproxyBorder : proxy.node.border = -2 :=
    (clearF_keys _).2.1.trans ((titleF_keys _).2.1.trans hgroup)
  obtain ⟨owner, sideIndex, side, howner, hside, hsideBorder, hsideOwner, _⟩ :=
    X_proxy_side_source hrun hproxy (Or.inl hproxyBorder)
  obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨group0, hgroup0, hdG, hbG, hpG⟩ := X_revKey execution hgroupSource
  obtain ⟨box, _, hdeclG, hpathG⟩ := X_groupPath execution hgroup0 (hbG.trans hgroup)
  have hproxyLast : proxy.node.clusterPath.getLast? = some node.decl := by
    change (clearF (titleF ⟨node, false, none, false⟩)).node.clusterPath.getLast? = _
    rw [(clearF_keys _).2.2.1, (titleF_keys _).2.2.1, ← hpG, hpathG]
    simp [← hdeclG, hdG]
  exact ⟨sideIndex, side, (X_border_record hrun hside hsideBorder).1,
    hsideBorder, hsideOwner.trans (howner.symm.trans hproxyLast)⟩

/-- Rect hulls preserve horizontal covering. -/
private theorem X_boundsOf_rects_right_nonneg (rects : List Rect) :
    0 ≤ (boundsOf rects []).right := by
  cases rects with
  | nil => exact Int.le_refl 0
  | cons first rest =>
    change 0 ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).right
    exact foldl_stepRect_le_right _ _

/-- Rect hulls preserve horizontal bounds. -/
private theorem X_boundsOf_rects_horizontal (rects : List Rect) (lo hi : Int)
    (hne : rects ≠ []) (hhi : 0 ≤ hi)
    (hrects : ∀ rect ∈ rects, lo ≤ rect.x ∧ rect.x + rect.w ≤ hi) :
    lo ≤ (boundsOf rects []).minX ∧ (boundsOf rects []).right ≤ hi := by
  have preserve : ∀ (remaining : List Rect) (initial : Bounds),
      lo ≤ initial.minX → initial.right ≤ hi →
      (∀ rect ∈ remaining, lo ≤ rect.x ∧ rect.x + rect.w ≤ hi) →
      lo ≤ (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).minX ∧
      (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).right ≤ hi := by
    intro remaining
    induction remaining with
    | nil =>
      intro initial hlo hupper _
      exact ⟨hlo, hupper⟩
    | cons first rest ih =>
      intro initial hlo hupper hall
      simp only [List.foldl_cons]
      apply ih
      · exact Int.le_min.mpr ⟨hlo, (hall first (by simp)).1⟩
      · exact Int.max_le.mpr ⟨hupper, (hall first (by simp)).2⟩
      · intro rect hr
        exact hall rect (List.mem_cons_of_mem _ hr)
  cases rects with
  | nil => exact (hne rfl).elim
  | cons first rest =>
    change lo ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).minX ∧ _
    exact preserve _ _ (hrects first (by simp)).1 hhi hrects

/-- Exact child frames lie horizontally in the parent frame. -/
private theorem X_child_frame_parent_horizontal {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run parentIndex).x ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).x ∧
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).x +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).w ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).x +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).w := by
  let cg := componentCandidate execution.graph comp candidate
  let parentFrame := frameRect execution.params cg run parentIndex
  let childFrame := frameRect execution.params cg run childIndex
  let borders := run.proper.nodes.zipIdx.filterMap fun entry =>
    if (entry.1.node.border == -1 || entry.1.node.border == 1) &&
        entry.1.node.clusterPath.getLast? == some child.decl then
      some (Labels.rectAt run.proper run.xs run.ys entry.2)
    else none
  let parentBorders := run.proper.nodes.zipIdx.filterMap fun entry =>
    if (entry.1.node.border == -1 || entry.1.node.border == 1) &&
        entry.1.node.clusterPath.getLast? == some parent.decl then
      some (Labels.rectAt run.proper run.xs run.ys entry.2)
    else none
  have hparentGet : cg.nodes.getD parentIndex default = parent := by
    simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
  have hchildGet : cg.nodes.getD childIndex default = child := by
    simp only [cg, List.getD_eq_getElem?_getD, hchild, Option.getD_some]
  obtain ⟨sideIndex, side, hside, hsideBorder, howner⟩ :=
    X_group_final_side execution hcomp hrun hchild hchildGroup
  have hmember : Labels.rectAt run.proper run.xs run.ys sideIndex ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(side, sideIndex), List.mk_mem_zipIdx_iff_getElem?.mpr hside, ?_⟩
    rcases hsideBorder with hb | hb <;> simp [hb, howner]
  have hnonempty : borders ≠ [] := by
    intro hempty
    rw [hempty] at hmember
    exact List.not_mem_nil hmember
  have hparentRight : parentFrame.x + parentFrame.w = (boundsOf parentBorders []).right := by
    dsimp only [parentFrame]
    simp only [frameRect, hparentGet, hparentGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    change (boundsOf parentBorders []).minX +
      ((boundsOf parentBorders []).right - (boundsOf parentBorders []).minX) = _
    omega
  have hupperNonnegative : 0 ≤ parentFrame.x + parentFrame.w := by
    rw [hparentRight]
    exact X_boundsOf_rects_right_nonneg _
  have hall : ∀ rect ∈ borders,
      parentFrame.x ≤ rect.x ∧ rect.x + rect.w ≤ parentFrame.x + parentFrame.w := by
    intro rect hrect
    obtain ⟨entry, hentry, heq⟩ := List.mem_filterMap.mp hrect
    split at heq
    · rename_i hcondition
      have hconditions := Bool.and_eq_true_iff.mp hcondition
      have hb : entry.1.node.border = -1 ∨ entry.1.node.border = 1 := by
        simpa only [Bool.or_eq_true, beq_iff_eq] using hconditions.1
      have ho : entry.1.node.clusterPath.getLast? = some child.decl :=
        beq_iff_eq.mp hconditions.2
      have hrectEq := Option.some.inj heq
      rw [← hrectEq]
      exact X_child_side_parent_horizontal execution hwf hcomp hrun
        hparent hparentGroup hchild hchildGroup hparentBox hchildBox hparentRef hne
        (List.mem_zipIdx_iff_getElem?.mp hentry) hb ho
    · cases heq
  have hhull := X_boundsOf_rects_horizontal borders parentFrame.x
    (parentFrame.x + parentFrame.w) hnonempty hupperNonnegative hall
  have hchildX : childFrame.x = (boundsOf borders []).minX := by
    dsimp only [childFrame]
    simp only [frameRect, hchildGet, hchildGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hchildRight : childFrame.x + childFrame.w = (boundsOf borders []).right := by
    dsimp only [childFrame]
    simp only [frameRect, hchildGet, hchildGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    change (boundsOf borders []).minX +
      ((boundsOf borders []).right - (boundsOf borders []).minX) = _
    omega
  change parentFrame.x ≤ childFrame.x ∧
    childFrame.x + childFrame.w ≤ parentFrame.x + parentFrame.w
  rw [hchildRight, hchildX]
  exact hhull

/-- Exact sized nodes preserve path scoping. -/
private theorem X_sizedNodes_scoped {c : Nat} {C : List Nat} {P : Params}
    {exact : List Nat} {labeled : Proper}
    (hlabeled : ∀ g ∈ labeled.nodes, PathScoped c C g.node.clusterPath) :
    ∀ s ∈ (sizeProperPortsX P exact labeled).nodes,
      PathScoped c C s.node.clusterPath := by
  intro s hs
  obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hs
  obtain ⟨original, horiginal, _, _, hpath⟩ :=
    X_sizeProperPorts_node_origin P exact labeled hindex
  rw [hpath]
  exact hlabeled original (List.mem_of_getElem? horiginal)

/-- Exact titled nodes preserve path scoping. -/
private theorem X_titled_nodes_scoped {c : Nat} {C : List Nat} {P : Params}
    {exact : List Nat} {labeled : Proper}
    (hlabeled : ∀ g ∈ labeled.nodes, PathScoped c C g.node.clusterPath) :
    ∀ f ∈ (titleReservations (sizeProperPortsX P exact labeled)).nodes,
      PathScoped c C f.node.clusterPath := by
  intro f hf
  rw [titleReservations_nodes] at hf
  rcases List.mem_append.mp hf with hleft | hright
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hleft
    rw [(titleF_keys s).2.2.1]
    exact X_sizedNodes_scoped hlabeled s hs
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hright
    have hmem : q.1 ∈ (sizeProperPortsX P exact labeled).nodes := by
      obtain ⟨hzip, _⟩ := List.mem_filter.mp hq
      exact List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hzip)
    exact X_sizedNodes_scoped hlabeled q.1 hmem

/-- Exact prepared coordinates preserve path scoping. -/
private theorem X_coordinatePrepared_scoped {c : Nat} {C : List Nat} {P : Params}
    {exact : List Nat} {labeled : Proper}
    (hlabeled : ∀ g ∈ labeled.nodes, PathScoped c C g.node.clusterPath) :
    ∀ e ∈ (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes,
      PathScoped c C e.node.clusterPath := by
  intro e he
  rw [clearProxyExtents_nodes] at he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  rw [(clearF_keys f).2.2.1]
  rcases addClusterBorders_node_origin _ _ f hf with htitled | ⟨top, htop, _, _, hpath⟩
  · exact X_titled_nodes_scoped hlabeled f htitled
  · rw [hpath]
    obtain ⟨hzip, _⟩ := List.mem_filter.mp htop
    exact X_titled_nodes_scoped hlabeled top.1
      (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hzip))

/-- Exact coordinate graphs preserve path scoping. -/
private theorem X_coordinateGraph_scoped {c : Nat} {C : List Nat} {P : Params}
    {exact : List Nat} {labeled : Proper}
    (hlabeled : ∀ g ∈ labeled.nodes, PathScoped c C g.node.clusterPath) :
    ∀ e ∈ (coordinateGraphX P exact labeled).nodes,
      PathScoped c C e.node.clusterPath :=
  materializeDummyPaths_scoped (X_coordinatePrepared_scoped hlabeled)

/-- Exact original nodes satisfy the child path scope. -/
private theorem X_original_path_scoped {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {childIndex : Nat} {child : Node}
    (hchild : execution.graph.nodes[childIndex]? = some child)
    (hchildGroup : child.border = -2)
    {index : Nat} {node : Node} (hnode : execution.graph.nodes[index]? = some node)
    (hborder : node.border = 0 ∨ node.border = -2 ∨ node.border = 2) :
    PathScoped child.decl child.clusterPath node.clusterPath := by
  obtain ⟨child0, hchild0, hdC, hbC, hpC⟩ := X_revKey execution hchild
  obtain ⟨node0, hnode0, hdN, hbN, hpN⟩ := X_revKey execution hnode
  obtain ⟨childBox, hchildBox, hchildDecl, hchildPath⟩ :=
    X_groupPath execution hchild0 (hbC.trans hchildGroup)
  have hchildDeclEq : child.decl = childIndex := hdC.symm.trans hchildDecl
  have hchildPathEq :
      child.clusterPath = Compound.path inp.boxes childBox ++ [childIndex] := by
    rw [← hpC, hchildPath]
  intro hin
  rcases hborder with hb | hb | hb
  · obtain ⟨box, hbox, _, hpath⟩ := X_plainPath execution hnode0 (hbN.trans hb)
    have hin' : child.decl ∈ Compound.path inp.boxes box := by
      have hpathN : node.clusterPath = Compound.path inp.boxes box := by
        rw [← hpN, hpath]
      rw [hpathN] at hin
      exact hin
    rw [hchildDeclEq] at hin'
    have hgoal : child.clusterPath <+: node.clusterPath := by
      have hpathN : node.clusterPath = Compound.path inp.boxes box := by
        rw [← hpN, hpath]
      rw [hpathN, hchildPathEq]
      exact Compound.path_ancestor_prefix (inputModel inp o) hwf hchildBox hbox hin'
    exact hgoal
  · obtain ⟨box, hbox, _hdecl, hpath⟩ := X_groupPath execution hnode0 (hbN.trans hb)
    have hpathN : node.clusterPath = Compound.path inp.boxes box ++ [index] := by
      rw [← hpN, hpath]
    have hin0 : child.decl ∈ Compound.path inp.boxes box ++ [index] := by
      rw [← hpN, hpath] at hin
      exact hin
    have hgoal : child.clusterPath <+: node.clusterPath := by
      rw [hpathN]
      rcases List.mem_append.mp hin0 with hin0 | hin0
      · rw [hchildDeclEq] at hin0
        rw [hchildPathEq]
        exact (Compound.path_ancestor_prefix (inputModel inp o) hwf hchildBox hbox
          hin0).trans (List.prefix_append _ _)
      · have hsame : childIndex = index :=
          hchildDeclEq.symm.trans (List.mem_singleton.mp hin0)
        subst hsame
        have hnodeEq : node = child := Option.some.inj (hnode.symm.trans hchild)
        subst hnodeEq
        rw [hpathN]
        exact List.prefix_refl _
    exact hgoal
  · obtain ⟨box, hbox0, hpath0⟩ := X_bottomPath execution hnode0 (hbN.trans hb)
    have hbox : inp.boxes[node.decl]? = some box := by
      rw [← hdN]
      exact hbox0
    have hpathN : node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
      rw [← hpN, hpath0, hdN]
    have hin0 : child.decl ∈ Compound.path inp.boxes box ++ [node.decl] := by
      rw [← hpN, hpath0, hdN] at hin
      exact hin
    have hgoal : child.clusterPath <+: node.clusterPath := by
      rw [hpathN]
      rcases List.mem_append.mp hin0 with hin0 | hin0
      · rw [hchildDeclEq] at hin0
        rw [hchildPathEq]
        exact (Compound.path_ancestor_prefix (inputModel inp o) hwf hchildBox hbox
          hin0).trans (List.prefix_append _ _)
      · have hsame : childIndex = node.decl :=
          hchildDeclEq.symm.trans (List.mem_singleton.mp hin0)
        rw [← hsame] at hbox
        have hboxEq : box = childBox := Option.some.inj (hbox.symm.trans hchildBox)
        subst hboxEq
        rw [hchildPathEq, ← hsame]
        exact List.prefix_refl _
    exact hgoal

/-- Exact candidate nodes satisfy the child path scope. -/
private theorem X_candidate_node_scoped {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate : Nat} {childIndex : Nat} {child : Node}
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {index : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node) :
    PathScoped child.decl child.clusterPath node.clusterPath := by
  by_cases hempty : node.clusterPath = []
  · rw [hempty]
    exact pathScoped_nil _ _
  · obtain ⟨_, _, hsource⟩ := componentCandidate_nonempty_path_source hnode hempty
    obtain ⟨_, _, hchildSource⟩ := componentCandidate_nonplain_source hchild (by omega)
    exact X_original_path_scoped execution hwf hchildSource hchildGroup hsource
      (X_marker_shape execution hnode).1

/-- Exact labeled nodes satisfy the child path scope. -/
private theorem X_labeled_nodes_scoped {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate : Nat} {childIndex : Nat} {child : Node}
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2) {labeled : Proper}
    (hkeys : NodeKeys (componentCandidate execution.graph comp candidate) labeled) :
    ∀ g ∈ labeled.nodes, PathScoped child.decl child.clusterPath g.node.clusterPath := by
  intro g hg
  obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hg
  rcases hkeys v g hv with ⟨n, hn, _, _, hpath⟩ | ⟨_, _, hpath⟩
  · rw [hpath]
    exact X_candidate_node_scoped execution hwf hchild hchildGroup hn
  · rw [hpath]
    exact pathScoped_nil _ _

/-- Exact proper runs satisfy the child path scope. -/
private theorem X_component_run_proper_scoped {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {childIndex : Nat} {child : Node}
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2) :
    ∀ e ∈ run.proper.nodes, PathScoped child.decl child.clusterPath e.node.clusterPath := by
  obtain ⟨labeled, hc, hk, _, _⟩ := X_coordinate_alignment hrun
  have hlabeled := X_labeled_nodes_scoped execution hwf hchild hchildGroup hk
  have hcoordinate := X_coordinateGraph_scoped (P := execution.params)
    (exact := exactDecls exactIds inp) hlabeled
  rw [hc] at hcoordinate
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  have hq := proxyWidths_nodes_scoped hproxy hcoordinate
  rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  exact hq

/-- Rect hulls preserve vertical covering. -/
private theorem X_boundsOf_rects_bottom_nonneg (rects : List Rect) :
    0 ≤ (boundsOf rects []).bottom := by
  cases rects with
  | nil => exact Int.le_refl 0
  | cons first rest =>
    change 0 ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).bottom
    exact foldl_stepRect_le_bottom _ _

/-- Rect hulls preserve vertical bounds. -/
private theorem X_boundsOf_rects_vertical (rects : List Rect) (lo hi : Int)
    (hne : rects ≠ []) (hhi : 0 ≤ hi)
    (hrects : ∀ rect ∈ rects, lo ≤ rect.y ∧ rect.y + rect.h ≤ hi) :
    lo ≤ (boundsOf rects []).minY ∧ (boundsOf rects []).bottom ≤ hi := by
  have preserve : ∀ (remaining : List Rect) (initial : Bounds),
      lo ≤ initial.minY → initial.bottom ≤ hi →
      (∀ rect ∈ remaining, lo ≤ rect.y ∧ rect.y + rect.h ≤ hi) →
      lo ≤ (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).minY ∧
      (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).bottom ≤ hi := by
    intro remaining
    induction remaining with
    | nil =>
      intro initial hlo hupper _
      exact ⟨hlo, hupper⟩
    | cons first rest ih =>
      intro initial hlo hupper hall
      simp only [List.foldl_cons]
      apply ih
      · exact Int.le_min.mpr ⟨hlo, (hall first (by simp)).1⟩
      · exact Int.max_le.mpr ⟨hupper, (hall first (by simp)).2⟩
      · intro rect hr
        exact hall rect (List.mem_cons_of_mem _ hr)
  cases rects with
  | nil => exact (hne rfl).elim
  | cons first rest =>
    change lo ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).minY ∧ _
    exact preserve _ _ (hrects first (by simp)).1 hhi hrects

/-- Exact child frames lie vertically in the parent frame. -/
private theorem X_child_frame_parent_vertical {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run parentIndex).y ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).y ∧
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).y +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex).h ≤
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).y +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run parentIndex).h := by
  let cg := componentCandidate execution.graph comp candidate
  let parentFrame := frameRect execution.params cg run parentIndex
  let childFrame := frameRect execution.params cg run childIndex
  let childRects := run.proper.nodes.zipIdx.filterMap fun entry =>
    if entry.1.node.clusterPath.contains child.decl then
      some (Labels.rectAt run.proper run.xs run.ys entry.2)
    else none
  let parentRects := run.proper.nodes.zipIdx.filterMap fun entry =>
    if entry.1.node.clusterPath.contains parent.decl then
      some (Labels.rectAt run.proper run.xs run.ys entry.2)
    else none
  have hparentGet : cg.nodes.getD parentIndex default = parent := by
    simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
  have hchildGet : cg.nodes.getD childIndex default = child := by
    simp only [cg, List.getD_eq_getElem?_getD, hchild, Option.getD_some]
  have hdirect := X_direct_group_path execution hwf hparent hparentGroup
    hchild hchildGroup hparentBox hchildBox hparentRef hne
  obtain ⟨_, _, hparentSource⟩ := componentCandidate_nonplain_source hparent (by omega)
  obtain ⟨parent0, hparent0, hdP, hbP, hpP⟩ := X_revKey execution hparentSource
  obtain ⟨parentBoxV, hparentBoxV, hparentDeclV, hparentPathV⟩ :=
    X_groupPath execution hparent0 (hbP.trans hparentGroup)
  have hparentOwn : parent.decl ∈ parent.clusterPath := by
    rw [← hpP, hparentPathV, ← hparentDeclV, hdP]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hparentInChild : parent.decl ∈ child.clusterPath := by
    apply (List.dropLast_prefix child.clusterPath).subset
    rw [hdirect]
    exact hparentOwn
  have hscope := X_component_run_proper_scoped execution hwf hrun hchild hchildGroup
  have hparentContains : ∀ entry ∈ run.proper.nodes.zipIdx,
      entry.1.node.clusterPath.contains child.decl = true →
      entry.1.node.clusterPath.contains parent.decl = true := by
    intro entry hentry hcontains
    have hmem : entry.1 ∈ run.proper.nodes :=
      List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hentry)
    have hprefix := hscope entry.1 hmem (List.contains_iff_mem.mp hcontains)
    exact List.contains_iff_mem.mpr (hprefix.subset hparentInChild)
  obtain ⟨sideIndex, side, hside, _, howner⟩ :=
    X_group_final_side execution hcomp hrun hchild hchildGroup
  have hmember : Labels.rectAt run.proper run.xs run.ys sideIndex ∈ childRects := by
    apply List.mem_filterMap.mpr
    refine ⟨(side, sideIndex), List.mk_mem_zipIdx_iff_getElem?.mpr hside, ?_⟩
    have hmem : child.decl ∈ side.node.clusterPath := List.mem_of_getLast? howner
    simp [hmem]
  have hnonempty : childRects ≠ [] := by
    intro hempty
    rw [hempty] at hmember
    exact List.not_mem_nil hmember
  have hparentBottom : parentFrame.y + parentFrame.h = (boundsOf parentRects []).bottom := by
    dsimp only [parentFrame]
    simp only [frameRect, hparentGet, hparentGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    change (boundsOf parentRects []).minY +
      ((boundsOf parentRects []).bottom - (boundsOf parentRects []).minY) = _
    omega
  have hupperNonnegative : 0 ≤ parentFrame.y + parentFrame.h := by
    rw [hparentBottom]
    exact X_boundsOf_rects_bottom_nonneg _
  have hall : ∀ rect ∈ childRects,
      parentFrame.y ≤ rect.y ∧ rect.y + rect.h ≤ parentFrame.y + parentFrame.h := by
    intro rect hrect
    obtain ⟨entry, hentry, heq⟩ := List.mem_filterMap.mp hrect
    split at heq
    · rename_i hcontains
      have hrectEq := Option.some.inj heq
      rw [← hrectEq]
      exact frameRect_member_vertical (P := execution.params) (cg := cg) (run := run)
        (i := parentIndex) (q := entry)
        (by rw [hparentGet]; exact hparentGroup) hentry
        (by rw [hparentGet]; exact hparentContains entry hentry hcontains)
    · cases heq
  have hhull := X_boundsOf_rects_vertical childRects parentFrame.y
    (parentFrame.y + parentFrame.h) hnonempty hupperNonnegative hall
  have hchildY : childFrame.y = (boundsOf childRects []).minY := by
    dsimp only [childFrame]
    simp only [frameRect, hchildGet, hchildGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hchildBottom : childFrame.y + childFrame.h = (boundsOf childRects []).bottom := by
    dsimp only [childFrame]
    simp only [frameRect, hchildGet, hchildGroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    change (boundsOf childRects []).minY +
      ((boundsOf childRects []).bottom - (boundsOf childRects []).minY) = _
    omega
  change parentFrame.y ≤ childFrame.y ∧
    childFrame.y + childFrame.h ≤ parentFrame.y + parentFrame.h
  rw [hchildBottom, hchildY]
  exact hhull

/-- Exact child frames lie in the parent group frame. -/
private theorem X_child_frame_contained {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {parentIndex childIndex : Nat} {parent child : Node}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? =
      some parent)
    (hparentGroup : parent.border = -2)
    (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? =
      some child)
    (hchildGroup : child.border = -2)
    {parentBox childBox : ModelBox}
    (hparentBox : inp.boxes[parent.decl]? = some parentBox)
    (hchildBox : inp.boxes[child.decl]? = some childBox)
    (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "") :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run parentIndex).Contained
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run childIndex) := by
  have hhorizontal := X_child_frame_parent_horizontal execution hwf hcomp hrun
    hparent hparentGroup hchild hchildGroup hparentBox hchildBox hparentRef hne
  have hvertical := X_child_frame_parent_vertical execution hwf hcomp hrun
    hparent hparentGroup hchild hchildGroup hparentBox hchildBox hparentRef hne
  unfold Rect.Contained
  exact ⟨hhorizontal.1, hhorizontal.2, hvertical.1, hvertical.2⟩

/-- Exact runs nest frames: plain members and child groups lie in their parent frame. -/
theorem exactRunFrameNesting {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true) :
    ExactRunFrameNesting execution := by
  refine ⟨?_, ?_⟩
  · intro comp candidate run orderOptions hcomp hrun
    intro index memberIndex node member hnode hgroup hmember hplain hinside
    exact X_member_contained execution hwf hcomp hrun hnode hgroup
      hmember hplain hinside
  · intro comp candidate run orderOptions hcomp hrun
    intro parentIndex childIndex parent child hparent hgroup hchild hgroup2
    intro parentBox childBox hpBox hcBox href hne
    exact X_child_frame_contained execution hwf hcomp hrun hparent hgroup
      hchild hgroup2 hpBox hcBox href hne

/-- Exact member frames are contained in their parent frame, without hypotheses. -/
theorem exactMemberInFrame' {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true) :
    (∀ (comp : List Nat) (candidate : Nat) (run : Run) (orderOptions : OrderOptions),
      comp ∈ components execution.graph →
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate) execution.measured
        orderOptions = .ok run →
      ∀ (memberIndex key parentKey parentIndex : Nat) (member : Node),
        comp[memberIndex]? = some key → key < inp.boxes.length →
        (componentCandidate execution.graph comp candidate).nodes[memberIndex]? =
          some member →
        ∀ (childBox : ModelBox), inp.boxes[key]? = some childBox →
        ∀ (parentBox : ModelBox), inp.boxes[parentKey]? = some parentBox →
        childBox.parent = parentBox.id → childBox.parent ≠ "" →
        comp[parentIndex]? = some parentKey →
        (frameRect execution.params (componentCandidate execution.graph comp candidate)
          run parentIndex).Contained
          (frameRect execution.params (componentCandidate execution.graph comp candidate)
            run memberIndex)) := by
  exact exactMemberInFrame execution hwf hframed
    (exactRunFrameNesting execution hwf hframed)
end PipelineImpl
end Layered
end Elegant

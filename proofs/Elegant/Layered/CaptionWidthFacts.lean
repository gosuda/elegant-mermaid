import Elegant.Layered.GroupFrameSizingFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ExecutedPortsFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

theorem coordinateGraph_title_record {P : Params} {p : Proper}
    {i : Nat} {node : ProperNode}
    (hnode : p.nodes[i]? = some node) (hborder : node.node.border = -2)
    (hdummy : node.dummy = false) :
    ∃ j : Nat, (coordinateGraph P p).nodes[p.nodes.length + j]? =
      some (copyF (node, i)) := by
  have hsized : (sizeProperPorts P p).nodes[i]? = some node := by
    simp only [sizeProperPorts, List.getElem?_map, List.getElem?_zipIdx,
      hnode, Option.map_some]
    simp [hborder]
  have hmember : (node, i) ∈ titleNodes (sizeProperPorts P p) := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_zipIdx_iff_getElem?.mpr hsized, by simp [hborder]⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmember
  have hjlt := (List.getElem?_eq_some_iff.mp hj).1
  have hlength : p.nodes.length + j <
      (titleReservations (sizeProperPorts P p)).nodes.length := by
    rw [titleReservations_nodes]
    simp only [List.length_append, List.length_map, sizeProperPorts_length]
    omega
  have hreserved : (titleReservations (sizeProperPorts P p)).nodes[p.nodes.length + j]? =
      some (copyF (node, i)) := by
    rw [titleReservations_nodes]
    rw [List.getElem?_append_right (by
      simp only [List.length_map, sizeProperPorts_length]
      omega : ((sizeProperPorts P p).nodes.map titleF).length ≤ p.nodes.length + j)]
    have hoffset : p.nodes.length + j -
        ((sizeProperPorts P p).nodes.map titleF).length = j := by
      simp only [List.length_map, sizeProperPorts_length]
      omega
    rw [hoffset, List.getElem?_map, hj]
    rfl
  obtain ⟨extra, hextra, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPorts P p)) P.clusterBorderW
  have hborders : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW).nodes[p.nodes.length + j]? =
      some (copyF (node, i)) := by
    rw [hextra, List.getElem?_append_left hlength]
    exact hreserved
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW)).nodes[p.nodes.length + j]? =
      some (copyF (node, i)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hborders]
    simp [clearF, copyF]
  refine ⟨j, ?_⟩
  unfold coordinateGraph materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  simp [copyF, hdummy]

theorem componentRun_group_title_width_source
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hnode : cg.nodes[i]? = some node)
    (hborder : node.border = -2) :
    ∃ v : Nat, run.coordinateProper.nodes[v]? =
        some (copyF (⟨node, false, none, false⟩, i)) ∧
      run.proper.nodes[v]? = some (copyF (⟨node, false, none, false⟩, i)) := by
  obtain ⟨ranks, normalized, labeled, routed, hnormalize, hlabels, hcoordinate,
    -, -, hproxy, hdrop, -, -, -, -, -⟩ := componentRun_spec h
  have hnormalized := normalize_node_record hnormalize hnode
  have hlabeled := addLabelNodes_untouched_node hlabels hnormalized (by rfl)
  obtain ⟨j, hj⟩ := coordinateGraph_title_record hlabeled hborder (by rfl)
  have hcoord : run.coordinateProper.nodes[labeled.nodes.length + j]? =
      some (copyF (⟨node, false, none, false⟩, i)) := by
    rw [← hcoordinate]
    exact hj
  obtain ⟨-, -, -, -, -, hpreserve⟩ := proxyWidths_rel hproxy
  have hrouted : routed.nodes[labeled.nodes.length + j]? =
      some (copyF (⟨node, false, none, false⟩, i)) :=
    (hpreserve _ _ hcoord (by simp [copyF])).1
  have hnodes : run.proper.nodes = routed.nodes := by
    have heq := congrArg Proper.nodes hdrop
    rw [OrderImpl.dropSynthetic_nodes] at heq
    exact heq.symm
  exact ⟨labeled.nodes.length + j, hcoord, by rw [hnodes]; exact hrouted⟩

theorem SceneExecution.component_caption_cross_axis_reservation
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {i key : Nat} (hkey : part.1[i]? = some key)
    {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = -2) :
    ∃ index run loops area,
      componentRun execution.params (componentCandidate execution.graph part.1 index)
        execution.measured (candidateOrder index) = .ok run ∧
      part.2 = { placeComponent execution.params
        (componentCandidate execution.graph part.1 index)
        run 0 execution.measured loops with area := area } ∧
      ∃ (v : Nat) (title : ProperNode), run.coordinateProper.nodes[v]? = some title ∧
        run.proper.nodes[v]? = some title ∧ title.node.border = 3 ∧
        title.node.clusterPath = node.clusterPath ∧
        title.node.w = (match o.direction with
          | .LR | .RL =>
            (max 1 (execution.lines.getD key []).length : Int) * execution.params.lineH
          | .TB | .BT =>
            (execution.lines.getD key []).foldl
              (fun (width : Int) (line : Measure.Line) => max width line.width) 0) := by
  obtain ⟨index, run, loops, area, hrun, _, hplace, _, _, _, _⟩ :=
    execution.actual_component_sizing hpart
  have hlocal : (componentCandidate execution.graph part.1 index).nodes[i]? =
      some node := by
    rw [componentCandidate_nodes]
    change (part.1.map (fun key => execution.graph.nodes.getD key default))[i]? = some node
    simp only [List.getElem?_map, hkey, Option.map_some,
      List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  obtain ⟨v, hcoordinate, hproper⟩ :=
    componentRun_group_title_width_source hrun hlocal hborder
  have hwidth := (actual_title_caption_fit execution.graph_eq hlocal hborder).1
  have hkeyD : part.1.getD i 0 = key := by simp [List.getD, hkey]
  rw [hkeyD] at hwidth
  exact ⟨index, run, loops, area, hrun, hplace, v,
    copyF (⟨node, false, none, false⟩, i), hcoordinate, hproper, rfl, rfl, hwidth⟩

theorem componentRun_group_title_interval_source
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hnode : cg.nodes[i]? = some node)
    (hborder : node.border = -2) :
    ∃ v : Nat, run.coordinateProper.nodes[v]? =
        some (copyF (⟨node, false, none, false⟩, i)) ∧
      run.proper.nodes[v]? = some (copyF (⟨node, false, none, false⟩, i)) ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 ∧
      (Labels.rectAt run.proper run.xs run.ys v).x =
        run.coordinateXs.getD v 0 - Int.fdiv node.w 2 ∧
      (Labels.rectAt run.proper run.xs run.ys v).w = node.w ∧
      0 ≤ node.w := by
  obtain ⟨v, hcoordinate, hproper⟩ :=
    componentRun_group_title_width_source h hnode hborder
  obtain ⟨_, _, _, _, _, _, _, _, hcross, hproxy, _⟩ := componentRun_spec h
  obtain ⟨_, _, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  have hnonneg : 0 ≤ node.w := by
    simpa only [copyF] using
      (sizesNonneg_lookup hsizes v _ hcoordinate).1
  have hx := ((proxyWidths_rel hproxy).2.2.2.2.2 v _ hcoordinate
    (by simp [copyF])).2
  have hxs : run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
    simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]
  refine ⟨v, hcoordinate, hproper, hxs, ?_, ?_, hnonneg⟩
  · simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt,
      RouteImpl.nodeW, hproper, copyF, hxs]
  · simp only [Labels.rectAt, Labels.labelRect, RouteImpl.nodeW, hproper, copyF]

theorem componentRun_group_title_rank_layer
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hnode : cg.nodes[i]? = some node)
    (hborder : node.border = -2) :
    ∃ (v position : Nat),
      run.coordinateProper.nodes[v]? = some (copyF (⟨node, false, none, false⟩, i)) ∧
      run.proper.nodes[v]? = some (copyF (⟨node, false, none, false⟩, i)) ∧
      (OrderImpl.lay run.coordinateProper v) < run.layers.length ∧
      (run.layers.getD (OrderImpl.lay run.coordinateProper v) [])[position]? = some v ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 ∧
      (Labels.rectAt run.proper run.xs run.ys v).x =
        run.coordinateXs.getD v 0 - Int.fdiv node.w 2 ∧
      (Labels.rectAt run.proper run.xs run.ys v).w = node.w ∧
      0 ≤ node.w := by
  obtain ⟨v, hcoordinate, hproper, hxs, hx, hw, hnonneg⟩ :=
    componentRun_group_title_interval_source h hnode hborder
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, hord, hlayers⟩, _⟩ := componentRun_spec h
  have hvalid : OrderImpl.Valid run.coordinateProper := by
    by_cases hv : OrderImpl.Valid run.coordinateProper
    · exact hv
    · simp [orderWithBudget, hv] at hord
  have hlayering : OrderImpl.Layering run.coordinateProper run.layers := by
    rw [← hlayers]
    exact (OrderImpl.orderWithBudget_spec _ _ _ hord).1
  have hv : v < run.coordinateProper.rank.length := by
    rw [← hvalid.1]
    exact (List.getElem?_eq_some_iff.mp hcoordinate).1
  have hr : OrderImpl.lay run.coordinateProper v < run.layers.length := by
    rw [hlayering.1]
    exact OrderImpl.lay_lt_layerCount _ hv
  have hmember : v ∈ run.layers.getD (OrderImpl.lay run.coordinateProper v) [] :=
    (OrderImpl.layer_mem hlayering hr).mpr ⟨hv, rfl⟩
  obtain ⟨position, hposition⟩ := List.mem_iff_getElem?.mp hmember
  exact ⟨v, position, hcoordinate, hproper, hr, hposition, hxs, hx, hw, hnonneg⟩

theorem componentRun_group_caption_placement_source
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hnode : cg.nodes[i]? = some node)
    (hborder : node.border = -2) :
    ∃ title : ProperNode × Nat,
      (run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == node.clusterPath)) = some title ∧
      run.proper.nodes[title.2]? = some title.1 ∧
      title.1.node.border = 3 ∧ title.1.node.clusterPath = node.clusterPath ∧
      (i, Rect.mk
        (run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2)
        ((frameRect P cg run i).y + P.clusterPad)
        node.w (node.h - P.clusterPad)) ∈ componentTitles P cg run := by
  obtain ⟨v, _, hproper⟩ := componentRun_group_title_width_source h hnode hborder
  have hmember :
      (copyF (⟨node, false, none, false⟩, i), v) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hproper
  cases hfind : run.proper.nodes.zipIdx.find? (fun q =>
      q.1.node.border == 3 && q.1.node.clusterPath == node.clusterPath) with
  | none =>
    have hmissing := List.find?_eq_none.mp hfind _ hmember
    simp [copyF] at hmissing
  | some title =>
    have hselected := List.find?_some hfind
    have hmetadata : title.1.node.border = 3 ∧
        title.1.node.clusterPath = node.clusterPath := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using hselected
    have hlookup : run.proper.nodes[title.2]? = some title.1 :=
      List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfind)
    refine ⟨title, rfl, hlookup, hmetadata.1, hmetadata.2, ?_⟩
    unfold componentTitles
    apply List.mem_filterMap.mpr
    refine ⟨(node, i), List.mk_mem_zipIdx_iff_getElem?.mpr hnode, ?_⟩
    simp [hborder, hfind]

theorem componentRun_title_coordinate_record
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {title : ProperNode} (htitle : run.proper.nodes[v]? = some title)
    (hborder : title.node.border = 3) :
    run.coordinateProper.nodes[v]? = some title ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _⟩ :=
    componentRun_spec h
  obtain ⟨_, _, hlength, _, hrecords, hunchanged⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = routed.nodes := by rw [← hdrop]; rfl
  have hv : v < run.coordinateProper.nodes.length := by
    have hv := (List.getElem?_eq_some_iff.mp htitle).1
    rw [hnodes, hlength] at hv
    exact hv
  have hsource : run.coordinateProper.nodes[v]? =
      some (run.coordinateProper.nodes[v]'hv) := List.getElem?_eq_getElem hv
  obtain ⟨updated, hupdated, _, hb, _⟩ := hrecords v _ hsource
  have heq : updated = title := by
    rw [← hnodes, htitle] at hupdated
    exact Option.some.inj hupdated.symm
  have hb3 : (run.coordinateProper.nodes[v]'hv).node.border = 3 := by
    rw [← hb, heq, hborder]
  obtain ⟨hrecord, hx⟩ := hunchanged v _ hsource (by omega)
  have hsourceEq : run.coordinateProper.nodes[v]'hv = title := by
    rw [← hnodes, htitle] at hrecord
    exact Option.some.inj hrecord.symm
  refine ⟨by simpa only [hsourceEq] using hsource, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

theorem componentRun_group_caption_selected_copy
    {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) (hshape : CgShape cg)
    {i : Nat} {node : Node} (hnode : cg.nodes[i]? = some node)
    (hborder : node.border = -2) :
    ∃ v : Nat,
      (run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == node.clusterPath)) =
          some (copyF (⟨node, false, none, false⟩, i), v) ∧
      run.coordinateProper.nodes[v]? = some (copyF (⟨node, false, none, false⟩, i)) ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 ∧
      (i, Rect.mk (run.coordinateXs.getD v 0 - Int.fdiv node.w 2)
        ((frameRect P cg run i).y + P.clusterPad)
        node.w (node.h - P.clusterPad)) ∈ componentTitles P cg run := by
  obtain ⟨v, hcopyCoordinate, hcopyProper, hxs, _, _, _⟩ :=
    componentRun_group_title_interval_source h hnode hborder
  obtain ⟨title, hfind, htitle, hb3, hpath, hplacement⟩ :=
    componentRun_group_caption_placement_source h hnode hborder
  obtain ⟨hselectedCoordinate, _⟩ :=
    componentRun_title_coordinate_record h htitle hb3
  obtain ⟨labeled, hcoordinate, hkeys, _⟩ := componentRun_coordinate_source_alignment h
  have hindex : title.2 = v := by
    apply pc_title_unique hkeys hshape
      (by rw [hcoordinate]; exact hselectedCoordinate)
      (by rw [hcoordinate]; exact hcopyCoordinate) hb3 (by rfl)
    exact hpath
  have hrecord : title.1 = copyF (⟨node, false, none, false⟩, i) := by
    rw [hindex, hcopyProper] at htitle
    exact Option.some.inj htitle.symm
  have htitleEq : title = (copyF (⟨node, false, none, false⟩, i), v) :=
    Prod.ext hrecord hindex
  subst title
  refine ⟨v, hfind, hcopyCoordinate, hxs, ?_⟩
  simpa only [copyF, hxs] using hplacement

theorem measured_component_caption_cross_axis_source
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run)
    {i : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[i]? = some node)
    (hborder : node.border = -2) :
    ∃ v : Nat,
      (run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == node.clusterPath)) =
          some (copyF (⟨node, false, none, false⟩, i), v) ∧
      run.coordinateProper.nodes[v]? = some (copyF (⟨node, false, none, false⟩, i)) ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 ∧
      (i, Rect.mk (run.coordinateXs.getD v 0 - Int.fdiv node.w 2)
        ((frameRect P (componentCandidate graph comp candidate) run i).y + P.clusterPad)
        node.w (node.h - P.clusterPad)) ∈
          componentTitles P (componentCandidate graph comp candidate) run ∧
      node.w = (match o.direction with
        | .LR | .RL => (max 1 (lines.getD (comp.getD i 0) []).length : Int) * P.lineH
        | .TB | .BT => (lines.getD (comp.getD i 0) []).foldl
            (fun (width : Int) (line : Measure.Line) => max width line.width) 0) := by
  have hshape : CgShape (componentCandidate graph comp candidate) :=
    componentCandidate_shape (components_nodup graph comp hcomp)
      (measuredGraph_shape hgraph) candidate
  obtain ⟨v, hfind, hcoordinate, hxs, hplacement⟩ :=
    componentRun_group_caption_selected_copy hrun hshape hnode hborder
  exact ⟨v, hfind, hcoordinate, hxs, hplacement,
    (actual_title_caption_fit hgraph hnode hborder).1⟩

theorem measured_component_caption_border_interval
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run)
    {i : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[i]? = some node)
    (hborder : node.border = -2) :
    ∃ (v left right : Nat),
      (run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == node.clusterPath)) =
          some (copyF (⟨node, false, none, false⟩, i), v) ∧
      run.proper.nodes[left]? =
        some (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, i) P.clusterBorderW) ∧
      run.proper.nodes[right]? =
        some (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, i) P.clusterBorderW) ∧
      (Labels.rectAt run.proper run.xs run.ys left).x ≤
        run.coordinateXs.getD v 0 - Int.fdiv node.w 2 ∧
      run.coordinateXs.getD v 0 - Int.fdiv node.w 2 + node.w ≤
        (Labels.rectAt run.proper run.xs run.ys right).x +
          (Labels.rectAt run.proper run.xs run.ys right).w := by
  obtain ⟨v, hfind, htitle, _, _, _⟩ :=
    measured_component_caption_cross_axis_source hgraph hcomp hrun hnode hborder
  obtain ⟨ord, left, right, horder, hlayers, hleft, hright, hbracket⟩ :=
    componentRun_group_title_bracket hgraph hcomp hrun hnode hborder htitle
      (by rfl) (by rfl)
  obtain ⟨li, ti, ri, hli, hti, hri, hlt, htr⟩ := hbracket.positions
  rw [hlayers] at hli hti hri
  have hlayer := hbracket.layer_mem
  rw [hlayers] at hlayer
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRun_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨labeled, hcoordinate, hkeys, _⟩ :=
    componentRun_coordinate_source_alignment hrun
  have hshape : CgShape (componentCandidate graph comp candidate) :=
    componentCandidate_shape (components_nodup graph comp hcomp)
      (measuredGraph_shape hgraph) candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact pc_title_unique hkeys hshape
      (by rw [hcoordinate]; exact ha) (by rw [hcoordinate]; exact hb) hba hbb hp
  have hleftSep := cluster_all_pairs_separated hcross hunique _ hlayer
    li ti left v _ _ hlt hli hti hleft htitle
    (by change (-1 : Int) ≠ -2; decide) (by change (-1 : Int) ≠ 2; decide)
    (by change (3 : Int) ≠ -2; decide) (by change (3 : Int) ≠ 2; decide)
  have hrightSep := cluster_all_pairs_separated hcross hunique _ hlayer
    ti ri v right _ _ htr hti hri htitle hright
    (by change (3 : Int) ≠ -2; decide) (by change (3 : Int) ≠ 2; decide)
    (by change (1 : Int) ≠ -2; decide) (by change (1 : Int) ≠ 2; decide)
  obtain ⟨hleftFinal, hleftX⟩ :=
    componentRun_border_record hrun hleft (Or.inl rfl)
  obtain ⟨hrightFinal, hrightX⟩ :=
    componentRun_border_record hrun hright (Or.inr rfl)
  have hwidth : 0 ≤ node.w := by
    simpa only [copyF] using (sizesNonneg_lookup hsizes v _ htitle).1
  have hsideWidth : 0 ≤ P.clusterBorderW := by
    simpa only [OrderImpl.borderLeft] using
      (sizesNonneg_lookup hsizes left _ hleft).1
  simp only [coordSep, CoordsImpl.nodeW, hleft, hright, htitle, copyF,
    OrderImpl.borderLeft, OrderImpl.borderRight, titleF, hborder] at hleftSep hrightSep
  refine ⟨v, left, right, hfind, hleftFinal, hrightFinal, ?_, ?_⟩
  · simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hleftFinal, hleftX, OrderImpl.borderLeft]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hleftSep ⊢
    omega
  · simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hrightFinal, hrightX, OrderImpl.borderRight]
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hrightSep ⊢
    omega

theorem measured_component_caption_frame_containment
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions =
      .ok run)
    {i : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[i]? = some node)
    (hborder : node.border = -2) :
    ∃ caption : Rect,
      (i, caption) ∈ componentTitles P (componentCandidate graph comp candidate) run ∧
      caption.w = node.w ∧ caption.h = node.h - P.clusterPad ∧
      (frameRect P (componentCandidate graph comp candidate) run i).x ≤ caption.x ∧
      (frameRect P (componentCandidate graph comp candidate) run i).y ≤ caption.y ∧
      caption.x + caption.w ≤
        (frameRect P (componentCandidate graph comp candidate) run i).x +
          (frameRect P (componentCandidate graph comp candidate) run i).w ∧
      caption.y + caption.h ≤
        (frameRect P (componentCandidate graph comp candidate) run i).y +
          (frameRect P (componentCandidate graph comp candidate) run i).h := by
  obtain ⟨v, left, right, hfind, hleft, hright, hleftInterval, hrightInterval⟩ :=
    measured_component_caption_border_interval hgraph hcomp hrun hnode hborder
  obtain ⟨selected, hselected, _, _, hplacement, _⟩ :=
    measured_component_caption_cross_axis_source hgraph hcomp hrun hnode hborder
  have hselectedIndex : selected = v := by
    exact congrArg Prod.snd (Option.some.inj (hselected.symm.trans hfind))
  subst selected
  obtain ⟨original, _, horiginal⟩ :=
    componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨_, box, _, _, hpath⟩ := measuredGraph_group_origin hgraph horiginal hborder
  have howner : node.clusterPath.getLast? = some node.decl := by
    rw [hpath]
    simp
  have hself : node.clusterPath.contains node.decl := by
    rw [hpath]
    simp
  let borders := run.proper.nodes.zipIdx.filterMap fun q =>
    if (q.1.node.border == -1 || q.1.node.border == 1) &&
        q.1.node.clusterPath.getLast? == some node.decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none
  have hleftMem : Labels.rectAt run.proper run.xs run.ys left ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, left), List.mk_mem_zipIdx_iff_getElem?.mpr hleft, ?_⟩
    simp [OrderImpl.borderLeft, titleF, hborder, howner]
  have hrightMem : Labels.rectAt run.proper run.xs run.ys right ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, right), List.mk_mem_zipIdx_iff_getElem?.mpr hright, ?_⟩
    simp [OrderImpl.borderRight, titleF, hborder, howner]
  have hlo := boundsOf_minX_le_rect_x borders []
    (Labels.rectAt run.proper run.xs run.ys left) hleftMem
  have hhi := rect_right_le_boundsOf_right borders []
    (Labels.rectAt run.proper run.xs run.ys right) hrightMem
  have hframeX :
      (frameRect P (componentCandidate graph comp candidate) run i).x =
        (boundsOf borders []).minX := by
    simp [frameRect, List.getD_eq_getElem?_getD, hnode, hborder, borders]
  have hframeW :
      (frameRect P (componentCandidate graph comp candidate) run i).w =
        (boundsOf borders []).right - (boundsOf borders []).minX := by
    exact frameRect_group_width_eq_horizontal_span hnode hborder
  have hheight := componentRun_group_frame_height_ge hrun hnode hborder hself
    (th := node.h - P.clusterPad) (by omega)
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRun_spec hrun
  have hpad := (crossCoordsClusterWith_spec hcross).2.1
  refine ⟨_, hplacement, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · change _ ≤ run.coordinateXs.getD v 0 - Int.fdiv node.w 2
    rw [hframeX]
    omega
  · change _ ≤ _ + P.clusterPad
    omega
  · change run.coordinateXs.getD v 0 - Int.fdiv node.w 2 + node.w ≤ _
    rw [hframeX, hframeW]
    omega
  · change _ + P.clusterPad + (node.h - P.clusterPad) ≤ _
    omega

theorem SceneExecution.component_caption_frame_containment
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {i key : Nat} (hkey : part.1[i]? = some key)
    {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = -2) :
    ∃ (caption frame : Rect),
      (i, caption) ∈ part.2.titles ∧ part.2.rects[i]? = some frame ∧
      frame.Contained caption ∧
      ∀ height dx dy : Int,
        (shiftRect dx dy (orientRect o.direction height frame)).Contained
          (shiftRect dx dy (orientRect o.direction height caption)) := by
  obtain ⟨hcomponents, _⟩ :=
    actual_components_parts_geometry (by rfl) execution.components_eq
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hcomponents]
    exact List.mem_map.mpr ⟨part, hpart, rfl⟩
  obtain ⟨index, run, loops, area, hrun, _, hplace, _, _, _, _⟩ :=
    execution.actual_component_sizing hpart
  have hlocal : (componentCandidate execution.graph part.1 index).nodes[i]? =
      some node := by
    rw [componentCandidate_nodes]
    change (part.1.map (fun key => execution.graph.nodes.getD key default))[i]? = some node
    simp only [List.getElem?_map, hkey, Option.map_some,
      List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  obtain ⟨caption, hcaption, _, _, hx, hy, hr, hb⟩ :=
    measured_component_caption_frame_containment execution.graph_eq hcomp hrun hlocal hborder
  let cg := componentCandidate execution.graph part.1 index
  let bounds := placeBounds execution.params cg run execution.measured loops
  let dx := 0 - bounds.minX
  let dy := 0 - bounds.minY
  let frame := frameRect execution.params cg run i
  have hplacedTitle : (i, shiftRect dx dy caption) ∈ part.2.titles := by
    rw [hplace]
    change (i, shiftRect dx dy caption) ∈
      (componentTitles execution.params cg run).map
        (fun q => (q.1, shiftRect dx dy q.2))
    exact List.mem_map.mpr ⟨(i, caption), hcaption, rfl⟩
  have hi : i < cg.nodes.length := (List.getElem?_eq_some_iff.mp hlocal).1
  have hplacedFrame : part.2.rects[i]? = some (shiftRect dx dy frame) := by
    rw [hplace]
    change (((List.range cg.nodes.length).map (frameRect execution.params cg run)).map
      (shiftRect dx dy))[i]? = some (shiftRect dx dy frame)
    simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some, frame]
  have hcontained : (shiftRect dx dy frame).Contained (shiftRect dx dy caption) := by
    unfold Rect.Contained shiftRect
    dsimp only
    change frame.x + dx ≤ caption.x + dx ∧
      caption.x + dx + caption.w ≤ frame.x + dx + frame.w ∧
      frame.y + dy ≤ caption.y + dy ∧
      caption.y + dy + caption.h ≤ frame.y + dy + frame.h
    dsimp only [frame, cg]
    exact ⟨by omega, by omega, by omega, by omega⟩
  refine ⟨shiftRect dx dy caption, shiftRect dx dy frame,
    hplacedTitle, hplacedFrame, hcontained, ?_⟩
  intro height offsetX offsetY
  unfold Rect.Contained at hcontained ⊢
  unfold shiftRect orientRect at *
  cases o.direction <;> dsimp only at * <;> omega

private theorem pack_caption_fold_titles
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).titles = start.titles ++
      pairs.flatMap (fun pair => pair.1.2.titles.map
        (fun title => (pair.1.1.getD title.1 0,
          shiftRect pair.2.x pair.2.y title.2))) := by
  induction pairs generalizing start with
  | nil => simp
  | cons pair rest ih =>
    simp [List.foldl_cons, ih, packStep, List.append_assoc]

theorem SceneExecution.packed_caption_frame_containment
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {i key : Nat} (hkey : part.1[i]? = some key)
    {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = -2) :
    ∃ (caption frame : Rect),
      (key, caption) ∈ execution.packedAcc.titles ∧
      execution.packedAcc.rects.getD key default = frame ∧
      frame.Contained caption ∧
      ∀ height dx dy : Int,
        (shiftRect dx dy (orientRect o.direction height frame)).Contained
          (shiftRect dx dy (orientRect o.direction height caption)) := by
  obtain ⟨caption, frame, htitle, hframe, hcontained, _⟩ :=
    execution.component_caption_frame_containment hpart hkey hnode hborder
  have hpack := execution.packed_eq
  unfold packAcc at hpack
  obtain ⟨packed, hpacked, hpack⟩ := bind_ok hpack
  have hpackedAcc : execution.packedAcc =
      (execution.componentsAcc.parts.zip packed.boxes).foldl packStep
        { execution.componentsAcc with
          canvasW := packed.width, canvasH := packed.height, titles := [] } :=
    (Except.ok.inj hpack).symm
  obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hpart
  have hclt : c < packed.boxes.length := by
    rw [Pack.pack_count hpacked]
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hc).1
  let box := packed.boxes[c]'hclt
  have hbox : packed.boxes[c]? = some box := List.getElem?_eq_getElem hclt
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
      some (part, box) := by
    exact List.getElem?_zip_eq_some.mpr ⟨hc, hbox⟩
  have hentry : (part.1.zip part.2.rects)[i]? = some (key, frame) := by
    exact List.getElem?_zip_eq_some.mpr ⟨hkey, hframe⟩
  have hsize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    obtain ⟨hdecl, source, hsource, _, _⟩ :=
      measuredGraph_group_origin execution.graph_eq hnode hborder
    have hindex := (List.getElem?_eq_some_iff.mp hsource).1
    simpa only [List.length_map, hdecl] using hindex
  have hvalue := actual_components_packed_rect_value (by rfl) execution.components_eq
    execution.packed_eq packed hpacked hselected hentry hsize default
  have hpackedTitle :
      (key, shiftRect box.x box.y caption) ∈ execution.packedAcc.titles := by
    rw [hpackedAcc, pack_caption_fold_titles]
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨(part, box), List.mem_of_getElem? hselected, ?_⟩
    apply List.mem_map.mpr
    refine ⟨(i, caption), htitle, ?_⟩
    simp only [List.getD_eq_getElem?_getD, hkey, Option.getD_some]
  have hshift : (shiftRect box.x box.y frame).Contained
      (shiftRect box.x box.y caption) := by
    unfold Rect.Contained shiftRect at *
    dsimp only at *
    omega
  refine ⟨shiftRect box.x box.y caption, shiftRect box.x box.y frame,
    hpackedTitle, hvalue, hshift, ?_⟩
  intro height dx dy
  unfold Rect.Contained at hshift ⊢
  unfold shiftRect orientRect at *
  cases o.direction <;> dsimp only at * <;> omega

theorem SceneExecution.scene_caption_box_containment
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = -2) :
    ∃ (box : Box) (caption : String × Rect),
      res.scene.layoutDump.box? source.id = some box ∧ caption.1 = source.id ∧
      caption ∈ execution.packedAcc.titles.filterMap (fun stored => do
        let owner ← inp.boxes[stored.1]?
        let textLines := execution.lines.getD stored.1 []
        let width := textLines.foldl (fun value line => max value line.width) 0
        let height := (max 1 textLines.length : Int) * execution.params.lineH
        let size := match o.direction with
          | .LR | .RL => Size.mk height width
          | .TB | .BT => Size.mk width height
        pure (owner.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            { stored.2 with w := size.w, h := size.h }))) ∧
      box.rect.Contained caption.2 := by
  have hk : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨part, hpart, entry, hentry, hentryKey⟩ :=
    execution.parts_coverage key _ (Array.getElem?_eq_getElem hk)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hentry
  have hkey : part.1[i]? = some key := by
    have hkey := zip_getElem?_left hi
    simpa only [hentryKey] using hkey
  obtain ⟨stored, frame, hstored, hframe, hcontained, _⟩ :=
    execution.packed_caption_frame_containment hpart hkey hnode hborder
  let textLines := execution.lines.getD key []
  let width := textLines.foldl (fun value line => max value line.width) 0
  let height := (max 1 textLines.length : Int) * execution.params.lineH
  let size := match o.direction with
    | .LR | .RL => Size.mk height width
    | .TB | .BT => Size.mk width height
  have hfit := execution.packed_title_caption_fit (key, stored) hstored
  change 0 ≤ size.w ∧ 0 ≤ size.h ∧ size.w ≤ stored.w ∧ size.h ≤ stored.h at hfit
  have hmeasured : frame.Contained { stored with w := size.w, h := size.h } := by
    unfold Rect.Contained at hcontained ⊢
    dsimp only
    exact ⟨hcontained.1, by omega, hcontained.2.2.1, by omega⟩
  let finalCaption : Rect :=
    shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        { stored with w := size.w, h := size.h })
  let finalFrame : Rect :=
    shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH frame)
  have hfinal : finalFrame.Contained finalCaption := by
    unfold finalFrame finalCaption Rect.Contained shiftRect orientRect at *
    cases o.direction <;> dsimp only at * <;> omega
  have hlookup := execution.source_box_lookup_of_box_ids_nodup
    (Model.boxIds_nodup hwf) hsource
  rw [hframe] at hlookup
  refine ⟨Box.mk source.id source.role.id finalFrame source.parent source.exclusive,
    (source.id, finalCaption), hlookup, rfl, ?_, hfinal⟩
  apply List.mem_filterMap.mpr
  refine ⟨(key, stored), hstored, ?_⟩
  simp only [hsource]
  rfl

private theorem component_caption_indices_nodup (P : Params) (cg : Graph) (run : Run) :
    ((componentTitles P cg run).map Prod.fst).Nodup := by
  let emit : Node × Nat → Option (Nat × Rect) := fun top => do
    if top.1.border != -2 then none else do
      let title ← run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath)
      let frame := frameRect P cg run top.2
      pure (top.2, Rect.mk
        (run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2)
        (frame.y + P.clusterPad) top.1.w (top.1.h - P.clusterPad))
  have identity : ∀ top caption, emit top = some caption → caption.1 = top.2 := by
    intro top caption he
    unfold emit at he
    split at he
    · contradiction
    · cases hf : run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath) with
      | none => simp [hf] at he
      | some title =>
        simp [hf] at he
        subst caption
        rfl
  have hindices : (cg.nodes.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hp := List.pairwise_map.mp hindices
  change ((componentTitles P cg run).map Prod.fst).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  change (cg.nodes.zipIdx.filterMap emit).Pairwise (fun a b => a.1 ≠ b.1)
  apply List.Pairwise.filterMap emit _ hp
  intro a b hne ca hca cb hcb
  rw [identity a ca hca, identity b cb hcb]
  exact hne

private theorem SceneExecution.part_caption_keys
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts) :
    (part.2.titles.map Prod.fst).Nodup ∧
      ∀ title ∈ part.2.titles, title.1 < part.1.length := by
  obtain ⟨index, run, loops, area, _, _, hplace, _, _, _, _⟩ :=
    execution.actual_component_sizing hpart
  let cg := componentCandidate execution.graph part.1 index
  have hkeys : part.2.titles.map Prod.fst =
      (componentTitles execution.params cg run).map Prod.fst := by
    simp [hplace, placeComponent, List.map_map, cg]
  refine ⟨by rw [hkeys]; exact component_caption_indices_nodup _ _ _, ?_⟩
  intro title htitle
  rw [hplace] at htitle
  change title ∈ (componentTitles execution.params cg run).map _ at htitle
  obtain ⟨raw, hraw, heq⟩ := List.mem_map.mp htitle
  obtain ⟨top, htop, _, hindex, _, _⟩ :=
    componentTitles_dimension_source execution.params cg run hraw
  have hi := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp htop)).1
  have hlen : cg.nodes.length = part.1.length := by
    simp only [cg, componentCandidate_nodes, componentGraph, List.length_map]
  have hkey : title.1 = raw.1 := by rw [← heq]
  rw [hkey, hindex]
  omega

theorem SceneExecution.packed_caption_keys_nodup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    (execution.packedAcc.titles.map Prod.fst).Nodup := by
  have hpack := execution.packed_eq
  unfold packAcc at hpack
  obtain ⟨packed, _, hpack⟩ := bind_ok hpack
  have hout : execution.packedAcc =
      (execution.componentsAcc.parts.zip packed.boxes).foldl packStep
        { execution.componentsAcc with
          canvasW := packed.width, canvasH := packed.height, titles := [] } :=
    (Except.ok.inj hpack).symm
  rw [hout, pack_caption_fold_titles]
  simp only [List.nil_append, List.map_flatMap, List.map_map, Function.comp_def]
  have hcomponents :=
    (actual_components_parts_geometry (by rfl) execution.components_eq).1
  have hpartNodup : (execution.componentsAcc.parts.map (fun p => p.1)).Nodup := by
    rw [hcomponents]
    exact components_entries_nodup execution.graph
  have component : ∀ part ∈ execution.componentsAcc.parts,
      part.1 ∈ components execution.graph := by
    intro part hp
    rw [← hcomponents]
    exact List.mem_map.mpr ⟨part, hp, rfl⟩
  apply List.pairwise_flatMap.mpr
  constructor
  · intro pair hpair
    have hp := (List.of_mem_zip hpair).1
    obtain ⟨hlocal, hbounds⟩ := execution.part_caption_keys hp
    have hcomp := component pair.1 hp
    have hnd := components_nodup execution.graph pair.1.1 hcomp
    apply List.pairwise_map.mpr
    apply (List.pairwise_map.mp hlocal).imp_of_mem
    intro a b ha hb hab heq
    exact hab ((List.Nodup.getD_inj (hbounds a ha) (hbounds b hb) hnd).mp heq)
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    let a := (execution.componentsAcc.parts.zip packed.boxes)[i]'hi
    let b := (execution.componentsAcc.parts.zip packed.boxes)[j]'hj
    have hai : (execution.componentsAcc.parts.zip packed.boxes)[i]? = some a :=
      List.getElem?_eq_getElem hi
    have hbj : (execution.componentsAcc.parts.zip packed.boxes)[j]? = some b :=
      List.getElem?_eq_getElem hj
    have hpa := zip_getElem?_left hai
    have hpb := zip_getElem?_left hbj
    have hma := List.mem_of_getElem? hpa
    have hmb := List.mem_of_getElem? hpb
    have hne : a.1.1 ≠ b.1.1 := by
      have hp := List.pairwise_iff_getElem.mp hpartNodup
      have h := hp i j (by simpa using (List.getElem?_eq_some_iff.mp hpa).1)
        (by simpa using (List.getElem?_eq_some_iff.mp hpb).1) hij
      simpa only [List.getElem_map,
        (List.getElem?_eq_some_iff.mp hpa).2,
        (List.getElem?_eq_some_iff.mp hpb).2, List.get_eq_getElem, a, b] using h
    intro x hx y hy heq
    obtain ⟨ta, hta, hxa⟩ := List.mem_map.mp hx
    obtain ⟨tb, htb, hyb⟩ := List.mem_map.mp hy
    have hva : ta.1 < a.1.1.length := by
      simpa only [List.get_eq_getElem, a] using
        (execution.part_caption_keys hma).2 ta hta
    have hvb : tb.1 < b.1.1.length := by
      simpa only [List.get_eq_getElem, b] using
        (execution.part_caption_keys hmb).2 tb htb
    have hkeya : a.1.1.getD ta.1 0 ∈ a.1.1 := by
      rw [← List.getElem_eq_getD (h := hva) 0]
      exact List.getElem_mem hva
    have hkeyb : b.1.1.getD tb.1 0 ∈ b.1.1 := by
      rw [← List.getElem_eq_getD (h := hvb) 0]
      exact List.getElem_mem hvb
    have hsame : a.1.1.getD ta.1 0 = b.1.1.getD tb.1 0 := hxa.trans (heq.trans hyb.symm)
    exact components_disjoint (component a.1 hma) (component b.1 hmb) hne
      hkeya (hsame.symm ▸ hkeyb)

theorem SceneExecution.scene_caption_owner_keys_nodup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) :
    let captions := execution.packedAcc.titles.filterMap (fun stored => do
      let owner ← inp.boxes[stored.1]?
      let textLines := execution.lines.getD stored.1 []
      let width := textLines.foldl (fun value line => max value line.width) 0
      let height := (max 1 textLines.length : Int) * execution.params.lineH
      let size := match o.direction with
        | .LR | .RL => Size.mk height width
        | .TB | .BT => Size.mk width height
      pure (owner.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          { stored.2 with w := size.w, h := size.h })))
    (captions.map Prod.fst).Nodup := by
  let emit : Nat × Rect → Option (String × Rect) := fun stored => do
    let owner ← inp.boxes[stored.1]?
    let textLines := execution.lines.getD stored.1 []
    let width := textLines.foldl (fun value line => max value line.width) 0
    let height := (max 1 textLines.length : Int) * execution.params.lineH
    let size := match o.direction with
      | .LR | .RL => Size.mk height width
      | .TB | .BT => Size.mk width height
    pure (owner.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        { stored.2 with w := size.w, h := size.h }))
  have identity : ∀ stored caption, emit stored = some caption →
      ∃ owner : ModelBox, inp.boxes[stored.1]? = some owner ∧ caption.1 = owner.id := by
    intro stored caption he
    unfold emit at he
    cases ho : inp.boxes[stored.1]? with
    | none => simp [ho] at he
    | some owner =>
      refine ⟨owner, rfl, ?_⟩
      simp only [ho] at he
      exact (congrArg Prod.fst (Option.some.inj he)).symm
  change ((execution.packedAcc.titles.filterMap emit).map Prod.fst).Pairwise (· ≠ ·)
  rw [List.pairwise_map]
  apply List.Pairwise.filterMap emit _
    (List.pairwise_map.mp execution.packed_caption_keys_nodup)
  intro a b hne ca hca cb hcb heq
  obtain ⟨oa, hoa, hida⟩ := identity a ca hca
  obtain ⟨ob, hob, hidb⟩ := identity b cb hcb
  have ha : (inp.boxes.map (·.id))[a.1]? = some oa.id := by
    simp only [List.getElem?_map, hoa, Option.map_some]
  have hb : (inp.boxes.map (·.id))[b.1]? = some ob.id := by
    simp only [List.getElem?_map, hob, Option.map_some]
  have hid : oa.id = ob.id := hida.symm.trans (heq.trans hidb)
  have hlookups : (inp.boxes.map (·.id))[a.1]? = (inp.boxes.map (·.id))[b.1]? :=
    ha.trans ((congrArg some hid).trans hb.symm)
  have hbound : a.1 < (inp.boxes.map (·.id)).length := by
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hoa).1
  exact hne ((List.Nodup.getElem?_inj hbound (Model.boxIds_nodup hwf)).mp hlookups)

theorem SceneExecution.scene_caption_selector_containment
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = -2) :
    let captions := execution.packedAcc.titles.filterMap (fun stored => do
      let owner ← inp.boxes[stored.1]?
      let textLines := execution.lines.getD stored.1 []
      let width := textLines.foldl (fun value line => max value line.width) 0
      let height := (max 1 textLines.length : Int) * execution.params.lineH
      let size := match o.direction with
        | .LR | .RL => Size.mk height width
        | .TB | .BT => Size.mk width height
      pure (owner.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          { stored.2 with w := size.w, h := size.h })))
    ∃ (box : Box) (caption : String × Rect),
      res.scene.layoutDump.box? source.id = some box ∧
      captions.find? (fun title => title.1 == source.id) = some caption ∧
      box.rect.Contained caption.2 := by
  obtain ⟨box, caption, hbox, hid, hmember, hcontained⟩ :=
    execution.scene_caption_box_containment hwf hsource hnode hborder
  refine ⟨box, caption, hbox, ?_, hcontained⟩
  rw [← hid]
  exact Assembly.keyed_lookup_eq Prod.fst _ (execution.scene_caption_owner_keys_nodup hwf)
    caption hmember

theorem applyTitles_box_caption_emission
    (P : Params) (inp : Input) (boxes : List Box) (routes : List Route)
    (lines : List (List Measure.Line)) (labels : List SceneLabel)
    (titles : List (String × Rect))
    {box : Box} (hbox : box ∈ boxes) (hrole : box.role = "group")
    {caption : String × Rect}
    (hselector : titles.find? (fun title => title.1 == box.id) = some caption) :
    ∃ (group : Group) (text : SceneText),
      group ∈ applyTitles titles (sceneItems P inp boxes routes lines labels) ∧
      group.role = .group ∧ group.owner = box.id ∧
      Primitive.text text ∈ group.items ∧ text.rect = caption.2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hbox
  let raw : Group := ⟨.group, box.id, groupItems P box.rect (lines.getD j [])⟩
  have hrawList : raw ∈
      ((boxes.zipIdx.filter fun q => q.1.role == "group").map fun q =>
        (⟨.group, q.1.id, groupItems P q.1.rect (lines.getD q.2 [])⟩ : Group)) := by
    apply List.mem_map.mpr
    refine ⟨(box, j), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · exact List.mk_mem_zipIdx_iff_getElem?.mpr hj
    · simp [hrole]
  have hraw : raw ∈ sceneItems P inp boxes routes lines labels := by
    simp only [sceneItems, List.mem_append, hrawList, true_or]
  let installed : Group := { raw with items := raw.items.map fun item =>
    match item with
    | .text text => .text { text with rect := caption.2 }
    | _ => item }
  have hemitted : installed ∈ applyTitles titles (sceneItems P inp boxes routes lines labels) := by
    unfold applyTitles
    apply List.mem_map.mpr
    refine ⟨raw, hraw, ?_⟩
    have hselected : titles.find? (fun title => title.1 == raw.owner) = some caption := by
      simpa only [raw] using hselector
    rw [hselected]
    rfl
  let text : SceneText := {
    rect := caption.2, role := .label, size := 14, align := .middle, style := "text"
    lines := (lines.getD j []).map fun line => [⟨String.ofList line.text, false, false⟩] }
  refine ⟨installed, text, hemitted, rfl, rfl, ?_, rfl⟩
  simp [installed, raw, groupItems, text]

theorem SceneExecution.installed_group_caption_containment
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hgroup : source.role = .group)
    {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = -2) :
    ∃ (box : Box) (group : Group) (text : SceneText),
      res.scene.layoutDump.box? source.id = some box ∧
      group ∈ res.scene.items ∧ group.role = .group ∧ group.owner = source.id ∧
      Primitive.text text ∈ group.items ∧ box.rect.Contained text.rect := by
  let captions := execution.packedAcc.titles.filterMap (fun stored => do
    let owner ← inp.boxes[stored.1]?
    let textLines := execution.lines.getD stored.1 []
    let width := textLines.foldl (fun value line => max value line.width) 0
    let height := (max 1 textLines.length : Int) * execution.params.lineH
    let size := match o.direction with
      | .LR | .RL => Size.mk height width
      | .TB | .BT => Size.mk width height
    pure (owner.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        { stored.2 with w := size.w, h := size.h })))
  obtain ⟨box, caption, hbox, hselector, hcontained⟩ :=
    execution.scene_caption_selector_containment hwf hsource hnode hborder
  change captions.find? (fun title => title.1 == source.id) = some caption at hselector
  have hlookup := execution.source_box_lookup_of_box_ids_nodup
    (Model.boxIds_nodup hwf) hsource
  have hboxeq := Option.some.inj (hbox.symm.trans hlookup)
  have hid : box.id = source.id := by rw [hboxeq]
  have hrole : box.role = "group" := by rw [hboxeq, hgroup]; rfl
  have hboxmem : box ∈ res.scene.boxes := List.mem_of_find?_eq_some hbox
  have hitems : res.scene.items =
      applyTitles captions (sceneItems execution.params inp res.scene.boxes res.scene.routes
        execution.lines res.scene.labels) := by
    rw [execution.scene_eq]
    simp only [sceneOf, execution.straight_titles, execution.straight_canvasH] <;> rfl
  obtain ⟨installed, text, hemitted, hgroupRole, howner, htext, hrect⟩ :=
    applyTitles_box_caption_emission execution.params inp res.scene.boxes res.scene.routes
      execution.lines res.scene.labels captions hboxmem hrole
      (by simpa only [hid] using hselector)
  refine ⟨box, installed, text, hbox, ?_, hgroupRole, ?_, htext, ?_⟩
  · rw [hitems]
    exact hemitted
  · exact howner.trans hid
  · rw [hrect]
    exact hcontained

theorem SceneExecution.nonfixed_group_caption_containment
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hgroup : source.role = .group)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false) :
    ∃ (box : Box) (group : Group) (text : SceneText),
      res.scene.layoutDump.box? source.id = some box ∧
      group ∈ res.scene.items ∧ group.role = .group ∧ group.owner = source.id ∧
      Primitive.text text ∈ group.items ∧ box.rect.Contained text.rect := by
  obtain ⟨nodes, edges, titles, hprepared, hlength, _⟩ :=
    measuredGraph_prepared_source execution.graph_eq
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    simp only [boxLines] at h
    calc execution.lines.length = (inp.boxes.zipIdx).length := (mapM_getElem? _ _ _ h).1
         _ = inp.boxes.length := List.length_zipIdx
  have hi : key < nodes.length := by
    rw [hlength, hlines]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hpreparedSource :
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[key]? = some source := by
    simp [List.getElem?_map, hsource, hfixed]
  have hrecord := Compound.prepare_group_title_record
    (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)
    execution.params.clusterPad titles
    { nodes := nodes, edges := edges, slot := execution.params.slot }
    hi hpreparedSource hgroup
  rw [← hprepared] at hrecord
  exact execution.installed_group_caption_containment hwf hsource hgroup hrecord rfl

theorem layout_nonfixed_group_caption_containment
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (_hlimits : WithinLimits (inputModel inp o))
    (hsuccess : layout inp o = .ok res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hgroup : source.role = .group)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false) :
    ∃ (box : Box) (group : Group) (text : SceneText),
      res.scene.layoutDump.box? source.id = some box ∧
      group ∈ res.scene.items ∧ group.role = .group ∧ group.owner = source.id ∧
      Primitive.text text ∈ group.items ∧ box.rect.Contained text.rect := by
  let execution := Classical.choice (layout_sceneExecution hsuccess)
  exact execution.nonfixed_group_caption_containment hwf hsource hgroup hfixed

theorem applyTitles_group_caption_record
    (P : Params) (inp : Input) (boxes : List Box) (routes : List Route)
    (lines : List (List Measure.Line)) (labels : List SceneLabel)
    (titles : List (String × Rect))
    {group : Group}
    (hgroup : group ∈ applyTitles titles (sceneItems P inp boxes routes lines labels))
    (hrole : group.role = .group) :
    ∃ (frame : Rect) (paint : Paint) (text : SceneText),
      group.items = [Primitive.rect frame paint, Primitive.text text] ∧
      (group.owner, text.rect) ∈
        groupTitles (applyTitles titles (sceneItems P inp boxes routes lines labels)) := by
  have hshape : ∃ (frame : Rect) (paint : Paint) (text : SceneText),
      group.items = [Primitive.rect frame paint, Primitive.text text] := by
    unfold applyTitles at hgroup
    obtain ⟨raw, hraw, heq⟩ := List.mem_map.mp hgroup
    have hrawRole : raw.role = .group := by
      have he := congrArg Group.role heq
      cases hf : titles.find? (fun title => title.1 == raw.owner) <;>
        simp only [hf] at he <;> exact he.trans hrole
    have hsource : ∃ (box : Box) (index : Nat),
        raw = (⟨.group, box.id, groupItems P box.rect (lines.getD index [])⟩ : Group) := by
      unfold sceneItems at hraw
      rcases List.mem_append.mp hraw with hfirst | hnodes
      · rcases List.mem_append.mp hfirst with hboxes | hroutes
        · obtain ⟨q, _, hq⟩ := List.mem_map.mp hboxes
          exact ⟨q.1, q.2, hq.symm⟩
        · obtain ⟨q, _, hq⟩ := List.mem_map.mp hroutes
          rw [← hq] at hrawRole
          contradiction
      · obtain ⟨q, _, hq⟩ := List.mem_map.mp hnodes
        rw [← hq] at hrawRole
        contradiction
    obtain ⟨box, index, hrawEq⟩ := hsource
    cases hf : titles.find? (fun title => title.1 == raw.owner) with
    | none =>
      simp only [hf] at heq
      rw [← heq, hrawEq]
      exact ⟨_, _, _, rfl⟩
    | some selected =>
      simp only [hf] at heq
      rw [← heq, hrawEq]
      exact ⟨_, _, _, rfl⟩
  obtain ⟨frame, paint, text, hitems⟩ := hshape
  refine ⟨frame, paint, text, hitems, ?_⟩
  unfold groupTitles
  apply List.mem_filterMap.mpr
  refine ⟨group, hgroup, ?_⟩
  simp [hrole, hitems]

theorem SceneExecution.fixed_source_box_minimum_dimensions_with_role
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) = some entry) :
    ∃ box : Box,
      res.scene.layoutDump.box? source.id = some box ∧
      box.role = source.role.id ∧ entry.2.w ≤ box.rect.w ∧ entry.2.h ≤ box.rect.h := by
  have hlines := execution.lines_eq
  unfold boxLines at hlines
  obtain ⟨_, hlineLookup⟩ := mapM_getElem? _ _ _ hlines
  obtain ⟨lines, _, hline⟩ := hlineLookup key (source, key)
    (by simp only [List.getElem?_zipIdx, hsource, Option.map_some, Nat.zero_add])
  obtain ⟨node, hnode, _, hborder, hw, hh⟩ :=
    measuredGraph_fixed_node_dims execution.graph_eq hline hsource hfixed
  obtain ⟨rect, hrect⟩ :=
    execution.packed_rect_exists (List.getElem?_eq_some_iff.mp hsource).1
  have hminimum := execution.packed_rect_minimum_dims_of_coverage
    execution.parts_coverage hnode hborder hrect
  have hget : execution.packedAcc.rects.getD key default = rect := by
    obtain ⟨hi, heq⟩ := Array.getElem?_eq_some_iff.mp hrect
    simpa [Array.getD, hi] using heq
  have hbox := execution.source_box_lookup_of_box_ids_nodup hids hsource
  rw [hget] at hbox
  refine ⟨Box.mk source.id source.role.id
    (shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH rect))
    source.parent source.exclusive, hbox, rfl, ?_, ?_⟩
  all_goals
    cases hd : o.direction <;>
      simp only [hd, shiftRect, orientRect] at hw hh ⊢ <;> omega

theorem SceneExecution.fixed_source_box_minimum_dimensions
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) = some entry) :
    ∃ box : Box,
      res.scene.layoutDump.box? source.id = some box ∧
      entry.2.w ≤ box.rect.w ∧ entry.2.h ≤ box.rect.h := by
  obtain ⟨box, hbox, _, hw, hh⟩ :=
    execution.fixed_source_box_minimum_dimensions_with_role hids hsource hfixed
  exact ⟨box, hbox, hw, hh⟩

theorem layoutRecursive_fixed_source_box_minimum_dimensions_with_role
    (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (hids : (inp.boxes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hsuccess : layoutRecursive fuel inp o = .ok res)
    {source : ModelBox} (hsource : source ∈ inp.boxes)
    {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) = some entry) :
    ∃ box : Box,
      res.scene.layoutDump.box? source.id = some box ∧
      box.role = source.role.id ∧ entry.2.w ≤ box.rect.w ∧ entry.2.h ≤ box.rect.h := by
  induction fuel generalizing inp o res source with
  | zero =>
    obtain ⟨key, hkey⟩ := List.mem_iff_getElem?.mp hsource
    let execution := Classical.choice (layout_sceneExecution hsuccess)
    exact execution.fixed_source_box_minimum_dimensions_with_role hids hkey hfixed
  | succ fuel ih =>
    cases hselected : inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) with
    | none =>
      have hflat : layout inp o = .ok res := by
        rcases layoutRecursive_succ hsuccess with ⟨_, hflat⟩ | ⟨_, hfound, _⟩
        · exact hflat
        · rw [hselected] at hfound
          contradiction
      obtain ⟨key, hkey⟩ := List.mem_iff_getElem?.mp hsource
      let execution := Classical.choice (layout_sceneExecution hflat)
      exact execution.fixed_source_box_minimum_dimensions_with_role hids hkey hfixed
    | some selected =>
      obtain ⟨P, metric, child, titleLines, parent, dx, dy,
        _, _, hchild, _, hparent, _, hchildLookup, hparentLookup, _⟩ :=
        layoutRecursive_embedding_box_lookup_sources hids hcovered hselected hsuccess
      let childInput := selectInput inp
        (fun box => Compound.inside inp.boxes selected.id box.id) selected.id
      let baseParent := selectInput inp
        (fun box => !Compound.inside inp.boxes selected.id box.id)
      let size := childFrameSize selected.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩
      let parentInput : Input := { baseParent with
        fixedSizes := baseParent.fixedSizes ++ [(selected.id, size)]
        fixedChildren := baseParent.fixedChildren ++ [(selected.id, child.scene)]
        fixedAreas := baseParent.fixedAreas ++ [(selected.id, child.itemArea)] }
      change layoutRecursive fuel childInput
        { o with direction := directionOf selected.direction } = .ok child at hchild
      change layoutRecursive fuel parentInput o = .ok parent at hparent
      by_cases hins : Compound.inside inp.boxes selected.id source.id = true
      · let next := if source.parent == selected.id then { source with parent := "" } else source
        obtain ⟨sourceIndex, hsourceIndex⟩ := List.mem_iff_getElem?.mp hsource
        have hnext : next ∈ childInput.boxes := by
          change next ∈ ((inp.boxes.zipIdx.filter fun q =>
            Compound.inside inp.boxes selected.id q.1.id).map fun q =>
              if q.1.parent == selected.id then { q.1 with parent := "" } else q.1)
          exact List.mem_map.mpr ⟨(source, sourceIndex),
            List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hsourceIndex, hins⟩, rfl⟩
        have hid : next.id = source.id := by dsimp only [next]; split <;> rfl
        have hnextRole : next.role = source.role := by dsimp only [next]; split <;> rfl
        have hchildIds : (childInput.boxes.map (·.id)).Nodup := by
          rw [selectInput_box_ids]
          exact List.Nodup.sublist ((List.filter_sublist).map _) hids
        have hnextFixed :
            childInput.fixedSizes.find? (fun fixed => fixed.1 == next.id) = some entry := by
          change inp.fixedSizes.find? (fun fixed => fixed.1 == next.id) = some entry
          rw [hid]
          exact hfixed
        obtain ⟨box, hbox, hrole, hw, hh⟩ :=
          ih hchildIds (selectInput_routesCovered inp _ selected.id) hchild hnext hnextFixed
        have hboxId : box.id = next.id := by
          change child.scene.boxes.find? (fun box => box.id == next.id) = some box at hbox
          simpa using List.find?_some hbox
        have htransport := hchildLookup box (by simpa only [hboxId] using hbox)
        rw [hboxId, hid] at htransport
        refine ⟨{ box with rect := shiftRect dx dy box.rect, parent := if box.parent == "" then selected.id else box.parent }, ?_, ?_, ?_, ?_⟩
        · simpa only [hboxId, hid] using htransport
        · simpa only [hnextRole] using hrole
        · simpa only [shiftRect] using hw
        · simpa only [shiftRect] using hh
      · have hout : (!Compound.inside inp.boxes selected.id source.id) = true := by
          cases hi : Compound.inside inp.boxes selected.id source.id <;> simp_all
        let next := if source.parent == "" then { source with parent := "" } else source
        obtain ⟨sourceIndex, hsourceIndex⟩ := List.mem_iff_getElem?.mp hsource
        have hnext : next ∈ parentInput.boxes := by
          change next ∈ ((inp.boxes.zipIdx.filter fun q =>
            !Compound.inside inp.boxes selected.id q.1.id).map fun q =>
              if q.1.parent == "" then { q.1 with parent := "" } else q.1)
          exact List.mem_map.mpr ⟨(source, sourceIndex),
            List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hsourceIndex, hout⟩, rfl⟩
        have hid : next.id = source.id := by dsimp only [next]; split <;> rfl
        have hnextRole : next.role = source.role := by dsimp only [next]; split <;> rfl
        have hparentIds : (parentInput.boxes.map (·.id)).Nodup := by
          change (baseParent.boxes.map (·.id)).Nodup
          rw [selectInput_box_ids]
          exact List.Nodup.sublist ((List.filter_sublist).map _) hids
        have hnextFixed :
            parentInput.fixedSizes.find? (fun fixed => fixed.1 == next.id) = some entry := by
          change (inp.fixedSizes ++ [(selected.id, size)]).find?
            (fun fixed => fixed.1 == next.id) = some entry
          simp [List.find?_append, hid, hfixed]
        have hparentCovered : RoutesCovered parentInput := by
          change RoutesCovered baseParent
          exact selectInput_routesCovered inp
            (fun box => !Compound.inside inp.boxes selected.id box.id) ""
        obtain ⟨box, hbox, hrole, hw, hh⟩ :=
          ih hparentIds hparentCovered hparent hnext hnextFixed
        have hboxId : box.id = next.id := by
          change parent.scene.boxes.find? (fun box => box.id == next.id) = some box at hbox
          simpa using List.find?_some hbox
        have htransport := hparentLookup box (by simpa only [hboxId] using hbox)
        rw [hboxId, hid] at htransport
        exact ⟨box, htransport, by simpa only [hnextRole] using hrole, hw, hh⟩

theorem layoutRecursive_fixed_source_box_minimum_dimensions
    (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
    (hids : (inp.boxes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hsuccess : layoutRecursive fuel inp o = .ok res)
    {source : ModelBox} (hsource : source ∈ inp.boxes)
    {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) = some entry) :
    ∃ box : Box,
      res.scene.layoutDump.box? source.id = some box ∧
      entry.2.w ≤ box.rect.w ∧ entry.2.h ≤ box.rect.h := by
  obtain ⟨box, hbox, _, hw, hh⟩ :=
    layoutRecursive_fixed_source_box_minimum_dimensions_with_role
      fuel hids hcovered hsuccess hsource hfixed
  exact ⟨box, hbox, hw, hh⟩

theorem layoutRecursive_selected_caption_containment
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    (hids : (inp.boxes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hgroup : inp.boxes.find? (fun box =>
      Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hsuccess : layoutRecursive (fuel + 1) inp o = .ok res) :
    ∃ (P : Params) (metric : Measure.Metric) (titleLines : List Measure.Line) (frame : Box),
      checkedParams o.profile inp.kind = .ok P ∧ metricOf o.profile o.fontFamily = .ok metric ∧
      StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
            .ok titleLines ∧
      res.scene.layoutDump.box? group.id = some frame ∧
      frame.rect.Contained (childTitleRect group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH) frame.rect) ∧
      ∃ (installed : Group) (text : SceneText),
        installed ∈ res.scene.items ∧ installed.role = .group ∧ installed.owner = group.id ∧
        Primitive.text text ∈ installed.items ∧
        text.rect = childTitleRect group.direction P.clusterPad
          (titleLines.foldl (fun width line => max width line.width) 0)
          ((max 1 titleLines.length : Int) * P.lineH) frame.rect := by
  obtain ⟨P, metric, child, titleLines, parent, frame, lines, dx, dy,
    hP, hm, hchild, hwrap, hparent, hexpand, hframe, hlines,
    hdx, hdy, hchildLookup, hparentLookup, hroutes, hitems⟩ :=
    layoutRecursive_embedding_assembly_sources hids hcovered hgroup hsuccess
  let width := titleLines.foldl (fun width line => max width line.width) 0
  let height := (max 1 titleLines.length : Int) * P.lineH
  let size := childFrameSize group.direction P.clusterPad width height
    ⟨child.scene.canvas.w - 2 * P.canvasMargin, child.scene.canvas.h - 2 * P.canvasMargin⟩
  let baseParent := selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)
  let parentInput : Input := { baseParent with
    fixedSizes := baseParent.fixedSizes ++ [(group.id, size)]
    fixedChildren := baseParent.fixedChildren ++ [(group.id, child.scene)]
    fixedAreas := baseParent.fixedAreas ++ [(group.id, child.itemArea)] }
  change layoutRecursive fuel parentInput o = .ok parent at hparent
  have hparentIds : (parentInput.boxes.map (·.id)).Nodup := by
    change (baseParent.boxes.map (·.id)).Nodup
    rw [selectInput_box_ids]
    exact List.Nodup.sublist ((List.filter_sublist).map _) hids
  have hparentCovered : RoutesCovered parentInput := by
    change RoutesCovered baseParent
    exact selectInput_routesCovered inp
      (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hparentOutputIds := (layoutRecursive_ids (fun _ _ _ h => layout_ids h)
    fuel parentInput o parent hparentCovered hparent).1
  have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
  have hparentSourceId : group.id ∈ parentInput.boxes.map (·.id) := by
    rw [← hparentOutputIds, ← hframeId]
    exact List.mem_map.mpr ⟨frame, List.mem_of_find?_eq_some hframe, rfl⟩
  obtain ⟨source, hsource, hsourceId⟩ := List.mem_map.mp hparentSourceId
  have hsourceBase : source ∈ baseParent.boxes := hsource
  obtain ⟨original, horiginal, _, hsourceEq⟩ :=
    selectInput_box_source inp (fun box => !Compound.inside inp.boxes group.id box.id)
      "" source hsourceBase
  have hsourceOriginalId : source.id = original.id := by
    rw [hsourceEq]
    split <;> rfl
  have horiginalId : original.id = group.id := hsourceOriginalId.symm.trans hsourceId
  have horiginalLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes hids original horiginal
  have hgroupLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes hids group
    (List.mem_of_find?_eq_some hgroup)
  rw [horiginalId] at horiginalLookup
  have horiginalEq : original = group :=
    Option.some.inj (horiginalLookup.symm.trans hgroupLookup)
  have hsourceRole : source.role = group.role := by
    rw [hsourceEq]
    split <;> simp only [horiginalEq]
  have hgroupRole : group.role = .group := by
    have hs := List.find?_some hgroup
    simp only [Bool.and_eq_true] at hs
    have hi := hs.1
    unfold Compound.independent at hi
    simp only [Bool.and_eq_true] at hi
    exact beq_iff_eq.mp hi.1.1
  have hnotfixed : inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
    have hs := List.find?_some hgroup
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
    exact hs.2
  have hnone : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hnotfixed)
  have hfixed : parentInput.fixedSizes.find? (fun fixed => fixed.1 == source.id) =
      some (group.id, size) := by
    change (inp.fixedSizes ++ [(group.id, size)]).find?
      (fun fixed => fixed.1 == source.id) = some (group.id, size)
    simp [List.find?_append, hsourceId, hnone]
  obtain ⟨actual, hactual, hactualRole, hw, hh⟩ :=
    layoutRecursive_fixed_source_box_minimum_dimensions_with_role fuel hparentIds hparentCovered
      hparent hsource hfixed
  rw [hsourceId] at hactual
  have hactualEq : actual = frame := Option.some.inj (hactual.symm.trans hframe)
  subst actual
  have hframeRole : frame.role = "group" := by
    rw [hactualRole, hsourceRole, hgroupRole]
    rfl
  let origin : FrameOrigin o group.id size := {
    source := inp, group := group, fuel := fuel, params := P, metric := metric,
    child := child, titleLines := titleLines, group_found := hgroup, id_eq := rfl,
    checked := hP, metric_eq := hm, child_eq := hchild, title_eq := hwrap,
    size_eq := by simp only [size, width, height, checkedParams_canvasMargin hP] }
  have hfit := origin.title_fit
  change width + 2 * P.clusterPad ≤ size.w ∧ height + 2 * P.clusterPad ≤ size.h at hfit
  have hwidth : width + 2 * P.clusterPad ≤ frame.rect.w := Int.le_trans hfit.1 hw
  have hheight : height + 2 * P.clusterPad ≤ frame.rect.h := Int.le_trans hfit.2 hh
  have hpad := checkedParams_clusterPad_nonneg hP
  have hlookup : res.scene.layoutDump.box? group.id = some frame := by
    have hparentFrame : parent.scene.layoutDump.box? frame.id = some frame := by
      change parent.scene.boxes.find? (fun box => box.id == frame.id) = some frame
      simpa only [hframeId] using hframe
    have h := hparentLookup frame hparentFrame
    simpa only [hframeId] using h
  have hcaptionFit : frame.rect.Contained
      (childTitleRect group.direction P.clusterPad width height frame.rect) := by
    unfold childTitleRect
    split <;> unfold Rect.Contained <;> dsimp only <;>
      simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] <;> omega
  let caption := childTitleRect group.direction P.clusterPad width height frame.rect
  let titles := (group.id, caption) ::
    ((groupTitles child.scene.items).map (fun title => (title.1, shiftRect dx dy title.2)) ++
      groupTitles parent.scene.items)
  have hframeMem : frame ∈ res.scene.boxes := List.mem_of_find?_eq_some hlookup
  have hselector : titles.find? (fun title => title.1 == frame.id) =
      some (group.id, caption) := by
    simp [titles, hframeId]
  obtain ⟨installed, text, hemitted, hrole, howner, htext, hrect⟩ :=
    applyTitles_box_caption_emission P inp res.scene.boxes res.scene.routes lines
      res.scene.labels titles hframeMem hframeRole hselector
  refine ⟨P, metric, titleLines, frame, hP, hm, hwrap, hlookup, hcaptionFit,
    installed, text, ?_, hrole, howner.trans hframeId, htext, hrect⟩
  rw [hitems]
  exact hemitted

theorem layoutRecursive_selected_caption_frame_containment
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult} {group : ModelBox}
    (hids : (inp.boxes.map (·.id)).Nodup) (hcovered : RoutesCovered inp)
    (hgroup : inp.boxes.find? (fun box =>
      Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hsuccess : layoutRecursive (fuel + 1) inp o = .ok res) :
    ∃ (P : Params) (metric : Measure.Metric) (titleLines : List Measure.Line) (frame : Box),
      checkedParams o.profile inp.kind = .ok P ∧ metricOf o.profile o.fontFamily = .ok metric ∧
      StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
            .ok titleLines ∧
      res.scene.layoutDump.box? group.id = some frame ∧
      frame.rect.Contained (childTitleRect group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH) frame.rect) := by
  obtain ⟨P, metric, titleLines, frame, hP, hm, hwrap, hlookup, hfit, _⟩ :=
    layoutRecursive_selected_caption_containment hids hcovered hgroup hsuccess
  exact ⟨P, metric, titleLines, frame, hP, hm, hwrap, hlookup, hfit⟩

end Elegant.Layered.PipelineImpl

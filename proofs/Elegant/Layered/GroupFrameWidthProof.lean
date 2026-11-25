import Elegant.Layered.CaptionWidthFacts
import Elegant.Layered.BracketInsidePremisesProof
import Elegant.Layered.SideMarkerPathsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open Elegant Layered CoordsImpl

theorem componentRun_group_frame_cross_fit {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {i : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[i]? = some node)
    (hborder : node.border = -2) :
    2 * P.clusterPad ≤ (frameRect P (componentCandidate graph comp candidate) run i).w := by
  obtain ⟨title, htitle, _⟩ := componentRun_group_title_width_source hrun hnode hborder
  obtain ⟨ord, left, right, horder, hlayers, hleft, hright, bracket⟩ :=
    componentRun_group_title_bracket hgraph hcomp hrun hnode hborder htitle rfl rfl
  obtain ⟨li, ti, ri, hli, _, hri, hlt, htr⟩ := bracket.positions
  let layer := ord.layers.getD (OrderImpl.lay run.coordinateProper title) []
  have hlayer : layer ∈ run.layers := hlayers ▸ bracket.layer_mem
  have hn : ri < layer.length := (List.getElem?_eq_some_iff.mp hri).1
  have hfirstPos : li + 1 < layer.length := by omega
  have hlastPos : ri - 1 < layer.length := by omega
  have hfirst : layer[li + 1]? = some layer[li + 1] := List.getElem?_eq_getElem hfirstPos
  have hlast : layer[ri - 1]? = some layer[ri - 1] := List.getElem?_eq_getElem hlastPos
  have hOrd : OrderImpl.order run.coordinateProper orderOptions = .ok run.layers := by
    simp [OrderImpl.order, horder, hlayers]
  have hInfix := OrderImpl.order_clusters_contiguous run.coordinateProper orderOptions
    run.layers hOrd layer hlayer node.clusterPath
  have hNd : layer.Nodup := OrderImpl.layer_nodup
    (OrderImpl.orderWithBudget_spec _ _ _ horder).1 bracket.rank_lt
  have hlPath : OrderImpl.nodePath run.coordinateProper left = node.clusterPath :=
    by simpa [OrderImpl.borderLeft, titleF, hborder] using
      OrderImpl.nodePath_of_nondummy hleft rfl
  have hrPath : OrderImpl.nodePath run.coordinateProper right = node.clusterPath :=
    by simpa [OrderImpl.borderRight, titleF, hborder] using
      OrderImpl.nodePath_of_nondummy hright rfl
  have hls : left ∈ layer.filter (fun v => node.clusterPath.isPrefixOf
      (OrderImpl.nodePath run.coordinateProper v)) := by
    exact List.mem_filter.mpr ⟨List.mem_of_getElem? hli,
      by rw [hlPath]; exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl⟩
  have hrs : right ∈ layer.filter (fun v => node.clusterPath.isPrefixOf
      (OrderImpl.nodePath run.coordinateProper v)) := by
    exact List.mem_filter.mpr ⟨List.mem_of_getElem? hri,
      by rw [hrPath]; exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl⟩
  have hInside {pos v : Nat} (hv : layer[pos]? = some v) (hla : li < pos) (hra : pos < ri) :
      node.clusterPath <+: OrderImpl.nodePath run.coordinateProper v :=
    List.isPrefixOf_iff_prefix.mp (List.mem_filter.mp
      (mem_of_between_infix
        hNd hInfix hls hrs hli hv hri hla hra)).2
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRun_spec hrun
  have hInRange := (crossCoordsClusterWith_spec hcross).2.2.1
  have hWell := componentRun_coordinate_bordersWellFormed hgraph hcomp hrun
  obtain ⟨_, _, hGraphNode⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨_, _, _, _, hPath⟩ := measuredGraph_group_origin hgraph hGraphNode hborder
  have hDecl : node.clusterPath.getLast? = some node.decl := by simp [hPath]
  have hMember {pos v : Nat} (hv : layer[pos]? = some v) (hla : li < pos) (hra : pos < ri) :
      ∃ n, run.coordinateProper.nodes[v]? = some n ∧ n.node.clusterPath.contains node.decl = true := by
    have hbound := CoordsImpl.layers_mem_lt hInRange hlayer hv
    let n := run.coordinateProper.nodes[v]
    have hn : run.coordinateProper.nodes[v]? = some n := List.getElem?_eq_getElem hbound
    have hPathV : OrderImpl.nodePath run.coordinateProper v = n.node.clusterPath := by
      cases hd : n.dummy with
      | false => exact OrderImpl.nodePath_of_nondummy hn hd
      | true => exact plainNodePathEq hrun hn (hWell.2.2 _ _ hn hd)
    have hp := hInside hv hla hra
    rw [hPathV] at hp
    exact ⟨n, hn, List.contains_iff_mem.mpr (hp.sublist.subset (List.mem_of_getLast? hDecl))⟩
  obtain ⟨_, hnfirst, hfirstMember⟩ := hMember hfirst (by omega) (by omega)
  obtain ⟨_, hnlast, hlastMember⟩ := hMember hlast (by omega) (by omega)
  have hleftMember : borderMember run.coordinateProper left layer[li + 1] = true := by
    simp [borderMember, hleft, hnfirst, OrderImpl.borderLeft, titleF, hborder,
      hDecl, List.contains_iff_mem.mp hfirstMember]
  have hrightMember : borderMember run.coordinateProper layer[ri - 1] right = true := by
    simp [borderMember, hright, hnlast, OrderImpl.borderRight, titleF, hborder,
      hDecl, List.contains_iff_mem.mp hlastMember]
  have hgroup : ((componentCandidate graph comp candidate).nodes.getD i default).border = -2 := by
    simp [List.getD_eq_getElem?_getD, hnode, hborder]
  exact componentRun_border_hull_width_of_layer_configuration hrun hgroup hlayer
    (by omega) hli hfirst hlast (by simpa only [show ri - 1 + 1 = ri by omega] using hri)
    hleftMember hrightMember hleft hright rfl rfl
    (by simpa [OrderImpl.borderLeft, titleF, hborder, List.getD_eq_getElem?_getD, hnode] using hDecl)
    (by simpa [OrderImpl.borderRight, titleF, hborder, List.getD_eq_getElem?_getD, hnode] using hDecl)

private theorem SceneExecution.component_group_cross_fit
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {i key : Nat} (hkey : part.1[i]? = some key)
    {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = -2)
    {rect : Rect} (hrect : part.2.rects[i]? = some rect) :
    2 * execution.params.clusterPad ≤ rect.w := by
  obtain ⟨index, run, _, _, hcomp, hrun, hrects⟩ := execution.part_frame_rects hpart
  have hlocal := candidate_node_of_part_key (index := index) hkey hnode
  have hplaced := hrects (List.getElem?_eq_some_iff.mp hlocal).1
  rw [hrect] at hplaced
  rw [Option.some.inj hplaced]
  exact componentRun_group_frame_cross_fit execution.graph_eq hcomp hrun hlocal hborder

theorem SceneExecution.nonfixed_group_output_dimensions
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {index : Nat} {box : Box} (hbox : res.scene.boxes[index]? = some box)
    {source : ModelBox} (hsource : inp.boxes[index]? = some source)
    (hgroup : source.role = .group)
    (hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false) :
    match o.direction with
    | .LR | .RL =>
      (execution.lines.getD index []).foldl (fun w line => max w line.width) 0 +
        execution.params.clusterPad ≤ box.rect.w ∧
        2 * execution.params.clusterPad ≤ box.rect.h
    | .TB | .BT =>
      2 * execution.params.clusterPad ≤ box.rect.w ∧
      (max 1 (execution.lines.getD index []).length : Int) * execution.params.lineH +
        execution.params.clusterPad ≤ box.rect.h := by
  obtain ⟨node, hnode, hborder, _⟩ := execution.nonfixed_group_graph_node hsource hgroup hfixed
  let caption : Int :=
    (match o.direction with
      | .LR | .RL =>
        (execution.lines.getD index []).foldl (fun w line => max w line.width) 0
      | .TB | .BT =>
        (max 1 (execution.lines.getD index []).length : Int) * execution.params.lineH) +
      execution.params.clusterPad
  obtain ⟨rect, hrect, hwidth, hheight⟩ := execution.packed_key_rect_minimum_dims
    (List.getElem?_eq_some_iff.mp hsource).1 ⟨2 * execution.params.clusterPad, caption⟩ (by
      intro part hpart _ placed hk hp
      exact ⟨execution.component_group_cross_fit hpart hk hnode hborder hp,
        execution.component_group_caption_rank_fit hpart hk hnode hborder hsource hp⟩)
  obtain ⟨_, _, hboxeq⟩ := execution.box_index_origin hbox
  have hget : execution.packedAcc.rects.getD index default = rect := by
    obtain ⟨hi, heq⟩ := Array.getElem?_eq_some_iff.mp hrect
    simpa [Array.getD, hi] using heq
  rw [hboxeq, hget]
  cases hd : o.direction <;> simp only [hd, orientRect, shiftRect, caption] at hheight ⊢
  · exact ⟨hwidth, hheight⟩
  · exact ⟨hwidth, hheight⟩
  · exact ⟨hheight, hwidth⟩
  · exact ⟨hheight, hwidth⟩

end Elegant.Layered.PipelineImpl

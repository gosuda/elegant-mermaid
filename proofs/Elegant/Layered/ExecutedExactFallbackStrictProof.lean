import Elegant.Layered.ExactBorderSpanRunFactsProof
import Elegant.Layered.ExactCaptionAncestorLinkVerticalProof
import Elegant.Layered.ExactParentInComponent
import Elegant.Layered.FallbackOwnerFrameProof
import Elegant.Layered.LabelsClearance

set_option autoImplicit false

namespace Elegant.Layered
namespace PipelineImpl

private theorem exactInputNode {exactIds : List String} {inp : Input} {o : Options}
    (execution : ExactFramePrefix exactIds inp o)
    {key : Nat} {box : ModelBox} (hbox : inp.boxes[key]? = some box) :
    ∃ node, execution.graph.nodes[key]? = some node ∧ node.decl = key ∧
      if box.role = .group ∧ inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false then
        node.border = -2 ∧ node.clusterPath = Compound.path inp.boxes box ++ [key]
      else
        node.border = 0 ∧ node.clusterPath = Compound.path inp.boxes box := by
  let demote := fun source : ModelBox =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
      { source with role := .node } else source
  obtain ⟨_, hdemoted, hpath⟩ := fixedSizes_path_index inp hbox
  have hdemoteGroup : (demote box).role = .group ↔
      box.role = .group ∧ inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false := by
    cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) <;> simp [demote, hf]
  have hlines : key < execution.lines.length := by
    rw [execution.lines_length]
    exact (List.getElem?_eq_some_iff.mp hbox).1
  by_cases hgroup : box.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false
  · obtain ⟨top, _, htop, _, hborder, _, hdecl, _, hcluster, _, _, _⟩ :=
      measuredGraph_paired_markers execution.graph0_eq hlines hdemoted
        (hdemoteGroup.mpr hgroup)
    obtain ⟨node, hnode, hb, hp, hd⟩ := exactGraph_node_key execution.graph_eq htop
    refine ⟨node, hnode, hd.trans hdecl, ?_⟩
    simp only [ite_eq_left hgroup]
    exact ⟨hb.trans hborder, hp.trans (hcluster.trans (congrArg (· ++ [key]) hpath))⟩
  · obtain ⟨nodes, edges, titles, hprepared, hlength, hmetadata⟩ :=
      measuredGraph_prepared_source execution.graph0_eq
    have hindex : key < nodes.length := by
      rw [hlength]
      exact hlines
    have hrecord := Compound.prepare_plain_node_record (inp.boxes.map demote)
      execution.params.clusterPad titles ⟨nodes, edges, execution.params.slot⟩
      hindex hdemoted (fun hg => hgroup (hdemoteGroup.mp hg))
    dsimp only [demote] at hrecord
    rw [← hprepared] at hrecord
    have hmeta := hmetadata key nodes[key] (List.getElem?_eq_getElem hindex)
    obtain ⟨node, hnode, hb, hp, hd⟩ := exactGraph_node_key execution.graph_eq hrecord
    refine ⟨node, hnode, hd.trans hmeta.1, ?_⟩
    simp only [ite_eq_right hgroup]
    exact ⟨hb.trans hmeta.2, hp.trans hpath⟩

private theorem exactCoordinateNonproxy {P : Params} {exact : List Nat} {labeled : Proper}
    {k : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
      P.clusterBorderW).nodes[k]? = some node)
    (hreal : node.dummy = false) (hborder : ¬ (node.node.border = -2 ∨ node.node.border = 2)) :
    (coordinateGraphX P exact labeled).nodes[k]? = some node := by
  have hnot : ¬ ((node.node.border == -2 || node.node.border == 2) = true) := by
    simpa only [Bool.or_eq_true, beq_iff_eq] using hborder
  have hclear : clearF node = node := by simp [clearF, hnot]
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, clearProxyExtents_nodes, hnode,
    Option.map_some, Nat.zero_add, hclear, hreal, Bool.false_eq_true, ↓reduceIte]

private theorem exactPlainCoordinate {P : Params} {exact : List Nat} {labeled : Proper}
    {k : Nat} {member : Node} (hsource : labeled.nodes[k]? = some ⟨member, false, none, false⟩)
    (hplain : member.border = 0) :
    ∃ actual, (coordinateGraphX P exact labeled).nodes[k]? = some actual ∧
      actual.dummy = false ∧ actual.node.border = 0 ∧ actual.node.clusterPath = member.clusterPath := by
  obtain ⟨actual, hsized, hreal, hb, hp⟩ :
      ∃ actual, (sizeProperPortsX P exact labeled).nodes[k]? = some actual ∧
        actual.dummy = false ∧ actual.node.border = 0 ∧
        actual.node.clusterPath = member.clusterPath := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hsource, Option.map_some]
    split <;> exact ⟨_, rfl, rfl, hplain, rfl⟩
  have htitled : (titleReservations (sizeProperPortsX P exact labeled)).nodes[k]? =
      some actual := by
    have hk := (List.getElem?_eq_some_iff.mp hsized).1
    rw [titleReservations_nodes, List.getElem?_append_left (by simpa only [List.length_map] using hk)]
    simp [List.getElem?_map, hsized, titleF, hb]
  obtain ⟨_, hbordered, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
      P.clusterBorderW).nodes[k]? = some actual := by
    rw [hbordered, List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitled).1]
    exact htitled
  exact ⟨actual, exactCoordinateNonproxy hplaced hreal (by rw [hb]; decide), hreal, hb, hp⟩

private theorem exactStrictBandGap {P : Params} {exactIds : List String} {inp : Input}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {r s : Nat} {layer nextLayer : List Nat}
    (hrs : r < s) (hr : run.layers[r]? = some layer) (hs : run.layers[s]? = some nextLayer) :
    run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper layer < run.top.getD s 0 := by
  rw [componentRunX_eq_gen] at hrun
  obtain ⟨_, _, _, _, _, top, _, _, _, _, _, _, _, _, _, _, hry, _, hreserve, _⟩ :=
    componentRunGen_spec hrun
  obtain ⟨extra, shifts, _, hnonneg, hprefix, hshiftsLen, htops, _⟩ :=
    (runHooksShift_exact P exactIds inp cg labels).shifts _ _ _ _ _ _ hreserve
  have htopLen := (CoordsImpl.rankCoordsWith_length hry).2
  have hsLayer : s < run.layers.length := (List.getElem?_eq_some_iff.mp hs).1
  have hsTop : s < top.length := by rw [htopLen]; exact hsLayer
  have hsShift : s < shifts.length := by rw [hshiftsLen]; exact hsTop
  have hrShift : r < shifts.length := Nat.lt_trans hrs hsShift
  have hpair : shifts.Pairwise (· ≤ ·) := by
    rw [hprefix]
    exact reserveShift_prefix_pairwise extra hnonneg 0 [] (by simp) (by simp)
  have hshiftOrder : shifts.getD r 0 ≤ shifts.getD s 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hrShift, List.getElem?_eq_getElem hsShift]
    exact hpair.rel_getElem_of_lt hrShift hsShift hrs
  have hbefore := rankAxis_band_top_strict hry r s layer nextLayer hrs hr hs
  rw [htops r (Nat.lt_trans hrs hsTop), htops s hsTop]
  omega

set_option maxHeartbeats 3000000 in
private theorem exactPlainFrameStrict {exactIds : List String} {inp : Input} {o : Options}
    (execution : ExactFramePrefix exactIds inp o)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {parentPos memberPos : Nat} {parent member : Node} {path : List Nat}
    (hparent : (componentCandidate execution.graph comp candidate).nodes[parentPos]? = some parent)
    (hgroup : parent.border = -2) (hparentPath : parent.clusterPath = path ++ [parent.decl])
    (hmember : (componentCandidate execution.graph comp candidate).nodes[memberPos]? = some member)
    (hplain : member.border = 0) (hmemberPath : member.clusterPath = parent.clusterPath) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run parentPos).StrictInside
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run memberPos) := by
  let cg := componentCandidate execution.graph comp candidate
  let P := execution.params
  let exact := exactDecls exactIds inp
  let rect := Labels.rectAt run.proper run.xs run.ys
  obtain ⟨rr, labeled, bottom, hrr, hc, hk, hready, hrecords, hranks, htitle, hbottom⟩ :=
    X_group_bottom_source execution.graph0_eq execution.graph_eq hcomp hrun hparent hgroup
  obtain ⟨bottomNode, hbottomNode, hbottomBorder, hbottomPath, _, hbottomFind⟩ :=
    X_bottom_constraint_source execution.graph0_eq execution.graph_eq hk hrecords hparent hgroup hbottom
  have hrankOrder := ranked_compound_member_interval hrr
    (List.mk_mem_zipIdx_iff_getElem?.mpr hparent) hgroup hbottomFind
    (List.mk_mem_zipIdx_iff_getElem?.mpr hmember) hplain (by simp [hmemberPath, hparentPath])
  let titled := titleReservations (sizeProperPortsX P exact labeled)
  let top : ProperNode × Nat := (titleF ⟨parent, false, none, false⟩, parentPos)
  have htopPath : top.1.node.clusterPath = parent.clusterPath := (titleF_keys _).2.2.1
  have htopBorder : top.1.node.border = -2 := (titleF_keys _).2.1.trans hgroup
  have htitledPathBottom : (titled.nodes.zipIdx.find? fun entry =>
      entry.1.node.border == 2 && entry.1.node.clusterPath == top.1.node.clusterPath) =
        some bottom := by rw [htopPath]; exact hbottom
  have hrank : rankWithBudget (Compound.rankingGraph cg) = .ok rr := hrr
  have hrankPreserved : ∀ k, k < cg.nodes.length →
      rk titled.rank k = rk rr.ranks k ∧ rk run.coordinateProper.rank k = rk rr.ranks k := by
    intro k hklen
    obtain ⟨_, _, hshape, _⟩ := RankImpl.rank_spec
      (g := Compound.rankingGraph cg) (r := rr.ranks) (by simp only [RankImpl.rank, hrank])
    have hkRank : k < rr.ranks.length := by rw [hshape.1]; exact hklen
    have hr := List.getElem?_eq_getElem hkRank
    have hl := hranks k rr.ranks[k] hr
    have ht : titled.rank[k]? = some rr.ranks[k] := by
      change (labeled.rank ++ _)[k]? = some rr.ranks[k]
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]
      exact hl
    obtain ⟨_, hprefix⟩ := (coordinateGraphX_anchor_prefix P exact labeled).2
    have hpc : run.coordinateProper.rank[k]? = some rr.ranks[k] := by
      rw [← hc, hprefix, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]
      exact hl
    simp only [rk, List.getD_eq_getElem?_getD, ht, hpc, hr, Option.getD_some, and_self]
  have htRank := hrankPreserved parentPos (List.getElem?_eq_some_iff.mp hparent).1
  have hmRank := hrankPreserved memberPos (List.getElem?_eq_some_iff.mp hmember).1
  have hbRank := hrankPreserved bottom.2 (List.getElem?_eq_some_iff.mp hbottomNode).1
  have hmemberNN := rankWithBudget_rk_nonneg hrr memberPos
  let rank := (rk rr.ranks memberPos).toNat
  have hrankEq : (rank : Int) = rk rr.ranks memberPos := Int.toNat_of_nonneg hmemberNN
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    addClusterBorders_rank_pair titled P.clusterBorderW hready.2.2.2.1
      (List.mk_mem_zipIdx_iff_getElem?.mpr htitle) htopBorder htitledPathBottom
      (rank := rank)
      (by dsimp only [top, rank] at *; omega)
      (by dsimp only [rank] at *; omega)
  let leftMarker := OrderImpl.borderLeft top P.clusterBorderW
  let rightMarker := OrderImpl.borderRight top P.clusterBorderW
  have hleftNP : ¬ (leftMarker.node.border = -2 ∨ leftMarker.node.border = 2) := by
    change ¬ ((-1 : Int) = -2 ∨ (-1 : Int) = 2)
    decide
  have hrightNP : ¬ (rightMarker.node.border = -2 ∨ rightMarker.node.border = 2) := by
    change ¬ ((1 : Int) = -2 ∨ (1 : Int) = 2)
    decide
  have hleftCoord : run.coordinateProper.nodes[left]? = some leftMarker := by
    rw [← hc]
    exact exactCoordinateNonproxy hleft rfl hleftNP
  have hrightCoord : run.coordinateProper.nodes[right]? = some rightMarker := by
    rw [← hc]
    exact exactCoordinateNonproxy hright rfl hrightNP
  obtain ⟨actual, hactualCoord, hactualReal, hactualPlain, hactualPath⟩ :=
    exactPlainCoordinate (P := P) (exact := exact) (hrecords _ _ hmember) hplain
  rw [hc] at hactualCoord
  have sideLay {v : Nat}
      (hsideRank : (OrderImpl.addClusterBorders titled P.clusterBorderW).rank[v]? =
        some (rank : Int)) :
      OrderImpl.lay run.coordinateProper v = OrderImpl.lay run.coordinateProper memberPos := by
    have hv : rk run.coordinateProper.rank v = (rank : Int) := by
      rw [← hc]
      change rk (OrderImpl.addClusterBorders titled P.clusterBorderW).rank v = _
      simp only [rk, List.getD_eq_getElem?_getD, hsideRank, Option.getD_some]
    unfold OrderImpl.lay
    rw [hv, hmRank.2, hrankEq]
  have hscope : top.1.node.clusterPath = actual.node.clusterPath :=
    htopPath.trans (hmemberPath.symm.trans hactualPath.symm)
  have hleftNe : left ≠ memberPos := by
    intro h
    rw [h] at hleftCoord
    have hb := congrArg (fun nd : ProperNode => nd.node.border)
      (Option.some.inj (hleftCoord.symm.trans hactualCoord))
    change (-1 : Int) = actual.node.border at hb
    omega
  have hrightNe : right ≠ memberPos := by
    intro h
    rw [h] at hrightCoord
    have hb := congrArg (fun nd : ProperNode => nd.node.border)
      (Option.some.inj (hrightCoord.symm.trans hactualCoord))
    change (1 : Int) = actual.node.border at hb
    omega
  obtain ⟨_, _, _, q0, _, _, _, ⟨ord, horder, hlayers⟩, _, hproxy, hdrop, hroute, _, _⟩ :=
    componentRunX_spec hrun
  have hwellBordered : OrderImpl.BordersWellFormed run.coordinateProper := by
    rw [← hc]
    exact materializeDummyPaths_bordersWellFormed (clearProxyExtents_bordersWellFormed
      (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))
  have hprefix : top.1.node.clusterPath <+: actual.node.clusterPath := by
    simpa only [hscope] using (List.prefix_rfl : actual.node.clusterPath <+: actual.node.clusterPath)
  have hbracket := ExecutedBorderOrder.bracket run.coordinateProper orderOptions ord
    horder hwellBordered left memberPos right leftMarker actual rightMarker
    hleftCoord hactualCoord hrightCoord (sideLay hleftRank) (sideLay hrightRank)
    rfl rfl rfl hactualReal rfl hprefix hprefix hleftNe hrightNe
  obtain ⟨li, mi, ri, hli, hmi, hri, hlm, hmr⟩ := hbracket.positions
  rw [hlayers] at hli hmi hri
  have hlayer := hbracket.layer_mem
  rw [hlayers] at hlayer
  have hactualNP : ¬ (actual.node.border = -2 ∨ actual.node.border = 2) := by
    rw [hactualPlain]; decide
  have hleftSep := XB_orderedIntervals_holds exactIds execution.graph0_eq execution.graph_eq
    hcomp hrun hlayer hlm hli hmi hleftCoord hactualCoord hleftNP hactualNP
  have hrightSep := XB_orderedIntervals_holds exactIds execution.graph0_eq execution.graph_eq
    hcomp hrun hlayer hmr hmi hri hactualCoord hrightCoord hactualNP hrightNP
  have hleftFinal := ((proxyWidths_rel hproxy).2.2.2.2.2 left _ hleftCoord hleftNP).1
  have hrightFinal := ((proxyWidths_rel hproxy).2.2.2.2.2 right _ hrightCoord hrightNP).1
  have hactualFinal := ((proxyWidths_rel hproxy).2.2.2.2.2 memberPos _ hactualCoord hactualNP).1
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  rw [← hnodes] at hleftFinal hrightFinal hactualFinal
  have hgetParent : cg.nodes.getD parentPos default = parent := by
    simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
  have hf : (cg.nodes.getD parentPos default).border = -2 := by rw [hgetParent]; exact hgroup
  have hmarkerPath : top.1.node.clusterPath = path ++ [(cg.nodes.getD parentPos default).decl] := by
    rw [hgetParent, htopPath, hparentPath]
  have hleftIn : (frameRect P cg run parentPos).Contained (rect left) :=
    frameRect_side_marker_contained (P := P) (cg := cg) (run := run)
      hf (List.mk_mem_zipIdx_iff_getElem?.mpr hleftFinal) (Or.inl rfl) hmarkerPath
  have hrightIn : (frameRect P cg run parentPos).Contained (rect right) :=
    frameRect_side_marker_contained (P := P) (cg := cg) (run := run)
      hf (List.mk_mem_zipIdx_iff_getElem?.mpr hrightFinal) (Or.inr rfl) hmarkerPath
  have hborderW : 1 ≤ P.clusterBorderW := checkedParams_clusterBorderW_ge_one execution.checked
  have hleftW : 0 < (rect left).w := by
    change 0 < RouteImpl.nodeW run.proper left
    simp only [RouteImpl.nodeW, hleftFinal, leftMarker, OrderImpl.borderLeft]
    exact Int.lt_of_lt_of_le (by decide) hborderW
  have hrightW : 0 < (rect right).w := by
    change 0 < RouteImpl.nodeW run.proper right
    simp only [RouteImpl.nodeW, hrightFinal, rightMarker, OrderImpl.borderRight]
    exact Int.lt_of_lt_of_le (by decide) hborderW
  change (rect left).x + (rect left).w ≤ (rect memberPos).x at hleftSep
  change (rect memberPos).x + (rect memberPos).w ≤ (rect right).x at hrightSep
  have hproxyIn : ∀ {k : Nat} {node : Node}, cg.nodes[k]? = some node →
      (node.border = -2 ∨ node.border = 2) → node.clusterPath = parent.clusterPath →
      (frameRect P cg run parentPos).y ≤ (rect k).y ∧
        (rect k).y + (rect k).h ≤ (frameRect P cg run parentPos).y + (frameRect P cg run parentPos).h := by
    intro k node hnode hborder hpath
    let titledNode := titleF ⟨node, false, none, false⟩
    let coordNode := clearF titledNode
    have hcoord : run.coordinateProper.nodes[k]? = some coordNode := by
      rw [← hc]
      exact X_coordinateGraph_marker_record (hrecords k node hnode) hborder rfl
    have hbc : coordNode.node.border = node.border :=
      (clearF_keys titledNode).2.1.trans (titleF_keys _).2.1
    obtain ⟨_, span, _, _, hfinal, _, _, _⟩ :=
      proxyWidths_proxy_interval hproxy hcoord (by rw [hbc]; exact hborder)
    rw [← hnodes] at hfinal
    have hpc : coordNode.node.clusterPath = parent.clusterPath :=
      (clearF_keys titledNode).2.2.1.trans ((titleF_keys _).2.2.1.trans hpath)
    exact frameRect_member_vertical (P := P) (cg := cg) (run := run)
      hf (List.mk_mem_zipIdx_iff_getElem?.mpr hfinal) (by
      change coordNode.node.clusterPath.contains _ = true
      rw [hgetParent, hpc, hparentPath]
      simp)
  have htopIn := hproxyIn hparent (Or.inl hgroup) rfl
  have hbottomIn := hproxyIn hbottomNode (Or.inr hbottomBorder) hbottomPath
  have hnodeSize := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.1
  have htopLen := componentRunX_original_nodes_covered hrun parentPos (List.getElem?_eq_some_iff.mp hparent).1
  have hmemberLen := (List.getElem?_eq_some_iff.mp hactualFinal).1
  have hbottomLen := componentRunX_original_nodes_covered hrun bottom.2 (List.getElem?_eq_some_iff.mp hbottomNode).1
  obtain ⟨topLayer, htopLayer, htopNN, _, htopHi⟩ := componentRunX_node_rank_band hrun htopLen
  obtain ⟨memberLayer, hmemberLayer, hmNN, hmLo, hmHi⟩ := componentRunX_node_rank_band hrun hmemberLen
  obtain ⟨bottomLayer, hbottomLayer, hbNN, hbLo, _⟩ := componentRunX_node_rank_band hrun hbottomLen
  have htR := X_proper_rank_eq_local hrun parentPos
  have hmR := X_proper_rank_eq_local hrun memberPos
  have hbR := X_proper_rank_eq_local hrun bottom.2
  have htm : (rk run.proper.rank parentPos).toNat < (rk run.proper.rank memberPos).toNat := by
    rw [htR, hmR, htRank.2, hmRank.2]
    dsimp only at hrankOrder
    omega
  have hmb : (rk run.proper.rank memberPos).toNat < (rk run.proper.rank bottom.2).toNat := by
    rw [hmR, hbR, hmRank.2, hbRank.2]
    dsimp only at hrankOrder
    omega
  have htopGap := exactStrictBandGap hrun htm htopLayer hmemberLayer
  have hbottomGap := exactStrictBandGap hrun hmb hmemberLayer hbottomLayer
  have htopH : 0 ≤ (rect parentPos).h := (hnodeSize parentPos htopLen).2
  have hbottomH : 0 ≤ (rect bottom.2).h := (hnodeSize bottom.2 hbottomLen).2
  change (rect parentPos).y + (rect parentPos).h ≤ _ at htopHi
  change _ ≤ (rect memberPos).y at hmLo
  change (rect memberPos).y + (rect memberPos).h ≤ _ at hmHi
  change _ ≤ (rect bottom.2).y at hbLo
  have hmemberRect : frameRect P cg run memberPos = rect memberPos := by
    have hget : cg.nodes.getD memberPos default = member := by
      simp only [cg, List.getD_eq_getElem?_getD, hmember, Option.getD_some]
    simp only [frameRect, hget, hplain, show ((0 : Int) != -2) = true from rfl, ↓reduceIte]
    change nodeRect cg run memberPos = Labels.rectAt run.proper run.xs run.ys memberPos
    rw [nodeRect_of_record hactualFinal, rectAt_eq]
    simp only [RouteImpl.nodeW, RouteImpl.nodeH, RouteImpl.yAt, hactualFinal]
  change (frameRect P cg run parentPos).StrictInside (frameRect P cg run memberPos)
  rw [hmemberRect]
  have ht := htopIn.1
  have hb := hbottomIn.2
  have hleftEdge := Int.lt_add_of_pos_right (rect left).x hleftW
  have hrightEdge := Int.lt_add_of_pos_right (rect right).x hrightW
  exact ⟨Int.lt_of_le_of_lt hleftIn.1 (Int.lt_of_lt_of_le hleftEdge hleftSep),
    Int.lt_of_lt_of_le (Int.lt_of_le_of_lt hrightSep hrightEdge) hrightIn.2.1,
    by omega, by omega⟩

/-- A direct model-parent link in an executed exact component, before packing. -/
theorem exactComponentDirectFrameStrict {exactIds : List String} {inp : Input}
    {o : Options} (execution : ExactFramePrefix exactIds inp o)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {memberPos parentPos key parentKey : Nat} {child parent : ModelBox}
    (hmPos : comp[memberPos]? = some key) (hpPos : comp[parentPos]? = some parentKey)
    (hchild : inp.boxes[key]? = some child) (hparent : inp.boxes[parentKey]? = some parent)
    (href : child.parent = parent.id) (hne : child.parent ≠ "") :
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run parentPos).StrictInside
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run memberPos) := by
  obtain ⟨framed, hframedMem, hframedId, hframedGroup, hframedFixed⟩ :=
    framedParents_parent hframed (List.mem_of_getElem? hchild) hne
  obtain ⟨fi, hfi⟩ := List.getElem?_of_mem hframedMem
  have hids : (inp.boxes.map (·.id))[fi]? = (inp.boxes.map (·.id))[parentKey]? := by
    rw [List.getElem?_map, hfi, List.getElem?_map, hparent]
    exact congrArg some (hframedId.trans href)
  have hfiLen : fi < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hfi).1
  have heq := ((Model.boxIds_nodup hwf).getElem?_inj hfiLen).mp hids
  have hpFi : inp.boxes[fi]? = some parent := by rw [heq]; exact hparent
  have hsame : framed = parent := Option.some.inj (hfi.symm.trans hpFi)
  subst framed
  obtain ⟨member, hmember, hmDecl, hmShape⟩ := exactInputNode execution hchild
  obtain ⟨group, hgroup, hgDecl, hgShape⟩ := exactInputNode execution hparent
  have hframedRole : parent.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == parent.id) = false :=
    ⟨hframedGroup, hframedFixed⟩
  rw [ite_eq_left hframedRole] at hgShape
  have hmLookup := component_node_lookupX (cand := candidate) hmPos hmember
  have hgLookup := component_node_lookupX (cand := candidate) hpPos hgroup
  split at hmShape
  · exact exactGroupFrameStrict execution hwf hframed hcomp hrun hgLookup hgShape.1
      hmLookup hmShape.1 (by simpa only [hgDecl] using hparent)
      (by simpa only [hmDecl] using hchild) href hne
  · have hpath := Compound.path_of_parent (inputModel inp o) hwf hparent hchild href hne
    refine exactPlainFrameStrict execution hcomp hrun (path := Compound.path inp.boxes parent)
      hgLookup hgShape.1 ?_ hmLookup hmShape.1 ?_
    · simpa only [hgDecl] using hgShape.2
    · exact hmShape.2.trans (hpath.trans hgShape.2.symm)


end PipelineImpl

open PipelineImpl in
/-- The group-parent step holds for the boxes emitted by the exact pipeline. -/
theorem fallbackOwnerStrictStep_executedX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true) :
    FallbackOwnerStrictStep res := by
  intro b hb hparentNe p hparentLookup _
  obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨child, hchild, _, hbpar, _, hbrect⟩ := sceneBox_source_rectX execution hbi
  have hne : child.parent ≠ "" := by rw [← hbpar]; exact hparentNe
  have hfind : res.scene.layoutDump.boxes.find? (fun x : Box => x.id == b.parent) = some p :=
    hparentLookup
  have hpMem : p ∈ res.scene.boxes := by
    simpa only [Scene.layoutDump] using List.mem_of_find?_eq_some hfind
  have hpId : p.id = b.parent := by simpa using List.find?_some hfind
  obtain ⟨pi, hpi⟩ := List.mem_iff_getElem?.mp hpMem
  obtain ⟨parent, hparent, hpid, _, _, hprect⟩ := sceneBox_source_rectX execution hpi
  have href : child.parent = parent.id := hbpar.symm.trans (hpId.symm.trans hpid)
  have hbiLen := (List.getElem?_eq_some_iff.mp hchild).1
  have hpiLen := (List.getElem?_eq_some_iff.mp hparent).1
  obtain ⟨member, hmember, _, _⟩ := exactInputNode execution.exactFramePrefix hchild
  obtain ⟨part, memberPos, k, hpart, hk, hmPos⟩ := key_part_positionX execution hbiLen
  have hcompMap := (actual_components_parts_geometryX (by rfl) execution.components_eq).1
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hcompMap]
    exact List.mem_map.mpr ⟨part, hpart, rfl⟩
  have hparentIn := exactParentInComponent execution hwf hframed part.1 hcomp bi pi
    hbiLen (List.mem_of_getElem? hmPos) member hmember child hchild parent hparent href hne
  obtain ⟨parentPos, hpPos⟩ := List.getElem?_of_mem hparentIn
  have hpackedEq := execution.packed_eq
  unfold packAcc at hpackedEq
  obtain ⟨packed, hpack, _⟩ := bind_ok hpackedEq
  have hkLen := part_packed_box_lenX execution packed hpack hk
  obtain ⟨cand, run, loops, _, hrun, _, _, hlookup⟩ := part_frame_lookupX execution packed hpack hk
    (List.getElem?_eq_getElem hkLen)
  let cg := componentCandidate execution.graph part.1 cand
  have hstrict := exactComponentDirectFrameStrict execution.exactFramePrefix hwf hframed
    hcomp hrun hmPos hpPos hchild hparent href hne
  let bounds := placeBoundsX execution.params cg run execution.measured loops
  have hcomponent := strictInside_shiftRect (dx := 0 - bounds.minX) (dy := -bounds.minY) hstrict
  have hpacked := strictInside_shiftRect (dx := packed.boxes[k].x) (dy := packed.boxes[k].y) hcomponent
  have horiented := strictInside_orientRect (d := o.direction) (h := execution.packedAcc.canvasH) hpacked
  have hmargins := strictInside_shiftRect (dx := execution.params.canvasMargin)
    (dy := execution.params.canvasMargin) horiented
  rw [hprect, hbrect, hlookup parentPos pi hpPos hpiLen, hlookup memberPos bi hmPos hbiLen]
  exact hmargins

end Elegant.Layered

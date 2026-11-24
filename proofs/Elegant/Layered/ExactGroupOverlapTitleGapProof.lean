import Elegant.Layered.ExactGroupLoopFixedLeafGapProof
import Elegant.Layered.LabelsC8b

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem nonproxy_forward {P : Params} {exact : List Nat} {cg : Graph}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {run : Run}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : ProperNode} (hv : run.coordinateProper.nodes[v]? = some node)
    (hb : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[v]? = some node ∧ run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v node hv hb
  rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  exact ⟨hnode, by simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]⟩

private theorem title_coordinate_record {P : Params} {exact : List Nat} {cg : Graph}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {run : Run}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {title : ProperNode} (hv : run.proper.nodes[v]? = some title)
    (hb : title.node.border = 3) : run.coordinateProper.nodes[v]? = some title := by
  obtain ⟨_, _, _, q, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨_, _, hlen, _, hrecords, _⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q.nodes := by rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  have hi : v < run.coordinateProper.nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hv).1
    rw [hnodes, hlen] at h
    exact h
  have hc : run.coordinateProper.nodes[v]? = some run.coordinateProper.nodes[v] :=
    List.getElem?_eq_getElem hi
  obtain ⟨out, hout, _, he, _⟩ := hrecords v _ hc
  rw [← hnodes, hv] at hout
  have houtEq : out = title := Option.some.inj hout.symm
  have hb' : run.coordinateProper.nodes[v].node.border = 3 := by
    rw [← he, houtEq, hb]
  have hf := (nonproxy_forward hrun hc (by rw [hb']; decide)).1
  rwa [Option.some.inj (hf.symm.trans hv)] at hc

private theorem sized_group_record (P : Params) (exact : List Nat) {labeled : Proper}
    {i : Nat} {node : Node}
    (hi : labeled.nodes[i]? = some (⟨node, false, none, false⟩ : ProperNode))
    (hb : node.border = -2) :
    (sizeProperPortsX P exact labeled).nodes[i]? = some ⟨node, false, none, false⟩ := by
  have hnonplain : (node.border != 0) = true := by rw [hb]; decide
  simp only [sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx, hi, Option.map_some]
  simp [hnonplain]

private theorem coordinate_title_copy {P : Params} {exact : List Nat} {labeled : Proper}
    {i : Nat} {node : Node}
    (hi : labeled.nodes[i]? = some (⟨node, false, none, false⟩ : ProperNode))
    (hb : node.border = -2) :
    ∃ v : Nat, (coordinateGraphX P exact labeled).nodes[v]? =
      some (copyF (⟨node, false, none, false⟩, i)) := by
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservations sized
  have he : (⟨node, false, none, false⟩, i) ∈ titleNodes sized := by
    unfold titleNodes
    exact List.mem_filter.mpr ⟨List.mem_zipIdx_iff_getElem?.mpr
      (sized_group_record P exact hi hb), by simp [hb]⟩
  have ht : copyF (⟨node, false, none, false⟩, i) ∈ titled.nodes := by
    change _ ∈ (titleReservations sized).nodes
    rw [titleReservations_nodes]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨_, he, rfl⟩)
  obtain ⟨extra, hnodes, _⟩ := addClusterBorders_extra titled P.clusterBorderW
  have hmem : copyF (⟨node, false, none, false⟩, i) ∈
      (OrderImpl.addClusterBorders titled P.clusterBorderW).nodes := by
    rw [hnodes]
    exact List.mem_append_left extra ht
  obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)).nodes[v]? =
      some (copyF (⟨node, false, none, false⟩, i)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hv]
    simp [clearF, copyF]
  obtain ⟨actual, hactual, _⟩ := materialize_exists _ hclear
  obtain ⟨before, hbefore, _, _, _, hreal⟩ := materialize_lookup _ hactual
  have hbeforeEq := Option.some.inj (hbefore.symm.trans hclear)
  subst before
  have heq : actual = copyF (⟨node, false, none, false⟩, i) := hreal rfl
  subst actual
  exact ⟨v, hactual⟩

private theorem coordinate_title_source {P : Params} {exact : List Nat} {labeled : Proper}
    {cg : Graph} (hkeys : NodeKeys cg labeled) (hshape : CgShape cg)
    (hrecords : ∀ (i : Nat) (node : Node), cg.nodes[i]? = some node →
      labeled.nodes[i]? = some (⟨node, false, none, false⟩ : ProperNode))
    {v : Nat} {title : ProperNode}
    (hv : (coordinateGraphX P exact labeled).nodes[v]? = some title)
    (hb : title.node.border = 3) :
    ∃ (i : Nat) (node : Node), cg.nodes[i]? = some node ∧ node.border = -2 ∧
      title = copyF (⟨node, false, none, false⟩, i) := by
  unfold coordinateGraphX at hv
  obtain ⟨before, hbefore, _, hborder, _, hreal⟩ := materialize_lookup _ hv
  simp only [clearProxyExtents_nodes, List.getElem?_map, Option.map_eq_some_iff] at hbefore
  obtain ⟨nd, hnd, hclear⟩ := hbefore
  have hb3 : nd.node.border = 3 := by
    rw [← (clearF_keys nd).2.1, hclear, ← hborder, hb]
  let sized := sizeProperPortsX P exact labeled
  let titled := titleReservations sized
  change (OrderImpl.addClusterBorders titled P.clusterBorderW).nodes[v]? = some nd at hnd
  obtain ⟨extra, hnodes, hall⟩ := addClusterBorders_extra titled P.clusterBorderW
  rw [hnodes] at hnd
  by_cases hin : v < titled.nodes.length
  · rw [List.getElem?_append_left hin] at hnd
    change (titleReservations sized).nodes[v]? = some nd at hnd
    rw [titleReservations_nodes] at hnd
    by_cases hp : v < sized.nodes.length
    · rw [List.getElem?_append_left (by simpa only [List.length_map] using hp),
        List.getElem?_map] at hnd
      obtain ⟨s, hs, hsEq⟩ := Option.map_eq_some_iff.mp hnd
      obtain ⟨orig, horig, _, hsB, _⟩ := X_sizeProperPorts_node_origin P exact labeled hs
      have horigB : orig.node.border = 3 := by
        rw [← hsB, ← (titleF_keys s).2.1, hsEq, hb3]
      rcases hkeys v orig horig with ⟨source, hsource, _, hsourceB, _⟩ | ⟨_, hzero, _⟩
      · exact (hshape.2 source (List.mem_of_getElem? hsource)
          (hsourceB.symm.trans horigB)).elim
      · omega
    · rw [List.getElem?_append_right (by
        simpa only [List.length_map] using Nat.le_of_not_lt hp), List.getElem?_map] at hnd
      obtain ⟨entry, hentry, hcopy⟩ := Option.map_eq_some_iff.mp hnd
      obtain ⟨hs, hbTop⟩ := titleNodes_spec hentry
      obtain ⟨orig, horig, _, hsb, _⟩ := X_sizeProperPorts_node_origin P exact labeled hs
      have horigB : orig.node.border = -2 := hsb.symm.trans hbTop
      rcases hkeys entry.2 orig horig with ⟨source, hsource, _, hbSource, _⟩ | ⟨_, hzero, _⟩
      · have htop : source.border = -2 := hbSource.symm.trans horigB
        have hsize := sized_group_record P exact (labeled := labeled) (i := entry.2)
          (node := source) (hrecords entry.2 source hsource) htop
        have he : entry.1 = (⟨source, false, none, false⟩ : ProperNode) :=
          Option.some.inj (hs.symm.trans hsize)
        have hcopied : copyF (⟨source, false, none, false⟩, entry.2) = nd := by
          rw [← he]
          exact hcopy
        have hbeforeEq : before = copyF (⟨source, false, none, false⟩, entry.2) := by
          rw [← hcopied] at hclear
          simpa [clearF, copyF] using hclear.symm
        exact ⟨entry.2, source, hsource, htop,
          (hreal (congrArg ProperNode.dummy hbeforeEq)).trans hbeforeEq⟩
      · omega
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hin)] at hnd
    rcases (hall nd (List.mem_of_getElem? hnd)).2 with h | h <;> omega

set_option maxHeartbeats 800000 in
private theorem measured_group_source {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate i : Nat} {node : Node}
    (hi : (componentCandidate execution.graph comp candidate).nodes[i]? = some node)
    (hb : node.border = -2) :
    ∃ j, comp[i]? = some j ∧ execution.graph0.nodes[j]? = some node ∧ node.decl = j := by
  obtain ⟨j, hj, hgraph⟩ := componentCandidate_nonplain_source hi (by omega)
  have hj0 : j < execution.graph0.nodes.length := by
    rw [← exactGraph_length execution.graph_eq]
    exact (List.getElem?_eq_some_iff.mp hgraph).1
  have hbase : execution.graph0.nodes[j]? = some execution.graph0.nodes[j] :=
    List.getElem?_eq_getElem hj0
  obtain ⟨out, hout, hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hbase
  have houtEq : out = node := Option.some.inj (hout.symm.trans hgraph)
  have hbaseB : execution.graph0.nodes[j].border = -2 := hborder.symm.trans (houtEq ▸ hb)
  obtain ⟨hdecl, effective, heffective, hrole, _⟩ :=
    measuredGraph_group_origin execution.graph0_eq hbase hbaseB
  rw [List.getElem?_map] at heffective
  obtain ⟨box, hbox, heq⟩ := Option.map_eq_some_iff.mp heffective
  have hfixed : inp.fixedSizes.any (fun f => f.1 == box.id) = false := by
    cases hf : inp.fixedSizes.any (fun f => f.1 == box.id) with
    | false => rfl
    | true =>
      simp only [hf, ↓reduceIte] at heq
      have h := congrArg ModelBox.role heq
      rw [hrole] at h
      cases h
  have hfind : inp.fixedSizes.find? (fun f => f.1 == box.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hfixed)
  have hg := execution.graph_eq
  unfold exactGraph at hg
  obtain ⟨updated, hupdated, hg⟩ := bind_ok hg
  obtain ⟨nd, hstep, hnd⟩ := (mapM_getElem? _ _ _ hupdated).2 j _ hbase
  have hnodes : execution.graph.nodes = updated := congrArg Graph.nodes (Except.ok.inj hg).symm
  rw [hnodes] at hgraph
  have hndEq : nd = node := Option.some.inj (hnd.symm.trans hgraph)
  have hsame : execution.graph0.nodes[j] = nd := by
    cases he : exactIds.contains box.id with
    | false =>
      have heq : (Except.ok execution.graph0.nodes[j] : Except LayoutError Node) = .ok nd := by
        simpa only [hbox, he, hfixed, Bool.and_false, Bool.not_false,
          Bool.true_and, ↓reduceIte, pure, Except.pure] using hstep
      exact Except.ok.inj heq
    | true =>
      simp only [hbox, he, hfixed, hfind, Bool.and_false, Bool.not_true,
        Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        throw, throwThe, MonadExceptOf.throw] at hstep
      cases hstep
  exact ⟨j, hj, by simpa only [hsame, hndEq] using hbase, (hsame.trans hndEq) ▸ hdecl⟩

/-- A border-3 record in a successful component run is the measured copy of a
candidate group top. Its owner path and horizontal position survive into routing. -/
theorem componentRunX_group_overlap_title_source {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat}
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {v : Nat} {title : ProperNode} (hv : run.proper.nodes[v]? = some title)
    (hb : title.node.border = 3) :
    ∃ i : Nat, ∃ node : Node, ∃ box : ModelBox,
      (componentCandidate execution.graph comp candidate).nodes[i]? = some node ∧
      node.border = -2 ∧ inp.boxes[node.decl]? = some box ∧
      title = copyF (⟨node, false, none, false⟩, i) ∧
      title.node.clusterPath = Compound.path inp.boxes box ++ [node.decl] ∧
      run.coordinateProper.nodes[v]? = some title ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 ∧
      let measured := titleCaptionSize execution.params o (execution.lines.getD node.decl [])
      title.node.w = measured.w ∧ measured.h + execution.params.clusterPad ≤ title.node.h := by
  have hc := title_coordinate_record hrun hv hb
  obtain ⟨_, labeled, _, hcoord, hkeys, _, hrecords, _, _⟩ :=
    X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
  have hshape := componentCandidate_shape (components_nodup _ _ hcomp)
    (exactGraph_shape (measuredGraph_shape execution.graph0_eq) execution.graph_eq) candidate
  have hcoordinate : (coordinateGraphX execution.params (exactDecls exactIds inp) labeled).nodes[v]? =
      some title := by rw [hcoord]; exact hc
  obtain ⟨i, node, hi, htop, he⟩ := coordinate_title_source hkeys hshape hrecords hcoordinate hb
  obtain ⟨box, hbox, hpath⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq hi htop
  obtain ⟨j, hj, hsource, hdecl⟩ := measured_group_source execution hi htop
  have hi0 : (componentCandidate execution.graph0 comp candidate).nodes[i]? = some node := by
    rw [componentCandidate_nodes]
    change (comp.map fun k => execution.graph0.nodes.getD k default)[i]? = some node
    simp only [List.getElem?_map, hj, Option.map_some, List.getD_eq_getElem?_getD,
      hsource, Option.getD_some]
  have hkey : comp.getD i 0 = node.decl := by
    simp only [List.getD_eq_getElem?_getD, hj, Option.getD_some, hdecl]
  have hfit := actual_title_caption_fit execution.graph0_eq hi0 htop
  rw [hkey] at hfit
  refine ⟨i, node, box, hi, htop, hbox, he, ?_, hc,
    (nonproxy_forward hrun hc (by rw [hb]; decide)).2, ?_⟩
  · simpa only [he, copyF] using hpath
  · cases hd : o.direction <;> simpa only [he, copyF, titleCaptionSize, hd] using hfit

private theorem candidate_slot (g : Graph) (comp : List Nat) (candidate : Nat) :
    (componentCandidate g comp candidate).slot = g.slot := by
  unfold componentCandidate
  dsimp only
  split
  · split <;> rfl
  · unfold cycleGraph
    split <;> rfl

set_option maxHeartbeats 800000 in
private theorem group_loop_required_height {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate t : Nat}
    {owner : Node} (howner : (componentCandidate execution.graph comp candidate).nodes[t]? = some owner)
    (hgroup : owner.border = -2) (hextent : 0 < owner.loopExtent) :
    let cg := componentCandidate execution.graph comp candidate
    Loops.requiredHeight cg.slot (loopSizes cg.edges execution.measured t cg.slot) ≤ owner.h := by
  obtain ⟨j, hj, hbase, hdecl⟩ := measured_group_source execution howner hgroup
  obtain ⟨_, box, hbox, hrole, _⟩ := measuredGraph_group_origin execution.graph0_eq hbase hgroup
  let boxes := inp.boxes.map fun b =>
    if inp.fixedSizes.any (fun f => f.1 == b.id) then { b with role := .node } else b
  have hbox' : boxes[j]? = some box := by simpa only [boxes, hdecl] using hbox
  let titles := execution.lines.map fun ls =>
    let width := ls.foldl (fun w line => max w line.width) 0
    let height := (max 1 ls.length : Int) * execution.params.lineH
    match o.direction with
    | .LR | .RL => (height, width)
    | .TB | .BT => (width, height)
  obtain ⟨metric, labels, raw, hm, hl, _, hrawSlot, hg, hreserve⟩ :=
    measuredGraph_loop_reservation_before_prepare execution.graph0_eq
  have hm' := Except.ok.inj (hm.symm.trans execution.metric_eq)
  subst metric
  have hl' := Except.ok.inj (hl.symm.trans execution.measured_eq)
  subst labels
  change execution.graph0 = Compound.prepare boxes execution.params.clusterPad titles raw at hg
  have hprepared := hbase
  rw [hg] at hprepared
  have hjRaw : j < raw.nodes.length := by
    by_cases hjRaw : j < raw.nodes.length
    · exact hjRaw
    · have hbottom := (Compound.prepare_bottom_of_index boxes execution.params.clusterPad titles
        raw j (Nat.le_of_not_lt hjRaw) hprepared).1
      omega
  have hnode := Compound.prepare_group_title_record boxes execution.params.clusterPad titles raw
    hjRaw hbox' hrole
  have he := Option.some.inj (hprepared.symm.trans hnode)
  have hext := congrArg Node.loopExtent he
  change owner.loopExtent = raw.nodes[j].loopExtent at hext
  have hnonzero : ¬ ((raw.nodes[j].loopExtent == 0) = true) := by
    intro hz
    have hzero := beq_iff_eq.mp hz
    rw [← hext] at hzero
    exact Nat.lt_irrefl 0 (hzero ▸ hextent)
  have hheight := congrArg Node.h he
  change owner.h = (if raw.nodes[j].loopExtent == 0 then
    (titles.getD j (0, 0)).2 + execution.params.clusterPad else
    max ((titles.getD j (0, 0)).2 + execution.params.clusterPad) raw.nodes[j].h) at hheight
  rw [ite_eq_right hnonzero] at hheight
  have hslot0 : execution.graph0.slot = execution.params.slot := by rw [hg]; exact hrawSlot
  have hgraph := execution.graph_eq
  unfold exactGraph at hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok hgraph
  have hslot : execution.graph.slot = execution.graph0.slot := by rw [← Except.ok.inj hgraph]
  dsimp only
  rw [candidate_slot, hslot,
    componentCandidate_loopSizes_preserved execution.graph comp (components_nodup _ _ hcomp)
      candidate t (List.getElem?_eq_some_iff.mp hj).1 execution.measured execution.graph0.slot,
    (List.getElem?_eq_some_iff.mp hj).2, exactGraph_edges execution.graph_eq, hslot0]
  have hrawSizes := prepare_loopSizes_preserved boxes execution.params.clusterPad titles
    raw j (List.getElem?_eq_some_iff.mp hbox').1 execution.measured execution.params.slot
  rw [← hg] at hrawSizes
  rw [hrawSizes, hheight]
  exact Int.le_trans (hreserve j _ (List.getElem?_eq_getElem hjRaw)) (Int.le_max_right _ _)

set_option maxHeartbeats 1200000 in
/-- Border-3 subcase of the exact group-loop overlap gap. The title can belong
 to a descendant or an unrelated group; its rank determines which executed
 marker is compared with the title. No clearance premise is needed. -/
theorem componentRunX_groupLoop_title_horizontal_gap {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph) {candidate : Nat}
    {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run)
    {k : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph comp candidate).edges[k]? = some edge)
    (hself : edge.tail = edge.head) {owner : Node}
    (howner : (componentCandidate execution.graph comp candidate).nodes[edge.tail]? = some owner)
    (hgroup : owner.border = -2) {v : Nat} {title : ProperNode}
    (htitle : run.proper.nodes[v]? = some title) (hb : title.node.border = 3) :
    let cg := componentCandidate execution.graph comp candidate
    let foot := loopFootprintExt cg run execution.measured edge.tail
    let box := RouteImpl.boxRect run.proper run.xs run.ys v
    max foot.y box.y < min (foot.y + foot.h) (box.y + box.h) →
    foot.x + foot.w ≤ box.x ∨ box.x + box.w ≤ foot.x := by
  let cg := componentCandidate execution.graph comp candidate
  let foot := loopFootprintExt cg run execution.measured edge.tail
  let frame := frameRect default cg run edge.tail
  let box := RouteImpl.boxRect run.proper run.xs run.ys v
  let sizes := loopSizes cg.edges execution.measured edge.tail cg.slot
  change max foot.y box.y < min (foot.y + foot.h) (box.y + box.h) →
    foot.x + foot.w ≤ box.x ∨ box.x + box.w ≤ foot.x
  intro hy
  obtain ⟨_, _, _, _, _, _, hcopy, _, hcoord, hx, _⟩ :=
    componentRunX_group_overlap_title_source execution hcomp hrun htitle hb
  have htitleExtent : title.node.loopExtent = 0 := congrArg (fun n => n.node.loopExtent) hcopy
  have hbNP : ¬(title.node.border = -2 ∨ title.node.border = 2) := by rw [hb]; decide
  have hloops : ∃ e ∈ cg.edges, e.tail = edge.tail ∧ e.head = edge.tail :=
    ⟨edge, List.mem_of_getElem? hedge, rfl, hself.symm⟩
  have hmarkers := XLEG_groupMarkerOrderX_of_leaves exactIds
    (xleg_loopMarkerCoreX_holds exactIds) (xleg_loopMarkerLayerOrderX_holds exactIds)
    (xleg_loopMarkerSpanX_holds exactIds)
    inp o res execution hwf hfp comp candidate run orderOptions cg hcomp rfl hrun
  obtain ⟨_, right, _, ndR, _, hcR, _, hbR, _, hlastR, hextR, _, hshare, _, hcross, hnonneg, _⟩ :=
    hmarkers.2 edge.tail owner howner hloops hgroup
  have hnpR : ¬(ndR.node.border = -2 ∨ ndR.node.border = 2) := by rw [hbR]; decide
  have hpR := (nonproxy_forward hrun hcR hnpR).1
  have hfootWidth : foot.w = (if run.exact.contains edge.tail then Loops.exactExtent cg.slot sizes
      else Loops.extent cg.slot sizes) := by
    change (if run.exact.contains edge.tail then Loops.exactExtent else Loops.extent) cg.slot sizes = _
    cases run.exact.contains edge.tail <;> rfl
  have hslot : 0 < cg.slot := by
    have hp : 1 ≤ execution.params.slot := (checkedParams_valid execution.checked).2.2.1
    have hg := execution.graph_eq
    unfold exactGraph at hg
    obtain ⟨_, _, hg⟩ := bind_ok hg
    have hs : execution.graph.slot = execution.graph0.slot := by rw [← Except.ok.inj hg]
    obtain ⟨_, _, _, hprep, _, _⟩ := measuredGraph_prepared_source execution.graph0_eq
    have hs0 := congrArg Graph.slot hprep
    change execution.graph0.slot = execution.params.slot at hs0
    change 0 < (componentCandidate execution.graph comp candidate).slot
    rw [candidate_slot, hs, hs0]
    omega
  have hlabel : stackSize cg.slot (routeLabels execution.measured edge.decl) ∈ sizes := by
    unfold sizes loopSizes loopEdges
    exact List.mem_map.mpr ⟨edge, List.mem_filter.mpr ⟨List.mem_of_getElem? hedge,
      by simp [hself]⟩, rfl⟩
  have hw : ∀ l ∈ sizes, 0 ≤ l.width := by
    intro l hl
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hl
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have fold_max_nonneg (f : LoopLabel → Int) (ls : List LoopLabel) (a : Int) (ha : 0 ≤ a) :
      0 ≤ ls.foldl (fun b l => max b (f l)) a := by
    induction ls generalizing a with
    | nil => exact ha
    | cons _ _ ih => exact ih _ (Int.le_trans ha (Int.le_max_left _ _))
  have hpositive : 0 < foot.w := by
    rw [hfootWidth]
    cases hx : run.exact.contains edge.tail with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hbound := Loops.outer_label_extent cg.slot sizes (by omega) hw _ hlabel
      have hproduct := Int.mul_pos hslot (show 0 < (sizes.length : Int) + 1 by omega)
      have hw0 := hw _ hlabel
      omega
    | true =>
      simp only [↓reduceIte, Loops.exactExtent]
      have hn : sizes.isEmpty = false := by
        cases hs : sizes with
        | nil => simp [hs] at hlabel
        | cons => rfl
      rw [hn]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hwide := fold_max_nonneg (·.width) sizes 0 (by omega)
      have hproduct := Int.mul_pos hslot (show 0 < 2 * (sizes.length : Int) + 1 by omega)
      omega
  have hextCopy := xleg_rightMarker_copies_extent execution.graph0_eq execution.graph_eq
    hcomp hrun howner hgroup hcR hbR hlastR
  have hownerExt : 0 < owner.loopExtent := by
    have hle : foot.w ≤ (owner.loopExtent : Int) := by rw [hfootWidth, ← hextCopy]; exact hextR
    omega
  have hrequired := group_loop_required_height execution hcomp howner hgroup hownerExt
  change Loops.requiredHeight cg.slot sizes ≤ owner.h at hrequired
  obtain ⟨_, _, labeled, _, hnormalize, hlabels, hcoordinates, _⟩ := componentRunX_spec hrun
  have hlabelRecord : labeled.nodes[edge.tail]? = some ⟨owner, false, none, false⟩ :=
    addLabelNodes_untouched_node hlabels (normalize_node_record hnormalize howner) rfl
  obtain ⟨u, hu⟩ := coordinate_title_copy (P := execution.params) (exact := exactDecls exactIds inp)
    hlabelRecord hgroup
  rw [hcoordinates] at hu
  have hparentTitle := (nonproxy_forward hrun hu (by simp [copyF])).1
  obtain ⟨_, _, hpath⟩ := X_cg_group_box execution.graph0_eq execution.graph_eq howner hgroup
  have hparentPath : (copyF (⟨owner, false, none, false⟩, edge.tail)).node.clusterPath.contains
      owner.decl = true := by
    change owner.clusterPath.contains owner.decl = true
    simp [hpath]
  have hmem : Labels.rectAt run.proper run.xs run.ys u ∈ groupMemberRects cg run owner.decl :=
    fbs_groupMemberRects_mem hparentTitle hparentPath
  have hframeHeight : owner.h ≤ frame.h := by
    have h := boundsOf_height_ge_member hmem
    rw [rectAt_eq] at h
    change RouteImpl.nodeH run.proper u ≤ _ at h
    simp only [RouteImpl.nodeH, hparentTitle, copyF] at h
    change owner.h ≤ (frameRect default cg run edge.tail).h
    rw [frameRect_group_span howner hgroup]
    exact h
  have hfit : (sizes.length : Int) * Loops.band cg.slot sizes ≤ frame.h := by
    have hband : 0 ≤ Loops.band cg.slot sizes :=
      fold_max_nonneg (·.height) sizes (2 * cg.slot) (by omega)
    have hproduct := Int.mul_nonneg (show 0 ≤ (sizes.length : Int) by omega) hband
    unfold Loops.requiredHeight at hrequired
    rw [Int.mul_assoc] at hrequired
    omega
  have hfootHeight : foot.h = frame.h := by
    change max frame.h ((sizes.length : Int) * Loops.band cg.slot sizes) = frame.h
    exact Int.max_eq_left hfit
  have hne : groupMemberRects cg run owner.decl ≠ [] := by
    intro h
    rw [h] at hmem
    cases hmem
  rw [show foot.y = frame.y from rfl, hfootHeight] at hy
  change max frame.y (run.ys.getD v 0) <
    min (frame.y + frame.h) (run.ys.getD v 0 + RouteImpl.nodeH run.proper v) at hy
  obtain ⟨⟨lo, loNode, hlo, hloPath, hloRank⟩, ⟨hi, hiNode, hhi, hhiPath, hhiRank⟩⟩ :=
    componentRunX_group_member_rank_bracket hrun howner hgroup htitle hne hy
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    unfold boxLines at h
    simpa only [List.length_zipIdx] using Sequence.mapM_ok_length _ _ _ h
  obtain ⟨_, m, _, marker, _, _, _, _, hm, hmarker, hlast, hrank⟩ :=
    XN_bracketMarkersAtRank_holds exactIds execution.graph0_eq execution.graph_eq hlines hwf hfp
      hcomp hrun (rk run.proper.rank v).toNat hlo hloPath hloRank hhi hhiPath hhiRank
  have hnp : ¬(marker.node.border = -2 ∨ marker.node.border = 2) := by rw [hmarker]; decide
  obtain ⟨hpm, hxm⟩ := nonproxy_forward hrun hm hnp
  have hr : Labels.rectAt run.proper run.xs run.ys right ∈ groupBorderRects cg run owner.decl :=
    groupBorderRects_mem_of_record hpR (Or.inr hbR) hlastR
  have hge : RouteImpl.leftOf run.proper run.xs right + RouteImpl.nodeW run.proper right ≤
      (boundsOf (groupBorderRects cg run owner.decl) []).right := by
    have h := (boundsOf_rect_mem hr).2
    rw [rectAt_eq] at h
    exact h
  have hle : (boundsOf (groupBorderRects cg run owner.decl) []).right ≤
      RouteImpl.leftOf run.proper run.xs right + RouteImpl.nodeW run.proper right :=
    boundsOf_right_le_of_all (rects := groupBorderRects cg run owner.decl) hnonneg
      (fun rect hrect => by
        obtain ⟨q, nd, hq, hside, hlastQ, he⟩ := groupBorderRects_inv hrect
        rw [he, rectAt_eq]
        dsimp only
        rcases hside with h | h
        · rw [((hshare hq hlastQ).1 h).2]
          exact hcross
        · rw [((hshare hq hlastQ).2 h).2] <;> exact Int.le_refl _)
  have hfootX : foot.x = RouteImpl.leftOf run.proper run.xs m + RouteImpl.nodeW run.proper m := by
    have hsame := ((hshare hpm hlast).2 hmarker).2
    calc
      foot.x = frame.x + frame.w := rfl
      _ = (boundsOf (groupBorderRects cg run owner.decl) []).right := by
        change (frameRect default cg run edge.tail).x +
          (frameRect default cg run edge.tail).w = _
        rw [frameRect_group_span (P := default) (cg := cg) (run := run) howner hgroup]
        dsimp only
        rw [Int.add_comm, Int.sub_add_cancel]
      _ = _ := (Int.le_antisymm hle hge).trans hsame.symm
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlanes, _, _⟩ := componentRunX_spec hrun
  have hcovered := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hlanes).1).2.2.2.1
  obtain ⟨layer, hlayer, hv, _⟩ := hcovered v (List.getElem?_eq_some_iff.mp htitle).1
  obtain ⟨otherLayer, hother, hmMem, _⟩ := hcovered m (List.getElem?_eq_some_iff.mp hpm).1
  rw [X_proper_rank_eq_local hrun m, hrank, Int.toNat_natCast, hlayer] at hother
  have heq : layer = otherLayer := Option.some.inj hother
  subst otherLayer
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmMem
  obtain ⟨iv, hiv⟩ := List.mem_iff_getElem?.mp hv
  rcases Nat.lt_trichotomy j iv with hbefore | hequal | hafter
  · left
    have hgap := xleg_rightMarker_later_gap hrun hm hmarker hcoord
      (List.mem_of_getElem? hlayer) hj hiv hbefore
    have hext : foot.w ≤ (marker.node.loopExtent : Int) := by
      rw [hfootWidth]
      exact xleg_rightMarker_extent_ge execution hcomp hrun howner hgroup hm hmarker hlast
    rw [hfootX]
    dsimp only [box]
    simp only [RouteImpl.boxRect, RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.nodeW,
      hpm, htitle, hx, hxm, htitleExtent, Int.natCast_zero, Int.mul_zero, Int.add_zero,
      Int.fdiv_eq_ediv_of_nonneg _ (by decide : 0 ≤ (2 : Int))] at hgap ⊢
    omega
  · subst iv
    have hmv : m = v := Option.some.inj (hj.symm.trans hiv)
    subst m
    have hn : marker = title := Option.some.inj (hm.symm.trans hcoord)
    rw [hn, hb] at hmarker
    omega
  · right
    have hordered := XB_orderedIntervals_holds exactIds execution.graph0_eq execution.graph_eq
      hcomp hrun (List.mem_of_getElem? hlayer) hafter hiv hj hcoord hm hbNP hnp
    have hwM := (componentRunX_dims_nonneg hrun) m marker hpm |>.1
    rw [hfootX]
    change RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤ _
    simp only [RouteImpl.nodeW, hpm] at hordered ⊢
    omega

end Elegant.Layered.PipelineImpl

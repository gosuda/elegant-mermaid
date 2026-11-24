import Elegant.Layered.ExactFlatFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- `sizeProperPortsX` preserves the node count, like `sizeProperPorts`. -/
theorem sizeProperPortsX_length (P : Params) (exact : List Nat) (p : Proper) :
    (sizeProperPortsX P exact p).nodes.length = p.nodes.length := by
  simp [sizeProperPortsX]

 /-- Mapping an edge-preserving function over indexed nodes preserves the edge
 key sequence. -/
 theorem map_edge_of_zipIdxMap (nodes : List ProperNode)
     (f : ProperNode × Nat → ProperNode) (hf : ∀ n, (f n).edge = n.1.edge) :
     (nodes.zipIdx.map f).map ProperNode.edge = nodes.map ProperNode.edge := by
   calc (nodes.zipIdx.map f).map ProperNode.edge
       = (nodes.zipIdx.map Prod.fst).map ProperNode.edge := by
         simp only [List.map_map]
         apply congrArg (fun g => nodes.zipIdx.map g)
         funext n
         exact hf n
     _ = nodes.map ProperNode.edge := by rw [List.zipIdx_map_fst]

 /-- `sizeProperPortsX` preserves every node edge key: the exact branch keeps the
 node and the widening branch only grows `w`. -/
 theorem sizeProperPortsX_edge (P : Params) (exact : List Nat) (p : Proper) :
     (sizeProperPortsX P exact p).nodes.map ProperNode.edge =
       p.nodes.map ProperNode.edge := by
   unfold sizeProperPortsX
   apply map_edge_of_zipIdxMap
   intro n
   split <;> rfl

/-- `sizeProperPortsX` leaves ranks untouched. -/
theorem sizeProperPortsX_rank (P : Params) (exact : List Nat) (p : Proper) :
    (sizeProperPortsX P exact p).rank = p.rank := rfl

/-- Appending coordinate-only nodes and ranks cannot change a first anchor
already found in the original, rank-aligned prefix: the exact variant. -/
theorem coordinateGraphX_anchor_prefix (P : Params) (exact : List Nat) (p : Proper) :
    (∃ extra, (coordinateGraphX P exact p).nodes.map ProperNode.edge =
      p.nodes.map ProperNode.edge ++ extra) ∧
    (∃ extra, (coordinateGraphX P exact p).rank = p.rank ++ extra) := by
  have mapped : ∀ (nodes : List ProperNode) (f : ProperNode → ProperNode),
      (∀ n, (f n).edge = n.edge) →
      (nodes.map f).map ProperNode.edge = nodes.map ProperNode.edge := by
    intro nodes f hf
    simp only [List.map_map]
    apply congrArg (fun g => nodes.map g)
    funext n
    exact hf n
  have hs : (sizeProperPortsX P exact p).nodes.map ProperNode.edge =
      p.nodes.map ProperNode.edge :=
    sizeProperPortsX_edge P exact p
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
      (materializeDummyPaths q).nodes.map ProperNode.edge =
        q.nodes.map ProperNode.edge := by
    intro q
    unfold materializeDummyPaths
    apply map_edge_of_zipIdxMap
    intro n
    split <;> rfl
  obtain ⟨extraNodes, hn, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  constructor
  · unfold coordinateGraphX
    rw [hm, hc, hn, List.map_append, titleReservations_nodes, List.map_append, ht, hs]
    refine ⟨((titleNodes (sizeProperPortsX P exact p)).map copyF).map ProperNode.edge ++
      extraNodes.map ProperNode.edge, ?_⟩
    rw [List.append_assoc]
  · obtain ⟨extraRanks, hr⟩ := addClusterBorders_rank_prefix
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
    have htitle : ∃ tail, (titleReservations (sizeProperPortsX P exact p)).rank =
        p.rank ++ tail :=
      ⟨_, rfl⟩
    obtain ⟨tail, htitle⟩ := htitle
    refine ⟨tail ++ extraRanks, ?_⟩
    change (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).rank = _
    rw [hr, htitle, List.append_assoc]

/-- Exact port sizing can keep an exact anchor, but title reservation, border
insertion, and display-path materialization cannot shrink its measured stack. -/
theorem coordinateGraphX_plain_anchor_dims (P : Params) {exact : List Nat} {p : Proper}
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
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]? =
        some sized := by
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

/-- The exact run performs the same rank-coordinate check as the plain run;
`reserveExactRanks` only shifts the resulting coordinates. -/
theorem componentRunX_rankCoordsWith {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ y top, rankCoordsWith P.rankGap P.slot run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots)) = .ok (y, top) := by
  unfold componentRunX at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p0, hp0, h⟩ := bind_ok h
  obtain ⟨q, hq, h⟩ := bind_ok h
  obtain ⟨ord, hord, h⟩ := bind_ok h
  obtain ⟨xs, hxs, h⟩ := bind_ok h
  obtain ⟨routed, hprojection, h⟩ := bind_ok h
  obtain ⟨lanes, hr, h⟩ := bind_ok h
  obtain ⟨yt, hy, h⟩ := bind_ok h
  obtain ⟨⟨ysV, topV⟩, hres, h⟩ := bind_ok h
  clear hres
  obtain ⟨routes, hroutes, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst he
  cases yt with
  | mk y top => exact ⟨y, top, hy⟩

/-- A successful exact run keeps nonnegative proper dimensions: the
coordinate check is shared with the plain pipeline. -/
theorem componentRunX_dims_nonneg {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ProperDimsNonneg run.proper := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hproper, _, hx, hprox, hdrop,
    _, _, _⟩ := componentRunX_spec h
  obtain ⟨y, top, hy⟩ := componentRunX_rankCoordsWith h
  have hsize : CoordsImpl.sizesNonneg run.coordinateProper = true :=
    (CoordsImpl.rankCoordsWith_spec hy).2.2.2.2.1
  have hd := proxyWidths_dims_nonneg (sizesNonneg_lookup hsize) hprox
  rw [← hdrop]
  exact hd

/-- A successful exact run rejects a negative component label-stack slot,
exactly like the plain run. -/
theorem componentRunX_slot_nonneg {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    0 ≤ cg.slot := by
  obtain ⟨_, _, _, _, hn, _⟩ := componentRunX_spec h
  unfold NormalizeImpl.normalize at hn
  split at hn
  · simp at hn
  · rename_i slot hs
    split at hn
    · rename_i hc
      by_cases hz : cg.slot = 0
      · omega
      · have he : cg.slot = slot := by
          simpa [NormalizeImpl.slotOf, hz] using hs
        rw [he]
        exact hc.2.2
    · simp at hn

/-- A successful exact run retains an index for every original component node
through the label, coordinate, and proxy-materialization phases. -/
theorem componentRunX_original_nodes_covered {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∀ i, i < cg.nodes.length → i < run.proper.nodes.length := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoord, _, _, hproxy, hdrop,
    _, _, _⟩ := componentRunX_spec h
  have hnlen := normalize_nodes_length_le hn
  have hllen : p0.nodes.length ≤ labeled.nodes.length := by
    by_cases hle : p0.nodes.length ≤ labeled.nodes.length
    · exact hle
    · have hi : labeled.nodes.length < p0.nodes.length := by omega
      have hmap := (Labels.addLabelNodes_metadata hl).2.2.2 labeled.nodes.length
      have hget : p0.nodes[labeled.nodes.length]? =
          some p0.nodes[labeled.nodes.length] := by simp [hi]
      simp [hget] at hmap
  let titled := titleReservations (sizeProperPortsX P exact labeled)
  obtain ⟨_, _, extra, hextra, _⟩ :=
    OrderImpl.addClusterBorders_metadata titled P.clusterBorderW
  have hclen : labeled.nodes.length ≤ run.coordinateProper.nodes.length := by
    rw [← hcoord]
    unfold coordinateGraphX materializeDummyPaths clearProxyExtents
    simp only [List.length_map]
    rw [hextra]
    dsimp only [titled, titleReservations]
    simp only [List.length_zipIdx, List.length_map, List.length_append,
      sizeProperPortsX_length]
    omega
  have hplen := (proxyWidths_rel hproxy).2.2.1
  intro i hi
  rw [← hdrop]
  change i < q0.nodes.length
  omega

 /-- The actual exact component pipeline carries the selected measured stack
 through coordinate construction and checked proxy materialization to the exact
 anchor that forward label rendering will use. Exact anchors keep their fixed
 size, which already covers their own measured stack. -/
 theorem componentRunX_forward_anchor_size {P : Params} {exact : List Nat} {cg : Graph}
     {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     {k : Nat} {edge : Edge} {first : MeasuredLabel}
     (h : componentRunX P exact cg labels orderOptions = .ok run)
     (hk : cg.edges[k]? = some edge) (hne : edge.tail ≠ edge.head)
     (hfirst : (routeLabels labels edge.decl).head? = some first) :
     ∃ index nd,
       labelAnchorIndex run.proper k
         (rk run.proper.rank edge.tail +
           Int.fdiv (rk run.proper.rank edge.head - rk run.proper.rank edge.tail) 2) =
             some index ∧
       run.proper.nodes[index]? = some nd ∧
       (stackSize cg.slot (routeLabels labels edge.decl)).width + first.gutter ≤ nd.node.w ∧
       nd.node.h = (stackSize cg.slot (routeLabels labels edge.decl)).height := by
   obtain ⟨ranks, p0, labeled, projected, hn, hl, hc, _, _, hproxy, hdrop,
     _, _, _⟩ := componentRunX_spec h
   obtain ⟨halign0, hwf⟩ := normalize_node_rank_alignment hn
   obtain ⟨hlrank, hlkeys⟩ := addLabelNodes_anchor_keys hl
   have hllen : labeled.nodes.length = p0.nodes.length := by
     have he := congrArg List.length hlkeys
     simpa only [List.length_map] using he
   have halign : labeled.nodes.length = labeled.rank.length := by
     rw [hllen, hlrank, halign0]
   have hnodes := normalize_nodes_length_le hn
   have hedgeBounds := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hk)
   have htailBound : edge.tail < labeled.rank.length := by
     rw [hlrank]
     omega
   have hheadBound : edge.head < labeled.rank.length := by
     rw [hlrank]
     omega
   obtain ⟨index, nd, hi, hnode, hw, hh⟩ :=
     componentLabels_selected_size hk hne hfirst hl
   have hedge := labelAnchorIndex_node_edge hi hnode
   have hplain := addLabelNodes_edgeAnchorsPlain (normalize_edgeAnchorsPlain hn) hl
   have hborder : nd.node.border = 0 :=
     hplain nd (List.mem_of_getElem? hnode) (by simp [hedge])
   obtain ⟨out, hout, _, hborderOut, hwidth, hheight⟩ :=
     coordinateGraphX_plain_anchor_dims P hnode hborder
   obtain ⟨hkeysPrefix, hrankPrefix⟩ := coordinateGraphX_anchor_prefix P exact labeled
   have hicoord := labelAnchorIndex_prefix halign hkeysPrefix hrankPrefix hi
   rw [hc] at hout hicoord hrankPrefix
   obtain ⟨_, hprank, _, _, _, hpreserve⟩ := proxyWidths_rel hproxy
   have hpnode := (hpreserve index out hout (by rw [hborderOut]; omega)).1
   have hlookup : run.proper.nodes[index]? = some out := by
     rw [← hdrop]
     exact hpnode
   obtain ⟨extraRanks, hcrank⟩ := hrankPrefix
   have hfinalrank : run.proper.rank = run.coordinateProper.rank := by
     rw [← hdrop]
     exact hprank
   have htail : rk run.proper.rank edge.tail = rk labeled.rank edge.tail := by
     rw [hfinalrank, hcrank, NormalizeImpl.rk_append_left htailBound]
   have hhead : rk run.proper.rank edge.head = rk labeled.rank edge.head := by
     rw [hfinalrank, hcrank, NormalizeImpl.rk_append_left hheadBound]
   refine ⟨index, out, ?_, hlookup, ?_, hheight.trans hh⟩
   · rw [htail, hhead, ← hdrop]
     change labelAnchorIndex projected k _ = some index
     unfold labelAnchorIndex
     rw [proxyWidths_edge_keys hproxy, hprank]
     exact hicoord
   · rw [hw] at hwidth
     exact hwidth

 /-- Every envelope produced by the successful exact component pipeline reserves
 its measured label stack. Forward anchors use the exact sizing/coordinate
 transport, while loops and reversed lanes reserve stack dimensions directly. -/
 theorem componentRunX_envelopeFits {P : Params} {exact : List Nat} {cg : Graph}
     {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRunX P exact cg labels orderOptions = .ok run)
     (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter) :
     EnvelopeFits P cg run labels := by
   intro k edge env hk henv
   have hslot := componentRunX_slot_nonneg hrun
   by_cases hloop : edge.tail = edge.head
   · exact labelEnvelope_loop_fits hk hloop henv hslot hlab
   · have hreserved :
         Labels.stackWidth ((routeLabels labels edge.decl).map fun l => (l.width, l.height)) ≤ env.w ∧
         Labels.stackHeight cg.slot
           ((routeLabels labels edge.decl).map fun l => (l.width, l.height)) ≤ env.h := by
       by_cases hrev : edge.reversed = true
       · obtain ⟨hw, hh⟩ := labelEnvelope_reversed_size hloop hrev henv
         rw [hw, hh, stackSize_width_eq, stackSize_height_eq]
         exact ⟨Int.le_refl _, Int.le_refl _⟩
       · have hfalse : edge.reversed = false := by
           cases he : edge.reversed with
           | false => rfl
           | true => exact False.elim (hrev he)
         have hforward := henv
         unfold labelEnvelope at hforward
         obtain ⟨first, hfirst, hforward⟩ := Option.bind_eq_some_iff.mp hforward
         have hb : (edge.tail == edge.head) = false := by simp [hloop]
         simp only [hb, hfalse, ↓reduceIte, Bool.false_eq_true] at hforward
         obtain ⟨found, hfound, hforward⟩ := Option.bind_eq_some_iff.mp hforward
         obtain ⟨index, nd, hi, hnode, hw, hh⟩ :=
           componentRunX_forward_anchor_size hrun hk hloop hfirst
         rw [labelAnchorIndex_eq] at hi
         have hindex : found.2 = index := by
           simpa only [hfound, Option.map_some, Option.some.injEq] using hi
         have hrect : env = Labels.textRectAt run.proper run.xs run.ys found.2 first.gutter :=
           (Option.some.inj hforward).symm
         rw [hrect, hindex]
         rw [stackSize_width_eq] at hw
         rw [stackSize_height_eq] at hh
         have hbound :
             Labels.stackWidth
                 ((routeLabels labels edge.decl).map fun l => (l.width, l.height)) ≤
               nd.node.w - first.gutter ∧
             Labels.stackHeight cg.slot
                 ((routeLabels labels edge.decl).map fun l => (l.width, l.height)) ≤ nd.node.h :=
           ⟨by omega, by omega⟩
         simpa [Labels.textRectAt, Labels.rectAt, Labels.labelRect,
           RouteImpl.nodeW, RouteImpl.nodeH, hnode] using hbound
     exact labelEnvelope_nonloop_fits hk hloop henv hlab hslot hreserved.1 hreserved.2

 /-- The exact execution's measured labels have nonnegative dimensions. -/
 theorem SceneExecutionX.measured_nonneg {exactIds : List String} {inp : Input}
     {o : Options} {res : FamilyResult}
     (execution : SceneExecutionX exactIds inp o res) :
     ∀ l ∈ execution.measured, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter := by
   have hs := (checkedParams_valid execution.checked).2.2.1
   have hline := (checkedParams_sizing_nonneg execution.checked).1
   exact measureLabels_nonneg hline (by omega) execution.measured_eq

 /-- Index a component candidate node through its component entry. -/
 private theorem candidate_nodes_getElem? {g : Graph} {comp : List Nat} {index i : Nat}
     {top : Node} (h : (componentCandidate g comp index).nodes[i]? = some top) :
     ∃ j, comp[i]? = some j ∧ g.nodes.getD j default = top := by
   rw [componentCandidate_nodes] at h
   have hmap : (componentGraph g comp).nodes =
       comp.map fun v => g.nodes.getD v default := rfl
   rw [hmap, List.getElem?_map] at h
   cases hc : comp[i]? with
   | none => simp [hc] at h
   | some j =>
     simp only [hc, Option.map_some] at h
     exact ⟨j, rfl, Option.some.inj h⟩

 /-- Residual (`exactGraph`): a successful exact graph keeps every group-title
 node. `exactGraph` replaces a node only when its box carries a fixed-size
 entry, and groups with fixed sizes are plain nodes in the measured graph, so a
 `border = -2` node is never replaced; an exact id without a fixed size is a
 domain error, so success rules that case out. -/
 def ExactBorder2Unchanged {exactIds : List String} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) : Prop :=
   ∀ {j : Nat} {top0 : Node}, execution.graph0.nodes[j]? = some top0 →
     top0.border = -2 → execution.graph.nodes[j]? = some top0

 /-- Title anchors of an exact component candidate keep their measured title
 dimensions: border `-2` nodes survive `exactGraph` unchanged. -/
 theorem actual_title_dims_nonnegX {exactIds : List String} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
     (hX : ExactBorder2Unchanged execution)
     {comp : List Nat} {index i : Nat} {top : Node}
     (htop : (componentCandidate execution.graph comp index).nodes[i]? = some top)
     (hborder : top.border = -2) :
     0 ≤ top.w ∧ execution.params.clusterPad ≤ top.h := by
   obtain ⟨j, hj, hgetD⟩ := candidate_nodes_getElem? htop
   have hlen : j < execution.graph.nodes.length := by
     by_cases hjlen : j < execution.graph.nodes.length
     · exact hjlen
     · have hnone : execution.graph.nodes[j]? = none :=
         List.getElem?_eq_none_iff.mpr (by omega)
       have hdefault : (default : Node) = top := by
         simpa [List.getD, hnone] using hgetD
       rw [← hdefault] at hborder
       have hz : (default : Node).border = 0 := rfl
       rw [hz] at hborder
       omega
   have hget : execution.graph.nodes[j]? = some top := by
     have he : execution.graph.nodes[j] = top := by
       simpa [List.getD, hlen] using hgetD
     simpa [hlen] using congrArg some he
   have hlen0 : j < execution.graph0.nodes.length := by
     have hlg := exactGraph_length execution.graph_eq
     omega
   have hget0 : execution.graph0.nodes[j]? = some (execution.graph0.nodes[j]) :=
     List.getElem?_eq_some_iff.mpr ⟨hlen0, rfl⟩
   obtain ⟨nd', hnd', hnb, _, _⟩ := exactGraph_node_key execution.graph_eq hget0
   have htopEq : top = nd' := Option.some.inj (hget.symm.trans hnd')
   have hborder0 : (execution.graph0.nodes[j]).border = -2 := by
     rw [← hnb, ← htopEq]
     exact hborder
   have hA := hX hget0 hborder0
   have htop0eq : top = execution.graph0.nodes[j] :=
     Option.some.inj (hget.symm.trans hA)
   have htop0 : (componentCandidate execution.graph0 comp index).nodes[i]? = some top := by
     rw [componentCandidate_nodes]
     have hmap : (componentGraph execution.graph0 comp).nodes =
         comp.map fun v => execution.graph0.nodes.getD v default := rfl
     rw [hmap, List.getElem?_map, hj]
     have hget0' : execution.graph0.nodes[j]? = some top := by
       rw [htop0eq]
       exact hget0
     have hgd : execution.graph0.nodes.getD j default = top := by
       rw [List.getD_eq_getElem?_getD, hget0', Option.getD_some]
     simp only [Option.map_some, hgd]
   have hline := (checkedParams_sizing_nonneg execution.checked).1
   exact actual_title_dims_nonneg execution.graph0_eq hline htop0 hborder

 /-- Recover all non-envelope sizing premises from the exact component execution
 that actually emitted the part. -/
 theorem SceneExecutionX.actual_component_sizing {exactIds : List String} {inp : Input}
     {o : Options} {res : FamilyResult}
     (execution : SceneExecutionX exactIds inp o res)
     (hX : ExactBorder2Unchanged execution)
     {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts) :
     ∃ index run loops area,
       componentRunX execution.params (exactDecls exactIds inp)
         (componentCandidate execution.graph part.1 index)
         execution.measured (candidateOrder index) = .ok run ∧
       componentLoops execution.params
         (componentCandidate execution.graph part.1 index) run execution.measured = .ok loops ∧
       part.2 = { placeComponentExact execution.params
         (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
         with area := area } ∧
       ProperDimsNonneg run.proper ∧
       (∀ i, i < (componentCandidate execution.graph part.1 index).nodes.length →
         i < run.proper.nodes.length) ∧
       (∀ (i : Nat) (top : Node),
         (componentCandidate execution.graph part.1 index).nodes[i]? = some top →
         top.border = -2 → 0 ≤ top.w ∧ execution.params.clusterPad ≤ top.h) ∧
       0 ≤ (componentCandidate execution.graph part.1 index).slot := by
   obtain ⟨_, hall⟩ := actual_components_parts_geometryX (by rfl) execution.components_eq
   obtain ⟨index, _, run, loops, area, _, _, _, hrun, hloops, heq⟩ := hall part hpart
   refine ⟨index, run, loops, area, hrun, hloops, heq,
     componentRunX_dims_nonneg hrun, componentRunX_original_nodes_covered hrun, ?_,
     componentRunX_slot_nonneg hrun⟩
   intro i top htop hb
   exact actual_title_dims_nonnegX execution hX htop hb

 /-- Rectangles of an exact placed component lie inside its bounds. -/
 theorem placeComponentExact_rects_bounds (P : Params) (cg : Graph) (run : Run)
     (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
     ∀ r' ∈ (placeComponentExact P cg run cursor labels loops).rects,
       cursor ≤ r'.x ∧
       r'.x + r'.w ≤ cursor + (placeComponentExact P cg run cursor labels loops).width ∧
       0 ≤ r'.y ∧
       r'.y + r'.h ≤ (placeComponentExact P cg run cursor labels loops).height := by
   intro r' hr'
   unfold placeComponentExact at hr' ⊢
   dsimp only at hr' ⊢
   obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
   have hmem : r ∈ ((List.range cg.nodes.length).map (frameRect P cg run) ++
       ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
         ⟨q.1.x + q.1.w, q.1.y,
           (if run.exact.contains q.2 then Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
             else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
           (if run.exact.contains q.2 then
             max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
               Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
             else q.1.h)⟩) ++
       labelBounds P cg run labels ++
       (componentTitles P cg run).map (·.2)) :=
     List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hr))
   have h := shiftRect_cursor_bounds _ (run.routes.flatMap (·.points) ++
     loops.flatMap (fun q => q.2.points)) r hmem cursor
   refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [shiftRect] at h ⊢ <;> omega

 /-- Title rectangles of an exact placed component lie inside its bounds. -/
 theorem placeComponentExact_titles_bounds (P : Params) (cg : Graph) (run : Run)
     (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
     ∀ t' ∈ (placeComponentExact P cg run cursor labels loops).titles,
       cursor ≤ t'.2.x ∧
       t'.2.x + t'.2.w ≤ cursor + (placeComponentExact P cg run cursor labels loops).width ∧
       0 ≤ t'.2.y ∧
       t'.2.y + t'.2.h ≤ (placeComponentExact P cg run cursor labels loops).height := by
   intro t' ht'
   unfold placeComponentExact at ht' ⊢
   dsimp only at ht' ⊢
   obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht'
   dsimp only
   have hmem : q.2 ∈ ((List.range cg.nodes.length).map (frameRect P cg run) ++
       ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
         ⟨q.1.x + q.1.w, q.1.y,
           (if run.exact.contains q.2 then Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
             else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
           (if run.exact.contains q.2 then
             max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
               Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
             else q.1.h)⟩) ++
       labelBounds P cg run labels ++
       (componentTitles P cg run).map (·.2)) :=
     List.mem_append_right _ (List.mem_map_of_mem hq)
   have h := shiftRect_cursor_bounds _ (run.routes.flatMap (·.points) ++
     loops.flatMap (fun q => q.2.points)) q.2 hmem cursor
   refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [shiftRect] at h ⊢ <;> omega

 theorem placeComponentExact_rects_bounds_zero (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
     ∀ r' ∈ (placeComponentExact P cg run 0 labels loops).rects,
       0 ≤ r'.x ∧
       r'.x + r'.w ≤ (placeComponentExact P cg run 0 labels loops).width ∧
       0 ≤ r'.y ∧
       r'.y + r'.h ≤ (placeComponentExact P cg run 0 labels loops).height := by
   intro r' hr'
   have h := placeComponentExact_rects_bounds P cg run 0 labels loops r' hr'
   omega

 theorem placeComponentExact_titles_bounds_zero (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
     ∀ t' ∈ (placeComponentExact P cg run 0 labels loops).titles,
       0 ≤ t'.2.x ∧
       t'.2.x + t'.2.w ≤ (placeComponentExact P cg run 0 labels loops).width ∧
       0 ≤ t'.2.y ∧
       t'.2.y + t'.2.h ≤ (placeComponentExact P cg run 0 labels loops).height := by
   intro t' ht'
   have h := placeComponentExact_titles_bounds P cg run 0 labels loops t' ht'
   omega

 theorem placeComponentExact_shifted_point_bounds (P : Params) (cg : Graph) (run : Run)
     (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
     (p : Point)
     (hp : p ∈ run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points)) :
     cursor ≤ (shiftPoint (cursor - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
           ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
             ⟨q.1.x + q.1.w, q.1.y,
               (if run.exact.contains q.2 then Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
                 else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
               (if run.exact.contains q.2 then
                 max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                   Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
                 else q.1.h)⟩) ++
           labelBounds P cg run labels ++
           (componentTitles P cg run).map (·.2))
         (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX)
       (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
           ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
             ⟨q.1.x + q.1.w, q.1.y,
               (if run.exact.contains q.2 then Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
                 else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
               (if run.exact.contains q.2 then
                 max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                   Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
                 else q.1.h)⟩) ++
           labelBounds P cg run labels ++
           (componentTitles P cg run).map (·.2))
         (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY) p).x ∧
     (shiftPoint (cursor - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
           ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
             ⟨q.1.x + q.1.w, q.1.y,
               (if run.exact.contains q.2 then Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
                 else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
               (if run.exact.contains q.2 then
                 max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                   Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
                 else q.1.h)⟩) ++
           labelBounds P cg run labels ++
           (componentTitles P cg run).map (·.2))
         (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX)
       (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
           ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
             ⟨q.1.x + q.1.w, q.1.y,
               (if run.exact.contains q.2 then Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
                 else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
               (if run.exact.contains q.2 then
                 max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                   Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
                 else q.1.h)⟩) ++
           labelBounds P cg run labels ++
           (componentTitles P cg run).map (·.2))
         (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY) p).x ≤
       cursor + (placeComponentExact P cg run cursor labels loops).width ∧
     0 ≤ (shiftPoint (cursor - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
           ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
             ⟨q.1.x + q.1.w, q.1.y,
               (if run.exact.contains q.2 then Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
                 else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
               (if run.exact.contains q.2 then
                 max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                   Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
                 else q.1.h)⟩) ++
           labelBounds P cg run labels ++
           (componentTitles P cg run).map (·.2))
         (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX)
       (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
           ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
             ⟨q.1.x + q.1.w, q.1.y,
               (if run.exact.contains q.2 then Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
                 else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
               (if run.exact.contains q.2 then
                 max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                   Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
                 else q.1.h)⟩) ++
           labelBounds P cg run labels ++
           (componentTitles P cg run).map (·.2))
         (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY) p).y ∧
     (shiftPoint (cursor - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
           ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
             ⟨q.1.x + q.1.w, q.1.y,
               (if run.exact.contains q.2 then Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
                 else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
               (if run.exact.contains q.2 then
                 max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                   Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
                 else q.1.h)⟩) ++
           labelBounds P cg run labels ++
           (componentTitles P cg run).map (·.2))
         (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX)
       (0 - (boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
           ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
             ⟨q.1.x + q.1.w, q.1.y,
               (if run.exact.contains q.2 then Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
                 else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
               (if run.exact.contains q.2 then
                 max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                   Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
                 else q.1.h)⟩) ++
           labelBounds P cg run labels ++
           (componentTitles P cg run).map (·.2))
         (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY) p).y ≤
       (placeComponentExact P cg run cursor labels loops).height := by
   have h := shiftPoint_cursor_bounds ((List.range cg.nodes.length).map (frameRect P cg run) ++
       ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
         ⟨q.1.x + q.1.w, q.1.y,
           (if run.exact.contains q.2 then Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
             else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
           (if run.exact.contains q.2 then
             max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
               Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
             else q.1.h)⟩) ++
       labelBounds P cg run labels ++
       (componentTitles P cg run).map (·.2))
     (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points)) p hp cursor
   unfold placeComponentExact
   dsimp only
   exact h

 theorem placeComponentExact_shifted_point_bounds_zero (P : Params) (cg : Graph)
     (run : Run) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
     (p : Point)
     (hp : p ∈ run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points)) :
     0 ≤ (shiftPoint (0 - (placeBoundsX P cg run labels loops).minX)
       (-(placeBoundsX P cg run labels loops).minY) p).x ∧
     (shiftPoint (0 - (placeBoundsX P cg run labels loops).minX)
       (-(placeBoundsX P cg run labels loops).minY) p).x ≤
       (placeComponentExact P cg run 0 labels loops).width ∧
     0 ≤ (shiftPoint (0 - (placeBoundsX P cg run labels loops).minX)
       (-(placeBoundsX P cg run labels loops).minY) p).y ∧
     (shiftPoint (0 - (placeBoundsX P cg run labels loops).minX)
       (-(placeBoundsX P cg run labels loops).minY) p).y ≤
       (placeComponentExact P cg run 0 labels loops).height := by
   have h := placeComponentExact_shifted_point_bounds P cg run 0 labels loops p hp
   unfold placeBoundsX
   dsimp only
   refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [shiftPoint] at h ⊢ <;> omega

 /-- An exact placed component part is bounded when its proper nodes have
 nonnegative dimensions, its title anchors do, its measured labels do, and the
 label envelopes fit their stacks. The exact extents only enlarge the bounds. -/
 theorem placeComponentExact_partBounded (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
     (hdims : ProperDimsNonneg run.proper)
     (hprop : ∀ i, i < cg.nodes.length → i < run.proper.nodes.length)
     (htitles : ∀ (i : Nat) (top : Node), cg.nodes[i]? = some top → top.border = -2 →
       0 ≤ top.w ∧ P.clusterPad ≤ top.h)
     (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
     (hslot : 0 ≤ cg.slot)
     (hfit : EnvelopeFits P cg run labels) :
     PartBounded (placeComponentExact P cg run 0 labels loops) := by
   have lb_dims := labelBounds_dims P cg run labels hlab hfit
   have ct_dims := componentTitles_dims_nonneg P cg run htitles
   have width_nonneg : 0 ≤ (placeComponentExact P cg run 0 labels loops).width := by
     unfold placeComponentExact
     refine boundsOf_width_nonneg ?_
     by_cases hp : (run.routes.flatMap (·.points) ++ loops.flatMap fun q => q.2.points) = []
     · by_cases hr1 : (List.range cg.nodes.length).map (frameRect P cg run) = []
       · by_cases hr2 :
           ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx = []
         · by_cases hr3 : labelBounds P cg run labels = []
           · by_cases hr4 : (componentTitles P cg run).map (·.2) = []
             · refine Or.inr (Or.inr ⟨?_, hp⟩)
               rw [hr2, hr1, hr3, hr4]
               simp
             · obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hr4
               obtain ⟨t0, ht0, ht1⟩ := List.mem_map.mp ht
               subst ht1
               refine Or.inl ⟨t0.2, ?_, (ct_dims t0 ht0).1⟩
               rw [hr2, hr1, hr3]
               exact List.mem_append.mpr (Or.inr ht)
           · obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hr3
             refine Or.inl ⟨r, ?_, (lb_dims r hr).1⟩
             rw [hr2, hr1]
             exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hr)))
         · exfalso
           have hp0 : 0 <
               ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.length :=
             List.length_pos_iff.mpr hr2
           rw [List.length_zipIdx] at hp0
           rw [hr1] at hp0
           simp at hp0
       · obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil _ hr1
         obtain ⟨i0, hi0mem, hr0e⟩ := List.mem_map.mp hr0
         subst hr0e
         have hi0 : i0 < cg.nodes.length := List.mem_range.mp hi0mem
         have hd := frameRect_dims_nonneg P cg run i0 hdims (hprop i0 hi0)
         refine Or.inl ⟨frameRect P cg run i0, ?_, hd.1⟩
         exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
           (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨i0, hi0mem, rfl⟩))))))
     · exact Or.inr (Or.inl hp)
   have height_nonneg : 0 ≤ (placeComponentExact P cg run 0 labels loops).height := by
     unfold placeComponentExact
     refine boundsOf_height_nonneg ?_
     by_cases hp : (run.routes.flatMap (·.points) ++ loops.flatMap fun q => q.2.points) = []
     · by_cases hr1 : (List.range cg.nodes.length).map (frameRect P cg run) = []
       · by_cases hr2 :
           ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx = []
         · by_cases hr3 : labelBounds P cg run labels = []
           · by_cases hr4 : (componentTitles P cg run).map (·.2) = []
             · refine Or.inr (Or.inr ⟨?_, hp⟩)
               rw [hr2, hr1, hr3, hr4]
               simp
             · obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hr4
               obtain ⟨t0, ht0, ht1⟩ := List.mem_map.mp ht
               subst ht1
               refine Or.inl ⟨t0.2, ?_, (ct_dims t0 ht0).2⟩
               rw [hr2, hr1, hr3]
               exact List.mem_append.mpr (Or.inr ht)
           · obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hr3
             refine Or.inl ⟨r, ?_, (lb_dims r hr).2⟩
             rw [hr2, hr1]
             exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hr)))
         · exfalso
           have hp0 : 0 <
               ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.length :=
             List.length_pos_iff.mpr hr2
           rw [List.length_zipIdx] at hp0
           rw [hr1] at hp0
           simp at hp0
       · obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil _ hr1
         obtain ⟨i0, hi0mem, hr0e⟩ := List.mem_map.mp hr0
         subst hr0e
         have hi0 : i0 < cg.nodes.length := List.mem_range.mp hi0mem
         have hd := frameRect_dims_nonneg P cg run i0 hdims (hprop i0 hi0)
         refine Or.inl ⟨frameRect P cg run i0, ?_, hd.2⟩
         exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
           (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨i0, hi0mem, rfl⟩))))))
     · exact Or.inr (Or.inl hp)
   refine ⟨width_nonneg, height_nonneg, ?_, ?_, ?_, ?_⟩
   · intro r hr
     have hb := placeComponentExact_rects_bounds_zero P cg run labels loops r hr
     have hdims : 0 ≤ r.w ∧ 0 ≤ r.h := by
       obtain ⟨r0, hr0, hr1⟩ := List.mem_map.mp hr
       subst hr1
       obtain ⟨i0, hi0mem, hr2⟩ := List.mem_map.mp hr0
       subst hr2
       exact frameRect_dims_nonneg P cg run i0 hdims
         (hprop i0 (List.mem_range.mp hi0mem))
     exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hdims.1, hdims.2⟩
   · intro t ht'
     have hb := placeComponentExact_titles_bounds_zero P cg run labels loops t ht'
     obtain ⟨q0, hq0m, rfl⟩ := List.mem_map.mp ht'
     have hdim := ct_dims q0 hq0m
     exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hdim.1, hdim.2⟩
   · intro route hroute p hp
     have hb : 0 ≤ p.x ∧ p.x ≤ (placeComponentExact P cg run 0 labels loops).width ∧
         0 ≤ p.y ∧ p.y ≤ (placeComponentExact P cg run 0 labels loops).height := by
       obtain ⟨q, hqmem, hr1⟩ := List.mem_map.mp hroute
       subst hr1
       dsimp only at hp ⊢
       obtain ⟨origP, horigP, hr2⟩ := List.mem_map.mp hp
       rw [← hr2]
       cases hloop : loops.find? (fun l => l.1 == q.1.decl) with
       | some loopPt =>
         simp only [hloop, Option.map_some, Option.getD_some] at horigP
         have hpt_in : origP ∈ loops.flatMap (fun q => q.2.points) := by
           rw [List.mem_flatMap]
           exact ⟨loopPt, List.mem_of_find?_eq_some hloop, horigP⟩
         have hpt_all : origP ∈ run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points) :=
           List.mem_append_right _ hpt_in
         exact placeComponentExact_shifted_point_bounds_zero P cg run labels loops origP hpt_all
       | none =>
         simp only [hloop, Option.map_none, Option.getD_none, edgePoints] at horigP
         have hpt_in : origP ∈ run.routes.flatMap (·.points) := by
           rw [List.mem_flatMap]
           cases hrun : run.routes[q.2]? with
           | none =>
             simp only [List.getD_eq_getElem?_getD, hrun, Option.getD_none] at horigP
             change origP ∈ ([] : List Point) at horigP
             contradiction
           | some rt =>
             simp only [List.getD_eq_getElem?_getD, hrun, Option.getD_some] at horigP
             exact ⟨rt, List.mem_of_getElem? hrun, horigP⟩
         have hpt_all : origP ∈ run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points) :=
           List.mem_append_left _ hpt_in
         exact placeComponentExact_shifted_point_bounds_zero P cg run labels loops origP hpt_all
     exact hb
   · intro l hl
     obtain ⟨q0, hq0m, hl1⟩ := List.mem_map.mp hl
     have hpm : q0 ∈ placedLabels P cg run labels := hq0m
     have hb := placedLabels_within P cg run labels
       ((List.range cg.nodes.length).map (frameRect P cg run) ++
         ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
           ⟨q.1.x + q.1.w, q.1.y,
             (if run.exact.contains q.2 then Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
               else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
             (if run.exact.contains q.2 then
               max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                 Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
               else q.1.h)⟩) ++
         labelBounds P cg run labels ++ (componentTitles P cg run).map (·.2))
       (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))
       (fun r hr' => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hr'))))
       hslot hlab hfit q0 hpm
     rw [← hl1]
     dsimp only [shiftRect]
     obtain ⟨hx, hxw, hy, hyh, hw, hh⟩ := hb
     have hwidth : (placeComponentExact P cg run 0 labels loops).width =
         (boundsOf
           (List.map (frameRect P cg run) (List.range cg.nodes.length) ++
                 List.map
                   (fun q =>
                     ⟨q.1.x + q.1.w, q.1.y,
                       (if run.exact.contains q.2 then
                         Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
                         else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
                       (if run.exact.contains q.2 then
                         max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                           Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
                         else q.1.h)⟩)
                   ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx ++
               labelBounds P cg run labels ++ (componentTitles P cg run).map (·.2))
           (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).right -
       (boundsOf
           (List.map (frameRect P cg run) (List.range cg.nodes.length) ++
                 List.map
                   (fun q =>
                     ⟨q.1.x + q.1.w, q.1.y,
                       (if run.exact.contains q.2 then
                         Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
                         else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
                       (if run.exact.contains q.2 then
                         max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                           Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
                         else q.1.h)⟩)
                   ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx ++
               labelBounds P cg run labels ++ (componentTitles P cg run).map (·.2))
           (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX := rfl
     have hheight : (placeComponentExact P cg run 0 labels loops).height =
         (boundsOf
           (List.map (frameRect P cg run) (List.range cg.nodes.length) ++
                 List.map
                   (fun q =>
                     ⟨q.1.x + q.1.w, q.1.y,
                       (if run.exact.contains q.2 then
                         Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
                         else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
                       (if run.exact.contains q.2 then
                         max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                           Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
                         else q.1.h)⟩)
                   ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx ++
               labelBounds P cg run labels ++ (componentTitles P cg run).map (·.2))
           (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).bottom -
       (boundsOf
           (List.map (frameRect P cg run) (List.range cg.nodes.length) ++
                 List.map
                   (fun q =>
                     ⟨q.1.x + q.1.w, q.1.y,
                       (if run.exact.contains q.2 then
                         Loops.exactExtent cg.slot (loopSizes cg.edges labels q.2 cg.slot)
                         else Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot)),
                       (if run.exact.contains q.2 then
                         max q.1.h (((loopSizes cg.edges labels q.2 cg.slot).length : Int) *
                           Loops.band cg.slot (loopSizes cg.edges labels q.2 cg.slot))
                         else q.1.h)⟩)
                   ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx ++
               labelBounds P cg run labels ++ (componentTitles P cg run).map (·.2))
           (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY := rfl
     rw [hwidth, hheight]
     refine ⟨?_, ?_, ?_, ?_, hw, hh⟩
     · omega
     · omega
     · omega
     · omega

 /-- Every exact component part is bounded by its part dimensions. -/
 theorem exactPartsBounded {exactIds : List String} {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
     (hX : ExactBorder2Unchanged execution) :
     ∀ q ∈ execution.componentsAcc.parts, PartBounded q.2 := by
   intro q hq
   obtain ⟨index, run, loops, area, hrun, hloops, heq, hdims, hcoverage, htitles, hslot⟩ :=
     execution.actual_component_sizing hX hq
   have hbound := placeComponentExact_partBounded execution.params
     (componentCandidate execution.graph q.1 index) run execution.measured loops
     hdims hcoverage htitles execution.measured_nonneg hslot
     (componentRunX_envelopeFits hrun execution.measured_nonneg)
   rw [heq]
   exact hbound



 end PipelineImpl
 end Layered
 end Elegant

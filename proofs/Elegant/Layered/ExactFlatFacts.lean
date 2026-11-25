import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.SceneBounds
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.OrthogonalityFacts
import Elegant.Layered.InsetFit
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.MemberInFrame
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.StraightenFacts

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- One executed exact flat layout: the same phase equations as `SceneExecution`,
adapted to `exactGraph`, `sizeProperPortsX` (inside `componentRunX`),
`reserveExactRanks` (inside `componentRunX`), and `placeComponentExact`
(inside `layoutComponentX`). No field asserts a geometric bound. -/
structure SceneExecutionX (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) where
  params : Params
  metric : Measure.Metric
  lines : List (List Measure.Line)
  measured : List MeasuredLabel
  graph0 : Graph
  graph : Graph
  componentsAcc : Acc
  packedAcc : Acc
  straightAcc : Acc
  checked : checkedParams o.profile inp.kind = .ok params
  metric_eq : metricOf o.profile = .ok metric
  lines_eq : boxLines metric
    (Measure.wrapTarget metric.profile params.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
    inp = .ok lines
  measured_eq : measureLabels params metric
    (Measure.wrapTarget metric.profile params.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
    inp o.direction = .ok measured
  graph0_eq : measuredGraph params inp o lines = .ok graph0
  graph_eq : exactGraph params exactIds inp o measured graph0 = .ok graph
  components_eq : (components graph).foldlM
    (fun acc comp => layoutComponentX params exactIds inp o graph acc comp measured)
    ⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ = .ok componentsAcc
  packed_eq : packAcc params o componentsAcc = .ok packedAcc
  straight_eq : straightenAcc inp packedAcc = .ok straightAcc
  scene_eq : res.scene = sceneOf params inp o lines straightAcc measured

/-- Recover the exact phases `layoutX` used: measured graph, exact graph,
selected-component fold, and packed accumulator. -/
theorem layoutX_success_phases {exactIds : List String} {inp : Input} {o : Options}
    {result : FamilyResult} (h : layoutX exactIds inp o = .ok result) :
    ∃ P metric lines measured graph0 graph mid packed straight,
      checkedParams o.profile inp.kind = .ok P ∧
      metricOf o.profile = .ok metric ∧
      boxLines metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0)) inp = .ok lines ∧
      measureLabels P metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0)) inp o.direction = .ok measured ∧
      measuredGraph P inp o lines = .ok graph0 ∧
      exactGraph P exactIds inp o measured graph0 = .ok graph ∧
      (components graph).foldlM
        (fun acc comp => layoutComponentX P exactIds inp o graph acc comp measured)
        ⟨0, 0, 0, Array.replicate inp.boxes.length default,
          Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
          false, [], []⟩ = .ok mid ∧
      packAcc P o mid = .ok packed ∧
      straightenAcc inp packed = .ok straight ∧
      result.scene = sceneOf P inp o lines straight measured ∧
      result.budgetExhausted = straight.budget ∧
      result.itemArea = straight.parts.foldl (fun area part => area + part.2.area) 0 := by
  unfold layoutX at h
  obtain ⟨P, hP, h⟩ := bind_ok h
  obtain ⟨metric, hm, h⟩ := bind_ok h
  obtain ⟨lines, hl, h⟩ := bind_ok h
  obtain ⟨measured, hmeasured, h⟩ := bind_ok h
  obtain ⟨graph0, hg0, h⟩ := bind_ok h
  obtain ⟨graph, hg, h⟩ := bind_ok h
  obtain ⟨mid, hmid, h⟩ := bind_ok h
  obtain ⟨packed, hpacked, h⟩ := bind_ok h
  obtain ⟨straight, hstraight, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · have he := Except.ok.inj h
    subst result
    exact ⟨P, metric, lines, measured, graph0, graph, mid, packed, straight,
      hP, hm, hl, hmeasured, hg0, hg, hmid, hpacked, hstraight, rfl, rfl, rfl⟩

/-- Extract the exact measured graph, selected-component fold, and packed
accumulator that `layoutX` used. -/
theorem layoutX_sceneExecution {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res) :
    Nonempty (SceneExecutionX exactIds inp o res) := by
  obtain ⟨P, metric, lines, measured, graph0, graph, componentsAcc, packedAcc, straightAcc,
    hP, hm, hl, hmeasured, hg0, hg, hc, hp, hstraight, hs, _, _⟩ := layoutX_success_phases h
  exact ⟨⟨P, metric, lines, measured, graph0, graph, componentsAcc, packedAcc, straightAcc,
    hP, hm, hl, hmeasured, hg0, hg, hc, hp, hstraight, hs⟩⟩

private theorem orientNode_key (d : Direction) (n : Node) :
    (orientNode d n).border = n.border ∧ (orientNode d n).clusterPath = n.clusterPath ∧
      (orientNode d n).decl = n.decl := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold orientNode; split <;> rfl)


/-- `List.mapM` preserves length on success. -/
private theorem mapM_ok_len {α β : Type} (f : α → Except LayoutError β) :
    ∀ (l : List α) (out : List β), l.mapM f = Except.ok out → out.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro out h
    have he : [] = out := Except.ok.inj h
    subst out
    rfl
  | cons x xs ih =>
    intro out h
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_ok h
    obtain ⟨rest, hr, h⟩ := bind_ok h
    have he : y :: rest = out := Except.ok.inj h
    subst out
    simp only [List.length_cons, ih rest hr]

/-- `exactGraph` leaves edges untouched. -/
theorem exactGraph_edges {P : Params} {exactIds : List String} {inp : Input} {o : Options}
    {measured : List MeasuredLabel} {g g' : Graph}
    (h : exactGraph P exactIds inp o measured g = .ok g') : g'.edges = g.edges := by
  unfold exactGraph at h
  obtain ⟨nodes, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst g'
  rfl

/-- `exactGraph` preserves the node count. -/
theorem exactGraph_length {P : Params} {exactIds : List String} {inp : Input} {o : Options}
    {measured : List MeasuredLabel} {g g' : Graph}
    (h : exactGraph P exactIds inp o measured g = .ok g') :
    g'.nodes.length = g.nodes.length := by
  unfold exactGraph at h
  obtain ⟨nodes, hnodes, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst g'
  simp only
  exact mapM_ok_len _ _ _ hnodes

/-- The exact-size record only changes `w`, `h`, and `loopExtent`. -/
private theorem exactNode_success_key (d : Direction) (nd : Node) (w h : Int) (e : Int) :
    ({ orientNode d { nd with w := w, h := h } with loopExtent := e.toNat } : Node).border =
      nd.border ∧
    ({ orientNode d { nd with w := w, h := h } with loopExtent := e.toNat } : Node).clusterPath =
      nd.clusterPath ∧
    ({ orientNode d { nd with w := w, h := h } with loopExtent := e.toNat } : Node).decl =
      nd.decl := by
  obtain ⟨hb, hc, hd⟩ := orientNode_key d { nd with w := w, h := h }
  exact ⟨by simpa using hb, by simpa using hc, by simpa using hd⟩

/-- `exactGraph` preserves each node's key fields: only `w`, `h`, and
`loopExtent` change. -/
theorem exactGraph_node_key {P : Params} {exactIds : List String} {inp : Input} {o : Options}
    {measured : List MeasuredLabel} {g g' : Graph}
    (h : exactGraph P exactIds inp o measured g = .ok g')
    {v : Nat} {nd : Node} (hv : g.nodes[v]? = some nd) :
    ∃ nd', g'.nodes[v]? = some nd' ∧ nd'.border = nd.border ∧
      nd'.clusterPath = nd.clusterPath ∧ nd'.decl = nd.decl := by
  unfold exactGraph at h
  obtain ⟨nodes, hnodes, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst he
  obtain ⟨nd', hnd', hmem⟩ := (mapM_getElem? _ _ _ hnodes).2 v nd hv
  cases hbox : inp.boxes[nd.decl]? with
  | none =>
    simp only [hbox, pure, Except.pure] at hnd'
    have hred : nd' = nd := Except.ok.inj hnd'.symm
    rw [hred] at hmem
    exact ⟨nd, hmem, rfl, rfl, rfl⟩
  | some box =>
    simp only [hbox] at hnd'
    split at hnd'
    · simp only [pure, Except.pure] at hnd'
      have hred : nd' = nd := Except.ok.inj hnd'.symm
      rw [hred] at hmem
      exact ⟨nd, hmem, rfl, rfl, rfl⟩
    · cases hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
      | none =>
        simp only [hfind] at hnd'
        cases hnd'
      | some fixed =>
        simp only [hfind] at hnd'
        split at hnd'
        · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hnd'
          cases hnd'
        · split at hnd'
          · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hnd'
            cases hnd'
          · simp only [pure, Except.pure] at hnd'
            have hred := Except.ok.inj hnd'
            subst hred
            have key := exactNode_success_key o.direction nd fixed.2.w fixed.2.h
              (Loops.exactExtent P.slot (loopSizes g.edges measured nd.decl P.slot))
            exact ⟨_, hmem, key.1, key.2.1, key.2.2⟩

/-- `exactGraph` preserves declaration uniqueness: edges are untouched. -/
theorem exactGraph_decls_nodup {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {g0 g : Graph} (h0 : measuredGraph P inp o lines = .ok g0)
    (h : exactGraph P exactIds inp o measured g0 = .ok g) :
    (g.edges.map (·.decl)).Nodup := by
  rw [exactGraph_edges h]
  exact measuredGraph_decls_nodup h0

/-- `exactGraph` preserves the source-graph shape: borders and cluster paths
are untouched. -/
theorem exactGraph_shape {P : Params} {exactIds : List String} {inp : Input} {o : Options}
    {measured : List MeasuredLabel} {g0 g : Graph} (hs : CgShape g0)
    (h : exactGraph P exactIds inp o measured g0 = .ok g) : CgShape g := by
  have hlen : g.nodes.length = g0.nodes.length := exactGraph_length h
  constructor
  · intro a b na nb ha hb hna hnb hpath
    have ha' : a < g0.nodes.length := by
      have hlt := (List.getElem?_eq_some_iff.mp ha).1
      omega
    have hb' : b < g0.nodes.length := by
      have hlt := (List.getElem?_eq_some_iff.mp hb).1
      omega
    have hma : g0.nodes[a]? = some g0.nodes[a] := List.getElem?_eq_getElem ha'
    have hmb : g0.nodes[b]? = some g0.nodes[b] := List.getElem?_eq_getElem hb'
    obtain ⟨na', hna', hnab, hnap, -⟩ := exactGraph_node_key h hma
    obtain ⟨nb', hnb', hnbb, hnbp, -⟩ := exactGraph_node_key h hmb
    have e1 : na' = na := Option.some.inj (hna'.symm.trans ha)
    have e2 : nb' = nb := Option.some.inj (hnb'.symm.trans hb)
    have hmaB : (g0.nodes[a]).border = -2 := by rw [← hnab, e1]; exact hna
    have hmbB : (g0.nodes[b]).border = -2 := by rw [← hnbb, e2]; exact hnb
    have hmpath : (g0.nodes[a]).clusterPath = (g0.nodes[b]).clusterPath := by
      rw [← hnap, ← hnbp, e1, e2]; exact hpath
    exact hs.1 a b _ _ hma hmb hmaB hmbB hmpath
  · intro n hn
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hn
    have hi' : i < g0.nodes.length := by
      have hlt := (List.getElem?_eq_some_iff.mp hi).1
      omega
    have hmi : g0.nodes[i]? = some g0.nodes[i] := List.getElem?_eq_getElem hi'
    obtain ⟨n', hn', hnb, -, -⟩ := exactGraph_node_key h hmi
    have e : n' = n := Option.some.inj (hn'.symm.trans hi)
    rw [← e, hnb]
    exact hs.2 _ (List.mem_of_getElem? hmi)

/-- The exact execution covers every input box with a graph node. -/
private theorem sceneExecutionX_lines_len {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  calc execution.lines.length = (inp.boxes.zipIdx).length := mapM_ok_len _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

theorem sceneExecutionX_graph_len {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {i : Nat} (hi : i < inp.boxes.length) : i < execution.graph.nodes.length := by
  have h1 := measuredGraph_nodes_length_ge execution.graph0_eq
    (sceneExecutionX_lines_len execution)
  have h2 := exactGraph_length execution.graph_eq
  omega

/-- `sizeProperPortsX` preserves key fields, like `sizeProperPorts`. -/
theorem sizeProperPortsX_key (P : Params) (exact : List Nat) (p : Proper) (v : Nat) :
    ((sizeProperPortsX P exact p).nodes[v]?).map
        (fun nd => (nd.dummy, nd.node.border, nd.node.clusterPath)) =
      (p.nodes[v]?).map (fun nd => (nd.dummy, nd.node.border, nd.node.clusterPath)) := by
  cases hv : p.nodes[v]? with
  | none => simp [sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx, hv]
  | some nd =>
    simp only [sizeProperPortsX, List.getElem?_map, List.getElem?_zipIdx, hv,
      Option.map_some]
    split <;> rfl

/-- Chains pass through `coordinateGraphX` untouched. -/
theorem coordinateGraphX_chains (P : Params) (exact : List Nat) (p : Proper) :
    (coordinateGraphX P exact p).chains = p.chains := by
  unfold coordinateGraphX materializeDummyPaths clearProxyExtents
  exact (OrderImpl.addClusterBorders_metadata
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).2.1

/-- The exact run equations: routing and placement read the reserved
coordinates. -/
theorem componentRunX_spec {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ ranks p0 labeled q0, normalize cg ranks = .ok p0 ∧
      Labels.addLabelNodes cg p0 (componentLabels cg labels) = .ok labeled ∧
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      (∃ ord, orderWithBudget run.coordinateProper orderOptions = .ok ord ∧
        ord.layers = run.layers) ∧
      crossCoordsClusterWith P.nodeGap P.clusterPad run.coordinateProper run.layers =
        .ok run.coordinateXs ∧
      proxyWidths run.coordinateProper run.coordinateXs = .ok (q0, run.xs) ∧
      OrderImpl.dropSynthetic q0 = run.proper ∧
      RouteImpl.routeWithLanes P.slot run.proper run.layers run.xs
        (cg.edges.map (·.reversed))
        (cg.edges.map fun edge => (stackSize cg.slot (routeLabels labels edge.decl)).width) =
          .ok run.lanes ∧ run.lanes.routing = run.routing ∧
      RouteImpl.routePointsWithLanes P.slot run.proper run.layers run.xs run.ys run.top
        run.lanes = .ok run.routes := by
  unfold componentRunX at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p0, hp0, h⟩ := bind_ok h
  obtain ⟨p, hp, h⟩ := bind_ok h
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
  exact ⟨rr.ranks, p0, p, routed.1, hp0, hp, rfl, ⟨ord, hord, rfl⟩,
    hxs, hprojection, rfl, hr, rfl, hroutes⟩

/-- The exact run keeps a well-shaped proper graph. -/
theorem componentRunX_properShape {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    RouteImpl.ProperShape run.proper := by
  obtain ⟨ranks, p0, labeled, q0, hn, hlabels, hproper, _, hx, hprox, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  obtain ⟨he, _, _, hdummy⟩ := Labels.addLabelNodes_metadata hlabels
  have hlabeled : RouteImpl.ProperShape labeled :=
    RouteImpl.properShape_of_metadata he hdummy (normalize_shape hn)
  have hK : NodeKeys cg labeled := addLabelNodes_keys _ _ _ (normalize_keys hn) hlabels
  have hsized : Metadata.NodeMetadata labeled (sizeProperPortsX P exact labeled) := by
    apply Metadata.nodeMetadata_of_lookup_maps
    intro v
    have hk := congrArg (Option.map (fun t : Bool × Int × List Nat => t.1))
      (sizeProperPortsX_key P exact labeled v)
    simpa [Option.map_map, Function.comp_def] using hk
  have hs1 : RouteImpl.ProperShape (sizeProperPortsX P exact labeled) :=
    Metadata.properShape_transfer (p := labeled) (q := sizeProperPortsX P exact labeled)
      rfl hsized hlabeled
  have hT : RouteImpl.ProperShape (titleReservations (sizeProperPortsX P exact labeled)) :=
    Metadata.properShape_transfer (p := sizeProperPortsX P exact labeled) rfl
      (Metadata.nodeMetadata_map_append titleF (fun n => (titleF_keys n).1) _
        (titleReservations_nodes _)) hs1
  have hclean : ∀ e ∈ (titleReservations (sizeProperPortsX P exact labeled)).edges,
      e.synthetic = false := by
    intro e he'
    have hTe : (titleReservations (sizeProperPortsX P exact labeled)).edges = p0.edges := he
    rw [hTe] at he'
    exact normalize_clean hn e he'
  have hext := OrderImpl.addClusterBorders_metadata
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  have hAdd := Metadata.properShape_borderExtension hext hclean hT
  obtain ⟨hrE, hrR, hlen, hxlen, hP1, hP2⟩ := proxyWidths_rel hprox
  have hdropE : (OrderImpl.dropSynthetic q0).edges = (OrderImpl.dropSynthetic
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).edges := by
    show q0.edges.filter (fun e => !e.synthetic) = _
    rw [hrE, ← hproper]
    rfl
  have hmeta : Metadata.NodeMetadata (OrderImpl.dropSynthetic
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)) (OrderImpl.dropSynthetic q0) := by
    intro v nd hv'
    have hv'' : (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW).nodes[v]? = some nd := hv'
    have h1 : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)).nodes[v]? =
          some (clearF nd) := by
      rw [clearProxyExtents_nodes]
      simp only [List.getElem?_map, hv'']
      rfl
    obtain ⟨n2, hn2, hd2⟩ := materialize_exists _ h1
    have hc : (coordinateGraphX P exact labeled).nodes[v]? = some n2 := hn2
    rw [hproper] at hc
    obtain ⟨nd', hq', hd', _, _⟩ := hP1 v _ hc
    exact ⟨nd', hq', hd'.trans (hd2.trans (clearF_keys nd).1)⟩
  have hshape : RouteImpl.ProperShape run.proper := by
    rw [← hdrop]
    exact Metadata.properShape_transfer hdropE hmeta hAdd
  exact hshape

/-- Exact-run chains cover every component-graph edge. -/
theorem componentRunX_proper_chains_length {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    run.proper.chains.length = cg.edges.length := by
  obtain ⟨ranks, p0, labeled, q0, hn, hlabels, hproper, _, _, hprox, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have hdropC : run.proper.chains = q0.chains := by
    rw [← hdrop, OrderImpl.dropSynthetic_chains]
  have hproxC : q0.chains = run.coordinateProper.chains := proxyWidths_chains hprox
  have hcoordC : run.coordinateProper.chains = labeled.chains := by
    rw [← hproper]
    exact coordinateGraphX_chains P exact labeled
  obtain ⟨_, _, hlblC, _⟩ := Labels.addLabelNodes_metadata hlabels
  have hnorm : p0.chains.length = cg.edges.length := normalize_chains_length hn
  rw [hdropC, hproxC, hcoordC, hlblC, hnorm]

/-- Exact-run routes cover every proper chain. -/
theorem componentRunX_routes_length {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    run.routes.length = run.proper.chains.length := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hroutes⟩ := componentRunX_spec h
  unfold RouteImpl.routePointsWithLanes at hroutes
  split at hroutes
  · simp at hroutes
  · simpa using RouteImpl.mapOk_length _ _ _ hroutes

/-- Every component-graph edge index resolves to an exact-run route. -/
theorem componentRunX_route_of_index {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) {i : Nat}
    (hi : i < cg.edges.length) :
    ∃ rt : EdgeRoute, run.routes[i]? = some rt ∧ rt.original = i ∧
      RouteImpl.laneRouteOf P.slot run.proper run.ys run.top
        (run.layers.map (RouteImpl.layerHeight run.proper)) run.lanes i = .ok rt := by
  have hcov : i < run.proper.chains.length := by
    rw [componentRunX_proper_chains_length h]
    exact hi
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hroutes⟩ := componentRunX_spec h
  unfold RouteImpl.routePointsWithLanes at hroutes
  split at hroutes
  · simp at hroutes
  · have hrange : i < (List.range run.proper.chains.length).length := by
      simpa only [List.length_range] using hcov
    obtain ⟨rt, hget, hok⟩ := RouteImpl.mapOk_getElem _ _ _ hroutes i hrange
    have hri : (List.range run.proper.chains.length)[i] = i := by simp
    rw [hri] at hok
    exact ⟨rt, hget, RouteImpl.laneRouteOf_original hok, hok⟩

/-- Exact-run edge points read the resolved route. -/
theorem componentRunX_edgePoints_of_index {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {e : Edge} (h : componentRunX P exact cg labels orderOptions = .ok run) {i : Nat}
    (hi : i < cg.edges.length) :
    edgePoints run i e = (run.routes[i]'(by
      rw [componentRunX_routes_length h, componentRunX_proper_chains_length h]
      exact hi)).points := by
  obtain ⟨rt, hget, _, _⟩ := componentRunX_route_of_index h hi
  have hir : i < run.routes.length := (List.getElem?_eq_some_iff.mp hget).1
  have hrt : run.routes[i]'hir = rt := (List.getElem?_eq_some_iff.mp hget).2
  simp only [edgePoints, List.getD_eq_getElem?_getD, hget, Option.getD_some, hrt]

theorem componentRunX_routes_orthogonal {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∀ rt ∈ run.routes, Polyline.isOrthogonal rt.points = true := by
  have hshape := componentRunX_properShape h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hr, _, hroutes⟩ := componentRunX_spec h
  exact Layered.route_orthogonal hshape hr hroutes

theorem componentRunX_edgePoints_orthogonal {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    (i : Nat) (hi : i < cg.edges.length) :
    Polyline.isOrthogonal (edgePoints run i cg.edges[i]) = true := by
  rw [componentRunX_edgePoints_of_index h hi]
  exact componentRunX_routes_orthogonal h _ (List.getElem_mem _)

/-- Exact placement emits orthogonal routes: loops use the shared loop
facts, plain edges use the exact run. -/
theorem placeComponentExact_routes_orthogonal {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {loops : List (Nat × LoopPlacement)}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (hloops : componentLoops P cg run labels = .ok loops) (cursor : Int) :
    ∀ q ∈ (placeComponentExact P cg run cursor labels loops).routes,
      Polyline.isOrthogonal q.2 = true := by
  intro q hq
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hq
  apply (Layered.isOrthogonal_shift _ _ _).mpr
  cases hf : loops.find? (fun l => l.1 == entry.1.decl) with
  | some loop =>
    simpa only [hf, Option.map_some, Option.getD_some] using
      componentLoops_orthogonal hloops loop (List.mem_of_find?_eq_some hf)
  | none =>
    simp only [Option.map_none, Option.getD_none]
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp
      (List.mem_zipIdx_iff_getElem?.mp hentry)
    rw [← he]
    exact componentRunX_edgePoints_orthogonal hrun _ hi

private def RoutesOrthogonalX (a : Array (List Point)) : Prop :=
  ∀ k, Polyline.isOrthogonal (a.getD k []) = true

private theorem routes_fold_orthogonalX (entries : List (Nat × List Point))
    (f : List Point → List Point)
    (hf : ∀ points, Polyline.isOrthogonal points = true →
      Polyline.isOrthogonal (f points) = true)
    (he : ∀ q ∈ entries, Polyline.isOrthogonal q.2 = true)
    (a : Array (List Point)) (ha : RoutesOrthogonalX a) :
    RoutesOrthogonalX (entries.foldl (fun arr q => arr.set! q.1 (f q.2)) a) := by
  induction entries generalizing a with
  | nil => exact ha
  | cons q rest ih =>
    simp only [List.foldl_cons]
    apply ih (fun r hr => he r (List.mem_cons_of_mem _ hr))
    intro k
    rw [RankImpl.getD_set!]
    split
    · exact hf q.2 (he q List.mem_cons_self)
    · exact ha k

private theorem placePartX_routes_orthogonal {P : Params} {exact : List Nat}
    {comp : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {acc out : Acc}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (ha : RoutesOrthogonalX acc.routes)
    (h : placePart comp cg run P acc labels (@placeComponentExact) true = .ok out) :
    RoutesOrthogonalX out.routes := by
  unfold placePart at h
  obtain ⟨loops, hloops, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp at h
  · have he := Except.ok.inj h
    subst out
    exact routes_fold_orthogonalX _ id (fun _ h => h)
      (placeComponentExact_routes_orthogonal hrun hloops 0) _ ha


/-- The exact component record: chosen portfolio trial with exact run,
loops, and exact-placed routes. -/
def ActualPartX (P : Params) (exactIds : List String) (inp : Input) (o : Options)
    (g : Graph) (labels : List MeasuredLabel) (q : List Nat × Part) : Prop :=
  ∃ index chosen run loops,
    index < 5 ∧
    Portfolio.portfolio o.thoroughness
      (componentTrialX P exactIds inp o g q.1 labels) = .ok chosen ∧
    chosen.value = (componentCandidate g q.1 index, run) ∧
    componentRunX P (exactDecls exactIds inp) (componentCandidate g q.1 index) labels
      (candidateOrder index) = .ok run ∧
    componentLoops P (componentCandidate g q.1 index) run labels = .ok loops ∧
    q.2.routes = (placeComponentExact P (componentCandidate g q.1 index) run 0 labels
      loops).routes

theorem placePartX_parts {comp : List Nat} {cg : Graph} {run : Run}
    {P : Params} {acc out : Acc} {labels : List MeasuredLabel}
    (h : placePart comp cg run P acc labels (@placeComponentExact) true = .ok out) :
    ∃ loops part, componentLoops P cg run labels = .ok loops ∧
      out.parts = acc.parts ++ [(comp, part)] ∧
      part.routes = (placeComponentExact P cg run 0 labels loops).routes := by
  unfold placePart at h
  obtain ⟨loops, hloops, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp at h
  · have he := Except.ok.inj h
    subst out
    exact ⟨loops, _, hloops, rfl, rfl⟩

theorem layoutComponentX_parts {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {g : Graph} {acc out : Acc} {comp : List Nat}
    {labels : List MeasuredLabel}
    (h : layoutComponentX P exactIds inp o g acc comp labels = .ok out) :
    ∃ part, out.parts = acc.parts ++ [(comp, part)] ∧
      ActualPartX P exactIds inp o g labels (comp, part) := by
  unfold layoutComponentX at h
  obtain ⟨chosen, hc, h⟩ := bind_ok h
  obtain ⟨placed, hp, h⟩ := bind_ok h
  obtain ⟨metric, _, h⟩ := bind_ok h
  obtain ⟨areas, _, h⟩ := bind_ok h
  obtain ⟨loops, part, hl, hparts, hroutes⟩ := placePartX_parts hp
  obtain ⟨index, trial, hi, ht, hv, _⟩ := Portfolio.portfolio_selected hc
  unfold componentTrialX at ht
  obtain ⟨run, hrun, ht⟩ := bind_ok ht
  obtain ⟨_, _, ht⟩ := bind_ok ht
  have htrial := Except.ok.inj ht
  subst trial
  dsimp only at hv
  have he := Except.ok.inj h
  subst out
  let childArea := inp.fixedAreas.foldl (fun total child =>
    if chosen.scene.boxes.any (fun box => box.id == child.1) then total + child.2 else total) 0
  let augmented := { part with area := part.area + childArea + areas.sum }
  refine ⟨augmented, ?_, ?_⟩
  · simp [hparts, augmented, childArea]
  · unfold ActualPartX
    refine ⟨index, chosen, run, loops, hi, hc, hv, hrun, ?_, ?_⟩
    · simpa only [hv] using hl
    · simpa only [hv] using hroutes

theorem foldlM_layout_components_partsX (P : Params) (exactIds : List String) (inp : Input)
    (o : Options) (g : Graph) (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels)
        start = .ok out →
      ∃ parts, out.parts = start.parts ++ parts ∧ parts.map (·.1) = comps ∧
        ∀ q ∈ parts, ActualPartX P exactIds inp o g labels q := by
  intro comps
  induction comps with
  | nil =>
    intro start out h
    simp only [List.foldlM_nil] at h
    have hout : start = out := Except.ok.inj h
    subst out
    exact ⟨[], by simp, rfl, by simp⟩
  | cons comp comps ih =>
    intro start out h
    rw [List.foldlM_cons] at h
    obtain ⟨next, hn, hrest⟩ := bind_ok h
    obtain ⟨part, hp, hprod⟩ := layoutComponentX_parts hn
    obtain ⟨parts, hout, hmap, hall⟩ := ih next out hrest
    refine ⟨(comp, part) :: parts, ?_, ?_, ?_⟩
    · rw [hout, hp]
      simp only [List.append_assoc, List.singleton_append]
    · simp only [List.map_cons, hmap]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hprod
      · exact hall q hq

theorem actual_components_partsX {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {g : Graph} {labels : List MeasuredLabel} {start out : Acc}
    (hempty : start.parts = [])
    (h : (components g).foldlM
      (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels) start = .ok out) :
    out.parts.map (·.1) = components g ∧
      ∀ q ∈ out.parts, ActualPartX P exactIds inp o g labels q := by
  obtain ⟨parts, hp, hm, hall⟩ :=
    foldlM_layout_components_partsX P exactIds inp o g labels _ _ _ h
  simp only [hempty, List.nil_append] at hp
  subst parts
  exact ⟨hm, hall⟩

private theorem layoutComponentX_routes_orthogonal {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {g : Graph} {comp : List Nat}
    {labels : List MeasuredLabel} {acc out : Acc}
    (ha : RoutesOrthogonalX acc.routes)
    (h : layoutComponentX P exactIds inp o g acc comp labels = .ok out) :
    RoutesOrthogonalX out.routes := by
  unfold layoutComponentX at h
  obtain ⟨chosen, hc, h⟩ := bind_ok h
  obtain ⟨placed, hp, h⟩ := bind_ok h
  obtain ⟨metric, _, h⟩ := bind_ok h
  obtain ⟨areas, _, h⟩ := bind_ok h
  obtain ⟨index, trial, _, ht, hv, _⟩ := Portfolio.portfolio_selected hc
  unfold componentTrialX at ht
  obtain ⟨run, hrun, ht⟩ := bind_ok ht
  obtain ⟨_, _, ht⟩ := bind_ok ht
  have htrial := Except.ok.inj ht
  subst trial
  dsimp only at hv
  rw [hv] at hp
  have hplaced := placePartX_routes_orthogonal hrun ha hp
  have he := Except.ok.inj h
  subst out
  exact hplaced

private theorem componentsX_routes_orthogonal {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {g : Graph} {labels : List MeasuredLabel} :
    ∀ (comps : List (List Nat)) (start out : Acc),
      RoutesOrthogonalX start.routes →
      comps.foldlM (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels)
        start = .ok out →
      RoutesOrthogonalX out.routes := by
  intro comps
  induction comps with
  | nil =>
    intro start out ha h
    have he : start = out := Except.ok.inj h
    subst out
    exact ha
  | cons comp comps ih =>
    intro start out ha h
    simp only [List.foldlM_cons] at h
    obtain ⟨mid, hm, h⟩ := bind_ok h
    apply ih mid out
    · exact layoutComponentX_routes_orthogonal ha hm
    · exact h

private theorem packAccX_routes_orthogonal {P : Params} {o : Options} {acc out : Acc}
    (ha : RoutesOrthogonalX acc.routes)
    (hparts : ∀ q ∈ acc.parts, ∀ route ∈ q.2.routes,
      Polyline.isOrthogonal route.2 = true)
    (h : packAcc P o acc = .ok out) : RoutesOrthogonalX out.routes := by
  unfold packAcc at h
  obtain ⟨packed, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst out
  rw [packAcc_routes_eq_foldl]
  have hpairs : ∀ q ∈ acc.parts.zip packed.boxes,
      ∀ route ∈ q.1.2.routes, Polyline.isOrthogonal route.2 = true := by
    intro q hq
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hq
    exact hparts q.1 (List.mem_of_getElem? (zip_getElem?_left hk))
  have preserve : ∀ (pairs : List ((List Nat × Part) × Rect)) (a : Array (List Point)),
      (∀ q ∈ pairs, ∀ route ∈ q.1.2.routes,
        Polyline.isOrthogonal route.2 = true) →
      RoutesOrthogonalX a →
      RoutesOrthogonalX (pairs.foldl (fun arr q => q.1.2.routes.foldl
        (fun a r => a.set! r.1 (r.2.map (shiftPoint q.2.x q.2.y))) arr) a) := by
    intro pairs
    induction pairs with
    | nil => intro a _ ha; exact ha
    | cons q pairs ih =>
      intro a hpairs ha
      simp only [List.foldl_cons]
      apply ih _ (fun r hr => hpairs r (List.mem_cons_of_mem _ hr))
      exact routes_fold_orthogonalX _ _
        (fun points h => (Layered.isOrthogonal_shift _ _ points).mpr h)
        (hpairs q List.mem_cons_self) _ ha
  exact preserve _ _ hpairs ha

theorem SceneExecutionX.routes_orthogonal {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    ∀ route ∈ res.scene.routes, Polyline.isOrthogonal route.points = true := by
  have hinit : RoutesOrthogonalX (Array.replicate inp.routes.length ([] : List Point)) := by
    intro k
    simp [Array.getD, Polyline.isOrthogonal]
  have hmid := componentsX_routes_orthogonal _ _ _ hinit execution.components_eq
  have hparts : ∀ q ∈ execution.componentsAcc.parts,
      ∀ route ∈ q.2.routes, Polyline.isOrthogonal route.2 = true := by
    obtain ⟨_, hall⟩ := actual_components_partsX rfl execution.components_eq
    intro q hq
    obtain ⟨_, _, run, loops, _, _, _, hrun, hloops, hroutes⟩ := hall q hq
    rw [hroutes]
    exact placeComponentExact_routes_orthogonal hrun hloops 0
  have hpacked := packAccX_routes_orthogonal hmid hparts execution.packed_eq
  have hstart : ∀ (j : Nat) (pts : List Point), execution.packedAcc.routes[j]? = some pts →
      Polyline.isOrthogonal pts = true := by
    intro j pts hj
    have hget : execution.packedAcc.routes.getD j [] = pts := by
      rw [Array.getD_eq_getD_getElem?, hj, Option.getD_some]
    rw [← hget]
    exact hpacked j
  have hstraight := straightenAcc_routes_orthogonal execution.straight_eq hstart
  have hstraightD : ∀ k, Polyline.isOrthogonal (execution.straightAcc.routes.getD k []) = true := by
    intro k
    cases hget : execution.straightAcc.routes[k]? with
    | none =>
      rw [Array.getD_eq_getD_getElem?, hget, Option.getD_none]
      rfl
    | some pts =>
      rw [Array.getD_eq_getD_getElem?, hget, Option.getD_some]
      exact hstraight k pts hget
  rw [execution.scene_eq]
  intro route hroute
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hroute
  exact (Layered.isOrthogonal_shift_orient _ _ _ _ _).mpr (hstraightD q.2)

/-- Clause 4 of the layout validator for a successful exact flat
`PipelineImpl.layoutX`: every scene route is orthogonal. -/
theorem layoutX_c4 {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res) :
    Validator.C4 res.scene.layoutDump := by
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  intro route hroute _
  exact execution.routes_orthogonal route hroute

/-- Residual: exact component placement facts used by the inset and
parent-containment lifts.

The exact flat layout shares packing, scene assembly, routing, and loop
placement with the plain pipeline, but four phases differ: `exactGraph`
(fixed node sizes), `sizeProperPortsX` (no port widening for exact nodes),
`reserveExactRanks` (loop-band rank reservation), and `placeComponentExact`
with `exactFootprints := true` (exact extents). The three facts below are the
only changed-phase obligations the flat lifts need:

* every exact component part is bounded by its part dimensions
  (`PartBounded`), which the inset lift needs;
* inside every successful exact component run, every member frame lies in its
  parent group frame, which the parent-containment lift needs;
* every parent-group key lies in the same executed component as its member
  key, which the parent-containment lift needs to locate the parent frame.
  This is a purely combinatorial fact about the executed graph and its
  components (no scene geometry): `exactGraph` preserves the edges,
  declarations, borders, and cluster paths the plain argument uses, so the
  same constraint edges join the same endpoints.

All three hold for executed layouts under `WellFormed (inputModel inp o)` and
`framedParents inp = true`: on success the exact sizes come from the
recursion's `childFrameSize` reservations (nonnegative, with exact loop
extents checked nonnegative by `exactGraph`), and frame nesting follows the
same cluster geometry as plain runs. The unguarded member-frame form is false
without those premises (a node used as a parent is not a group frame). They
are stated here as the single hypothesis the two lifts share because proving
them needs the exact coordinate facts (`reserveExactRanks` shifts and exact
port widths), not because they are in doubt for executed layouts. -/
def ExactComponentPlacement (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  WellFormed (inputModel inp o) → framedParents inp = true →
  ∀ (execution : SceneExecutionX exactIds inp o res),
    (∀ q ∈ execution.componentsAcc.parts, PartBounded q.2) ∧
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
            run memberIndex)) ∧
    (∀ (comp : List Nat) (_hcomp : comp ∈ components execution.graph)
      (key parentKey : Nat) (_hkeyLen : key < inp.boxes.length) (_hkeyIn : key ∈ comp)
      (member : Node) (_hmemberGraph : execution.graph.nodes[key]? = some member)
      (childBox : ModelBox) (_hchildBox : inp.boxes[key]? = some childBox)
      (parentBox : ModelBox) (_hparentBox : inp.boxes[parentKey]? = some parentBox)
      (_hparentRef : childBox.parent = parentBox.id) (_hparentNe : childBox.parent ≠ ""),
      parentKey ∈ comp)

theorem layoutComponentX_rects_cover {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {g : Graph} {acc acc' : Acc} {comp : List Nat}
    {measured : List MeasuredLabel}
    (h : layoutComponentX P exactIds inp o g acc comp measured = .ok acc') :
    ∀ i (r : Rect), acc'.rects[i]? = some r →
      (∃ part ∈ acc'.parts, RectCovered part.1 part.2.rects.length i ∧ i < acc.rects.size) ∨
      acc.rects[i]? = some r := by
  unfold layoutComponentX at h
  obtain ⟨chosen, hchosen, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  intro i r hi
  rw [← congrArg Acc.rects he] at hi
  dsimp only at hi
  unfold placePart at hresult
  obtain ⟨loops, hloops, hres⟩ := bind_ok hresult
  dsimp only at hres
  split at hres
  · simp at hres
  · obtain ⟨part0, _hPl, hrects0⟩ :
        ∃ p : Part, result.parts = acc.parts ++ [(comp, p)] ∧
          p.rects = (placeComponentExact P chosen.value.1 chosen.value.2 0 measured
            loops).rects := by
      apply Exists.intro
      refine ⟨Eq.symm (congrArg Acc.parts (Except.ok.inj hres)), rfl⟩
    have heq := Except.ok.inj hres
    subst heq
    dsimp only at hi
    rcases zipCover_rects id _ comp acc.rects i r hi with hz | h
    · obtain ⟨k, hk, hkl, hil⟩ := hz
      obtain ⟨partApp, hmem0, hpartsEq⟩ : ∃ p : Part,
          acc'.parts = acc.parts ++ [(comp, p)] ∧ p.rects = part0.rects := by
        rw [← congrArg Acc.parts he]
        apply Exists.intro
        · refine ⟨?_, ?_⟩
          · simp only [List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero,
              List.map_cons, List.map_nil, List.nil_append]
            try rfl
          · exact hrects0.symm
      refine Or.inl ⟨(comp, partApp), ?_, ?_, hil⟩
      · rw [hmem0]
        exact List.mem_append.mpr (Or.inr (by simp))
      · rw [hpartsEq, hrects0]
        exact ⟨k, hk, hkl⟩
    · exact Or.inr h

theorem layoutComponentX_routes_cover {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {g : Graph} {acc acc' : Acc} {comp : List Nat}
    {measured : List MeasuredLabel}
    (h : layoutComponentX P exactIds inp o g acc comp measured = .ok acc') :
    ∀ i (pts : List Point), acc'.routes[i]? = some pts →
      (∃ part ∈ acc'.parts, RouteCovered part.2.routes i ∧ i < acc.routes.size) ∨
      acc.routes[i]? = some pts := by
  unfold layoutComponentX at h
  obtain ⟨chosen, hchosen, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  intro i pts hi
  rw [← congrArg Acc.routes he] at hi
  dsimp only at hi
  unfold placePart at hresult
  obtain ⟨loops, hloops, hres⟩ := bind_ok hresult
  dsimp only at hres
  split at hres
  · simp at hres
  · obtain ⟨part0, _hPl, hroutes0⟩ : ∃ p : Part,
        result.parts = acc.parts ++ [(comp, p)] ∧
          p.routes = (placeComponentExact P chosen.value.1 chosen.value.2 0 measured
            loops).routes := by
      apply Exists.intro
      exact ⟨Eq.symm (congrArg Acc.parts (Except.ok.inj hres)), rfl⟩
    have heq := Except.ok.inj hres
    subst heq
    dsimp only at hi
    rcases keyCover_pts id _ acc.routes i pts hi with hz | h
    · obtain ⟨r, hr, hke, hil⟩ := hz
      obtain ⟨partApp, hmem0, hpartsEq⟩ : ∃ p : Part,
          acc'.parts = acc.parts ++ [(comp, p)] ∧ p.routes = part0.routes := by
        rw [← congrArg Acc.parts he]
        apply Exists.intro
        · refine ⟨?_, ?_⟩
          · simp only [List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero,
              List.map_cons, List.map_nil, List.nil_append]
            try rfl
          · exact hroutes0.symm
      refine Or.inl ⟨(comp, partApp), ?_, ?_, hil⟩
      · rw [hmem0]
        exact List.mem_append.mpr (Or.inr (by simp))
      · rw [hpartsEq, hroutes0]
        exact ⟨r, hr, hke⟩
    · exact Or.inr h

theorem layoutComponentX_labels_cover {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {g : Graph} {acc acc' : Acc} {comp : List Nat}
    {measured : List MeasuredLabel}
    (h : layoutComponentX P exactIds inp o g acc comp measured = .ok acc') :
    ∀ i (r : Rect), acc'.labels[i]? = some r →
      (∃ part ∈ acc'.parts, LabelCovered part.2.labels i ∧ i < acc.labels.size) ∨
      acc.labels[i]? = some r := by
  unfold layoutComponentX at h
  obtain ⟨chosen, hchosen, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  intro i r hi
  rw [← congrArg Acc.labels he] at hi
  dsimp only at hi
  unfold placePart at hresult
  obtain ⟨loops, hloops, hres⟩ := bind_ok hresult
  dsimp only at hres
  split at hres
  · simp at hres
  · obtain ⟨part0, _hPl, hlabels0⟩ : ∃ p : Part,
        result.parts = acc.parts ++ [(comp, p)] ∧
          p.labels = (placeComponentExact P chosen.value.1 chosen.value.2 0 measured
            loops).labels := by
      apply Exists.intro
      exact ⟨Eq.symm (congrArg Acc.parts (Except.ok.inj hres)), rfl⟩
    have heq := Except.ok.inj hres
    subst heq
    dsimp only at hi
    rcases keyCover_rects id _ acc.labels i r hi with hz | h
    · obtain ⟨q, hq, hke, hil⟩ := hz
      obtain ⟨partApp, hmem0, hpartsEq⟩ : ∃ p : Part,
          acc'.parts = acc.parts ++ [(comp, p)] ∧ p.labels = part0.labels := by
        rw [← congrArg Acc.parts he]
        apply Exists.intro
        · refine ⟨?_, ?_⟩
          · simp only [List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero,
              List.map_cons, List.map_nil, List.nil_append]
            try rfl
          · exact hlabels0.symm
      refine Or.inl ⟨(comp, partApp), ?_, ?_, hil⟩
      · rw [hmem0]
        exact List.mem_append.mpr (Or.inr (by simp))
      · rw [hpartsEq, hlabels0]
        exact ⟨q, hq, hke⟩
    · exact Or.inr h

theorem layoutComponentX_sizes {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {g : Graph} {acc acc' : Acc} {comp : List Nat}
    {measured : List MeasuredLabel}
    (h : layoutComponentX P exactIds inp o g acc comp measured = .ok acc') :
    acc.rects.size = acc'.rects.size ∧ acc.routes.size = acc'.routes.size ∧
      acc.labels.size = acc'.labels.size := by
  unfold layoutComponentX at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  have hr := congrArg Acc.rects he
  have ho := congrArg Acc.routes he
  have hl := congrArg Acc.labels he
  unfold placePart at hresult
  obtain ⟨_, _, hres⟩ := bind_ok hresult
  dsimp only at hres
  split at hres
  · simp at hres
  · have heq := Except.ok.inj hres
    subst heq
    dsimp only at hr ho hl
    refine ⟨?_, ?_, ?_⟩
    · rw [← hr]; exact (size_zipFold_eq id _ _ _).symm
    · rw [← ho]; exact (size_keyFold_pts_eq id _ _).symm
    · rw [← hl]; exact (size_keyFold_rects_eq id _ _).symm

theorem layoutComponentX_parts_mono {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {g : Graph} {acc acc' : Acc} {comp : List Nat}
    {measured : List MeasuredLabel}
    (h : layoutComponentX P exactIds inp o g acc comp measured = .ok acc') :
    ∀ q ∈ acc.parts, q ∈ acc'.parts := by
  unfold layoutComponentX at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  have hp := congrArg Acc.parts he
  intro q hq
  rw [← hp]
  exact List.mem_append.mpr (Or.inl hq)

theorem SceneExecutionX.packedAcc_bounded {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hparts : ∀ q ∈ execution.componentsAcc.parts, PartBounded q.2) :
    AccBounded execution.packedAcc.canvasW execution.packedAcc.canvasH
      execution.packedAcc := by
  have hstart_rects : ∀ (i : Nat) (r : Rect),
      execution.componentsAcc.rects[i]? = some r →
      ((∀ q ∈ execution.componentsAcc.parts, ¬ RectCovered q.1 q.2.rects.length i) ∨
        i ≥ execution.componentsAcc.rects.size) → r = default := by
    refine foldlM_rects_uncovered
      (fun a c => layoutComponentX execution.params exactIds inp o
        execution.graph a c execution.measured)
      (fun start comp acc' hc => layoutComponentX_rects_cover hc)
      (fun start comp acc' hc => layoutComponentX_parts_mono hc)
      (components execution.graph)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩
      execution.componentsAcc execution.components_eq ?_
    exact fun i r hi _ => (layout_startAcc_defaults inp).1 i r hi
  have hstart_routes : ∀ (i : Nat) (pts : List Point),
      execution.componentsAcc.routes[i]? = some pts →
      ((∀ q ∈ execution.componentsAcc.parts, ¬ RouteCovered q.2.routes i) ∨
        i ≥ execution.componentsAcc.routes.size) → pts = [] := by
    refine foldlM_routes_uncovered
      (fun a c => layoutComponentX execution.params exactIds inp o
        execution.graph a c execution.measured)
      (fun start comp acc' hc => layoutComponentX_routes_cover hc)
      (fun start comp acc' hc => layoutComponentX_parts_mono hc)
      (components execution.graph)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩
      execution.componentsAcc execution.components_eq ?_
    exact fun i pts hi _ => (layout_startAcc_defaults inp).2.1 i pts hi
  have hstart_labels : ∀ (i : Nat) (r : Rect),
      execution.componentsAcc.labels[i]? = some r →
      ((∀ q ∈ execution.componentsAcc.parts, ¬ LabelCovered q.2.labels i) ∨
        i ≥ execution.componentsAcc.labels.size) → r = default := by
    refine foldlM_labels_uncovered
      (fun a c => layoutComponentX execution.params exactIds inp o
        execution.graph a c execution.measured)
      (fun start comp acc' hc => layoutComponentX_labels_cover hc)
      (fun start comp acc' hc => layoutComponentX_parts_mono hc)
      (components execution.graph)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩
      execution.componentsAcc execution.components_eq ?_
    exact fun i r hi _ => (layout_startAcc_defaults inp).2.2 i r hi
  exact packAcc_bounded hparts hstart_rects hstart_routes hstart_labels execution.packed_eq

theorem SceneExecutionX.straightAcc_bounded {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hparts : ∀ q ∈ execution.componentsAcc.parts, PartBounded q.2) :
    AccBounded execution.straightAcc.canvasW execution.straightAcc.canvasH
      execution.straightAcc := by
  have hp := execution.packedAcc_bounded hparts
  obtain ⟨r1, r2, r3, r4, r5, _, hroutes⟩ :=
    straightenAcc_bounded execution.straight_eq hp.routes_bounded
  rw [r4, r5]
  refine ⟨hp.canvas_w_nonneg, hp.canvas_h_nonneg, ?_, ?_, hroutes, ?_⟩
  · intro i r hi
    rw [r1] at hi
    exact hp.rects_bounded i r hi
  · intro t ht
    rw [r3] at ht
    exact hp.titles_bounded t ht
  · intro i r hi
    rw [r2] at hi
    exact hp.labels_bounded i r hi

/-- The exact flat `layoutX` keeps every box inside the margin inset of its
canvas, with the parameters the execution actually used. -/
theorem layoutX_inset {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hX : ExactComponentPlacement exactIds inp o res) :
    ∃ P : Params, checkedParams o.profile inp.kind = .ok P ∧
      0 ≤ P.canvasMargin ∧ InsetC1 res.scene P.canvasMargin := by
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hacc := SceneExecutionX.straightAcc_bounded execution ((hX hwf hframed execution).1)
  have hm1 := checkedParams_canvasMargin_ge_one execution.checked
  refine ⟨execution.params, execution.checked, by omega, ?_⟩
  rw [execution.scene_eq]
  exact sceneOf_boxes_inset execution.params inp o execution.lines
    execution.straightAcc execution.measured hacc (by omega)

private theorem componentFold_rects_sizeX (P : Params) (exactIds : List String) (inp : Input)
    (o : Options) (g : Graph) (measured : List MeasuredLabel) (comps : List (List Nat)) :
    ∀ start out : Acc,
      comps.foldlM (fun acc comp => layoutComponentX P exactIds inp o g acc comp measured)
        start = .ok out → out.rects.size = start.rects.size := by
  induction comps with
  | nil =>
    intro start out h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
  | cons comp rest ih =>
    intro start out h
    simp only [List.foldlM_cons] at h
    cases hc : layoutComponentX P exactIds inp o g start comp measured with
    | error e => simp [hc, bind, Except.bind] at h
    | ok next =>
      simp only [hc, bind, Except.bind] at h
      exact (ih next out h).trans (layoutComponentX_sizes hc).1.symm

theorem SceneExecutionX.components_rects_size {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    execution.componentsAcc.rects.size = inp.boxes.length := by
  have h := componentFold_rects_sizeX execution.params exactIds inp o execution.graph
    execution.measured (components execution.graph) _ _ execution.components_eq
  simpa only [Array.size_replicate] using h

theorem sceneExecutionX_edges_bounded {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    ∀ e ∈ execution.graph.edges ++ Compound.constraints execution.graph,
      e.tail < execution.graph.nodes.length ∧
        e.head < execution.graph.nodes.length := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · rw [exactGraph_edges execution.graph_eq] at he
    have hlines := sceneExecutionX_lines_len execution
    have hbd := measuredGraph_edges_bounded execution.graph0_eq hlines e he
    have hlen := exactGraph_length execution.graph_eq
    omega
  · exact constraints_bounded _ e he

private theorem placeComponentExact_rects_length (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run cursor labels loops).rects.length = cg.nodes.length := by
  unfold placeComponentExact
  simp [List.length_map, List.length_range]

private theorem componentCandidate_nodes_lengthX (g : Graph) (comp : List Nat)
    (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  show (comp.map fun v => g.nodes.getD v default).length = comp.length
  exact List.length_map ..

private theorem mem_zip_introX {α β : Type} {l : List α} {l' : List β} {i : Nat}
    {a : α} {b : β} (h1 : l[i]? = some a) (h2 : l'[i]? = some b) : (a, b) ∈ l.zip l' := by
  induction l generalizing l' i with
  | nil => rw [List.getElem?_nil] at h1; exact absurd h1 (by simp)
  | cons x xs ih =>
    cases l' with
    | nil => rw [List.getElem?_nil] at h2; exact absurd h2 (by simp)
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq]
      cases i with
      | zero =>
        rw [List.getElem?_cons_zero] at h1 h2
        simp only [Option.some.injEq] at h1 h2
        subst h1
        subst h2
        exact Or.inl ⟨rfl, rfl⟩
      | succ i' =>
        rw [List.getElem?_cons_succ] at h1 h2
        exact Or.inr (ih h1 h2)

/-- The exact component geometry record: chosen portfolio trial with the
exact-placed part up to its area. -/
def ActualPartGeometryX (P : Params) (exactIds : List String) (inp : Input)
    (o : Options) (g : Graph) (labels : List MeasuredLabel) (q : List Nat × Part) : Prop :=
  ∃ index chosen run loops area,
    index < 5 ∧
    Portfolio.portfolio o.thoroughness
      (componentTrialX P exactIds inp o g q.1 labels) = .ok chosen ∧
    chosen.value = (componentCandidate g q.1 index, run) ∧
    componentRunX P (exactDecls exactIds inp) (componentCandidate g q.1 index) labels
      (candidateOrder index) = .ok run ∧
    componentLoops P (componentCandidate g q.1 index) run labels = .ok loops ∧
    q.2 = { placeComponentExact P (componentCandidate g q.1 index) run 0 labels loops
      with area := area }

theorem placePartX_parts_geometry {comp : List Nat} {cg : Graph} {run : Run}
    {P : Params} {acc out : Acc} {labels : List MeasuredLabel}
    (h : placePart comp cg run P acc labels (@placeComponentExact) true = .ok out) :
    ∃ loops area,
      componentLoops P cg run labels = .ok loops ∧
      out.parts = acc.parts ++ [(comp,
        { placeComponentExact P cg run 0 labels loops with area := area })] := by
  unfold placePart at h
  obtain ⟨loops, hl, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp at h
  · have he := Except.ok.inj h
    subst out
    exact ⟨loops, _, hl, rfl⟩

theorem layoutComponentX_parts_geometry {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {g : Graph} {acc out : Acc} {comp : List Nat}
    {labels : List MeasuredLabel}
    (h : layoutComponentX P exactIds inp o g acc comp labels = .ok out) :
    ∃ part, out.parts = acc.parts ++ [(comp, part)] ∧
      ActualPartGeometryX P exactIds inp o g labels (comp, part) := by
  unfold layoutComponentX at h
  obtain ⟨chosen, hc, h⟩ := bind_ok h
  obtain ⟨placed, hp, h⟩ := bind_ok h
  obtain ⟨metric, _, h⟩ := bind_ok h
  obtain ⟨areas, _, h⟩ := bind_ok h
  obtain ⟨loops, area, hl, hparts⟩ := placePartX_parts_geometry hp
  obtain ⟨index, trial, hi, ht, hv, _⟩ := Portfolio.portfolio_selected hc
  unfold componentTrialX at ht
  obtain ⟨run, hrun, ht⟩ := bind_ok ht
  obtain ⟨_, _, ht⟩ := bind_ok ht
  have htrial := Except.ok.inj ht
  subst trial
  dsimp only at hv
  have he := Except.ok.inj h
  subst out
  let childArea := inp.fixedAreas.foldl (fun total child =>
    if chosen.scene.boxes.any (fun box => box.id == child.1) then total + child.2 else total) 0
  let base := placeComponentExact P chosen.value.1 chosen.value.2 0 labels loops
  let augmented := { base with area := area + childArea + areas.sum }
  refine ⟨augmented, ?_, ?_⟩
  · simp [hparts, augmented, base, childArea]
  · unfold ActualPartGeometryX
    refine ⟨index, chosen, run, loops, area + childArea + areas.sum,
      hi, hc, hv, hrun, ?_, ?_⟩
    · simpa only [hv] using hl
    · simp only [augmented, base, hv]

theorem foldlM_layout_components_parts_geometryX (P : Params) (exactIds : List String)
    (inp : Input) (o : Options) (g : Graph) (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels)
        start = .ok out →
      ∃ parts, out.parts = start.parts ++ parts ∧ parts.map (·.1) = comps ∧
        ∀ q ∈ parts, ActualPartGeometryX P exactIds inp o g labels q := by
  intro comps
  induction comps with
  | nil =>
    intro start out h
    simp only [List.foldlM_nil] at h
    have hout : start = out := Except.ok.inj h
    subst out
    exact ⟨[], by simp, rfl, by simp⟩
  | cons comp comps ih =>
    intro start out h
    rw [List.foldlM_cons] at h
    obtain ⟨next, hn, hrest⟩ := bind_ok h
    obtain ⟨part, hp, hprod⟩ := layoutComponentX_parts_geometry hn
    obtain ⟨parts, hout, hmap, hall⟩ := ih next out hrest
    refine ⟨(comp, part) :: parts, ?_, ?_, ?_⟩
    · rw [hout, hp]
      simp only [List.append_assoc, List.singleton_append]
    · simp only [List.map_cons, hmap]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hprod
      · exact hall q hq

theorem actual_components_parts_geometryX {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {g : Graph} {labels : List MeasuredLabel} {start out : Acc}
    (hempty : start.parts = [])
    (h : (components g).foldlM
      (fun acc comp => layoutComponentX P exactIds inp o g acc comp labels) start = .ok out) :
    out.parts.map (·.1) = components g ∧
      ∀ q ∈ out.parts, ActualPartGeometryX P exactIds inp o g labels q := by
  obtain ⟨parts, hp, hm, hall⟩ :=
    foldlM_layout_components_parts_geometryX P exactIds inp o g labels _ _ _ h
  simp only [hempty, List.nil_append] at hp
  subst parts
  exact ⟨hm, hall⟩

private theorem guarded_rect_writeX (a : Array Rect) (key : Nat) (rect : Rect) :
    (if key < a.size then a.set! key rect else a) = a.set! key rect := by
  by_cases h : key < a.size
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, Array.set!_eq_setIfInBounds]
    simp only [Array.setIfInBounds, h, ↓reduceDIte]

private theorem guarded_rect_foldX (entries : List (Nat × Rect)) (a : Array Rect)
    (transform : Rect → Rect) :
    entries.foldl (fun out entry =>
      if entry.1 < out.size then out.set! entry.1 (transform entry.2) else out) a =
      entries.foldl (fun out entry => out.set! entry.1 (transform entry.2)) a := by
  have hstep : (fun (out : Array Rect) (entry : Nat × Rect) =>
      if entry.1 < out.size then out.set! entry.1 (transform entry.2) else out) =
      (fun out entry => out.set! entry.1 (transform entry.2)) := by
    funext out entry
    exact guarded_rect_writeX out entry.1 (transform entry.2)
  rw [hstep]

private theorem pack_rects_fold_untouchedX (pairs : List ((List Nat × Part) × Rect))
    (a : Array Rect) (key : Nat) (fallback : Rect)
    (hnot : ∀ q ∈ pairs, key ∉ q.1.1) :
    (pairs.foldl (fun a q => (q.1.1.zip q.1.2.rects).foldl
      (fun out entry => out.set! entry.1 (shiftRect q.2.x q.2.y entry.2)) a) a).getD
      key fallback =
      a.getD key fallback := by
  induction pairs generalizing a with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun q' hq' => hnot q' (List.mem_cons_of_mem _ hq'))]
    apply routes_foldl_getD_ne
    intro hm
    obtain ⟨entry, hentry, hkey⟩ := List.mem_map.mp hm
    exact hnot q List.mem_cons_self (hkey ▸ (List.of_mem_zip hentry).1)

private theorem zip_rect_keys_nodupX (keys : List Nat) (rects : List Rect)
    (hn : keys.Nodup) : ((keys.zip rects).map (·.1)).Nodup := by
  induction keys generalizing rects with
  | nil => simp
  | cons key keys ih =>
    cases rects with
    | nil => simp
    | cons rect rects =>
      obtain ⟨hkey, hkeys⟩ := List.nodup_cons.mp hn
      simp only [List.zip_cons_cons, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih rects hkeys⟩
      intro hm
      obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hm
      exact hkey (heq ▸ (List.of_mem_zip hentry).1)

private theorem pack_rects_eq_foldX (pairs : List ((List Nat × Part) × Rect))
    (start : Acc) :
    (pairs.foldl packStep start).rects =
      pairs.foldl (fun a q => (q.1.1.zip q.1.2.rects).foldl
        (fun out entry => out.set! entry.1 (shiftRect q.2.x q.2.y entry.2)) a) start.rects := by
  induction pairs generalizing start with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    unfold packStep
    dsimp only
    rw [guarded_rect_foldX]

private theorem pack_rects_fold_selectedX
    (pairs : List ((List Nat × Part) × Rect)) (a : Array Rect)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (hselected : pairs[c]? = some q)
    (i key : Nat) (rect fallback : Rect)
    (hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect))
    (hnodup : q.1.1.Nodup) (hsize : key < a.size)
    (hnot : ∀ q' ∈ pairs.drop (c + 1), key ∉ q'.1.1) :
    (pairs.foldl (fun a q => (q.1.1.zip q.1.2.rects).foldl
      (fun out entry => out.set! entry.1 (shiftRect q.2.x q.2.y entry.2)) a) a).getD
      key fallback =
      shiftRect q.2.x q.2.y rect := by
  induction pairs generalizing a c with
  | nil => simp at hselected
  | cons current rest ih =>
    simp only [List.foldl_cons]
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hselected
      subst current
      simp only [List.drop_succ_cons, List.drop_zero] at hnot
      rw [pack_rects_fold_untouchedX rest _ key fallback hnot]
      exact routes_foldl_getD_mem (shiftRect q.2.x q.2.y) _ a i key rect fallback
        hentry (zip_rect_keys_nodupX _ _ hnodup) hsize
    | succ c =>
      simp only [List.getElem?_cons_succ] at hselected
      simp only [List.drop_succ_cons] at hnot
      apply ih _ c hselected
      · rw [routes_foldl_size]
        exact hsize
      · exact hnot

theorem actual_components_packed_rect_valueX
    {P : Params} {exactIds : List String} {inp : Input} {o : Options} {graph : Graph}
    {labels : List MeasuredLabel} {start mid out : Acc}
    (hempty : start.parts = [])
    (hfold : (components graph).foldlM
      (fun acc comp => layoutComponentX P exactIds inp o graph acc comp labels) start = .ok mid)
    (hpack : packAcc P o mid = .ok out)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (mid.parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (mid.parts.zip packed.boxes)[c]? = some q)
    {i key : Nat} {rect : Rect}
    (hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect))
    (hsize : key < mid.rects.size) (fallback : Rect) :
    out.rects.getD key fallback = shiftRect q.2.x q.2.y rect := by
  obtain ⟨hparts, _⟩ := actual_components_partsX hempty hfold
  have hpart : mid.parts[c]? = some q.1 := zip_getElem?_left hselected
  have hmember : q.1 ∈ mid.parts := List.mem_of_getElem? hpart
  have hcomponent : q.1.1 ∈ components graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hmember
  have hnodup : q.1.1.Nodup := components_nodup graph q.1.1 hcomponent
  have hkey : key ∈ q.1.1 := (List.of_mem_zip (List.mem_of_getElem? hentry)).1
  have hnot : ∀ later ∈ (mid.parts.zip packed.boxes).drop (c + 1), key ∉ later.1.1 := by
    intro later hlater
    obtain ⟨j, hcj, hj⟩ := zip_drop_mem_later_getElem? hlater
    have hpartsNodup : (mid.parts.map (·.1)).Nodup := by
      rw [hparts]
      exact components_entries_nodup graph
    obtain ⟨hc, hqc⟩ := List.getElem?_eq_some_iff.mp hpart
    obtain ⟨hjbound, hqj⟩ := List.getElem?_eq_some_iff.mp hj
    have hne : q.1.1 ≠ later.1.1 := by
      have hp := List.pairwise_iff_getElem.mp hpartsNodup
      have hneq := hp c j (by simpa using hc) (by simpa using hjbound) hcj
      simpa only [List.getElem_map, hqc, hqj] using hneq
    have hlaterComponent : later.1.1 ∈ components graph := by
      rw [← hparts]
      exact List.mem_map_of_mem (List.mem_of_getElem? hj)
    exact components_disjoint hcomponent hlaterComponent hne hkey
  unfold packAcc at hpack
  obtain ⟨actualPacked, hactualPacked, hpack⟩ := bind_ok hpack
  have heq : actualPacked = packed := by
    rw [hpacked] at hactualPacked
    exact (Except.ok.inj hactualPacked).symm
  subst actualPacked
  have hout := Except.ok.inj hpack
  subst out
  change ((mid.parts.zip packed.boxes).foldl packStep
    { mid with canvasW := packed.width, canvasH := packed.height, titles := [] }).rects.getD
      key fallback = _
  rw [pack_rects_eq_foldX]
  exact pack_rects_fold_selectedX _ _ c q hselected i key rect fallback hentry hnodup hsize hnot

/-- The placement bounds of `placeComponentExact`: the `boundsOf` argument
the exact placement itself builds. -/
def placeBoundsX (P : Params) (cg : Graph) (run : Run) (labels : List MeasuredLabel)
    (loops : List (Nat × LoopPlacement)) : Bounds :=
  boundsOf ((List.range cg.nodes.length).map (frameRect P cg run) ++
      ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
        let sizes := loopSizes cg.edges labels q.2 cg.slot
        let width := if run.exact.contains q.2 then Loops.exactExtent cg.slot sizes
          else Loops.extent cg.slot sizes
        let height := if run.exact.contains q.2 then
          max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes) else q.1.h
        ⟨q.1.x + q.1.w, q.1.y, width, height⟩) ++
      labelBounds P cg run labels ++
      (componentTitles P cg run).map (·.2))
    (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))

private theorem placeComponentExact_rects_get {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)} {cursor : Int}
    {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponentExact P cg run cursor labels loops).rects[i]? =
      some (shiftRect (cursor - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponentExact placeBoundsX
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]
theorem actual_components_packed_frame_sourceX
    {P : Params} {exactIds : List String} {inp : Input} {o : Options} {graph : Graph}
    {labels : List MeasuredLabel} {start mid out : Acc}
    (hempty : start.parts = [])
    (hfold : (components graph).foldlM
      (fun acc comp => layoutComponentX P exactIds inp o graph acc comp labels) start = .ok mid)
    (hpack : packAcc P o mid = .ok out)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (mid.parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (mid.parts.zip packed.boxes)[c]? = some q)
    {i key : Nat} (hkey : q.1.1[i]? = some key)
    (hsize : key < mid.rects.size) (fallback : Rect) :
    ∃ candidate run loops area,
      componentRunX P (exactDecls exactIds inp) (componentCandidate graph q.1.1 candidate) labels
        (candidateOrder candidate) = .ok run ∧
      componentLoops P (componentCandidate graph q.1.1 candidate) run labels = .ok loops ∧
      q.1.2 = { placeComponentExact P (componentCandidate graph q.1.1 candidate) run 0 labels
        loops with area := area } ∧
      let cg := componentCandidate graph q.1.1 candidate
      let bounds := placeBoundsX P cg run labels loops
      out.rects.getD key fallback =
        shiftRect q.2.x q.2.y
          (shiftRect (0 - bounds.minX) (-bounds.minY) (frameRect P cg run i)) := by
  obtain ⟨_, hall⟩ := actual_components_parts_geometryX hempty hfold
  have hpart : q.1 ∈ mid.parts := List.mem_of_getElem? (zip_getElem?_left hselected)
  obtain ⟨candidate, _, run, loops, area, _, _, _, hrun, hloops, hpartdef⟩ := hall q.1 hpart
  let cg := componentCandidate graph q.1.1 candidate
  let bounds := placeBoundsX P cg run labels loops
  let rect := shiftRect (0 - bounds.minX) (-bounds.minY) (frameRect P cg run i)
  have hi : i < cg.nodes.length := by
    have hk := (List.getElem?_eq_some_iff.mp hkey).1
    dsimp only [cg]
    rw [componentCandidate_nodes]
    simpa only [componentGraph, List.length_map] using hk
  have hrect : q.1.2.rects[i]? = some rect := by
    rw [hpartdef]
    exact placeComponentExact_rects_get hi
  have hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect) :=
    List.getElem?_zip_eq_some.mpr ⟨hkey, hrect⟩
  refine ⟨candidate, run, loops, area, hrun, hloops, hpartdef, ?_⟩
  exact actual_components_packed_rect_valueX hempty hfold hpack packed hpacked
    hselected hentry hsize fallback

theorem sceneExecutionX_parts_entry {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {i : Nat} (hi : i < inp.boxes.length) :
    ∃ part ∈ execution.componentsAcc.parts,
      ∃ entry ∈ part.1.zip part.2.rects, entry.1 = i := by
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hm, hall⟩ := actual_components_parts_geometryX hempty execution.components_eq
  have hin := sceneExecutionX_graph_len execution hi
  obtain ⟨comp, hcomp, hiv⟩ := components_cover hin (sceneExecutionX_edges_bounded execution)
  have hmem : comp ∈ execution.componentsAcc.parts.map (·.1) := by
    rw [hm]
    exact hcomp
  obtain ⟨part, hpart, hpc⟩ := List.mem_map.mp hmem
  obtain ⟨index, chosen, run, loops, area, _, _, _, _, _, hpartdef⟩ := hall part hpart
  have hrectlen : part.2.rects.length = comp.length := by
    rw [hpartdef]
    change (placeComponentExact execution.params
      (componentCandidate execution.graph part.1 index) run 0
      execution.measured loops).rects.length = comp.length
    rw [placeComponentExact_rects_length, componentCandidate_nodes_lengthX, hpc]
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hiv
  have hjlt : j < comp.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjrect : j < part.2.rects.length := by rw [hrectlen]; exact hjlt
  refine ⟨part, hpart, (i, part.2.rects[j]'hjrect), ?_, rfl⟩
  apply mem_zip_introX
  · simpa only [hpc] using hj
  · exact List.getElem?_eq_some_iff.mpr ⟨hjrect, rfl⟩

theorem SceneExecutionX.parts_coverage {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    ∀ i rect, execution.componentsAcc.rects[i]? = some rect →
      ∃ part ∈ execution.componentsAcc.parts,
        ∃ entry ∈ part.1.zip part.2.rects, entry.1 = i := by
  intro i rect hrect
  have hi := (Array.getElem?_eq_some_iff.mp hrect).1
  rw [execution.components_rects_size] at hi
  exact sceneExecutionX_parts_entry execution hi
theorem key_part_positionX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {key : Nat}
    (hkey : key < inp.boxes.length) :
    ∃ (part : List Nat × Part) (pos k : Nat),
      part ∈ execution.componentsAcc.parts ∧
      execution.componentsAcc.parts[k]? = some part ∧
      part.1[pos]? = some key := by
  have hsizeC : execution.componentsAcc.rects.size = inp.boxes.length :=
    execution.components_rects_size
  have hrect : execution.componentsAcc.rects[key]? =
      some execution.componentsAcc.rects[key] :=
    Array.getElem?_eq_some_iff.mpr ⟨by rw [hsizeC]; exact hkey, rfl⟩
  obtain ⟨part, hpart, entry, hentry, hentryKey⟩ := execution.parts_coverage _ _ hrect
  have hkeyIn : key ∈ part.1 := by
    rw [← hentryKey]
    exact (List.of_mem_zip hentry).1
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hkeyIn
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hpart
  exact ⟨part, pos, k, hpart, hk, hpos⟩

theorem part_packed_box_lenX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {k : Nat} {part : List Nat × Part}
    (hk : execution.componentsAcc.parts[k]? = some part) :
    k < packed.boxes.length := by
  have hkbl : k < execution.componentsAcc.parts.length :=
    (List.getElem?_eq_some_iff.mp hk).1
  have hcount := Pack.pack_count hpack
  rw [hcount, List.length_map]
  exact hkbl

theorem component_node_lookupX {graph : Graph} {comp : List Nat} {cand : Nat}
    {pos key : Nat} (hkey : comp[pos]? = some key) {node : Node}
    (hnode : graph.nodes[key]? = some node) :
    (componentCandidate graph comp cand).nodes[pos]? = some node := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.getElem?_map, Option.map_some, hkey,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

theorem SceneExecutionX.boxes_eq_mapX {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    res.scene.boxes = (inp.boxes.zipIdx.map fun q =>
      Box.mk q.1.id q.1.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD q.2 default)))
        q.1.parent q.1.exclusive) :=
  calc res.scene.boxes
      = (sceneOf execution.params inp o execution.lines execution.straightAcc
        execution.measured).boxes :=
        congrArg (fun s : Scene => s.boxes) execution.scene_eq
    _ = (sceneOf execution.params inp o execution.lines execution.packedAcc
        execution.measured).boxes :=
        (sceneOf_straightenAcc execution.params inp o execution.lines execution.packedAcc
          execution.straightAcc execution.measured execution.straight_eq).2.1
    _ = _ := rfl

theorem sceneBox_source_rectX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {bi : Nat} {b : Box} (hb : res.scene.boxes[bi]? = some b) :
    ∃ source : ModelBox, inp.boxes[bi]? = some source ∧
      b.id = source.id ∧ b.parent = source.parent ∧ b.exclusive = source.exclusive ∧
      b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD bi default)) := by
  have hbiLT : bi < inp.boxes.length := by
    have h := (List.getElem?_eq_some_iff.mp hb).1
    rw [execution.boxes_eq_mapX] at h
    simpa only [List.length_map, List.length_zipIdx] using h
  have hbox : res.scene.boxes[bi]? = some
      (Box.mk inp.boxes[bi].id inp.boxes[bi].role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD bi default)))
        inp.boxes[bi].parent inp.boxes[bi].exclusive) := by
    rw [execution.boxes_eq_mapX]
    simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hbiLT,
      Option.map_some, Nat.zero_add]
  have hbeq : b = Box.mk inp.boxes[bi].id inp.boxes[bi].role.id
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD bi default)))
      inp.boxes[bi].parent inp.boxes[bi].exclusive :=
    Option.some.inj (hb.symm.trans hbox)
  refine ⟨inp.boxes[bi], List.getElem?_eq_getElem hbiLT, ?_, ?_, ?_, ?_⟩ <;>
    rw [hbeq]

theorem part_frame_lookupX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {k : Nat} {entry : List Nat × Part} {box : Rect}
    (hentry : execution.componentsAcc.parts[k]? = some entry)
    (hbox : packed.boxes[k]? = some box) :
    ∃ candidate run loops area,
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph entry.1 candidate) execution.measured
        (candidateOrder candidate) = .ok run ∧
      componentLoops execution.params
        (componentCandidate execution.graph entry.1 candidate) run execution.measured = .ok loops ∧
      entry.2 = { placeComponentExact execution.params
        (componentCandidate execution.graph entry.1 candidate) run 0 execution.measured loops
        with area := area } ∧
      ∀ (i key : Nat), entry.1[i]? = some key → key < inp.boxes.length →
        execution.packedAcc.rects.getD key default =
          shiftRect box.x box.y
            (shiftRect (0 - (placeBoundsX execution.params
                (componentCandidate execution.graph entry.1 candidate) run execution.measured loops).minX)
              (-(placeBoundsX execution.params
                (componentCandidate execution.graph entry.1 candidate) run execution.measured loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph entry.1 candidate) run i)) := by
  have hmem : entry ∈ execution.componentsAcc.parts := List.mem_of_getElem? hentry
  obtain ⟨candidate, -, run, loops, area, -, -, -, hrun, hloops, hpartdef⟩ :=
    (actual_components_parts_geometryX (by rfl) execution.components_eq).2 entry hmem
  have hrectlen : entry.2.rects.length = entry.1.length := by
    rw [hpartdef]
    have h : { placeComponentExact execution.params
        (componentCandidate execution.graph entry.1 candidate) run 0
        execution.measured loops with area := area }.rects.length = entry.1.length := by
      have hl : (placeComponentExact execution.params
          (componentCandidate execution.graph entry.1 candidate) run 0
          execution.measured loops).rects.length = entry.1.length := by
        unfold placeComponentExact
        simp only [List.length_map, List.length_range]
        rw [componentCandidate_nodes]
        simp [componentGraph]
      simpa using hl
    exact h
  refine ⟨candidate, run, loops, area, hrun, hloops, hpartdef, ?_⟩
  intro i key hkey hkeyBound
  have hi : i < entry.1.length := (List.getElem?_eq_some_iff.mp hkey).1
  have hilen : i < entry.2.rects.length := by omega
  have hsize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact hkeyBound
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[k]? =
      some ((entry, box) : (List Nat × Part) × Rect) :=
    List.getElem?_zip_eq_some.mpr ⟨hentry, hbox⟩
  obtain ⟨candidate', run', loops', area', hrun', hloops', hpartdef', hrect⟩ :=
    actual_components_packed_frame_sourceX (by rfl) execution.components_eq execution.packed_eq
      packed hpacked hselected hkey hsize default
  have hiCG' : i < (componentCandidate execution.graph entry.1 candidate').nodes.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
    simpa using hi
  have hiCG : i < (componentCandidate execution.graph entry.1 candidate).nodes.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
    simpa using hi
  have hB : entry.2.rects[i]? = some
      (shiftRect (0 - (placeBoundsX execution.params
          (componentCandidate execution.graph entry.1 candidate') run' execution.measured loops').minX)
        (-(placeBoundsX execution.params
          (componentCandidate execution.graph entry.1 candidate') run' execution.measured loops').minY)
        (frameRect execution.params
          (componentCandidate execution.graph entry.1 candidate') run' i)) := by
    rw [hpartdef']
    exact placeComponentExact_rects_get hiCG'
  rw [hrect, Option.some.inj (hB.symm.trans (by
    rw [hpartdef]
    exact placeComponentExact_rects_get hiCG))]

set_option maxHeartbeats 2000000 in
theorem layoutX_c3 {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hX : ExactComponentPlacement exactIds inp o res) :
    Validator.C3 res.scene.layoutDump := by
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hXexec := hX hwf hframed execution
  have hpackedEq := execution.packed_eq
  unfold packAcc at hpackedEq
  obtain ⟨packed, hpack, -⟩ := bind_ok hpackedEq
  have hcompMap := (actual_components_parts_geometryX (by rfl)
    execution.components_eq).1
  intro b hb hbparent p hpLookup
  simp only [Scene.layoutDump] at hb
  obtain ⟨bi, hbi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨childBox, hchildBoxMem, -, hbpar, -, hbrect⟩ :=
    sceneBox_source_rectX execution hbi
  have hbiLen : bi < inp.boxes.length := (List.getElem?_eq_some_iff.mp hchildBoxMem).1
  have hparentNe : childBox.parent ≠ "" := by rw [← hbpar]; exact hbparent
  obtain ⟨parent, hparentMem, hpid, -, -⟩ :=
    framedParents_parent hframed (List.mem_of_getElem? hchildBoxMem) hparentNe
  obtain ⟨piIdx, hpi⟩ := List.mem_iff_getElem?.mp hparentMem
  have hpiLen : piIdx < inp.boxes.length := (List.getElem?_eq_some_iff.mp hpi).1
  have hfind : res.scene.layoutDump.boxes.find? (fun x : Box => x.id == b.parent) =
      some p := hpLookup
  have hpMemDump : p ∈ res.scene.layoutDump.boxes := List.mem_of_find?_eq_some hfind
  have hpMem : p ∈ res.scene.boxes := by
    simpa only [Scene.layoutDump] using hpMemDump
  have hpId : p.id = b.parent := by
    have hsome := List.find?_some hfind
    simpa using hsome
  obtain ⟨pj, hpj⟩ := List.mem_iff_getElem?.mp hpMem
  obtain ⟨pbox, hsp, hspid, -, -, hprect⟩ := sceneBox_source_rectX execution hpj
  have hjLen : pj < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsp).1
  have hmapLen2 : piIdx < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp hpi).1
  have hid : (inp.boxes.map (·.id))[piIdx]? = (inp.boxes.map (·.id))[pj]? := by
    rw [List.getElem?_map, hpi, List.getElem?_map, hsp]
    simp only [Option.map_some]
    rw [hpid.trans (hbpar.symm.trans (hpId.symm.trans hspid))]
  have hpe : piIdx = pj := (Model.boxIds_nodup hwf).getElem?_inj hmapLen2 |>.mp hid
  have hpiP : inp.boxes[pj]? = some parent := by rw [← hpe]; exact hpi
  obtain ⟨part, posB, k, -, hk, hposB⟩ := key_part_positionX execution hbiLen
  have hkLen := part_packed_box_lenX execution packed hpack hk
  have hbox : packed.boxes[k]? = some packed.boxes[k] :=
    List.getElem?_eq_some_iff.mpr ⟨hkLen, rfl⟩
  obtain ⟨cand, run, loops, _area, hrun, _hloops, _hpartdef, hlookup⟩ :=
    part_frame_lookupX execution packed hpack hk hbox
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hcompMap]
    exact List.mem_map.mpr ⟨part, List.mem_of_getElem? hk, rfl⟩
  have hgl : bi < execution.graph.nodes.length := sceneExecutionX_graph_len execution hbiLen
  have hmemberGraph : execution.graph.nodes[bi]? = some execution.graph.nodes[bi] :=
    List.getElem?_eq_some_iff.mpr ⟨hgl, rfl⟩
  have hmemberLookup :
      (componentCandidate execution.graph part.1 cand).nodes[posB]? =
        some execution.graph.nodes[bi] :=
    component_node_lookupX hposB hmemberGraph
  have hkeyIn : bi ∈ part.1 := List.mem_of_getElem? hposB
  have hparentIn : pj ∈ part.1 :=
    hXexec.2.2 part.1 hcomp bi pj hbiLen hkeyIn
      _ hmemberGraph _ hchildBoxMem _ hpiP hpid.symm hparentNe
  obtain ⟨parentIndex, hpIdx⟩ := List.getElem?_of_mem hparentIn
  have hcontained :=
    hXexec.2.1 part.1 cand run (candidateOrder cand) hcomp hrun posB bi pj parentIndex
      _ hposB hbiLen hmemberLookup _ hchildBoxMem _ hpiP hpid.symm hparentNe hpIdx
  have hchildRect := hlookup posB bi hposB hbiLen
  have hparentRect := hlookup parentIndex pj hpIdx hjLen
  have hstep1 := contained_shiftRect_imp
    (dx := 0 - (placeBoundsX execution.params
        (componentCandidate execution.graph part.1 cand) run execution.measured loops).minX)
    (dy := -(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 cand) run execution.measured loops).minY)
    hcontained
  have hstep2 := contained_shiftRect_imp
    (dx := packed.boxes[k].x) (dy := packed.boxes[k].y) hstep1
  have hstep3 := contained_orientRect (d := o.direction)
    (h := execution.packedAcc.canvasH) hstep2
  have htransport := contained_shiftRect_imp
    (dx := execution.params.canvasMargin) (dy := execution.params.canvasMargin) hstep3
  rw [hprect, hbrect, hchildRect, hparentRect]
  exact htransport


/-- Exact installed-route helpers: counterparts of the private `StraightenFacts`
lemmas used by `SceneExecution.installed_edge_installer`,
`installed_edge_positions`, `installed_part_edge_rects`, and
`installed_part_edge_key_ids`, proved over `componentRunX` /
`placeComponentExact` / `placeBoundsX` / `exactGraph`. -/
private theorem straightPort_loX {source target lo hi : Int} (hle : lo ≤ hi) :
    lo ≤ straightPort source target lo hi := by
  unfold straightPort
  by_cases h1 : lo ≤ source ∧ source ≤ hi
  · rw [ite_eq_left h1]
    exact h1.1
  · rw [ite_eq_right h1]
    by_cases h2 : lo ≤ target ∧ target ≤ hi
    · rw [ite_eq_left h2]
      exact h2.1
    · rw [ite_eq_right h2]
      omega

private theorem straightPort_hiX {source target lo hi : Int} (hle : lo ≤ hi) :
    straightPort source target lo hi ≤ hi := by
  unfold straightPort
  by_cases h1 : lo ≤ source ∧ source ≤ hi
  · rw [ite_eq_left h1]
    exact h1.2
  · rw [ite_eq_right h1]
    by_cases h2 : lo ≤ target ∧ target ≤ hi
    · rw [ite_eq_left h2]
      exact h2.2
    · rw [ite_eq_right h2]
      omega

private theorem bool_of_not_trueX {b : Bool} (h : (!b) = true) : b = false := by
  cases hb : b with
  | true =>
    simp only [hb] at h
    cases h
  | false => rfl

private theorem foldl_acc_partsX (step : Acc → ((List Nat × Part) × Rect) → Acc)
    (hstep : ∀ s q, (step s q).parts = s.parts) :
    ∀ (pairs : List (((List Nat) × Part) × Rect)) (start : Acc),
      (pairs.foldl step start).parts = start.parts := by
  intro pairs
  induction pairs with
  | nil => intro start; rfl
  | cons q qs ih =>
    intro start
    rw [List.foldl_cons]
    exact (ih (step start q)).trans (hstep start q)

private theorem packAcc_parts_eqX {P : Params} {o : Options} {acc out : Acc}
    (h : packAcc P o acc = .ok out) : out.parts = acc.parts := by
  unfold packAcc at h
  obtain ⟨packed, _, h2⟩ := bind_ok h
  have he := Except.ok.inj h2
  subst out
  refine foldl_acc_partsX _ ?_ _ _
  intro s q
  rfl

private theorem straightSpanOf_invX {ctx : StraightenCtx} {routing : Routing} {i : Nat}
    {span : StraightSpan} (h : straightSpanOf ctx routing i = .ok (some span)) :
    ∃ e, ctx.proper.edges[i]? = some e ∧ straightEdgeEligible ctx routing i e = true ∧
      span.decl = ctx.decls.getD e.original 0 ∧ span.top < span.bottom := by
  unfold straightSpanOf at h
  cases he : ctx.proper.edges[i]? with
  | none =>
    simp only [he] at h
    cases h
  | some e =>
    simp only [he] at h
    cases hel : !straightEdgeEligible ctx routing i e with
    | true =>
      simp only [hel] at h
      cases h
    | false =>
      simp only [hel] at h
      cases hgeom : straightGeom ctx routing i e with
      | mk tw hw th hh tailLeft headLeft lo hi cx =>
        simp only [hgeom] at h
        by_cases hlo : lo > hi
        · rw [ite_eq_left hlo] at h
          cases h
        · rw [ite_eq_right hlo] at h
          obtain ⟨pin, _, h⟩ := bind_ok h
          obtain ⟨top, _, h⟩ := bind_ok h
          obtain ⟨bottom, _, h⟩ := bind_ok h
          by_cases hge : top ≥ bottom
          · rw [ite_eq_left hge] at h
            cases h
          · rw [ite_eq_right hge] at h
            obtain ⟨column, _, h⟩ := bind_ok h
            have hlt : top < bottom := by omega
            have hs := Option.some.inj (Except.ok.inj h)
            have helig : straightEdgeEligible ctx routing i e = true := by
              cases hb : straightEdgeEligible ctx routing i e with
              | true => rfl
              | false =>
                simp only [hb] at hel
                cases hel
            subst hs
            exact ⟨e, rfl, helig, rfl, hlt⟩

private theorem straightSpanOf_column_memX {ctx : StraightenCtx} {routing : Routing} {i : Nat}
    {span : StraightSpan} (h : straightSpanOf ctx routing i = .ok (some span)) :
    span.tailRect.x ≤ span.column ∧ span.column ≤ span.tailRect.x + span.tailRect.w ∧
    span.headRect.x ≤ span.column ∧ span.column ≤ span.headRect.x + span.headRect.w := by
  unfold straightSpanOf at h
  cases he : ctx.proper.edges[i]? with
  | none =>
    simp only [he] at h
    cases h
  | some e =>
    simp only [he] at h
    cases hel : !straightEdgeEligible ctx routing i e with
    | true =>
      simp only [hel] at h
      cases h
    | false =>
      simp only [hel] at h
      cases hgeom : straightGeom ctx routing i e with
      | mk tw hw th hh tailLeft headLeft lo hi cx =>
        simp only [hgeom] at h
        by_cases hlo : lo > hi
        · rw [ite_eq_left hlo] at h
          cases h
        · rw [ite_eq_right hlo] at h
          obtain ⟨pin, _, h⟩ := bind_ok h
          obtain ⟨top, _, h⟩ := bind_ok h
          obtain ⟨bottom, _, h⟩ := bind_ok h
          by_cases hge : top ≥ bottom
          · rw [ite_eq_left hge] at h
            cases h
          · rw [ite_eq_right hge] at h
            obtain ⟨column, hcolNarrow, h⟩ := bind_ok h
            have hs := Option.some.inj (Except.ok.inj h)
            have hcolEq : column = cx + ctx.dx := by
              unfold narrowI32 at hcolNarrow
              by_cases hc : -2147483648 ≤ cx + ctx.dx ∧ cx + ctx.dx ≤ 2147483647
              · rw [ite_eq_left hc] at hcolNarrow
                exact (Except.ok.inj hcolNarrow).symm
              · rw [ite_eq_right hc] at hcolNarrow
                cases hcolNarrow
            simp only [straightGeom] at hgeom
            simp only [StraightGeom.mk.injEq] at hgeom
            obtain ⟨hEtw, hEhw, _, _, hEtl, hEhl, hElo, hEhi, hEcx⟩ := hgeom
            have hle : lo ≤ hi := by omega
            have hSP : straightPort (routing.sourceX.getD i 0) (routing.targetX.getD i 0) lo hi
                = cx := by
              rw [← hElo, ← hEhi]
              exact hEcx
            have hloCx : lo ≤ cx := by
              rw [← hSP]
              exact straightPort_loX hle
            have hhiCx : cx ≤ hi := by
              rw [← hSP]
              exact straightPort_hiX hle
            subst hs
            refine ⟨?_, ?_, ?_, ?_⟩
            · show tailLeft + ctx.dx ≤ column
              omega
            · show column ≤ tailLeft + ctx.dx + tw
              omega
            · show headLeft + ctx.dx ≤ column
              omega
            · show column ≤ headLeft + ctx.dx + hw
              omega

private theorem straightRealNode_existsX {p : Proper} {v : Nat}
    (h : straightRealNode p v = true) :
    ∃ n, p.nodes[v]? = some n ∧ n.dummy = false ∧ n.label = false ∧ n.node.border = 0 := by
  unfold straightRealNode at h
  cases hv : p.nodes[v]? with
  | none =>
    simp only [hv] at h
    cases h
  | some n =>
    simp only [hv, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hd, hl⟩, hbord⟩ := h
    exact ⟨n, rfl, bool_of_not_trueX hd, bool_of_not_trueX hl, hbord⟩

private theorem srNormSrcX
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ ranks normalized,
      normalize cg ranks = .ok normalized ∧
      run.proper.edges = normalized.edges ∧
      run.proper.chains = normalized.chains := by
  obtain ⟨ranks, normalized, labeled, projected, hn, hlabels, hcoordinate,
    _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨hlabelEdges, _, hlabelChains, _⟩ := Labels.addLabelNodes_metadata hlabels
  have hclean : ∀ e ∈ (titleReservations (sizeProperPortsX P exact labeled)).edges,
      e.synthetic = false := by
    intro e he
    have hedge : (titleReservations (sizeProperPortsX P exact labeled)).edges =
        normalized.edges := hlabelEdges
    rw [hedge] at he
    exact normalize_clean hn e he
  have hprojectedEdges := (proxyWidths_rel hproxy).1
  have hdropEdges : (OrderImpl.dropSynthetic projected).edges =
      (OrderImpl.dropSynthetic
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
          P.clusterBorderW)).edges := by
    show projected.edges.filter (fun e => !e.synthetic) = _
    rw [hprojectedEdges, ← hcoordinate]
    rfl
  refine ⟨ranks, normalized, hn, ?_, ?_⟩
  · rw [← hdrop, hdropEdges,
      OrderImpl.dropSynthetic_addClusterBorders_edges _ _ hclean]
    exact hlabelEdges
  · rw [← hdrop, OrderImpl.dropSynthetic_chains, proxyWidths_chains hproxy,
      ← hcoordinate, coordinateGraphX_chains P exact labeled, hlabelChains]

private theorem srChainOrigX {e : Edge} {idx n0 s : Nat} {pe : ProperEdge}
    (hmem : pe ∈ NormalizeImpl.chainEdges e idx n0 s) : pe.original = idx := by
  unfold NormalizeImpl.chainEdges at hmem
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hmem
  rfl

private theorem srZipIdxX {es : List Edge} {x : Edge × Nat}
    (hx : x ∈ es.zipIdx) : es[x.2]? = some x.1 :=
  List.mem_zipIdx_iff_getElem?.mp hx

private theorem srNormSelfEdgesX {slot : Int} {p p' : Proper} {e : Edge} {idx : Nat}
    (hself : e.tail = e.head)
    (h : NormalizeImpl.normalizeEdge slot p e idx = .ok p') :
    p'.edges = p.edges := by
  unfold NormalizeImpl.normalizeEdge at h
  simp only [hself, ↓reduceIte, Except.ok.injEq] at h
  subst h
  rfl

private theorem srNormAppendOrigX {slot : Int} {p p' : Proper} {e : Edge} {idx : Nat}
    (hne : e.tail ≠ e.head)
    (h : NormalizeImpl.normalizeEdge slot p e idx = .ok p') {pe : ProperEdge}
    (hmem : pe ∈ p'.edges) (hnot : pe ∉ p.edges) : pe.original = idx := by
  unfold NormalizeImpl.normalizeEdge at h
  simp only [hne, ↓reduceIte] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · have heq := Except.ok.inj h
      subst p'
      have hmem2 : pe ∈ p.edges ++ NormalizeImpl.chainEdges e idx p.nodes.length _ :=
        hmem
      rcases List.mem_append.mp hmem2 with hm | hm
      · exact absurd hm hnot
      · exact srChainOrigX hm

private theorem srNormLoopNoX {es : List Edge} {slot : Int} {i : Nat}
    {l : List (Edge × Nat)} {p p' : Proper}
    (hmem : ∀ x ∈ l, es[x.2]? = some x.1)
    (hself : ∃ e, es[i]? = some e ∧ e.tail = e.head)
    (hno : ∀ pe ∈ p.edges, pe.original ≠ i)
    (h : NormalizeImpl.normalizeLoop slot l p = .ok p') :
    ∀ pe ∈ p'.edges, pe.original ≠ i := by
  induction l generalizing p with
  | nil =>
    simp only [NormalizeImpl.normalizeLoop, Except.ok.injEq] at h
    subst h
    exact hno
  | cons q rest ih =>
    obtain ⟨e, idx⟩ := q
    simp only [NormalizeImpl.normalizeLoop] at h
    split at h
    · simp at h
    · next p1 h1 =>
      have hmemHead : es[idx]? = some e := hmem (e, idx) (by simp)
      have hmemRest : ∀ x ∈ rest, es[x.2]? = some x.1 := fun x hx =>
        hmem x (List.mem_cons_of_mem _ hx)
      have hno1 : ∀ pe ∈ p1.edges, pe.original ≠ i := by
        intro pe hpe hcon
        by_cases hidx : idx = i
        · subst hidx
          have heq : e = hself.choose :=
            Option.some.inj (hmemHead.symm.trans hself.choose_spec.1)
          have hselfE : e.tail = e.head := by
            rw [heq]
            exact hself.choose_spec.2
          have hedge : p1.edges = p.edges :=
            srNormSelfEdgesX hselfE h1
          rw [hedge] at hpe
          exact hno pe hpe hcon
        · by_cases hselfE : e.tail = e.head
          · have hedge : p1.edges = p.edges :=
              srNormSelfEdgesX hselfE h1
            rw [hedge] at hpe
            exact hno pe hpe hcon
          · have horig := srNormAppendOrigX hselfE h1 hpe
            by_cases hmemOld : pe ∈ p.edges
            · exact hno pe hmemOld hcon
            · have heq := horig hmemOld
              omega
      exact ih hmemRest hno1 h

private theorem srNormNoSelfX {cg : Graph} {ranks : List Int} {p0 : Proper}
    (hn : normalize cg ranks = .ok p0)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    (hself : edge.tail = edge.head) :
    ∀ pe ∈ p0.edges, pe.original ≠ i := by
  have hmem : ∀ x ∈ cg.edges.zipIdx, cg.edges[x.2]? = some x.1 :=
    fun x hx => srZipIdxX hx
  have hselfEx : ∃ e, cg.edges[i]? = some e ∧ e.tail = e.head :=
    ⟨edge, hedge, hself⟩
  have hno : ∀ (pe : ProperEdge), pe ∈
      (Proper.mk (cg.nodes.map (fun nd => ProperNode.mk nd false none false))
        [] ranks []).edges →
      pe.original ≠ i := by
    intro pe hpe
    simp at hpe
  unfold normalize at hn
  cases hslot : NormalizeImpl.slotOf cg with
  | none =>
    simp [hslot] at hn
  | some slot =>
    simp [hslot] at hn
    by_cases hcond : (cg.wellformed = true ∧ ranks.length = cg.nodes.length ∧ 0 ≤ slot)
    · simp [hcond] at hn
      have hn' : NormalizeImpl.normalizeLoop slot cg.edges.zipIdx
          (Proper.mk (cg.nodes.map (fun nd => ProperNode.mk nd false none false))
            [] ranks []) = .ok p0 := hn
      exact srNormLoopNoX hmem hselfEx hno hn'
    · simp [hcond] at hn

private theorem srSelfEmptyX {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {i : Nat} {edge : Edge}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (hedge : cg.edges[i]? = some edge) (hself : edge.tail = edge.head) :
    (RouteImpl.edgesOf run.proper i) = [] := by
  obtain ⟨ranks, normalized, hn, he, _⟩ := srNormSrcX hrun
  have hno : ∀ pe ∈ normalized.edges, pe.original ≠ i :=
    srNormNoSelfX hn hedge hself
  have hno' : ∀ pe ∈ run.proper.edges, pe.original ≠ i := by
    rw [he]
    exact hno
  exact List.eq_nil_iff_forall_not_mem.mpr fun j hj =>
    absurd (mem_edgesOf.mp hj).2 (hno' _ (edgeAt_mem (mem_edgesOf.mp hj).1))

private theorem normLoop_mem_chainX {slot : Int} :
    ∀ (l : List (Edge × Nat)) (q q' : Proper),
      NormalizeImpl.normalizeLoop slot l q = .ok q' →
      ∀ pe ∈ q'.edges,
      pe ∈ q.edges ∨
        ∃ e idx n0 s, (e, idx) ∈ l ∧ pe ∈ NormalizeImpl.chainEdges e idx n0 s ∧
          q.nodes.length ≤ n0 := by
  intro l
  induction l with
  | nil =>
    intro q q' h pe hmem
    have he : q = q' := Except.ok.inj h
    subst q'
    exact Or.inl hmem
  | cons hd tl ih =>
    intro q q' h pe hmem
    obtain ⟨e, idx⟩ := hd
    unfold NormalizeImpl.normalizeLoop at h
    split at h
    · simp at h
    · next q1 h1 =>
      have hgrow : q.nodes.length ≤ q1.nodes.length := by
        unfold NormalizeImpl.normalizeEdge at h1
        split at h1
        · have heq := Except.ok.inj h1
          subst q1
          exact Nat.le_refl _
        · split at h1
          · simp at h1
          · split at h1
            · simp at h1
            · have heq := Except.ok.inj h1
              subst q1
              simp [NormalizeImpl.appendChain]
      have hrest := ih q1 q' h pe hmem
      rcases hrest with hq1 | ⟨e', idx', n0, s, hmemL, hchain, hle0⟩
      · unfold NormalizeImpl.normalizeEdge at h1
        split at h1
        · have heq := Except.ok.inj h1
          subst q1
          exact Or.inl hq1
        · split at h1
          · simp at h1
          · split at h1
            · simp at h1
            · have heq := Except.ok.inj h1
              subst q1
              simp only [NormalizeImpl.appendChain] at hq1
              rcases List.mem_append.mp hq1 with hL | hR
              · exact Or.inl hL
              · exact Or.inr ⟨e, idx, _, _, List.mem_cons.mpr (Or.inl rfl), hR,
                  Nat.le_refl _⟩
      · exact Or.inr ⟨e', idx', n0, s, List.mem_cons_of_mem _ hmemL, hchain,
          Nat.le_trans hgrow hle0⟩

/-- A placed exact part's straightening context carries the run's proper graph. -/
private theorem placeComponentExact_straighten_proper (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    ((placeComponentExact P cg run cursor labels loops).straighten.map (·.proper)) =
      some run.proper := rfl

/-- The installing part of an exact `Installed` witness is an actual placed
component, and its straightening context is that component's context. -/
private theorem installed_run_of_memX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {q : List Nat × Part} {ctx0 : StraightenCtx}
    (hmem : q ∈ execution.componentsAcc.parts)
    (hctx : q.2.straighten = some ctx0) :
    ∃ (index : Nat) (run : Run) (loops : List (Nat × LoopPlacement)) (area : Int),
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph q.1 index)
        execution.measured (candidateOrder index) = .ok run ∧
      q.2 = { placeComponentExact execution.params
        (componentCandidate execution.graph q.1 index) run 0 execution.measured loops
        with area := area } ∧
      ctx0.proper = run.proper ∧ ctx0.xs = run.xs ∧ ctx0.ys = run.ys ∧
      ctx0.dx = 0 - (placeBoundsX execution.params
        (componentCandidate execution.graph q.1 index) run execution.measured loops).minX ∧
      ctx0.dy = -(placeBoundsX execution.params
        (componentCandidate execution.graph q.1 index) run execution.measured loops).minY := by
  obtain ⟨index, chosen, run, loops, area, _, _, _, hrun, _, hplace⟩ :=
    (actual_components_parts_geometryX (by rfl) execution.components_eq).2 q hmem
  have hU : (placeComponentExact execution.params
      (componentCandidate execution.graph q.1 index) run 0 execution.measured loops).straighten
      = some ctx0 := by
    rw [← hctx, hplace]
  unfold placeComponentExact at hU
  dsimp only at hU
  have hEq := Option.some.inj hU
  have hproper : ctx0.proper = run.proper := congrArg StraightenCtx.proper hEq.symm
  have hxs : ctx0.xs = run.xs := congrArg StraightenCtx.xs hEq.symm
  have hys : ctx0.ys = run.ys := congrArg StraightenCtx.ys hEq.symm
  have hdx : ctx0.dx = 0 - (placeBoundsX execution.params
    (componentCandidate execution.graph q.1 index) run execution.measured loops).minX :=
    congrArg StraightenCtx.dx hEq.symm
  have hdy : ctx0.dy = -(placeBoundsX execution.params
    (componentCandidate execution.graph q.1 index) run execution.measured loops).minY :=
    congrArg StraightenCtx.dy hEq.symm
  exact ⟨index, run, loops, area, hrun, hplace, hproper, hxs, hys, hdx, hdy⟩

private theorem componentRunX_declInvX {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) :
    DeclInv cg.edges run.proper := by
  obtain ⟨ranks, normalized, hn, he, _⟩ := srNormSrcX hrun
  unfold DeclInv
  rw [he]
  exact normalize_declInv hn

/-- The installer is the part that owns the edge: any installed-route witness and any
selected component edge with the same declaration name the same component, the same
part, and the same candidate edge index. Span geometry and offsets are not consulted. -/
theorem SceneExecutionX.installed_edge_installer {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} {pts : List Point} (_hinst : Installed execution.packedAcc key pts)
    {q : (List Nat × Part) × Rect} {packed : Pack.State} {c : Nat}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area }) :
    ∀ (qS : List Nat × Part) (ctx0 : StraightenCtx) (j : Nat) (eS : ProperEdge),
      qS ∈ execution.packedAcc.parts →
      qS.2.straighten = some ctx0 →
      ctx0.proper.edges[j]? = some eS →
      eS.decl = key →
      qS.1 = q.1.1 ∧ qS.2 = q.1.2 ∧ eS.original = i := by
  intro qS ctx0 j eS hmemS hctxS heS hdeclS
  have hpackEq : execution.packedAcc.parts = execution.componentsAcc.parts :=
    packAcc_parts_eqX execution.packed_eq
  have hmemSq : qS ∈ execution.componentsAcc.parts := by
    rw [← hpackEq]
    exact hmemS
  have hmemQ : q.1 ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? (zip_getElem?_left hselected)
  obtain ⟨hpartsEq, _⟩ := actual_components_parts_geometryX (by rfl) execution.components_eq
  have hcompS : qS.1 ∈ components execution.graph := by
    rw [← hpartsEq]
    exact List.mem_map_of_mem hmemSq
  have hcompQ : q.1.1 ∈ components execution.graph := by
    rw [← hpartsEq]
    exact List.mem_map_of_mem hmemQ
  obtain ⟨indexS, runS, loopsS, areaS, hrunS, hplaceS, hproperS, _, _, _, _⟩ :=
    installed_run_of_memX execution hmemSq hctxS
  have heSrun : eS ∈ runS.proper.edges := by
    rw [← hproperS]
    exact List.mem_of_getElem? heS
  obtain ⟨geS, hgeS, hdeclgeS⟩ := componentRunX_declInvX hrunS eS heSrun
  have hownsS : ownsDecl execution.graph qS.1 key := by
    have h0 := componentCandidate_edge_owns (List.mem_of_getElem? hgeS)
    have h1 : geS.decl = key := hdeclgeS.symm.trans hdeclS
    rw [h1] at h0
    exact h0
  have hownsQ : ownsDecl execution.graph q.1.1 key := by
    have h0 := componentCandidate_edge_owns (List.mem_of_getElem? hedge)
    rw [hdecl] at h0
    exact h0
  have hcompEq : qS.1 = q.1.1 :=
    ownsDecl_unique (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
      hcompS hcompQ hownsS hownsQ
  have hpartsNodup : (execution.componentsAcc.parts.map (·.1)).Nodup := by
    rw [hpartsEq]
    exact components_entries_nodup _
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hmemSq
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hmemQ
  have ha' : a < (execution.componentsAcc.parts.map (·.1)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp ha).1
  have hb' : b < (execution.componentsAcc.parts.map (·.1)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hb).1
  have hma : (execution.componentsAcc.parts.map (·.1))[a]? = some qS.1 := by
    rw [List.getElem?_map, ha]
    simp
  have hmb : (execution.componentsAcc.parts.map (·.1))[b]? = some q.1.1 := by
    rw [List.getElem?_map, hb]
    simp
  have hab : a = b :=
    hpartsNodup.eq_of_getElem?_eq ha' (by rw [hma, hmb, hcompEq])
  have hpair : qS = q.1 := by
    rw [hab] at ha
    exact Option.some.inj (ha.symm.trans hb)
  have hq2 : qS.2 = q.1.2 := congrArg Prod.snd hpair
  have hstraightC : (placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops).straighten = some ctx0 := by
    have hc := hctxS
    rw [hq2, hpart] at hc
    exact hc
  unfold placeComponentExact at hstraightC
  dsimp only at hstraightC
  obtain rfl := Option.some.inj hstraightC
  have heS' : run.proper.edges[j]? = some eS := heS
  have hmemE : eS ∈ run.proper.edges := List.mem_of_getElem? heS'
  obtain ⟨geS', hgeS', hdeclgeS'⟩ := componentRunX_declInvX hrun eS hmemE
  have hdeclEq : geS'.decl = edge.decl := hdeclgeS'.symm.trans (hdeclS.trans hdecl.symm)
  have hnd : ((componentCandidate execution.graph q.1.1 candidate).edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup execution.graph q.1.1 candidate
      (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
  have hidx : eS.original = i := nodup_map_inj (·.decl) hnd hgeS' hedge hdeclEq
  exact ⟨hcompEq, hq2, hidx⟩

/-- The candidate edge a straightened corridor installs is not reversed. -/
theorem SceneExecutionX.installed_edge_not_reversed {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} {pts : List Point} (hinst : Installed execution.packedAcc key pts)
    {q : (List Nat × Part) × Rect} {packed : Pack.State} {c : Nat}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area }) :
    edge.reversed = false := by
  obtain ⟨qS, ctx0, ox, oy, j, e, span, hmem, hctx, hoff, he0, hkey, hne, routing, hspan,
    hpts⟩ := hinst
  obtain ⟨e', he', helig, _, _⟩ := straightSpanOf_invX hspan
  have hid := execution.installed_edge_installer (q := q) (packed := packed) (c := c)
    ⟨qS, ctx0, ox, oy, j, e, span, hmem, hctx, hoff, he0, hkey, hne, routing, hspan, hpts⟩
    hselected hedge hdecl hrun hpart qS ctx0 j e hmem hctx he0 hkey
  have heqE : e' = e := Option.some.inj (he'.symm.trans he0)
  rw [heqE] at helig
  have hrev : (ctx0.reversed.getD i false) = false := by
    have h := helig
    unfold straightEdgeEligible at h
    simp_all only [Bool.and_eq_true, Bool.not_eq_true']
  have hstraight : (placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops).straighten = some ctx0 := by
    have hc := hctx
    rw [hid.2.1, hpart] at hc
    exact hc
  unfold placeComponentExact at hstraight
  dsimp only at hstraight
  obtain rfl := Option.some.inj hstraight
  have hrev' : ((componentCandidate execution.graph q.1.1 candidate).edges.map
      (·.reversed)).getD i false = false := hrev
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hedge, Option.map_some,
    Option.getD_some] at hrev'
  exact hrev'

/-- An installed edge is the whole chain: a proper edge with the installed
`original` whose ends index component nodes is the chain's single segment. -/
theorem SceneExecutionX.installed_edge_positions {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} {pts : List Point} (_hinst : Installed execution.packedAcc key pts)
    {q : (List Nat × Part) × Rect} {packed : Pack.State} {c : Nat}
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (_hdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area }) :
    ∀ (eS : ProperEdge), eS ∈ run.proper.edges → eS.original = i →
      (∃ n, (componentCandidate execution.graph q.1.1 candidate).nodes[eS.tail]? = some n) →
      (∃ n, (componentCandidate execution.graph q.1.1 candidate).nodes[eS.head]? = some n) →
      eS.tail = edge.tail ∧ eS.head = edge.head := by
  intro eS hmemS hOrig hTailEx hHeadEx
  obtain ⟨_, hTailCg⟩ := hTailEx
  obtain ⟨_, hHeadCg⟩ := hHeadEx
  obtain ⟨ranks, normalized, hn, he, _⟩ := srNormSrcX hrun
  have hmemN : eS ∈ normalized.edges := by
    rw [← he]
    exact hmemS
  have hcgLen : (componentCandidate execution.graph q.1.1 candidate).nodes.length =
      q.1.1.length := by
    simp [componentCandidate_nodes, componentGraph]
  have hTailLt : eS.tail < q.1.1.length := by
    rw [← hcgLen]
    exact (List.getElem?_eq_some_iff.mp hTailCg).1
  have hHeadLt : eS.head < q.1.1.length := by
    rw [← hcgLen]
    exact (List.getElem?_eq_some_iff.mp hHeadCg).1
  unfold NormalizeImpl.normalize at hn
  split at hn
  · simp at hn
  · next slot hs =>
    split at hn
    · have hmemOr := normLoop_mem_chainX _ _ _ hn eS hmemN
      rcases hmemOr with h0 | ⟨e', idx, n0, s, hmemL, hchain, hle0⟩
      · simp at h0
      · have hOrigIdx : idx = i := (srChainOrigX hchain).symm.trans hOrig
        rw [hOrigIdx] at hchain hmemL
        have hge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? =

            some e' :=
          srZipIdxX hmemL
        have heq : e' = edge := Option.some.inj (hge.symm.trans hedge)
        rw [heq] at hchain
        have hle0' : q.1.1.length ≤ n0 := by
          simpa [hcgLen] using hle0
        simp only [NormalizeImpl.chainEdges, List.mem_map, List.mem_range] at hchain
        obtain ⟨k, hkS, rfl⟩ := hchain
        have hTailLt' : NormalizeImpl.chainNode edge.tail edge.head n0 s k <
            q.1.1.length :=
          hTailLt
        have hHeadLt' : NormalizeImpl.chainNode edge.tail edge.head n0 s (k + 1) <
            q.1.1.length :=
          hHeadLt
        have hk0 : k = 0 := by
          refine Classical.byContradiction fun hk0 => ?_
          by_cases hks : k = s
          · omega
          · simp only [NormalizeImpl.chainNode, hk0, hks, ↓reduceIte] at hTailLt'
            omega
        subst hk0
        have hk1 : 0 + 1 = s := by
          refine Classical.byContradiction fun hk1 => ?_
          have hk10 : (0 : Nat) + 1 ≠ 0 := by omega
          simp only [NormalizeImpl.chainNode, hk10, hk1, ↓reduceIte] at hHeadLt'
          omega
        have hs1 : s = 1 := by omega
        subst hs1
        show edge.tail = edge.tail ∧ edge.head = edge.head
        exact ⟨rfl, rfl⟩
    · simp at hn

private theorem sizeProperPortsX_lengthX (P : Params) (exact : List Nat)
    (source : Proper) :
    (sizeProperPortsX P exact source).nodes.length = source.nodes.length := by
  simp [sizeProperPortsX]

private theorem installed_XBbs_coordinateGraph0_lookup (P : Params) (exact : List Nat)
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
  have hlen : (sizeProperPortsX P exact p).nodes.length = p.nodes.length :=
    sizeProperPortsX_lengthX P exact p
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

private theorem installed_XBbs_coordinateGraph_lookup (P : Params) (exact : List Nat)
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
  rcases installed_XBbs_coordinateGraph0_lookup P exact p hm1 with
    ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ | ⟨i, q, hq, hv, h1, h2, h3⟩
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

private theorem installed_proper_belowX {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd)
    (hd : nd.dummy = false) (hb : nd.node.border = 0) :
    v < cg.nodes.length := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoord, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hkeys : NodeKeys cg labeled := addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have hdropNodes : run.proper.nodes = q0.nodes := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  have hlenQ : q0.nodes.length = (coordinateGraphX P exact labeled).nodes.length := by
    rw [hcoord]
    exact (proxyWidths_rel hproxy).2.2.1
  have hvq : q0.nodes[v]? = some nd := by
    rw [← hdropNodes]
    exact hv
  have hlt : v < q0.nodes.length := (List.getElem?_eq_some_iff.mp hvq).1
  have hltPc : v < (coordinateGraphX P exact labeled).nodes.length := by
    rw [← hlenQ]
    exact hlt
  obtain ⟨ndpc, hpc⟩ : ∃ ndpc, (coordinateGraphX P exact labeled).nodes[v]? = some ndpc :=
    ⟨_, List.getElem?_eq_getElem hltPc⟩
  have hpc' : run.coordinateProper.nodes[v]? = some ndpc := by
    rw [← hcoord]
    exact hpc
  obtain ⟨nd', hq0', hdEq, hbEq, _⟩ := (proxyWidths_rel hproxy).2.2.2.2.1 v ndpc hpc'
  have hnd' : nd' = nd := Option.some.inj (hq0'.symm.trans hvq)
  subst hnd'
  have hpcDummy : ndpc.dummy = false := by
    rw [← hdEq]
    exact hd
  have hpcBorder : ndpc.node.border = 0 := by
    rw [← hbEq]
    exact hb
  rcases installed_XBbs_coordinateGraph_lookup P exact labeled hpc with
    ⟨m, hm, hdPc, _, _, _⟩ | ⟨_, hbS⟩ | ⟨_, _, _, _, _, hbT, _⟩
  · rcases hkeys v m hm with ⟨n, hnCg, _, _, _⟩ | ⟨hdLab, _, _⟩
    · exact (List.getElem?_eq_some_iff.mp hnCg).1
    · have hmf : m.dummy = false := by
        rw [← hdPc]
        exact hpcDummy
      rw [hmf] at hdLab
      exact absurd hdLab (by decide)
  · rcases hbS with h | h <;> omega
  · rw [hpcBorder] at hbT
    exact absurd hbT (by decide)

private theorem installed_proper_cg_nodeX {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd)
    (hd : nd.dummy = false) (hb : nd.node.border = 0) :
    ∃ n, cg.nodes[v]? = some n ∧ n.border = 0 := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoord, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hkeys : NodeKeys cg labeled := addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have hdropNodes : run.proper.nodes = q0.nodes := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  have hlenQ : q0.nodes.length = (coordinateGraphX P exact labeled).nodes.length := by
    rw [hcoord]
    exact (proxyWidths_rel hproxy).2.2.1
  have hvq : q0.nodes[v]? = some nd := by
    rw [← hdropNodes]
    exact hv
  have hlt : v < q0.nodes.length := (List.getElem?_eq_some_iff.mp hvq).1
  have hltPc : v < (coordinateGraphX P exact labeled).nodes.length := by
    rw [← hlenQ]
    exact hlt
  obtain ⟨ndpc, hpc⟩ : ∃ ndpc, (coordinateGraphX P exact labeled).nodes[v]? = some ndpc :=
    ⟨_, List.getElem?_eq_getElem hltPc⟩
  have hpc' : run.coordinateProper.nodes[v]? = some ndpc := by
    rw [← hcoord]
    exact hpc
  obtain ⟨nd', hq0', hdEq, hbEq, _⟩ := (proxyWidths_rel hproxy).2.2.2.2.1 v ndpc hpc'
  have hnd' : nd' = nd := Option.some.inj (hq0'.symm.trans hvq)
  subst hnd'
  have hpcDummy : ndpc.dummy = false := by
    rw [← hdEq]
    exact hd
  have hpcBorder : ndpc.node.border = 0 := by
    rw [← hbEq]
    exact hb
  rcases installed_XBbs_coordinateGraph_lookup P exact labeled hpc with
    ⟨m, hm, hdPc, hbPc, _, _⟩ | ⟨_, hbS⟩ | ⟨_, _, _, _, _, hbT, _⟩
  · rcases hkeys v m hm with ⟨n, hnCg, _, hbML, _⟩ | ⟨hdLab, _, _⟩
    · exact ⟨n, hnCg, by rw [← hbML, ← hbPc]; exact hpcBorder⟩
    · have hmf : m.dummy = false := by
        rw [← hdPc]
        exact hpcDummy
      rw [hmf] at hdLab
      exact absurd hdLab (by decide)
  · rcases hbS with h | h <;> omega
  · rw [hpcBorder] at hbT
    exact absurd hbT (by decide)

private theorem installed_comp_nodes_lengthX (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp [componentGraph]

private theorem installed_graph_markedX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    ∃ N : List Node, execution.graph0.nodes =
      Compound.markNodes
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box)
        execution.params.clusterPad
        (execution.lines.map fun ls =>
          let width := ls.foldl (fun w line => max w line.width) 0
          let height := (max 1 ls.length : Int) * execution.params.lineH
          match o.direction with
          | .LR | .RL => (height, width)
          | .TB | .BT => (width, height))
        N ∧ N.length = execution.lines.length := by
  have h := execution.graph0_eq
  unfold measuredGraph at h
  obtain ⟨nodes0, hn0, h⟩ := bind_ok h
  obtain ⟨edges, _, h⟩ := bind_ok h
  obtain ⟨mm, _, h⟩ := bind_ok h
  obtain ⟨labels, _, h⟩ := bind_ok h
  obtain ⟨nodes, hnodes, h⟩ := bind_ok h
  have hfin := Except.ok.inj h
  refine ⟨nodes, ?_, ?_⟩
  · rw [← hfin]
    rfl
  · have h0 : nodes0.length = execution.lines.length := by
      unfold sizedNodes at hn0
      have h0' := mapM_ok_len _ _ _ hn0
      rwa [List.length_zipIdx] at h0'
    have h1 : nodes.length = nodes0.length := by
      have h1' := mapM_ok_len _ _ _ hnodes
      rwa [List.length_zipIdx, List.length_map] at h1'
    rw [h1]
    exact h0

private theorem installed_lines_lenX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  calc execution.lines.length = (inp.boxes.zipIdx).length :=
        mapM_ok_len _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

private theorem installed_markNodes_splitX (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (nodes : List Node) :
    ∃ marked appended, Compound.markNodes boxes pad titles nodes = marked ++ appended ∧
      marked.length = nodes.length ∧
      (∀ r ∈ appended, r.border = 2) := by
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simp only [List.length_map, List.length_zipIdx]
  · intro r hr
    obtain ⟨qq, hqq, heq⟩ := List.mem_filterMap.mp hr
    cases hrole : qq.1.role == .group with
    | true =>
      simp only [hrole, ↓reduceIte] at heq
      obtain rfl := Option.some.inj heq
      rfl
    | false =>
      simp [hrole] at heq

private theorem installed_node_key_revX {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g0 g : Graph}
    (h : exactGraph P exactIds inp o measured g0 = .ok g)
    {v : Nat} {nd : Node} (hv : g.nodes[v]? = some nd) :
    ∃ nd0, g0.nodes[v]? = some nd0 ∧ nd0.border = nd.border ∧
      nd0.clusterPath = nd.clusterPath ∧ nd0.decl = nd.decl := by
  have hlen : g.nodes.length = g0.nodes.length := exactGraph_length h
  have hlt : v < g0.nodes.length := by
    have h1 := (List.getElem?_eq_some_iff.mp hv).1
    omega
  have h0 : g0.nodes[v]? = some (g0.nodes[v]'hlt) := List.getElem?_eq_getElem hlt
  obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key h h0
  have heq : nd' = nd := Option.some.inj (hnd'.symm.trans hv)
  subst heq
  exact ⟨_, h0, hnb.symm, hnap.symm, hnd.symm⟩

private theorem installed_key_lt_boxesX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {index : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {exact : List Nat}
    (hrun : componentRunX execution.params exact
      (componentCandidate execution.graph comp index)
      labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd)
    (hd : nd.dummy = false) (hb : nd.node.border = 0)
    (hcomp : comp ∈ components execution.graph)
    {key : Nat} (hkey : comp[v]? = some key) :
    key < inp.boxes.length := by
  obtain ⟨n, hnCg, hnBorder⟩ := installed_proper_cg_nodeX hrun hv hd hb
  have hcgmap : (componentCandidate execution.graph comp index).nodes =
      comp.map fun w => execution.graph.nodes.getD w default := by
    rw [componentCandidate_nodes]
    rfl
  rw [hcgmap, List.getElem?_map, hkey, Option.map_some] at hnCg
  have hfn : execution.graph.nodes.getD key default = n := Option.some.inj hnCg
  have hnB : (execution.graph.nodes.getD key default).border = 0 := by
    rw [hfn]
    exact hnBorder
  obtain ⟨r, hr⟩ := mem_components_eq hcomp
  have hkeyLt : key < execution.graph.nodes.length := by
    have h1 : key ∈ (List.range execution.graph.nodes.length).filter
        (fun w => (componentLab execution.graph)[w]! == r) := by
      rw [← hr]
      exact List.mem_of_getElem? hkey
    exact List.mem_range.mp (List.mem_filter.mp h1).1
  have hlenGraph : execution.graph.nodes.length = execution.graph0.nodes.length := by
    have h1 := exactGraph_length execution.graph_eq
    omega
  have hkeyLt0 : key < execution.graph0.nodes.length := by omega
  obtain ⟨N, hgraph, hNlen⟩ := installed_graph_markedX execution
  have hlines := installed_lines_lenX execution
  have hN : N.length = inp.boxes.length := by
    rw [hNlen]
    exact hlines
  have hkeyTot : key < (Compound.markNodes
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box)
      execution.params.clusterPad
      (execution.lines.map fun ls =>
        let width := ls.foldl (fun w line => max w line.width) 0
        let height := (max 1 ls.length : Int) * execution.params.lineH
        match o.direction with
        | .LR | .RL => (height, width)
        | .TB | .BT => (width, height))
      N).length := by
    rw [← hgraph]
    exact hkeyLt0
  obtain ⟨rr, hrGet⟩ : ∃ rr,
      (Compound.markNodes
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box)
        execution.params.clusterPad
        (execution.lines.map fun ls =>
          let width := ls.foldl (fun w line => max w line.width) 0
          let height := (max 1 ls.length : Int) * execution.params.lineH
          match o.direction with
          | .LR | .RL => (height, width)
          | .TB | .BT => (width, height))
        N)[key]? = some rr :=
    ⟨_, List.getElem?_eq_getElem hkeyTot⟩
  have hgetExact : execution.graph.nodes[key]? = some n := by
    have h1 : execution.graph.nodes[key]? = some (execution.graph.nodes[key]'hkeyLt) :=
      List.getElem?_eq_getElem hkeyLt
    have h2 : (execution.graph.nodes[key]?).getD default = n := by
      rw [← List.getD_eq_getElem?_getD]
      exact hfn
    have hval : execution.graph.nodes[key]'hkeyLt = n := by
      simpa only [h1, Option.getD_some] using h2
    rw [h1, hval]
  obtain ⟨nd0, hnd0, hnb0, _, _⟩ := installed_node_key_revX execution.graph_eq hgetExact
  have hnB0 : nd0.border = 0 := hnb0.trans hnBorder
  have hrn : rr = nd0 := by
    have h1 : (Compound.markNodes
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box)
        execution.params.clusterPad
        (execution.lines.map fun ls =>
          let width := ls.foldl (fun w line => max w line.width) 0
          let height := (max 1 ls.length : Int) * execution.params.lineH
          match o.direction with
          | .LR | .RL => (height, width)
          | .TB | .BT => (width, height))
        N).getD key default = nd0 := by
      have h2 : execution.graph0.nodes.getD key default = nd0 := by
        rw [List.getD_eq_getElem?_getD, hnd0, Option.getD_some]
      rwa [hgraph] at h2
    have h3 : ((Compound.markNodes
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
          else box)
        execution.params.clusterPad
        (execution.lines.map fun ls =>
          let width := ls.foldl (fun w line => max w line.width) 0
          let height := (max 1 ls.length : Int) * execution.params.lineH
          match o.direction with
          | .LR | .RL => (height, width)
          | .TB | .BT => (width, height))
        N)[key]?).getD default = nd0 := h1
    rwa [hrGet] at h3
  have hnBorder0 : nd0.border = 0 := hnB0
  obtain ⟨marked, appended, hsplit, hmlen, hbord⟩ :=
    installed_markNodes_splitX _ _ _ N
  rw [hsplit] at hrGet
  rw [List.getElem?_append] at hrGet
  split at hrGet
  · simp only [hmlen] at *
    rw [← hN]
    assumption
  · have hmem := List.mem_of_getElem? hrGet
    have hb2 := hbord rr hmem
    rw [hrn] at hb2
    rw [hnBorder0] at hb2
    exact absurd hb2 (by decide)
private theorem installed_plain_frame_eq_boxRectX (P : Params) (cg : Graph) (run : Run)
    (v : Nat) (hv : v < run.proper.nodes.length)
    (hplain : (cg.nodes.getD v default).border ≠ -2) :
    frameRect P cg run v = RouteImpl.boxRect run.proper run.xs run.ys v := by
  have hb : ((cg.nodes.getD v default).border != -2) = true := by
    simp only [bne_iff_ne]
    exact hplain
  unfold frameRect
  dsimp only
  rw [ite_eq_left hb]
  simp only [nodeRect,
    RouteImpl.boxRect, RouteImpl.xAt, RouteImpl.yAt,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv,
    Option.getD_some, RouteImpl.nodeW, RouteImpl.nodeH]

private theorem componentRunX_rankCoordsWithX {P : Params} {exact : List Nat} {cg : Graph}
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

private theorem componentRunX_dims_nonnegX {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ProperDimsNonneg run.proper := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hproper, _, hx, hprox, hdrop,
    _, _, _⟩ := componentRunX_spec h
  obtain ⟨y, top, hy⟩ := componentRunX_rankCoordsWithX h
  have hsize : CoordsImpl.sizesNonneg run.coordinateProper = true :=
    (CoordsImpl.rankCoordsWith_spec hy).2.2.2.2.1
  have hd := proxyWidths_dims_nonneg (sizesNonneg_lookup hsize) hprox
  rw [← hdrop]
  exact hd

private theorem installed_fold_rects_sizeX (P : Params) (exactIds : List String) (inp : Input)
    (o : Options) (graph : Graph) (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponentX P exactIds inp o graph acc comp labels) start = .ok out →
      out.rects.size = start.rects.size
  | [], start, out, h => by
    have he : start = out := Except.ok.inj h
    rw [he]
  | comp :: comps, start, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨next, hnext, hrest⟩ := bind_ok h
    rw [installed_fold_rects_sizeX P exactIds inp o graph labels comps next out hrest]
    exact (layoutComponentX_sizes hnext).1.symm

private theorem installed_place_rects_lengthX (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run 0 labels loops).rects.length = cg.nodes.length := by
  unfold placeComponentExact
  dsimp only
  simp only [List.length_map, List.length_range]

private theorem slIdxLookupX {comp : List Nat} {x : Nat} (hmem : x ∈ comp) :
    comp[comp.idxOf x]? = some x :=
  (List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem)).trans
    (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)))

private theorem slIdxMemOfLtX {l : List Nat} {x : Nat}
    (h : l.idxOf x < l.length) : x ∈ l :=
  List.idxOf_lt_length_iff.mp h

private theorem slEndpointCasesX {boxes : List ModelBox} (s : Bool) (i j : Nat) :
    Compound.endpoint boxes s i j = i ∨
      (Compound.endpoint boxes s i j = Compound.bottomIndex boxes i ∧
        ∀ box, boxes[i]? = some box → box.role = .group) := by
  unfold Compound.endpoint
  cases hbi : boxes[i]? with
  | none => exact Or.inl rfl
  | some box =>
    cases hbj : boxes[j]? with
    | none => exact Or.inl rfl
    | some target =>
      dsimp only
      by_cases hc : (box.role != .group || i == j) = true
      · rw [ite_eq_left hc]
        exact Or.inl rfl
      · rw [ite_eq_right hc]
        by_cases hd : (s == Compound.inside boxes box.id target.id) = true
        · rw [ite_eq_left hd]
          exact Or.inl rfl
        · rw [ite_eq_right hd]
          refine Or.inr ⟨rfl, ?_⟩
          intro box' hb'
          have heq : box' = box := (Option.some.inj hb').symm
          rw [heq]
          cases hbr : box.role
          · exfalso
            have h1 : (box.role != .group || i == j) = true := by
              rw [hbr]
              cases hij : (i == j) <;> rfl
            exact hc h1
          · rfl

private def slPreparedX (inp : Input) : List ModelBox :=
  inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
    else box

private theorem endpoint_flat_of_boundX {P : List ModelBox} {s : Bool} {i j key : Nat}
    (heq : key = Compound.endpoint P s i j) (hlt : key < P.length) : key = i := by
  rcases slEndpointCasesX s i j with hflat | ⟨hbot, _⟩
  · rw [heq]
    exact hflat
  · have hbig : P.length ≤ key := by
      rw [heq, hbot]
      unfold Compound.bottomIndex
      exact Nat.le_add_right _ _
    exact False.elim (absurd hbig (Nat.not_le_of_gt hlt))

private theorem installed_route_model_keysX
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel}
    {graph0 graph : Graph} {exactIds : List String}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate : Nat} {edge : Edge}
    (hmem : edge ∈ (componentCandidate graph comp candidate).edges)
    {key : Nat} (hdecl : edge.decl = key)
    {route : ModelRoute} (hroute : inp.routes[key]? = some route)
    (hrev : edge.reversed = false)
    (htailLt : edge.tail < comp.length) (hheadLt : edge.head < comp.length) :
    ∃ (raw : Edge) (source target : ModelBox),
      edgeOf inp route key = .ok raw ∧
      comp.idxOf (Compound.aliasEdge (slPreparedX inp) raw).tail = edge.tail ∧
      comp.idxOf (Compound.aliasEdge (slPreparedX inp) raw).head = edge.head ∧
      comp[comp.idxOf (Compound.aliasEdge (slPreparedX inp) raw).tail]? =
        some (Compound.aliasEdge (slPreparedX inp) raw).tail ∧
      comp[comp.idxOf (Compound.aliasEdge (slPreparedX inp) raw).head]? =
        some (Compound.aliasEdge (slPreparedX inp) raw).head ∧
      inp.boxes[raw.tail]? = some source ∧ source.id = route.fromId ∧
      inp.boxes[raw.head]? = some target ∧ target.id = route.toId := by
  obtain ⟨globalEdge, hglobal, _, hsemantic⟩ :=
    componentCandidate_semantic_source hmem
  have hglobal0 : globalEdge ∈ graph0.edges := by
    rw [exactGraph_edges hgraphX] at hglobal
    exact hglobal
  obtain ⟨index, route', raw, hroute', hrawOf, halias⟩ :=
    measuredGraph_edge_source hgraph0 hglobal0
  obtain ⟨hdeclRaw, hreversed, source, target, hsource, hsourceId, htarget, htargetId⟩ :=
    edgeOf_semantic_endpoints hrawOf
  have hdeclIdx : edge.decl = index := by
    calc
      edge.decl = globalEdge.decl := by
        simpa only [Edge.original_decl] using congrArg Edge.decl hsemantic
      _ = raw.decl := by rw [halias]; rfl
      _ = index := hdeclRaw
  have hglobalReversed : globalEdge.reversed = false := by
    rw [halias]; exact hreversed
  have horiginal : globalEdge.original = globalEdge := by
    cases globalEdge with
    | mk tail head minLen decl reversed =>
      cases hglobalReversed
      rfl
  have hidxKey : index = key := hdeclIdx.symm.trans hdecl
  have hrouteAt : inp.routes[index]? = some route := by
    rw [hidxKey]
    exact hroute
  have hrouteEq : route' = route := Option.some.inj (hroute'.symm.trans hrouteAt)
  have hrawOf' : edgeOf inp route key = .ok raw := by
    rw [← hidxKey, ← hrouteEq]
    exact hrawOf
  have hsl : slPreparedX inp = (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box) := rfl
  have hsem : edge.original =
      {Compound.aliasEdge (slPreparedX inp) raw with
        tail := comp.idxOf (Compound.aliasEdge (slPreparedX inp) raw).tail,
        head := comp.idxOf (Compound.aliasEdge (slPreparedX inp) raw).head} := by
    have h1 := hsemantic
    rw [horiginal, halias, ← hsl] at h1
    exact h1
  have htailEq : edge.original.tail =
      comp.idxOf (Compound.aliasEdge (slPreparedX inp) raw).tail :=
    congrArg Edge.tail hsem
  have hheadEq : edge.original.head =
      comp.idxOf (Compound.aliasEdge (slPreparedX inp) raw).head :=
    congrArg Edge.head hsem
  have htailOrig : edge.original.tail = edge.tail := by simp [Edge.original, hrev]
  have hheadOrig : edge.original.head = edge.head := by simp [Edge.original, hrev]
  have hcompTail : comp.idxOf (Compound.aliasEdge (slPreparedX inp) raw).tail =
      edge.tail :=
    htailEq.symm.trans htailOrig
  have hcompHead : comp.idxOf (Compound.aliasEdge (slPreparedX inp) raw).head =
      edge.head :=
    hheadEq.symm.trans hheadOrig
  have hmemTail : (Compound.aliasEdge (slPreparedX inp) raw).tail ∈ comp := by
    apply slIdxMemOfLtX
    rw [hcompTail]
    exact htailLt
  have hmemHead : (Compound.aliasEdge (slPreparedX inp) raw).head ∈ comp := by
    apply slIdxMemOfLtX
    rw [hcompHead]
    exact hheadLt
  have hsid : source.id = route.fromId := by
    rw [← hrouteEq]
    exact hsourceId
  have htid : target.id = route.toId := by
    rw [← hrouteEq]
    exact htargetId
  exact ⟨raw, source, target, hrawOf', hcompTail, hcompHead,
    slIdxLookupX hmemTail, slIdxLookupX hmemHead,
    hsource, hsid, htarget, htid⟩

private theorem installed_span_rect_transport_tiedX {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {q : List Nat × Part} {ctx0 : StraightenCtx} {ox oy : Int} {i : Nat}
    {e : ProperEdge} {span : StraightSpan} {routing : Routing}
    (hmem : q ∈ execution.packedAcc.parts)
    (hctx : q.2.straighten = some ctx0)
    (hoff : straightenOffset q.1 q.2 execution.packedAcc.rects = some (ctx0, ox, oy))
    (he : ctx0.proper.edges[i]? = some e)
    (hspan : straightSpanOf { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }
      routing i = .ok (some span)) :
    ∃ (tailKey headKey : Nat) (tailRect headRect : Rect),
      e.tail < q.1.length ∧ e.head < q.1.length ∧
      q.1[e.tail]? = some tailKey ∧ q.1[e.head]? = some headKey ∧
      execution.packedAcc.rects[tailKey]? = some tailRect ∧
      execution.packedAcc.rects[headKey]? = some headRect ∧
      0 ≤ tailRect.h ∧ 0 ≤ headRect.h ∧
      tailRect.x = span.tailRect.x ∧ tailRect.w = span.tailRect.w ∧
      headRect.x = span.headRect.x ∧ headRect.w = span.headRect.w ∧
      span.top = tailRect.y + tailRect.h ∧ span.bottom = headRect.y := by
  have hpartsEq := packAcc_parts_eqX execution.packed_eq
  have hmemC : q ∈ execution.componentsAcc.parts := by
    rwa [hpartsEq] at hmem
  obtain ⟨index, run, loops, area, hrun, hplace, hproper, hxs, hys, hdx, hdy⟩ :=
    installed_run_of_memX execution hmemC hctx
  obtain ⟨e', he', helig, _, _⟩ := straightSpanOf_invX hspan
  have he'2 : ctx0.proper.edges[i]? = some e' := he'
  have heq : e' = e := Option.some.inj (he'2.symm.trans he)
  rw [heq] at he' helig
  have helig0 : straightEdgeEligible ctx0 routing i e = true := helig
  unfold straightEdgeEligible at helig0
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at helig0
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hTail⟩, hHead⟩, _⟩, _⟩, _⟩ := helig0
  obtain ⟨tailNode, hvt0, htd, htl, htb⟩ := straightRealNode_existsX hTail
  obtain ⟨headNode, hvh0, hhd, hhl, hhb⟩ := straightRealNode_existsX hHead
  have hvt : run.proper.nodes[e.tail]? = some tailNode := by
    rw [← hproper]
    exact hvt0
  have hvh : run.proper.nodes[e.head]? = some headNode := by
    rw [← hproper]
    exact hvh0
  have htailLtCg : e.tail < (componentCandidate execution.graph q.1 index).nodes.length :=
    installed_proper_belowX hrun hvt htd htb
  have hheadLtCg : e.head < (componentCandidate execution.graph q.1 index).nodes.length :=
    installed_proper_belowX hrun hvh hhd hhb
  have hclen : (componentCandidate execution.graph q.1 index).nodes.length = q.1.length :=
    installed_comp_nodes_lengthX _ _ _
  have htailLt : e.tail < q.1.length := by
    rw [← hclen]
    exact htailLtCg
  have hheadLt : e.head < q.1.length := by
    rw [← hclen]
    exact hheadLtCg
  obtain ⟨tailKey, htk⟩ : ∃ k, q.1[e.tail]? = some k :=
    ⟨_, List.getElem?_eq_some_iff.mpr ⟨htailLt, rfl⟩⟩
  obtain ⟨headKey, hhk⟩ : ∃ k, q.1[e.head]? = some k :=
    ⟨_, List.getElem?_eq_some_iff.mpr ⟨hheadLt, rfl⟩⟩
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hparts, _⟩ := actual_components_parts_geometryX hempty execution.components_eq
  have hmember : (q.1, q.2) ∈ execution.componentsAcc.parts := hmemC
  have hcomp : q.1 ∈ components execution.graph := by
    have h1 : q.1 ∈ execution.componentsAcc.parts.map (·.1) :=
      List.mem_map_of_mem hmember
    rwa [hparts] at h1
  have hmidSize : execution.componentsAcc.rects.size = inp.boxes.length := by
    have hsz := installed_fold_rects_sizeX execution.params exactIds inp o execution.graph
      execution.measured (components execution.graph) _ _ execution.components_eq
    rw [hsz]
    exact Array.size_replicate
  have hsizeT_mid : tailKey < execution.componentsAcc.rects.size := by
    rw [hmidSize]
    exact installed_key_lt_boxesX execution hrun hvt htd htb hcomp htk
  have hsizeH_mid : headKey < execution.componentsAcc.rects.size := by
    rw [hmidSize]
    exact installed_key_lt_boxesX execution hrun hvh hhd hhb hcomp hhk
  have hsizeT : tailKey < execution.packedAcc.rects.size := by
    have h2 : inp.boxes.length = execution.packedAcc.rects.size := by
      rw [← hmidSize]
      exact (installed_packAcc_rects_size execution.packed_eq).symm
    have h1 : tailKey < inp.boxes.length :=
      installed_key_lt_boxesX execution hrun hvt htd htb hcomp htk
    omega
  have hsizeH : headKey < execution.packedAcc.rects.size := by
    have h2 : inp.boxes.length = execution.packedAcc.rects.size := by
      rw [← hmidSize]
      exact (installed_packAcc_rects_size execution.packed_eq).symm
    have h1 : headKey < inp.boxes.length :=
      installed_key_lt_boxesX execution hrun hvh hhd hhb hcomp hhk
    omega
  have hpackEq := execution.packed_eq
  unfold packAcc at hpackEq
  obtain ⟨packed, hpacked, hprest⟩ := bind_ok hpackEq
  have hplen : execution.componentsAcc.parts.length = packed.boxes.length := by
    have hcount := Pack.pack_count hpacked
    rw [hcount, List.length_map]
  obtain ⟨c, hc⟩ := List.getElem?_of_mem hmemC
  have hcLt : c < packed.boxes.length := by
    have h1 : c < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hc).1
    omega
  have hbox : packed.boxes[c]? = some packed.boxes[c] :=
    List.getElem?_eq_some_iff.mpr ⟨hcLt, rfl⟩
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
      some (q, packed.boxes[c]) :=
    List.getElem?_zip_eq_some.mpr ⟨hc, hbox⟩
  have hrectsLen : q.2.rects.length = q.1.length := by
    have h1 := installed_place_rects_lengthX execution.params
      (componentCandidate execution.graph q.1 index) run execution.measured loops
    have h2 := installed_comp_nodes_lengthX execution.graph q.1 index
    rw [hplace, h1]
    exact h2
  have hRt : e.tail < q.2.rects.length := by
    rw [hrectsLen]
    exact htailLt
  have hRh : e.head < q.2.rects.length := by
    rw [hrectsLen]
    exact hheadLt
  obtain ⟨rectT, hrT⟩ : ∃ r, q.2.rects[e.tail]? = some r :=
    ⟨_, List.getElem?_eq_getElem hRt⟩
  obtain ⟨rectH, hrH⟩ : ∃ r, q.2.rects[e.head]? = some r :=
    ⟨_, List.getElem?_eq_getElem hRh⟩
  have hentryT : (q.1.zip q.2.rects)[e.tail]? = some (tailKey, rectT) :=
    List.getElem?_zip_eq_some.mpr ⟨htk, hrT⟩
  have hentryH : (q.1.zip q.2.rects)[e.head]? = some (headKey, rectH) :=
    List.getElem?_zip_eq_some.mpr ⟨hhk, hrH⟩
  have hvalT := actual_components_packed_rect_valueX hempty execution.components_eq
    execution.packed_eq packed hpacked hselected hentryT hsizeT_mid default
  have hvalH := actual_components_packed_rect_valueX hempty execution.components_eq
    execution.packed_eq packed hpacked hselected hentryH hsizeH_mid default
  have hlookT : execution.packedAcc.rects[tailKey]?
      = some (shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectT) := by
    have hneT : execution.packedAcc.rects[tailKey]? ≠ none := by
      intro hcon
      have hle := Array.getElem?_eq_none_iff.mp hcon
      omega
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hneT
    have h2 : ((execution.packedAcc.rects[tailKey]?).getD default)
        = shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectT := by
      rw [← Array.getD_eq_getD_getElem?]
      exact hvalT
    have h3 : r = shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectT := by
      rw [hr] at h2
      simpa using h2
    rwa [h3] at hr
  have hlookH : execution.packedAcc.rects[headKey]?
      = some (shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectH) := by
    have hneH : execution.packedAcc.rects[headKey]? ≠ none := by
      intro hcon
      have hle := Array.getElem?_eq_none_iff.mp hcon
      omega
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hneH
    have h2 : ((execution.packedAcc.rects[headKey]?).getD default)
        = shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectH := by
      rw [← Array.getD_eq_getD_getElem?]
      exact hvalH
    have h3 : r = shiftRect (q, packed.boxes[c]).2.x (q, packed.boxes[c]).2.y rectH := by
      rw [hr] at h2
      simpa using h2
    rwa [h3] at hr
  have hdims := componentRunX_dims_nonnegX hrun
  let ctxS : StraightenCtx := { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }
  have hspanS : straightSpanOf ctxS routing i = .ok (some span) := hspan
  have hspanUnfold := hspanS
  unfold straightSpanOf at hspanUnfold
  cases heS : ctxS.proper.edges[i]? with
  | none =>
    simp only [heS] at hspanUnfold
    cases hspanUnfold
  | some eS =>
    simp only [heS] at hspanUnfold
    have heQ : ctx0.proper.edges[i]? = some eS := heS
    have heSEq : eS = e := Option.some.inj (heQ.symm.trans he)
    rw [heSEq] at hspanUnfold heS
    cases helS : !straightEdgeEligible ctxS routing i e with
    | true =>
      simp only [helS] at hspanUnfold
      cases hspanUnfold
    | false =>
      simp only [helS] at hspanUnfold
      cases hgeom : straightGeom ctxS routing i e with
      | mk tw hw th hh tailLeft headLeft lo hi cx =>
        simp only [hgeom] at hspanUnfold
        by_cases hlo : lo > hi
        · rw [ite_eq_left hlo] at hspanUnfold
          cases hspanUnfold
        · rw [ite_eq_right hlo] at hspanUnfold
          obtain ⟨pin, hpinN, hrest1⟩ := bind_ok hspanUnfold
          obtain ⟨top, htopN, hrest2⟩ := bind_ok hrest1
          obtain ⟨bottom, hbotN, hrest3⟩ := bind_ok hrest2
          by_cases hge : top ≥ bottom
          · rw [ite_eq_left hge] at hrest3
            cases hrest3
          · rw [ite_eq_right hge] at hrest3
            obtain ⟨column, hcolN, hfin⟩ := bind_ok hrest3
            have hsEq := Option.some.inj (Except.ok.inj hfin)
            have hpinEq : pin = cx := by
              unfold narrowI32 at hpinN
              by_cases hc : -2147483648 ≤ cx ∧ cx ≤ 2147483647
              · rw [ite_eq_left hc] at hpinN
                exact (Except.ok.inj hpinN).symm
              · rw [ite_eq_right hc] at hpinN
                cases hpinN
            have htopEq : top = ctx0.ys.getD e.tail 0 + th + (ctx0.dy + oy) := by
              unfold narrowI32 at htopN
              have hctxYs : ctxS.ys.getD e.tail 0 = ctx0.ys.getD e.tail 0 := rfl
              have hctxDy : ctxS.dy = ctx0.dy + oy := rfl
              by_cases hc : -2147483648 ≤ ctx0.ys.getD e.tail 0 + th +
                  (ctx0.dy + oy) ∧ ctx0.ys.getD e.tail 0 + th + (ctx0.dy + oy) ≤ 2147483647
              · have hc' : -2147483648 ≤ ctxS.ys.getD e.tail 0 + th + ctxS.dy ∧
                  ctxS.ys.getD e.tail 0 + th + ctxS.dy ≤ 2147483647 := by
                  rwa [hctxYs, hctxDy]
                rw [ite_eq_left hc'] at htopN
                have htop0 := (Except.ok.inj htopN).symm
                rwa [hctxYs, hctxDy] at htop0
              · have hc' : ¬ (-2147483648 ≤ ctxS.ys.getD e.tail 0 + th + ctxS.dy ∧
                  ctxS.ys.getD e.tail 0 + th + ctxS.dy ≤ 2147483647) := by
                  rwa [hctxYs, hctxDy]
                rw [ite_eq_right hc'] at htopN
                cases htopN
            have hbotEq : bottom = ctx0.ys.getD e.head 0 + (ctx0.dy + oy) := by
              unfold narrowI32 at hbotN
              have hctxYs : ctxS.ys.getD e.head 0 = ctx0.ys.getD e.head 0 := rfl
              have hctxDy : ctxS.dy = ctx0.dy + oy := rfl
              by_cases hc : -2147483648 ≤ ctx0.ys.getD e.head 0 +
                  (ctx0.dy + oy) ∧ ctx0.ys.getD e.head 0 + (ctx0.dy + oy) ≤ 2147483647
              · have hc' : -2147483648 ≤ ctxS.ys.getD e.head 0 + ctxS.dy ∧
                  ctxS.ys.getD e.head 0 + ctxS.dy ≤ 2147483647 := by
                  rwa [hctxYs, hctxDy]
                rw [ite_eq_left hc'] at hbotN
                have hbot0 := (Except.ok.inj hbotN).symm
                rwa [hctxYs, hctxDy] at hbot0
              · have hc' : ¬ (-2147483648 ≤ ctxS.ys.getD e.head 0 + ctxS.dy ∧
                  ctxS.ys.getD e.head 0 + ctxS.dy ≤ 2147483647) := by
                  rwa [hctxYs, hctxDy]
                rw [ite_eq_right hc'] at hbotN
                cases hbotN
            have hcolEq : column = cx + (ctx0.dx + ox) := by
              unfold narrowI32 at hcolN
              have hctxDx : ctxS.dx = ctx0.dx + ox := rfl
              by_cases hc : -2147483648 ≤ cx + (ctx0.dx + ox) ∧
                  cx + (ctx0.dx + ox) ≤ 2147483647
              · have hc' : -2147483648 ≤ cx + ctxS.dx ∧ cx + ctxS.dx ≤ 2147483647 := by
                  rwa [hctxDx]
                rw [ite_eq_left hc'] at hcolN
                have hcol0 := (Except.ok.inj hcolN).symm
                rwa [hctxDx] at hcol0
              · have hc' : ¬ (-2147483648 ≤ cx + ctxS.dx ∧ cx + ctxS.dx ≤ 2147483647) := by
                  rwa [hctxDx]
                rw [ite_eq_right hc'] at hcolN
                cases hcolN
            subst hsEq
            simp only [straightGeom] at hgeom
            simp only [StraightGeom.mk.injEq] at hgeom
            obtain ⟨hEtw, hEhw, hEth, hEhh, hEtl, hEhl, _, _, _⟩ := hgeom
            have hxsT : ctx0.xs.getD e.tail 0 = run.xs.getD e.tail 0 := by
              rw [hxs]
            have hxsH : ctx0.xs.getD e.head 0 = run.xs.getD e.head 0 := by
              rw [hxs]
            have hysT : ctx0.ys.getD e.tail 0 = run.ys.getD e.tail 0 := by
              rw [hys]
            have hysH : ctx0.ys.getD e.head 0 = run.ys.getD e.head 0 := by
              rw [hys]
            have hproperEq : ctx0.proper = run.proper := hproper
            have htwEq : tw = tailNode.node.w := by
              have htw0 : tw = RouteImpl.nodeW
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.tail := by
                rw [← hEtw]
                rfl
              have htw1 : RouteImpl.nodeW
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.tail =
                  RouteImpl.nodeW ctx0.proper e.tail := rfl
              rw [htw0, htw1, hproperEq]
              simp only [RouteImpl.nodeW, hvt]
            have hhwEq : hw = headNode.node.w := by
              have hhw0 : hw = RouteImpl.nodeW
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.head := by
                rw [← hEhw]
                rfl
              have hhw1 : RouteImpl.nodeW
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.head =
                  RouteImpl.nodeW ctx0.proper e.head := rfl
              rw [hhw0, hhw1, hproperEq]
              simp only [RouteImpl.nodeW, hvh]
            have hthEq : th = tailNode.node.h := by
              have hth0 : th = RouteImpl.nodeH
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.tail := by
                rw [← hEth]
                rfl
              have hth1 : RouteImpl.nodeH
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.tail =
                  RouteImpl.nodeH ctx0.proper e.tail := rfl
              rw [hth0, hth1, hproperEq]
              simp only [RouteImpl.nodeH, hvt]
            have hhhEq : hh = headNode.node.h := by
              have hhh0 : hh = RouteImpl.nodeH
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.head := by
                rw [← hEhh]
                rfl
              have hhh1 : RouteImpl.nodeH
                  ({ ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy }).proper e.head =
                  RouteImpl.nodeH ctx0.proper e.head := rfl
              rw [hhh0, hhh1, hproperEq]
              simp only [RouteImpl.nodeH, hvh]
            have hxsEqT : ctxS.xs.getD e.tail 0 = ctx0.xs.getD e.tail 0 := rfl
            have hxsEqH : ctxS.xs.getD e.head 0 = ctx0.xs.getD e.head 0 := rfl
            have htlEq : tailLeft = ctx0.xs.getD e.tail 0 - tw / 2 := by
              rw [← hEtl, hxsEqT, hEtw]
            have hhlEq : headLeft = ctx0.xs.getD e.head 0 - hw / 2 := by
              rw [← hEhl, hxsEqH, hEhw]
            have htailDims := hdims e.tail tailNode hvt
            have hheadDims := hdims e.head headNode hvh
            have hthNonneg : 0 ≤ th := by
              rw [hthEq]
              exact htailDims.2
            have hhhNonneg : 0 ≤ hh := by
              rw [hhhEq]
              exact hheadDims.2
            have htwNonneg : 0 ≤ tw := by
              rw [htwEq]
              exact htailDims.1
            have hwNonneg : 0 ≤ hw := by
              rw [hhwEq]
              exact hheadDims.1
            have hvtLt : e.tail < run.proper.nodes.length :=
              (List.getElem?_eq_some_iff.mp hvt).1
            have hvhLt : e.head < run.proper.nodes.length :=
              (List.getElem?_eq_some_iff.mp hvh).1
            obtain ⟨cgTail, hcgTail, hcgTailB⟩ :=
              installed_proper_cg_nodeX hrun hvt htd htb
            obtain ⟨cgHead, hcgHead, hcgHeadB⟩ :=
              installed_proper_cg_nodeX hrun hvh hhd hhb
            have hplainT : ((componentCandidate execution.graph q.1 index).nodes.getD
                e.tail default).border ≠ -2 := by
              have hget : (componentCandidate execution.graph q.1 index).nodes.getD
                  e.tail default = cgTail := by
                simp only [List.getD_eq_getElem?_getD, hcgTail, Option.getD_some]
              rw [hget, hcgTailB]
              omega
            have hplainH : ((componentCandidate execution.graph q.1 index).nodes.getD
                e.head default).border ≠ -2 := by
              have hget : (componentCandidate execution.graph q.1 index).nodes.getD
                  e.head default = cgHead := by
                simp only [List.getD_eq_getElem?_getD, hcgHead, Option.getD_some]
              rw [hget, hcgHeadB]
              omega
            have hframeT : frameRect execution.params
                (componentCandidate execution.graph q.1 index) run e.tail =
                RouteImpl.boxRect run.proper run.xs run.ys e.tail :=
              installed_plain_frame_eq_boxRectX _ _ _ _ hvtLt hplainT
            have hframeH : frameRect execution.params
                (componentCandidate execution.graph q.1 index) run e.head =
                RouteImpl.boxRect run.proper run.xs run.ys e.head :=
              installed_plain_frame_eq_boxRectX _ _ _ _ hvhLt hplainH
            have hrectTEq : rectT = shiftRect ctx0.dx ctx0.dy
                (frameRect execution.params
                  (componentCandidate execution.graph q.1 index) run e.tail) := by
              have hlookup : q.2.rects[e.tail]? = some (shiftRect ctx0.dx ctx0.dy
                  (frameRect execution.params
                    (componentCandidate execution.graph q.1 index) run e.tail)) := by
                rw [hplace]
                show (placeComponentExact execution.params
                  (componentCandidate execution.graph q.1 index) run 0
                  execution.measured loops).rects[e.tail]? = _
                unfold placeComponentExact
                dsimp only
                simp only [List.getElem?_map, List.getElem?_range htailLtCg,
                  Option.map_some]
                unfold placeBoundsX at hdx hdy
                rw [hdx, hdy]
              rw [hlookup] at hrT
              exact (Option.some.inj hrT).symm
            have hrectHEq : rectH = shiftRect ctx0.dx ctx0.dy
                (frameRect execution.params
                  (componentCandidate execution.graph q.1 index) run e.head) := by
              have hlookup : q.2.rects[e.head]? = some (shiftRect ctx0.dx ctx0.dy
                  (frameRect execution.params
                    (componentCandidate execution.graph q.1 index) run e.head)) := by
                rw [hplace]
                show (placeComponentExact execution.params
                  (componentCandidate execution.graph q.1 index) run 0
                  execution.measured loops).rects[e.head]? = _
                unfold placeComponentExact
                dsimp only
                simp only [List.getElem?_map, List.getElem?_range hheadLtCg,
                  Option.map_some]
                unfold placeBoundsX at hdx hdy
                rw [hdx, hdy]
              rw [hlookup] at hrH
              exact (Option.some.inj hrH).symm
            obtain ⟨v0, r0, base0, rest0, hzip0, hstraight0, hbase0, hox0, hoy0⟩ :
                ∃ (v : Nat) (r : Rect) (base : Rect) (rest : List (Nat × Rect)),
                  q.1.zip q.2.rects = (v, r) :: rest ∧
                  q.2.straighten = some ctx0 ∧
                  execution.packedAcc.rects[v]? = some base ∧
                  ox = base.x - r.x ∧ oy = base.y - r.y := by
              unfold straightenOffset at hoff
              cases h1off : q.2.straighten with
              | none =>
                simp only [h1off] at hoff
                cases hoff
              | some cc =>
                cases h2off : q.1.zip q.2.rects with
                | nil =>
                  simp only [h1off, h2off] at hoff
                  cases hoff
                | cons pr rest =>
                  cases pr with
                  | mk v r =>
                    cases h3off : execution.packedAcc.rects[v]? with
                    | none =>
                      simp only [h1off, h2off, h3off] at hoff
                      cases hoff
                    | some base =>
                      simp only [h1off, h2off, h3off] at hoff
                      have heq := Option.some.inj hoff
                      simp only [Prod.mk.injEq] at heq
                      obtain ⟨hctxEq, hoxEq, hoyEq⟩ := heq
                      exact Exists.intro v (Exists.intro r (Exists.intro base
                        (Exists.intro rest ⟨rfl, congrArg some hctxEq, h3off,
                          hoxEq.symm, hoyEq.symm⟩)))
            have hv0Packed : v0 < execution.packedAcc.rects.size := by
              obtain ⟨h, _⟩ := Array.getElem?_eq_some_iff.mp hbase0
              exact h
            have hv0Mid : v0 < execution.componentsAcc.rects.size := by
              have heqSize := installed_packAcc_rects_size execution.packed_eq
              omega
            have hentry0 : (q.1.zip q.2.rects)[0]? = some (v0, r0) := by
              simp [hzip0]
            have hval0 := actual_components_packed_rect_valueX hempty execution.components_eq
              execution.packed_eq packed hpacked hselected hentry0 hv0Mid default
            have hlook0 : execution.packedAcc.rects[v0]?
                = some (shiftRect (q, packed.boxes[c]).2.x
                  (q, packed.boxes[c]).2.y r0) := by
              have hne0 : execution.packedAcc.rects[v0]? ≠ none := by
                intro hcon
                have hle := Array.getElem?_eq_none_iff.mp hcon
                omega
              obtain ⟨rr, hrr⟩ := Option.ne_none_iff_exists'.mp hne0
              have h22 : ((execution.packedAcc.rects[v0]?).getD default)
                  = shiftRect (q, packed.boxes[c]).2.x
                    (q, packed.boxes[c]).2.y r0 := by
                rw [← Array.getD_eq_getD_getElem?]
                exact hval0
              have h33 : rr = shiftRect (q, packed.boxes[c]).2.x
                  (q, packed.boxes[c]).2.y r0 := by
                rw [hrr] at h22
                simpa using h22
              rwa [h33] at hrr
            have hbaseEq : base0 = shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y r0 :=
              Option.some.inj (hbase0.symm.trans hlook0)
            have hbxEq : base0.x = r0.x + (packed.boxes[c]).x := by
              have hbb : base0 = shiftRect (packed.boxes[c]).x
                  (packed.boxes[c]).y r0 := by
                have : (q, packed.boxes[c]).2.x = (packed.boxes[c]).x := rfl
                have : (q, packed.boxes[c]).2.y = (packed.boxes[c]).y := rfl
                rwa [this, this] at hbaseEq
              rw [hbb]
              rfl
            have hbyEq : base0.y = r0.y + (packed.boxes[c]).y := by
              have hbb : base0 = shiftRect (packed.boxes[c]).x
                  (packed.boxes[c]).y r0 := by
                have : (q, packed.boxes[c]).2.x = (packed.boxes[c]).x := rfl
                have : (q, packed.boxes[c]).2.y = (packed.boxes[c]).y := rfl
                rwa [this, this] at hbaseEq
              rw [hbb]
              rfl
            have hoxBx : ox = (packed.boxes[c]).x := by omega
            have hoyBy : oy = (packed.boxes[c]).y := by omega
            have hboxX : (q, packed.boxes[c]).2.x = (packed.boxes[c]).x := rfl
            have hboxY : (q, packed.boxes[c]).2.y = (packed.boxes[c]).y := rfl
            have hfdivT : Int.fdiv tailNode.node.w 2 = tailNode.node.w / 2 :=
              Int.fdiv_eq_ediv_of_nonneg _ (by decide)
            have hfdivH : Int.fdiv headNode.node.w 2 = headNode.node.w / 2 :=
              Int.fdiv_eq_ediv_of_nonneg _ (by decide)
            have htailRectX : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).x =
                tailLeft + (ctx0.dx + ox) := by
              rw [hrectTEq, hframeT, htlEq, htwEq, hxsT, hoxBx, hboxX]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.xAt,
                RouteImpl.nodeW, hvt, hfdivT]
              omega
            have htailRectW : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).w = tw := by
              rw [hrectTEq, hframeT, htwEq]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.nodeW, hvt]
            have hheadRectX : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).x =
                headLeft + (ctx0.dx + ox) := by
              rw [hrectHEq, hframeH, hhlEq, hhwEq, hxsH, hoxBx, hboxX]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.xAt,
                RouteImpl.nodeW, hvh, hfdivH]
              omega
            have hheadRectW : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).w = hw := by
              rw [hrectHEq, hframeH, hhwEq]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.nodeW, hvh]
            have htailRectY : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).y =
                ctx0.ys.getD e.tail 0 + (ctx0.dy + oy) := by
              rw [hrectTEq, hframeT, hysT, hoyBy, hboxY]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.yAt]
              omega
            have htailRectH : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).h = th := by
              rw [hrectTEq, hframeT, hthEq]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.nodeH, hvt]
            have hheadRectY : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).y =
                ctx0.ys.getD e.head 0 + (ctx0.dy + oy) := by
              rw [hrectHEq, hframeH, hysH, hoyBy, hboxY]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.yAt]
              omega
            have hheadRectH : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).h = hh := by
              rw [hrectHEq, hframeH, hhhEq]
              simp only [shiftRect, RouteImpl.boxRect, RouteImpl.nodeH, hvh]
            have htopEq' : top = (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).y +
                (shiftRect (q, packed.boxes[c]).2.x
                  (q, packed.boxes[c]).2.y rectT).h := by
              rw [htopEq, htailRectY, htailRectH]
              omega
            have hbotEq' : bottom = (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).y := by
              rw [hbotEq, hheadRectY]
            have hfinalTh : 0 ≤ (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).h := by
              rw [htailRectH]
              exact hthNonneg
            have hfinalHh : 0 ≤ (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).h := by
              rw [hheadRectH]
              exact hhhNonneg
            have hfinalTx : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).x =
                tailLeft + (ctx0.dx + ox) := htailRectX
            have hfinalTw : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectT).w = tw := htailRectW
            have hfinalHx : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).x =
                headLeft + (ctx0.dx + ox) := hheadRectX
            have hfinalHw : (shiftRect (q, packed.boxes[c]).2.x
                (q, packed.boxes[c]).2.y rectH).w = hw := hheadRectW
            exact ⟨tailKey, headKey, _, _, htailLt, hheadLt, htk, hhk,
              hlookT, hlookH, hfinalTh, hfinalHh, hfinalTx, hfinalTw,
              hfinalHx, hfinalHw, htopEq', hbotEq'⟩

/-- The proper edge of an installed route has the component edge's endpoints. -/
theorem SceneExecutionX.installed_edge_endpoints {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} {pts : List Point} (_hinst : Installed execution.packedAcc key pts)
    {q : (List Nat × Part) × Rect} {packed : Pack.State} {c : Nat}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area }) :
    ∀ (qS : List Nat × Part) (ctx0 : StraightenCtx) (j : Nat) (eS : ProperEdge),
      qS ∈ execution.packedAcc.parts →
      qS.2.straighten = some ctx0 →
      ctx0.proper.edges[j]? = some eS →
      eS.decl = key →
      ∀ {routing : Routing} {span : StraightSpan} {ox oy : Int},
      straightSpanOf { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy } routing j =
        .ok (some span) →
      eS.tail = edge.tail ∧ eS.head = edge.head := by
  intro qS ctx0 j eS hmem hctx he hdeclS _routing _span _ox _oy hspan
  have hid := execution.installed_edge_installer _hinst hselected hedge hdecl hrun hpart
    qS ctx0 j eS hmem hctx he hdeclS
  obtain ⟨_hq1, hq2, hOrig⟩ := hid
  have hstraightC : (placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops).straighten = some ctx0 := by
    have hc := hctx
    rw [hq2, hpart] at hc
    exact hc
  unfold placeComponentExact at hstraightC
  dsimp only at hstraightC
  obtain rfl := Option.some.inj hstraightC
  have hmemE : eS ∈ run.proper.edges := List.mem_of_getElem? he
  obtain ⟨e', he', helig, _, _⟩ := straightSpanOf_invX hspan
  have heq : e' = eS := Option.some.inj (he'.symm.trans he)
  rw [heq] at helig
  have helig0 : straightEdgeEligible _ _ j eS = true := helig
  unfold straightEdgeEligible at helig0
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at helig0
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hTail⟩, hHead⟩, _⟩, _⟩, _⟩ := helig0
  obtain ⟨tailNode, hvt0, htd, htl, htb⟩ := straightRealNode_existsX hTail
  obtain ⟨headNode, hvh0, hhd, hhl, hhb⟩ := straightRealNode_existsX hHead
  have hvt : run.proper.nodes[eS.tail]? = some tailNode := hvt0
  have hvh : run.proper.nodes[eS.head]? = some headNode := hvh0
  have htailLtCg : eS.tail < (componentCandidate execution.graph q.1.1 candidate).nodes.length :=
    installed_proper_belowX hrun hvt htd htb
  have hheadLtCg : eS.head < (componentCandidate execution.graph q.1.1 candidate).nodes.length :=
    installed_proper_belowX hrun hvh hhd hhb
  have hTailEx : ∃ n, (componentCandidate execution.graph q.1.1 candidate).nodes[eS.tail]? =
      some n :=
    ⟨_, List.getElem?_eq_getElem htailLtCg⟩
  have hHeadEx : ∃ n, (componentCandidate execution.graph q.1.1 candidate).nodes[eS.head]? =
      some n :=
    ⟨_, List.getElem?_eq_getElem hheadLtCg⟩
  exact execution.installed_edge_positions _hinst hselected hedge hdecl hrun hpart eS
    hmemE hOrig hTailEx hHeadEx

/-- The installed corridor's packed tail and head rectangles are exactly the
rectangles at this part's vertex keys: the installer's part is the selected
component, the installed edge is the whole chain, and the span is installed. -/
theorem SceneExecutionX.installed_part_edge_rects {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} {pts : List Point} (hinst : Installed execution.packedAcc key pts)
    {q : (List Nat × Part) × Rect} {packed : Pack.State} {c : Nat}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area }) :
    ∃ (tailKey headKey : Nat) (tailRect headRect : Rect) (span : StraightSpan),
      edge.tail < q.1.1.length ∧ edge.head < q.1.1.length ∧
      tailKey < inp.boxes.length ∧ headKey < inp.boxes.length ∧
      q.1.1[edge.tail]? = some tailKey ∧ q.1.1[edge.head]? = some headKey ∧
      execution.packedAcc.rects[tailKey]? = some tailRect ∧
      execution.packedAcc.rects[headKey]? = some headRect ∧
      0 ≤ tailRect.h ∧ 0 ≤ headRect.h ∧
      tailRect.x = span.tailRect.x ∧ tailRect.w = span.tailRect.w ∧
      headRect.x = span.headRect.x ∧ headRect.w = span.headRect.w ∧
      tailRect.x ≤ span.column ∧ span.column ≤ tailRect.x + tailRect.w ∧
      headRect.x ≤ span.column ∧ span.column ≤ headRect.x + headRect.w ∧
      span.top = tailRect.y + tailRect.h ∧ span.bottom = headRect.y ∧
      pts = span.points := by
  have hinstC := hinst
  obtain ⟨qI, ctx0I, oxI, oyI, iI, eI, spanI, hmemI, hctxI, hoffI, heI, hkeyI, hneI, _,
    hspanI, hptsI⟩ := hinst
  obtain ⟨hcompEq, hq2, hidx⟩ :=
    execution.installed_edge_installer hinstC hselected hedge hdecl hrun hpart
      qI ctx0I iI eI hmemI hctxI heI hkeyI
  have hstraightC : (placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops).straighten = some ctx0I := by
    have hc := hctxI
    rw [hq2, hpart] at hc
    exact hc
  have hproperI : ctx0I.proper = run.proper := by
    have h1 := placeComponentExact_straighten_proper execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
    rw [hstraightC] at h1
    simpa using h1
  have heI' : run.proper.edges[iI]? = some eI := by
    have h := heI
    rw [hproperI] at h
    exact h
  have hmemRun : eI ∈ run.proper.edges := List.mem_of_getElem? heI'
  obtain ⟨eI', heI', heligI, _, _⟩ := straightSpanOf_invX hspanI
  have heIw : ctx0I.proper.edges[iI]? = some eI' := heI'
  have heqI : eI' = eI := Option.some.inj (heIw.symm.trans heI)
  rw [heqI] at heligI
  unfold straightEdgeEligible at heligI
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at heligI
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hTail⟩, hHead⟩, _⟩, _⟩, _⟩ := heligI
  obtain ⟨tailNode, hvt, htd, htl, htb⟩ := straightRealNode_existsX hTail
  obtain ⟨headNode, hvh, hhd, hhl, hhb⟩ := straightRealNode_existsX hHead
  rw [hproperI] at hvt hvh
  obtain ⟨nT, hTailCg, _⟩ := installed_proper_cg_nodeX hrun hvt htd htb
  obtain ⟨nH, hHeadCg, _⟩ := installed_proper_cg_nodeX hrun hvh hhd hhb
  have hpos := execution.installed_edge_positions hinstC hselected hedge hdecl hrun hpart
    eI hmemRun hidx ⟨_, hTailCg⟩ ⟨_, hHeadCg⟩
  obtain ⟨ranks, normalized, hn, _, _⟩ := srNormSrcX hrun
  have hwf := (normalize_node_rank_alignment hn).2
  have hb := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hedge)
  have hlen : (componentCandidate execution.graph q.1.1 candidate).nodes.length =
      q.1.1.length :=
    installed_comp_nodes_lengthX _ _ _
  have hALt : edge.tail < q.1.1.length := by
    rw [← hlen]
    exact hb.1
  have hBLt : edge.head < q.1.1.length := by
    rw [← hlen]
    exact hb.2.1
  obtain ⟨tailKeyT, headKeyT, tailRectT, headRectT, hbtT, hbhT, htkT, hhkT, hlookT,
    hlookH, hthT, hhhT, htxT, htwT, hhxT, hhwT, htopT, hbotT⟩ :=
    installed_span_rect_transport_tiedX execution hmemI hctxI hoffI heI hspanI
  have hcol := straightSpanOf_column_memX hspanI
  have hcolT1 : tailRectT.x ≤ spanI.column := by
    rw [htxT]
    exact hcol.1
  have hcolT2 : spanI.column ≤ tailRectT.x + tailRectT.w := by
    rw [htxT, htwT]
    exact hcol.2.1
  have hcolH1 : headRectT.x ≤ spanI.column := by
    rw [hhxT]
    exact hcol.2.2.1
  have hcolH2 : spanI.column ≤ headRectT.x + headRectT.w := by
    rw [hhxT, hhwT]
    exact hcol.2.2.2
  have htkA : q.1.1[edge.tail]? = some tailKeyT := by
    have h1 := htkT
    rw [hcompEq, hpos.1] at h1
    exact h1
  have hhkA : q.1.1[edge.head]? = some headKeyT := by
    have h1 := hhkT
    rw [hcompEq, hpos.2] at h1
    exact h1
  have hpartsEq := packAcc_parts_eqX execution.packed_eq
  have hmemC : qI ∈ execution.componentsAcc.parts := by
    rwa [hpartsEq] at hmemI
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hparts, _⟩ := actual_components_parts_geometryX hempty execution.components_eq
  have hcompI : qI.1 ∈ components execution.graph := by
    have h1 : qI.1 ∈ execution.componentsAcc.parts.map (·.1) :=
      List.mem_map_of_mem hmemC
    rwa [hparts] at h1
  have hcompQ : q.1.1 ∈ components execution.graph := by
    rw [← hcompEq]
    exact hcompI
  have htkQ : q.1.1[eI.tail]? = some tailKeyT := by
    rw [← hcompEq]
    exact htkT
  have hhkQ : q.1.1[eI.head]? = some headKeyT := by
    rw [← hcompEq]
    exact hhkT
  have hsmallT : tailKeyT < inp.boxes.length :=
    installed_key_lt_boxesX execution hrun hvt htd htb hcompQ htkQ
  have hsmallH : headKeyT < inp.boxes.length :=
    installed_key_lt_boxesX execution hrun hvh hhd hhb hcompQ hhkQ
  exact ⟨tailKeyT, headKeyT, tailRectT, headRectT, spanI,
    hALt, hBLt, hsmallT, hsmallH, htkA, hhkA, hlookT, hlookH,
    hthT, hhhT, htxT, htwT, hhxT, hhwT, hcolT1, hcolT2, hcolH1, hcolH2,
    htopT, hbotT, hptsI⟩

/-- The route box ids for the keys of `installed_part_edge_rects`. -/
theorem SceneExecutionX.installed_part_edge_key_ids {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} {pts : List Point} (hinst : Installed execution.packedAcc key pts)
    {q : (List Nat × Part) × Rect} {packed : Pack.State} {c : Nat}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hdecl : edge.decl = key)
    {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    {route : ModelRoute}
    (hroute : inp.routes[key]? = some route)
    {tailKey headKey : Nat}
    (hT : tailKey < inp.boxes.length) (hH : headKey < inp.boxes.length) :
    q.1.1[edge.tail]? = some tailKey → q.1.1[edge.head]? = some headKey →
    (inp.boxes[tailKey]'hT).id = route.fromId ∧ (inp.boxes[headKey]'hH).id = route.toId := by
  have hinstC := hinst
  have hrev : edge.reversed = false :=
    execution.installed_edge_not_reversed hinstC hselected hedge hdecl hrun hpart
  obtain ⟨_ranks, _normalized, hn, _, _⟩ := srNormSrcX hrun
  have hwf := (normalize_node_rank_alignment hn).2
  have hb := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hedge)
  have hlen : (componentCandidate execution.graph q.1.1 candidate).nodes.length =
      q.1.1.length :=
    installed_comp_nodes_lengthX _ _ _
  have hALt : edge.tail < q.1.1.length := by
    rw [← hlen]
    exact hb.1
  have hBLt : edge.head < q.1.1.length := by
    rw [← hlen]
    exact hb.2.1
  have hlines : execution.lines.length = inp.boxes.length :=
    installed_lines_lenX execution
  obtain ⟨raw, source, target, _hrawOf, hcompTailM, hcompHeadM, _htkM, _hhkM,
      hsource, hsourceId, htarget, htargetId⟩ :=
    installed_route_model_keysX execution.graph0_eq execution.graph_eq
      (List.mem_of_getElem? hedge) hdecl hroute hrev hALt hBLt
  intro htk hhk
  have hmemTail : (Compound.aliasEdge (slPreparedX inp) raw).tail ∈ q.1.1 := by
    apply slIdxMemOfLtX
    rw [hcompTailM]
    exact hALt
  have hmemHead : (Compound.aliasEdge (slPreparedX inp) raw).head ∈ q.1.1 := by
    apply slIdxMemOfLtX
    rw [hcompHeadM]
    exact hBLt
  have htkA : q.1.1[q.1.1.idxOf (Compound.aliasEdge (slPreparedX inp) raw).tail]? =
      some tailKey := by
    rw [hcompTailM]
    exact htk
  have hhkA : q.1.1[q.1.1.idxOf (Compound.aliasEdge (slPreparedX inp) raw).head]? =
      some headKey := by
    rw [hcompHeadM]
    exact hhk
  have hlookupTail : q.1.1[q.1.1.idxOf
      (Compound.aliasEdge (slPreparedX inp) raw).tail]? =
      some (Compound.aliasEdge (slPreparedX inp) raw).tail :=
    slIdxLookupX hmemTail
  have hlookupHead : q.1.1[q.1.1.idxOf
      (Compound.aliasEdge (slPreparedX inp) raw).head]? =
      some (Compound.aliasEdge (slPreparedX inp) raw).head :=
    slIdxLookupX hmemHead
  have htailAlias : (Compound.aliasEdge (slPreparedX inp) raw).tail = tailKey := by
    have h := hlookupTail.symm.trans htkA
    exact Option.some.inj h
  have hheadAlias : (Compound.aliasEdge (slPreparedX inp) raw).head = headKey := by
    have h := hlookupHead.symm.trans hhkA
    exact Option.some.inj h
  have hTmap : (Compound.aliasEdge (slPreparedX inp) raw).tail =
      Compound.endpoint (slPreparedX inp) true raw.tail raw.head := rfl
  have hHmap : (Compound.aliasEdge (slPreparedX inp) raw).head =
      Compound.endpoint (slPreparedX inp) false raw.head raw.tail := rfl
  have hPlen : (slPreparedX inp).length = inp.boxes.length := by
    unfold slPreparedX
    simp
  have heqT : tailKey = Compound.endpoint (slPreparedX inp) true raw.tail raw.head := by
    rw [← htailAlias, hTmap]
  have heqH : headKey = Compound.endpoint (slPreparedX inp) false raw.head raw.tail := by
    rw [← hheadAlias, hHmap]
  have hsmallT : tailKey < (slPreparedX inp).length := by
    rw [hPlen]
    exact hT
  have hsmallH : headKey < (slPreparedX inp).length := by
    rw [hPlen]
    exact hH
  have htailEq : tailKey = raw.tail := endpoint_flat_of_boundX heqT hsmallT
  have hheadEq : headKey = raw.head := endpoint_flat_of_boundX heqH hsmallH
  have hsrcGet : inp.boxes[tailKey]? = some source := by
    rw [htailEq]
    exact hsource
  have htgtGet : inp.boxes[headKey]? = some target := by
    rw [hheadEq]
    exact htarget
  have hsrcEq : source = inp.boxes[tailKey]'hT :=
    Option.some.inj (hsrcGet.symm.trans (List.getElem?_eq_getElem hT))
  have htgtEq : target = inp.boxes[headKey]'hH :=
    Option.some.inj (htgtGet.symm.trans (List.getElem?_eq_getElem hH))
  have hfrom : (inp.boxes[tailKey]'hT).id = route.fromId := by
    rw [← hsrcEq]
    exact hsourceId
  have hto : (inp.boxes[headKey]'hH).id = route.toId := by
    rw [← htgtEq]
    exact htargetId
  exact ⟨hfrom, hto⟩

/-- A straightened corridor is never installed at a declaration whose component edge is a
self-loop: the installed proper edge has distinct ends, while every candidate's edge with
that declaration reduces to the same self-loop base edge through `Edge.original`. -/
theorem SceneExecutionX.straight_corridor_not_selfloop {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {packed : Pack.State} {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hself : edge.tail = edge.head)
    {pts : List Point} :
    ¬ Installed execution.packedAcc edge.decl pts := by
  intro hinst
  have hinstC := hinst
  obtain ⟨qS, ctx0, _ox, _oy, j, e, _span, hmem, hctx, _hoff, he0, hdeclS, hne,
    _routing, hspan, _hpts⟩ := hinst
  have hpackEq : execution.packedAcc.parts = execution.componentsAcc.parts :=
    packAcc_parts_eqX execution.packed_eq
  have hmemS : qS ∈ execution.componentsAcc.parts := by
    rw [← hpackEq]
    exact hmem
  have hmemQ : q.1 ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? (zip_getElem?_left hselected)
  obtain ⟨hpartsEq, hgeom⟩ :=
    actual_components_parts_geometryX (by rfl) execution.components_eq
  have hcompS : qS.1 ∈ components execution.graph := by
    rw [← hpartsEq]
    exact List.mem_map_of_mem hmemS
  have hcompQ : q.1.1 ∈ components execution.graph := by
    rw [← hpartsEq]
    exact List.mem_map_of_mem hmemQ
  obtain ⟨indexS, _chosenS, runS, loopsS, areaS, _, _, _, hrunS, _, hpartS⟩ :=
    hgeom qS hmemS
  have hstraightC : (placeComponentExact execution.params
      (componentCandidate execution.graph qS.1 indexS) runS 0 execution.measured
      loopsS).straighten = some ctx0 := by
    have hc := hctx
    rw [hpartS] at hc
    exact hc
  have h1 := placeComponentExact_straighten_proper execution.params
    (componentCandidate execution.graph qS.1 indexS) runS 0 execution.measured loopsS
  rw [hstraightC] at h1
  simp only [Option.map_some] at h1
  have hproperEq : ctx0.proper = runS.proper := Option.some.inj h1
  have heRun : e ∈ runS.proper.edges := by
    rw [← hproperEq]
    exact List.mem_of_getElem? he0
  obtain ⟨geS, hgeS, hdeclgeS⟩ := componentRunX_declInvX hrunS e heRun
  have hownsQ : ownsDecl execution.graph q.1.1 edge.decl :=
    componentCandidate_edge_owns (List.mem_of_getElem? hedge)
  have hownsS : ownsDecl execution.graph qS.1 edge.decl := by
    have h0 := componentCandidate_edge_owns (List.mem_of_getElem? hgeS)
    have hgeDecl : geS.decl = edge.decl := hdeclgeS.symm.trans hdeclS
    rw [hgeDecl] at h0
    exact h0
  have hcompEq : qS.1 = q.1.1 :=
    ownsDecl_unique (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
      hcompS hcompQ hownsS hownsQ
  have hpartsNodup : (execution.componentsAcc.parts.map (·.1)).Nodup := by
    rw [hpartsEq]
    exact components_entries_nodup _
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hmemS
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.mp hmemQ
  have ha' : a < (execution.componentsAcc.parts.map (·.1)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp ha).1
  have hb' : b < (execution.componentsAcc.parts.map (·.1)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hb).1
  have hma : (execution.componentsAcc.parts.map (·.1))[a]? = some qS.1 := by
    rw [List.getElem?_map, ha]
    simp
  have hmb : (execution.componentsAcc.parts.map (·.1))[b]? = some q.1.1 := by
    rw [List.getElem?_map, hb]
    simp
  have hab : a = b :=
    hpartsNodup.eq_of_getElem?_eq ha' (by rw [hma, hmb, hcompEq])
  have hpair : qS = q.1 := by
    rw [hab] at ha
    exact Option.some.inj (ha.symm.trans hb)
  have hq2 : qS.2 = q.1.2 := congrArg Prod.snd hpair
  have hrunS' : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 indexS) execution.measured
      (candidateOrder indexS) = .ok runS := by
    rw [← hcompEq]
    exact hrunS
  have hpart' : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 indexS) runS 0 execution.measured
      loopsS with area := areaS } := by
    rw [← hq2, ← hcompEq]
    exact hpartS
  have hedge' : (componentCandidate execution.graph q.1.1 indexS).edges[e.original]? =
      some geS := by
    rw [← hcompEq]
    exact hgeS
  have hdecl' : geS.decl = edge.decl := hdeclgeS.symm.trans hdeclS
  have hendpts := execution.installed_edge_endpoints hinstC hselected hedge' hdecl' hrunS'
    hpart' qS ctx0 j e hmem hctx he0 hdeclS hspan
  have hgeNS : geS.tail ≠ geS.head :=
    fun hcon => hne (hendpts.1.trans (hcon.trans hendpts.2.symm))
  have hsemE := componentCandidate_semantic_edges execution.graph q.1.1 candidate
  have hsemS := componentCandidate_semantic_edges execution.graph q.1.1 indexS
  have hmemE : edge.original ∈
      (componentGraph execution.graph q.1.1).edges.map Edge.original := by
    rw [← hsemE]
    exact List.mem_map_of_mem (List.mem_of_getElem? hedge)
  have hmemG : geS.original ∈
      (componentGraph execution.graph q.1.1).edges.map Edge.original := by
    rw [← hsemS]
    exact List.mem_map_of_mem (List.mem_of_getElem? hedge')
  have hndBase : ((componentGraph execution.graph q.1.1).edges.map (·.decl)).Nodup :=
    componentGraph_decls_nodup _ _
      (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
  have hndOrig : (((componentGraph execution.graph q.1.1).edges.map Edge.original).map
      (·.decl)).Nodup := by
    have h : (((componentGraph execution.graph q.1.1).edges.map Edge.original).map
        (·.decl)) =
        ((componentGraph execution.graph q.1.1).edges.map (·.decl)) := by
      simp only [List.map_map, Function.comp_def, Edge.original_decl]
    rw [h]
    exact hndBase
  have heqOrig : edge.original = geS.original :=
    nodup_map_eq_of_mem hndOrig hmemE hmemG
      ((Edge.original_decl edge).trans
        (hdecl'.symm.trans (Edge.original_decl geS).symm))
  have hgeOrigNS : geS.original.tail ≠ geS.original.head := by
    cases hr : geS.reversed
    · have h : geS.original = { geS with reversed := false } := by
        simp [Edge.original, hr]
      rw [h]
      exact hgeNS
    · have h : geS.original =
          { geS with tail := geS.head, head := geS.tail, reversed := false } := by
        simp [Edge.original, hr]
      rw [h]
      exact Ne.symm hgeNS
  have heOrigNS : edge.original.tail ≠ edge.original.head := by
    rw [heqOrig]
    exact hgeOrigNS
  have heNS : edge.tail ≠ edge.head := by
    cases hr : edge.reversed
    · have h : edge.original = { edge with reversed := false } := by
        simp [Edge.original, hr]
      rw [h] at heOrigNS
      exact heOrigNS
    · have h : edge.original =
          { edge with tail := edge.head, head := edge.tail, reversed := false } := by
        simp [Edge.original, hr]
      rw [h] at heOrigNS
      exact Ne.symm heOrigNS
  exact heNS hself

end PipelineImpl

end Layered
end Elegant

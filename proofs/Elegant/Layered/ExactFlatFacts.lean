import Elegant.Layered.Pipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.SceneBounds
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.OrthogonalityFacts
import Elegant.Layered.InsetFit
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.MemberInFrame

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
  checked : checkedParams o.profile inp.kind = .ok params
  metric_eq : metricOf o.profile o.fontFamily = .ok metric
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
  scene_eq : res.scene = sceneOf params inp o lines packedAcc measured

/-- Recover the exact phases `layoutX` used: measured graph, exact graph,
selected-component fold, and packed accumulator. -/
theorem layoutX_success_phases {exactIds : List String} {inp : Input} {o : Options}
    {result : FamilyResult} (h : layoutX exactIds inp o = .ok result) :
    ∃ P metric lines measured graph0 graph mid packed,
      checkedParams o.profile inp.kind = .ok P ∧
      metricOf o.profile o.fontFamily = .ok metric ∧
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
      result.scene = sceneOf P inp o lines packed measured ∧
      result.budgetExhausted = packed.budget ∧
      result.itemArea = packed.parts.foldl (fun area part => area + part.2.area) 0 := by
  unfold layoutX at h
  obtain ⟨P, hP, h⟩ := bind_ok h
  obtain ⟨metric, hm, h⟩ := bind_ok h
  obtain ⟨lines, hl, h⟩ := bind_ok h
  obtain ⟨measured, hmeasured, h⟩ := bind_ok h
  obtain ⟨graph0, hg0, h⟩ := bind_ok h
  obtain ⟨graph, hg, h⟩ := bind_ok h
  obtain ⟨mid, hmid, h⟩ := bind_ok h
  obtain ⟨packed, hpacked, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · have he := Except.ok.inj h
    subst result
    exact ⟨P, metric, lines, measured, graph0, graph, mid, packed,
      hP, hm, hl, hmeasured, hg0, hg, hmid, hpacked, rfl, rfl, rfl⟩

/-- Extract the exact measured graph, selected-component fold, and packed
accumulator that `layoutX` used. -/
theorem layoutX_sceneExecution {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res) :
    Nonempty (SceneExecutionX exactIds inp o res) := by
  obtain ⟨P, metric, lines, measured, graph0, graph, componentsAcc, packedAcc,
    hP, hm, hl, hmeasured, hg0, hg, hc, hp, hs, _, _⟩ := layoutX_success_phases h
  exact ⟨⟨P, metric, lines, measured, graph0, graph, componentsAcc, packedAcc,
    hP, hm, hl, hmeasured, hg0, hg, hc, hp, hs⟩⟩

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
  rw [execution.scene_eq]
  intro route hroute
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hroute
  exact (Layered.isOrthogonal_shift_orient _ _ _ _ _).mpr (hpacked q.2)

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
  have hacc := SceneExecutionX.packedAcc_bounded execution ((hX hwf hframed execution).1)
  have hm1 := checkedParams_canvasMargin_ge_one execution.checked
  refine ⟨execution.params, execution.checked, by omega, ?_⟩
  rw [execution.scene_eq]
  exact sceneOf_boxes_inset execution.params inp o execution.lines
    execution.packedAcc execution.measured hacc (by omega)

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
  congrArg (fun s : Scene => s.boxes) execution.scene_eq

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


end PipelineImpl

end Layered
end Elegant

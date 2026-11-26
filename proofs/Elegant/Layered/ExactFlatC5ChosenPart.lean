import Elegant.Layered.ExactFlatC5
import Elegant.Layered.ExactStraightenFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact flat C5 chosen-part row (`X_ChosenPart`).

Proves `x_chosenPart_holds`: the per-edge scene-emission assembly for one
selected exact component over `componentRunX` / `placeComponentExact`,
replaying `SceneExecution.chosen_part_group_c5_alias` from
`FlatGroupEndpointsProof.lean`.

Proved here (`X_` copies over the exact run, all well-formedness-free):
route declaration coverage and uniqueness for `placeComponentExact`, the
part route-entry projection, the frame entry, the exact fold route-array
size, the route-key noninterference chain, and the packed route projection.

Three uniform single-stage residuals stay open as hypotheses of the main
theorem (each strictly narrower than the target, about one named exact
stage; the precise blocker is noted at each definition):
`X_RunAttach` (run-level chain identification plus port attachment over
`componentRunX`), `X_DumpLookup` (part-level dump-box identification over
`placeComponentExact`), and `X_BottomMarkerDump` (bottom-marker dump box
plus frame boundary over the exact run). -/

/-- Exact part route-entry projection (counterpart of
`placeComponent_route_entry_of_producer` for `placeComponentExact`; the
routes construction is identical, only the bounds use the exact extents). -/
theorem X_placeComponentExact_route_entry_of_producer {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (cursor : Int) (loops : List (Nat × LoopPlacement)) (i : Nat)
    (hi : i < cg.edges.length)
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl) :
    (placeComponentExact P cg run cursor labels loops).routes[i]? =
      some ((cg.edges[i]).decl,
        (run.routes[i]'(by
          rw [componentRunX_routes_length hrun, componentRunX_proper_chains_length hrun]
          exact hi)).points.map
          (shiftPoint (cursor - (placeBoundsX P cg run labels loops).minX)
            (-(placeBoundsX P cg run labels loops).minY))) := by
  have hfind := loops_find?_none_of_ne hloop
  unfold placeComponentExact placeBoundsX
  dsimp only
  simp only [List.getElem?_map, zipIdx_getElem?, List.getElem?_eq_getElem hi,
    Option.map_some, hfind, Option.map_none, Option.getD_none, Nat.zero_add,
    componentRunX_edgePoints_of_index hrun hi]
/-- Exact frame entry (copy of `chosen_part_frame_entry` over
`placeComponentExact`, with the exact placement bounds). -/
private theorem X_chosen_part_frame_entry
    {P : Params} {graph : Graph} {component : List Nat} {candidate : Nat}
    {run : Run} {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)}
    {part : Part} {area : Int}
    (hpart : part = { placeComponentExact P (componentCandidate graph component candidate)
      run 0 labels loops with area := area })
    {localIndex key : Nat} (hkey : component[localIndex]? = some key) :
    (component.zip part.rects)[localIndex]? =
      some (key, shiftRect
        (0 - (placeBoundsX P (componentCandidate graph component candidate) run labels loops).minX)
        (-(placeBoundsX P (componentCandidate graph component candidate) run labels loops).minY)
        (frameRect P (componentCandidate graph component candidate) run localIndex)) := by
  have hlocal : localIndex < (componentCandidate graph component candidate).nodes.length := by
    have hk := (List.getElem?_eq_some_iff.mp hkey).1
    rw [componentCandidate_nodes]
    simpa only [componentGraph, List.length_map] using hk
  have hrect : (placeComponentExact P (componentCandidate graph component candidate)
      run 0 labels loops).rects[localIndex]? =
      some (shiftRect
        (0 - (placeBoundsX P (componentCandidate graph component candidate) run labels loops).minX)
        (-(placeBoundsX P (componentCandidate graph component candidate) run labels loops).minY)
        (frameRect P (componentCandidate graph component candidate) run localIndex)) := by
    unfold placeComponentExact placeBoundsX
    simp only [List.getElem?_map, List.getElem?_range hlocal, Option.map_some]
  apply List.getElem?_zip_eq_some.mpr
  refine ⟨hkey, ?_⟩
  rw [hpart]
  exact hrect

/-- Exact execution keeps the route array length. -/
private theorem SceneExecutionX.components_routes_sizeX {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    execution.componentsAcc.routes.size = inp.routes.length := by
  have h := ExactStraighten.components_fold_routes_size execution.params exactIds inp o execution.graph
    execution.measured (components execution.graph) _ _ execution.components_eq
  simpa only [Array.size_replicate] using h

/-- Exact scene route-entry projection (counterpart of
`sceneOf_route_entry_of_producer` for the exact run; `hrun` is used only for
the route-array length ascriptions). -/
theorem X_sceneOf_route_entry_of_producer {P : Params} {exact : List Nat} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {loops : List (Nat × LoopPlacement)}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (i : Nat) (hi : i < cg.edges.length)
    (_hloop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl)
    (out : Acc) (measured : List MeasuredLabel)
    (b : Bounds) (_hb : b = placeBoundsX P cg run labels loops)
    (box : Rect)
    (hroutes : out.routes.getD (cg.edges[i]).decl [] =
      ((run.routes[i]'(by
        rw [componentRunX_routes_length hrun, componentRunX_proper_chains_length hrun]
        exact hi)).points.map
        (shiftPoint (0 - b.minX) (-b.minY))).map (shiftPoint box.x box.y))
    (hk : (cg.edges[i]).decl < inp.routes.length) :
    let margin := P.canvasMargin
    (sceneOf P inp o lines out measured).routes[(cg.edges[i]).decl]? =
      some ⟨(inp.routes[(cg.edges[i]).decl]).id,
        (inp.routes[(cg.edges[i]).decl]).fromId,
        (inp.routes[(cg.edges[i]).decl]).toId,
        (inp.routes[(cg.edges[i]).decl]).orthogonal,
        (run.routes[i]'(by
          rw [componentRunX_routes_length hrun, componentRunX_proper_chains_length hrun]
          exact hi)).points.map
          (routePointTransport margin o.direction out.canvasH box.x box.y b.minX b.minY)⟩ := by
  have hscene := sceneOf_routes_getElem? P inp o lines out measured (cg.edges[i]).decl hk
  rw [hscene]
  dsimp only
  have hneg : -b.minY = 0 - b.minY := by omega
  rw [hroutes, hneg]
  rw [routePointTransport_eq]

/-- Transport a component route and its endpoint's frame through the same placement,
    orientation and canvas offset. This also applies when the route and box are
    identified at their final scene emission equations. -/
theorem parent_port_miss_transport {points : List Point} {r : Rect}
    (hmiss : ¬ Polyline.hitsRect points r)
    (margin : Int) (d : Direction) (canvasH boxX boxY minX minY : Int) :
    ¬ Polyline.hitsRect (points.map (routePointTransport margin d canvasH boxX boxY minX minY))
      (shiftRect margin margin (orientRect d canvasH (shiftRect (boxX - minX) (boxY - minY) r))) := by
  have hmap : points.map (routePointTransport margin d canvasH boxX boxY minX minY) =
      points.map (fun x => shiftPoint margin margin
        (orientPoint d canvasH (shiftPoint (boxX - minX) (boxY - minY) x))) := by
    apply List.map_congr_left
    intro x _
    rfl
  rw [hmap]
  simpa only [List.map_map, Function.comp_def] using
    not_hitsRect_shift_orient d canvasH margin margin _ _
      (not_hitsRect_shift (boxX - minX) (boxY - minY) _ _ hmiss)
theorem X_chosen_part_route_from_points
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {i k : Nat} {points : List Point} {minX minY : Int}
    (hget : q.1.2.routes[i]? = some (k,
      points.map (shiftPoint (0 - minX) (-minY))))
    (hnodup : (q.1.2.routes.map (·.1)).Nodup)
    {route : ModelRoute} (hroute : inp.routes[k]? = some route) :
    (res.scene.routes[k]? = some (Route.mk route.id route.fromId route.toId route.orthogonal
      (points.map (routePointTransport execution.params.canvasMargin o.direction
        execution.packedAcc.canvasH q.2.x q.2.y minX minY))) ∨
     ∃ pts : List Point, IsCorridor pts ∧
       res.scene.routes[k]? = some (Route.mk route.id route.fromId route.toId route.orthogonal
         (pts.map fun p => shiftPoint execution.params.canvasMargin execution.params.canvasMargin
           (orientPoint o.direction execution.packedAcc.canvasH p)))) := by
  have hk := (List.getElem?_eq_some_iff.mp hroute).1
  have hrouteEq : route = inp.routes[k]'hk := Option.some.inj (hroute.symm.trans (List.getElem?_eq_getElem hk))
  have hsize := execution.components_routes_sizeX
  have hrouteSize : k < execution.componentsAcc.routes.size := by rw [hsize]; exact hk
  have hp := ExactStraighten.actual_components_packAcc_routes_getD
    (by rfl) execution.components_eq (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
    packed execution.packed_eq hpacked c q hselected i _ _ [] hget hnodup hrouteSize
  have hstraight := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.straightAcc execution.measured k hk
  rw [← execution.scene_eq] at hstraight
  rw [ExactStraighten.straight_canvasH execution] at hstraight
  have hpsize : execution.packedAcc.routes.size = inp.routes.length := by
    rw [packAcc_routes_size execution.packed_eq, hsize]
  have hsizeEq : execution.straightAcc.routes.size = execution.packedAcc.routes.size :=
    ExactStraighten.straightenAcc_routes_size execution.straight_eq
  have hssize : k < execution.straightAcc.routes.size := by
    rw [hsizeEq, hpsize]; exact hk
  have hgetS : execution.straightAcc.routes[k]? =
      some (execution.straightAcc.routes.getD k []) := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hssize, Option.getD_some]
  rcases straightenAcc_route_cases execution.straight_eq k _ hgetS with hpackedPts | hcor
  · have hbridge : execution.packedAcc.routes.getD k [] =
        execution.straightAcc.routes.getD k [] := by
      simp only [Array.getD_eq_getD_getElem?, hpackedPts, Option.getD_some]
    have hneg : -minY = 0 - minY := by omega
    have hp' : execution.straightAcc.routes.getD k [] =
        (points.map (shiftPoint (0 - minX) (-minY))).map (shiftPoint q.2.x q.2.y) := by
      rw [← hbridge]
      simpa only [Array.getD_eq_getD_getElem?] using hp
    rw [hp', hneg, routePointTransport_eq, ← hrouteEq] at hstraight
    exact Or.inl hstraight
  · have hstraightC : res.scene.routes[k]? = some (Route.mk route.id route.fromId route.toId
        route.orthogonal
        ((execution.straightAcc.routes.getD k []).map fun p => shiftPoint
          execution.params.canvasMargin execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH p))) := by
      rw [← hrouteEq] at hstraight
      exact hstraight
    exact Or.inr ⟨execution.straightAcc.routes.getD k [], hcor, hstraightC⟩

/-- Exact scene-emission chain for `placeComponentExact` (counterpart of
`SceneExecution.chosen_part_route_entry` over `SceneExecutionX`). The
declaration bound comes from `X_candidate_model_endpoint_source`; everything
else replays the plain argument with the exact fold, pack, and scene facts. -/
theorem X_chosen_part_route_entry
    {exactIds : List String} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hloop : ∀ l ∈ loops, l.1 ≠ edge.decl) :
    ∃ route : ModelRoute, ∃ native : EdgeRoute,
      inp.routes[edge.decl]? = some route ∧
      run.routes[i]? = some native ∧ native.original = i ∧
      let cg := componentCandidate execution.graph q.1.1 candidate
      let bounds := placeBoundsX execution.params cg run execution.measured loops
      (res.scene.routes[edge.decl]? =
        some (Route.mk route.id route.fromId route.toId route.orthogonal
          (native.points.map (routePointTransport execution.params.canvasMargin o.direction
            execution.packedAcc.canvasH q.2.x q.2.y bounds.minX bounds.minY))) ∨
       ∃ pts : List Point, IsCorridor pts ∧
         res.scene.routes[edge.decl]? =
           some (Route.mk route.id route.fromId route.toId route.orthogonal
             (pts.map fun p => shiftPoint execution.params.canvasMargin execution.params.canvasMargin
               (orientPoint o.direction execution.packedAcc.canvasH p)))) := by
  let cg := componentCandidate execution.graph q.1.1 candidate
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have he : cg.edges[i]'hi = edge := (List.getElem?_eq_some_iff.mp hedge).2
  have he' := (List.getElem?_eq_some_iff.mp hedge).2
  have hlo : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl := by
    simpa only [he] using hloop
  obtain ⟨index, route, _, _, _, hroute, _, hdeclIdx, _, _, _, _, _⟩ :=
    X_candidate_model_endpoint_source execution.graph0_eq execution.graph_eq
      (List.mem_of_getElem? hedge)
  have hroute' : inp.routes[edge.decl]? = some route := by
    rw [hdeclIdx]
    exact hroute
  obtain ⟨native, hnative, horiginal, _⟩ := componentRunX_route_of_index hrun hi
  have hnativeGet := (List.getElem?_eq_some_iff.mp hnative).2
  have hget := X_placeComponentExact_route_entry_of_producer hrun 0 loops i hi hlo
  have hpartRoutes : q.1.2.routes =
      (placeComponentExact execution.params cg run 0 execution.measured loops).routes := by
    rw [hpart]
  rw [← hpartRoutes] at hget
  have hpoints : q.1.2.routes[i]? = some (edge.decl,
      native.points.map (shiftPoint (0 - (placeBoundsX execution.params cg run
        execution.measured loops).minX) (-(placeBoundsX execution.params cg run
        execution.measured loops).minY))) := by
    simpa only [he', hnativeGet] using hget
  have hnd : (cg.edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup execution.graph q.1.1 candidate
      (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
  have hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
    rw [hpartRoutes]
    exact ExactStraighten.placeComponentExact_routes_decls_nodup execution.params cg run 0 execution.measured loops hnd
  have hscene := X_chosen_part_route_from_points execution packed hpacked hselected
    hpoints hpartNodup hroute'
  refine ⟨route, native, hroute', hnative, horiginal, ?_⟩
  rcases hscene with hscene | ⟨pts, hcor, hsceneC⟩
  · exact Or.inl hscene
  · exact Or.inr ⟨pts, hcor, hsceneC⟩
/-- Exact normalized source: replay of `componentRun_normalized_source`
through `componentRunX_spec` (`coordinateGraphX_chains` in place of
`coordinateGraph_chains`; the sizing/title steps are node-only updates, so
their `.edges` equations transfer definitionally). -/
theorem X_componentRun_normalized_source {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ ranks normalized,
      normalize cg ranks = .ok normalized ∧
      run.proper.edges = normalized.edges ∧
      run.proper.chains = normalized.chains := by
  obtain ⟨ranks, normalized, labeled, q0, hn, hlabels, hcoord, _, _, hprox, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨hlabelEdges, _, hlabelChains, _⟩ := Labels.addLabelNodes_metadata hlabels
  have hclean : ∀ e ∈ (titleReservations (sizeProperPortsX P exact labeled)).edges,
      e.synthetic = false := by
    intro e he
    have hedge : (titleReservations (sizeProperPortsX P exact labeled)).edges =
        normalized.edges := hlabelEdges
    rw [hedge] at he
    exact normalize_clean hn e he
  have hprojectedEdges := (proxyWidths_rel hprox).1
  have hdropEdges : (OrderImpl.dropSynthetic q0).edges =
      (OrderImpl.dropSynthetic
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
          P.clusterBorderW)).edges := by
    show q0.edges.filter (fun e => !e.synthetic) = _
    rw [hprojectedEdges, ← hcoord]
    rfl
  refine ⟨ranks, normalized, hn, ?_, ?_⟩
  · rw [← hdrop, hdropEdges,
      OrderImpl.dropSynthetic_addClusterBorders_edges _ _ hclean]
    exact hlabelEdges
  · rw [← hdrop, OrderImpl.dropSynthetic_chains, proxyWidths_chains hprox,
      ← hcoord, coordinateGraphX_chains P exact labeled, hlabelChains]

/-- Exact executed nodes are real: replay of `componentRun_source_isReal`
through `componentRunX_spec` (`sizeProperPortsX_key` in place of
`sizeProperPorts_key`). -/
private theorem X_componentRun_source_isReal {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : Node} (hnode : cg.nodes[v]? = some node) :
    RouteImpl.IsReal run.proper v := by
  obtain ⟨_, _, labeled, q0, hn, hl, hc, _, _, hp, hd, _, _, _⟩ :=
    componentRunX_spec hrun
  have hnormalized := normalize_node_record hn hnode
  have hlabeled := addLabelNodes_untouched_node hl hnormalized rfl
  have hsized : Metadata.NodeMetadata labeled (sizeProperPortsX P exact labeled) := by
    apply Metadata.nodeMetadata_of_lookup_maps
    intro index
    have hk := congrArg (Option.map (fun t : Bool × Int × List Nat => t.1))
      (sizeProperPortsX_key P exact labeled index)
    simpa only [Option.map_map, Function.comp_def] using hk
  have htitled : Metadata.NodeMetadata (sizeProperPortsX P exact labeled)
      (titleReservations (sizeProperPortsX P exact labeled)) :=
    Metadata.nodeMetadata_map_append titleF (fun nd => (titleF_keys nd).1) _
      (titleReservations_nodes _)
  have hbordered := Metadata.nodeMetadata_borderExtension
    (OrderImpl.addClusterBorders_metadata (titleReservations (sizeProperPortsX P exact labeled))
      P.clusterBorderW)
  have hcleared : Metadata.NodeMetadata
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)
      (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW)) :=
    Metadata.nodeMetadata_map clearF (fun nd => (clearF_keys nd).1)
      (clearProxyExtents_nodes _)
  obtain ⟨sized, hs, hsd⟩ := hsized v _ hlabeled
  obtain ⟨titled, ht, htd⟩ := htitled v _ hs
  obtain ⟨bordered, hb, hbd⟩ := hbordered v _ ht
  obtain ⟨cleared, hclear, hcd⟩ := hcleared v _ hb
  obtain ⟨coordinate, hcoordinate, hmd⟩ := materialize_exists _ hclear
  have hcoordinate' : run.coordinateProper.nodes[v]? = some coordinate := by
    rw [← hc]
    exact hcoordinate
  obtain ⟨out, hout, hod, _, _⟩ := (proxyWidths_rel hp).2.2.2.2.1 v _ hcoordinate'
  have hfinal : run.proper.nodes[v]? = some out := by
    rw [← hd]
    exact hout
  intro nd hnd
  have heq := Option.some.inj (hnd.symm.trans hfinal)
  subst nd
  exact hod.trans (hmd.trans (hcd.trans (hbd.trans (htd.trans hsd))))

/-- First-edge lookup along a real-headed chain (copy of the private
`real_tail_first` of `ExecutedPortsFacts.lean`). -/
private theorem X_real_tail_first {p : Proper} {v : Nat} (hv : RouteImpl.IsReal p v) :
    ∀ es : List Nat, RouteImpl.chainRel (RouteImpl.ChainLink p) es →
      ∀ e ∈ es, (RouteImpl.edgeAt p e).tail = v →
        ∃ first, es.head? = some first ∧ (RouteImpl.edgeAt p first).tail = v
  | [], _, _, hm, _ => by simp at hm
  | [a], _, e, hm, ht => by
    have he : e = a := by simpa only [List.mem_singleton] using hm
    subst e
    exact ⟨a, rfl, ht⟩
  | a :: b :: rest, hc, e, hm, ht => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, rfl, ht⟩
    · obtain ⟨first, hfirst, htail⟩ := X_real_tail_first hv (b :: rest) hc.2 e hm ht
      have hbf : b = first := Option.some.inj hfirst
      have hb : (RouteImpl.edgeAt p b).tail = v := by simpa only [hbf] using htail
      obtain ⟨_, _, _, nd, hnd, hdummy⟩ := hc.1
      have hreal := hv nd (by rw [← hb]; exact hnd)
      rw [hreal] at hdummy
      contradiction

/-- Last-edge lookup along a real-headed chain (copy of the private
`real_head_last` of `ExecutedPortsFacts.lean`). -/
private theorem X_real_head_last {p : Proper} {v : Nat} (hv : RouteImpl.IsReal p v) :
    ∀ es : List Nat, RouteImpl.chainRel (RouteImpl.ChainLink p) es →
      ∀ e ∈ es, (RouteImpl.edgeAt p e).head = v →
        ∃ last, es.getLast? = some last ∧ (RouteImpl.edgeAt p last).head = v
  | [], _, _, hm, _ => by simp at hm
  | [a], _, e, hm, ht => by
    have he : e = a := by simpa only [List.mem_singleton] using hm
    subst e
    exact ⟨a, rfl, ht⟩
  | a :: b :: rest, hc, e, hm, ht => by
    rcases List.mem_cons.mp hm with rfl | hm
    · obtain ⟨_, _, hlink, nd, hnd, hdummy⟩ := hc.1
      have hb : (RouteImpl.edgeAt p b).tail = v := hlink.symm.trans ht
      have hreal := hv nd (by rw [← hb]; exact hnd)
      rw [hreal] at hdummy
      contradiction
    · obtain ⟨last, hlast, hhead⟩ := X_real_head_last hv (b :: rest) hc.2 e hm ht
      exact ⟨last, by simpa only [List.getLast?_cons_cons] using hlast, hhead⟩

/-- Edge-index lookup from a record (copy of the private `mem_edgesOf_of_record`
of `ExecutedPortsFacts.lean`). -/
private theorem X_mem_edgesOf_of_record {p : Proper} {i : Nat} {edge : ProperEdge}
    (hm : edge ∈ p.edges) (ho : edge.original = i) :
    ∃ k ∈ RouteImpl.edgesOf p i, RouteImpl.edgeAt p k = edge := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
  have hb := (List.getElem?_eq_some_iff.mp hk).1
  have hrecord : RouteImpl.edgeAt p k = edge := by
    simp only [RouteImpl.edgeAt, List.getD_eq_getElem?_getD, hk, Option.getD_some]
  refine ⟨k, ?_, hrecord⟩
  apply List.mem_filter.mpr
  exact ⟨List.mem_range.mpr hb, by simp only [hrecord, ho, beq_self_eq_true]⟩

/-- Exact-run semantic chains cover every component-graph edge (replay of
`componentRun_semantic_node_chain` via `X_componentRun_normalized_source`). -/
theorem X_componentRun_semantic_node_chain
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∃ chain : List Nat,
      run.proper.chains[i]? = some chain ∧ 2 ≤ chain.length ∧
      chain.head? = some edge.tail ∧ chain.getLast? = some edge.head ∧
      ∀ (j : Nat) (hj : j < chain.length) (hj1 : j + 1 < chain.length),
        ∃ properEdge ∈ run.proper.edges,
          properEdge.original = i ∧ properEdge.decl = edge.decl ∧
          properEdge.tail = chain[j] ∧ properEdge.head = chain[j + 1] := by
  obtain ⟨ranks, normalized, hn, he, hc⟩ := X_componentRun_normalized_source hrun
  have hchain := (normalize_ok hn).2.2 i (List.getElem?_eq_some_iff.mp hedge).1 edge hedge
  change NormalizeImpl.ChainFact cg.edges normalized (edge, i) normalized.chains[i]? at hchain
  obtain ⟨_, hchain⟩ := hchain
  rw [ite_eq_right hne] at hchain
  obtain ⟨chain, hget, hlen, hhead, hlast, hsegments⟩ := hchain
  refine ⟨chain, ?_, hlen, hhead, hlast, ?_⟩
  · rw [hc]
    exact hget
  · intro j hj hj1
    obtain ⟨properEdge, hm, ho, hd, ht, hh⟩ := hsegments j hj hj1
    refine ⟨properEdge, ?_, ho, hd, ht, hh⟩
    rw [he]
    exact hm

/-- Exact-run chains expose their endpoints (replay of
`componentRun_chain_endpoints` via the exact semantic chain, the exact
normalized source, and `componentRunX_properShape`). -/
theorem X_componentRun_chain_endpoints
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∃ first last,
      (RouteImpl.edgesOf run.proper i).head? = some first ∧
      (RouteImpl.edgesOf run.proper i).getLast? = some last ∧
      (RouteImpl.edgeAt run.proper first).tail = edge.tail ∧
      (RouteImpl.edgeAt run.proper last).head = edge.head := by
  obtain ⟨chain, hchain, hlen, hhead, hlast, hsegments⟩ :=
    X_componentRun_semantic_node_chain hrun hedge hne
  obtain ⟨ranks, normalized, hn, _, _⟩ := X_componentRun_normalized_source hrun
  have hwf := (normalize_node_rank_alignment hn).2
  have hbounds := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hedge)
  have htailReal : RouteImpl.IsReal run.proper edge.tail :=
    X_componentRun_source_isReal hrun
      (List.getElem?_eq_getElem hbounds.1)
  have hheadReal : RouteImpl.IsReal run.proper edge.head :=
    X_componentRun_source_isReal hrun
      (List.getElem?_eq_getElem hbounds.2.1)
  have hproper := (componentRunX_properShape hrun) i
  obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp hhead
  obtain ⟨firstEdge, hfirstMem, hfirstOriginal, _, hfirstTail, _⟩ :=
    hsegments 0 (by omega) (by omega)
  obtain ⟨firstIndex, hfirstIndex, hfirstRecord⟩ :=
    X_mem_edgesOf_of_record hfirstMem hfirstOriginal
  have hfirstValue : (RouteImpl.edgeAt run.proper firstIndex).tail = edge.tail := by
    rw [hfirstRecord]
    exact hfirstTail
  obtain ⟨first, hfirst, hfirstTail⟩ :=
    X_real_tail_first htailReal _ hproper firstIndex hfirstIndex hfirstValue
  obtain ⟨lastEdge, hlastMem, hlastOriginal, _, _, hlastHead⟩ :=
    hsegments ((edge.tail :: rest).length - 2) (by omega) (by omega)
  obtain ⟨lastIndex, hlastIndex, hlastRecord⟩ :=
    X_mem_edgesOf_of_record hlastMem hlastOriginal
  have hlastValue' : (RouteImpl.edgeAt run.proper lastIndex).head = edge.head := by
    rw [hlastRecord, hlastHead]
    have hk : (edge.tail :: rest).length - 2 + 1 =
        (edge.tail :: rest).length - 1 := by omega
    have hlastChain : (edge.tail :: rest)[(edge.tail :: rest).length - 1]'(by omega) =
        edge.head := by
      rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega)] at hlast
      exact Option.some.inj hlast
    simpa only [hk] using hlastChain
  obtain ⟨last, hlast, hlastHead⟩ :=
    X_real_head_last hheadReal _ hproper lastIndex hlastIndex hlastValue'
  exact ⟨first, last, hfirst, hlast, hfirstTail, hlastHead⟩

/-- The head-side route point of an exact run is the flat port on `ys`
(counterpart of the private `flat_head_port_on_ys` of
`FlatGroupEndpointsProof.lean`, replayed via `route_endpoints_on_ports` on
the exact run). -/
theorem X_flat_head_port_on_ys
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} (hi : i < cg.edges.length) {first last : Nat}
    (hfirst : (RouteImpl.edgesOf run.proper i).head? = some first)
    (hlast : (RouteImpl.edgesOf run.proper i).getLast? = some last)
    {rt : EdgeRoute} (hrt : run.routes[i]? = some rt) :
    ∃ qx : Int,
      (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper last).head).x ≤ qx ∧
      qx ≤ (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper last).head).x +
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper last).head).w ∧
      ((cg.edges.map (·.reversed)).getD i false = true →
        rt.points.head? = some ⟨qx,
          run.ys.getD (RouteImpl.edgeAt run.proper last).head 0⟩) ∧
      ((cg.edges.map (·.reversed)).getD i false = false →
        rt.points.getLast? = some ⟨qx,
          run.ys.getD (RouteImpl.edgeAt run.proper last).head 0⟩) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hr, _, hroutes⟩ :=
    componentRunX_spec hrun
  obtain ⟨rt', hrt', horiginal, _⟩ := componentRunX_route_of_index hrun hi
  have hrtEq : rt = rt' := Option.some.inj (hrt.symm.trans hrt')
  subst hrtEq
  have hm : rt ∈ run.routes := List.mem_iff_getElem?.mpr ⟨i, hrt⟩
  have hfirst' : (RouteImpl.edgesOf run.proper rt.original).head? = some first := by
    simpa only [horiginal] using hfirst
  have hlast' : (RouteImpl.edgesOf run.proper rt.original).getLast? = some last := by
    simpa only [horiginal] using hlast
  obtain ⟨px, qx, _, _, hpx0, hpx1, hqx0, hqx1, hend⟩ :=
    route_endpoints_on_ports hr hroutes rt hm first last hfirst' hlast'
  rw [horiginal] at hend
  split at hend
  · next hsplit =>
    refine ⟨qx, hqx0, hqx1, ?_, ?_⟩
    · intro _
      simpa only [RouteImpl.boxRect, RouteImpl.yAt] using hend.1
    · intro hcon
      rw [hcon] at hsplit
      exact absurd hsplit (by decide)
  · next hsplit =>
    refine ⟨qx, hqx0, hqx1, ?_, ?_⟩
    · intro hcon
      rw [hcon] at hsplit
      exact absurd hsplit (by decide)
    · intro _
      simpa only [RouteImpl.boxRect, RouteImpl.yAt] using hend.2
/-- Residual, exact run-level port attachment over `componentRunX`: the
transported frame/box boundaries for both route ends. This is the exact
counterpart of `GroupAttachMeasured` (`GroupRouteAttachment.lean`), stated
with the exact placement bounds (`placeBoundsX`): the same fact restricted
to graphs that arise as `componentCandidate` of the exact graph, since the
endpoint data it needs (the member routing bound over the cluster subtree)
is only provable there — the unrestricted per-graph form is refuted by the
same hand-built counterexample as the plain `GroupAttach`. It holds for
executed exact layouts: the attachment half replays
`componentRun_group_route_attachment_of_facts` via `route_endpoints_on_ports`
on the exact run plus the exact endpoint data derived from the rank
hypothesis (which the caller discharges with its `WellFormed` and
`framedParents` premises, as in `flatGroupEndpointsX`). -/
def X_RunAttach (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ (candidate : Nat) {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run →
    ∀ {i : Nat} (hi : i < (componentCandidate graph comp candidate).edges.length)
    {first last : Nat}
      (hfirst : (RouteImpl.edgesOf run.proper i).head? = some first)
      (hlast : (RouteImpl.edgesOf run.proper i).getLast? = some last)
      (cursor : Int) (loops : List (Nat × LoopPlacement))
      (hloop : ∀ l ∈ loops,
        l.1 ≠ ((componentCandidate graph comp candidate).edges[i]).decl)
      (margin : Int) (direction : Direction) (canvasH boxX boxY : Int),
      ∃ rt : EdgeRoute, ∃ start finish : Point,
        run.routes[i]? = some rt ∧ rt.original = i ∧
        (placeComponentExact P (componentCandidate graph comp candidate) run cursor labels
          loops).routes[i]? =
          some (((componentCandidate graph comp candidate).edges[i]).decl, rt.points.map
            (shiftPoint (cursor - (placeBoundsX P (componentCandidate graph comp candidate)
              run labels loops).minX)
              (-(placeBoundsX P (componentCandidate graph comp candidate)
                run labels loops).minY))) ∧
        rt.points.head? = some start ∧ rt.points.getLast? = some finish ∧
        Validator.onBoundary
          (routePointTransport margin direction canvasH boxX boxY
            (placeBoundsX P (componentCandidate graph comp candidate) run labels loops).minX
            (placeBoundsX P (componentCandidate graph comp candidate) run labels loops).minY
            start)
          (shiftRect margin margin
            (orientRect direction canvasH
              (shiftRect (boxX - (placeBoundsX P (componentCandidate graph comp candidate)
                run labels loops).minX)
                (boxY - (placeBoundsX P (componentCandidate graph comp candidate)
                  run labels loops).minY)
                (if ((componentCandidate graph comp candidate).edges.map
                    (·.reversed)).getD i false
                  then frameRect P (componentCandidate graph comp candidate) run
                    (RouteImpl.edgeAt run.proper last).head
                  else frameRect P (componentCandidate graph comp candidate) run
                    (RouteImpl.edgeAt run.proper first).tail)))) ∧
        Validator.onBoundary
          (routePointTransport margin direction canvasH boxX boxY
            (placeBoundsX P (componentCandidate graph comp candidate) run labels loops).minX
            (placeBoundsX P (componentCandidate graph comp candidate) run labels loops).minY
            finish)
          (shiftRect margin margin
            (orientRect direction canvasH
              (shiftRect (boxX - (placeBoundsX P (componentCandidate graph comp candidate)
                run labels loops).minX)
                (boxY - (placeBoundsX P (componentCandidate graph comp candidate)
                  run labels loops).minY)
                (if ((componentCandidate graph comp candidate).edges.map
                    (·.reversed)).getD i false
                  then frameRect P (componentCandidate graph comp candidate) run
                    (RouteImpl.edgeAt run.proper first).tail
                  else frameRect P (componentCandidate graph comp candidate) run
                    (RouteImpl.edgeAt run.proper last).head))))
/-- Residual, exact part-level dump-box identification over
`placeComponentExact` (uniform in the position): the layout-dump box for a
directly resolved input box. This is the exact counterpart of the dump-box
half of `aligned_dump_box` (`FlatGroupEndpointsProof.lean`). It holds for
executed exact layouts by replaying `part_entry_box_lookup_of_box_ids_nodupX`
(`X_chosen_part_frame_entry` plus `actual_components_packed_rect_valueX`);
the caller supplies box-id uniqueness from `WellFormed (inputModel inp o)`. -/
def X_DumpLookup (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    {pos key : Nat} (_hkey : q.1.1[pos]? = some key)
    {s : ModelBox} (_hsource : inp.boxes[key]? = some s),
    res.scene.layoutDump.box? s.id =
      some (Box.mk s.id s.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect (q.2.x - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run
                execution.measured loops).minX)
              (q.2.y - (placeBoundsX execution.params
                (componentCandidate execution.graph q.1.1 candidate) run
                execution.measured loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run pos))))
        s.parent s.exclusive)

/-- Residual, exact bottom-marker dump box plus frame boundary over the exact
run (uniform in the marker position): the group dump box for a `border = 2`
endpoint and the transported flat-port point on its frame. This is the exact
counterpart of `bottom_dump_box_boundary` (`FlatGroupEndpointsProof.lean`).
It holds for executed exact layouts by replaying that proof: anchor selection
on the measured graph, the `X_BottomBoundary` row, and the flat-port span
transported through the top-title entry; the caller supplies `WellFormed`,
`framedParents`, and box-id uniqueness. -/
def X_BottomMarkerDump (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (_hbottom : X_BottomBoundary exactIds)
    (_hanchor : GroupAnchorSelection)
    (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) labels orderOptions = .ok run)
    {loops : List (Nat × LoopPlacement)} {area : Int}
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 labels
      loops with area := area })
    {pos w : Nat} (_hpos : q.1.1[pos]? = some w)
    {n : Node} (_hn : execution.graph.nodes[w]? = some n) (_hb2 : n.border = 2)
    {s : ModelBox} (_hs : inp.boxes[n.decl]? = some s) (_hgrp : s.role = .group)
    (_hcomp : q.1.1 ∈ components execution.graph)
    {px : Int}
    (_hspan : (RouteImpl.boxRect run.proper run.xs run.ys pos).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys pos).x +
        (RouteImpl.boxRect run.proper run.xs run.ys pos).w),
    ∃ b : Box,
      res.scene.layoutDump.box? s.id = some b ∧
      Validator.onBoundary (routePointTransport execution.params.canvasMargin
        o.direction execution.packedAcc.canvasH q.2.x q.2.y
        (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
          run labels loops).minX
        (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
          run labels loops).minY
        ⟨px, run.ys.getD pos 0⟩) b.rect
/-- Exact scene-box lookup from box ids (private copy of
`SceneExecutionX.source_box_lookup_of_box_ids_nodupX`, kept local so this
module does not depend on the in-progress self-routes file). -/
private theorem Xc_source_box_lookup_of_box_ids_nodupX {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hboxIds : (inp.boxes.map (·.id)).Nodup)
    {index : Nat} {source : ModelBox}
    (hsource : inp.boxes[index]? = some source) :
    res.scene.layoutDump.box? source.id =
      some (Box.mk source.id source.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD index default)))
        source.parent source.exclusive) := by
  let box := Box.mk source.id source.role.id
    (shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD index default)))
    source.parent source.exclusive
  have hbox : res.scene.boxes[index]? = some box := by
    rw [execution.boxes_eq_mapX]
    simp only [List.getElem?_map, List.getElem?_zipIdx, hsource,
      Option.map_some, Nat.zero_add]
    rfl
  have hids : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
    rw [execution.boxes_eq_mapX, List.map_map]
    exact zipIdx_map_comp (·.id) inp.boxes 0
  have hnodup : (res.scene.boxes.map (·.id)).Nodup := by
    rw [hids]
    exact hboxIds
  change res.scene.boxes.find? (fun candidate => candidate.id == source.id) = some box
  exact Assembly.keyed_lookup_eq (·.id) res.scene.boxes hnodup box
    (List.mem_of_getElem? hbox)

/-- Exact part-entry dump lookup (private copy of
`SceneExecutionX.part_entry_box_lookup_of_box_ids_nodupX`, kept local for
the same reason). -/
private theorem Xc_part_entry_box_lookup_of_box_ids_nodupX {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {i key : Nat} {rect : Rect}
    (hentry : (q.1.1.zip q.1.2.rects)[i]? = some (key, rect))
    {source : ModelBox} (hsource : inp.boxes[key]? = some source) :
    res.scene.layoutDump.box? source.id =
      some (Box.mk source.id source.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect q.2.x q.2.y rect)))
        source.parent source.exclusive) := by
  have hsize : execution.componentsAcc.rects.size = inp.boxes.length :=
    execution.components_rects_size
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [hsize]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hrect := actual_components_packed_rect_valueX (by rfl) execution.components_eq
    execution.packed_eq packed hpacked hselected hentry hkeysize default
  have hlookup := Xc_source_box_lookup_of_box_ids_nodupX execution hids hsource
  rw [hrect] at hlookup
  exact hlookup

/-- Negation as zero-minus, for normalizing the `placeComponentExact` y-shift
into the `shiftRect_pack_normalize` form. -/
private theorem Xc_neg_eq_zero_sub (x : Int) : -x = 0 - x := by omega

/-- The exact part-level dump-box identification holds: box-id uniqueness
follows from the bound `WellFormed`, and the proof replays `aligned_dump_box`
(`X_chosen_part_frame_entry` plus the part-entry lookup, normalized by
`shiftRect_pack_normalize`). -/
theorem X_DumpLookup_holds (exactIds : List String) : X_DumpLookup exactIds := by
  intro inp o res execution hwf packed hpacked c q hselected candidate run loops area
    hpart pos key hkey s hsource
  have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hentry := X_chosen_part_frame_entry hpart hkey
  rw [Xc_neg_eq_zero_sub] at hentry
  have hlookup := Xc_part_entry_box_lookup_of_box_ids_nodupX execution hids packed
    hpacked hselected hentry hsource
  rw [shiftRect_pack_normalize] at hlookup
  exact hlookup

/-- Observation projection for constraint congruence: index, border,
declaration, and cluster path — everything `Compound.constraints` inspects. -/
private def Xc_obs (q : Node × Nat) : Nat × Int × Nat × List Nat :=
  (q.2, q.1.border, q.1.decl, q.1.clusterPath)

/-- The exact graph preserves per-node observations over `zipIdx` (mirror of
`X_projMap` in `ExactFlatC2.lean`). -/
private theorem Xc_zip_obs_eq {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g0 g : Graph}
    (h : exactGraph P exactIds inp o measured g0 = .ok g) :
    (g.nodes.zipIdx.map Xc_obs) = (g0.nodes.zipIdx.map Xc_obs) := by
  have hlen : g.nodes.length = g0.nodes.length := exactGraph_length h
  apply List.ext_getElem?
  intro v
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_zipIdx]
  cases h0 : g0.nodes[v]? with
  | none =>
      have hnone : g.nodes[v]? = none := by
        rw [List.getElem?_eq_none_iff] at h0 ⊢
        omega
      rw [hnone]
  | some nd0 =>
      obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key h h0
      rw [hnd']
      simp only [Option.map_some, Xc_obs, hnb, hnap, hnd]

/-- Filter congruence over observation-equal lists: only the observed
projection matters, so filtering by a factored predicate commutes with the
observation map. -/
private theorem Xc_filter_obs_map {l l' : List (Node × Nat)}
    (h : l.map Xc_obs = l'.map Xc_obs) (f : Nat × Int × Nat × List Nat → Bool) :
    ((l.filter fun q => f (Xc_obs q)).map Xc_obs) =
    ((l'.filter fun q => f (Xc_obs q)).map Xc_obs) := by
  induction l generalizing l' with
  | nil =>
      cases l' with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases l' with
      | nil => simp at h
      | cons y ys =>
          rw [List.map_cons, List.map_cons, List.cons.injEq] at h
          obtain ⟨hxy, hrest⟩ := h
          have hff : f (Xc_obs x) = f (Xc_obs y) := by rw [hxy]
          by_cases hfx : f (Xc_obs x) = true
          · have hfy : f (Xc_obs y) = true := hff ▸ hfx
            rw [List.filter_cons, List.filter_cons, ite_eq_left hfx, ite_eq_left hfy,
              List.map_cons, List.map_cons, hxy, ih hrest]
          · have hfy_neg : ¬ f (Xc_obs y) = true := by rw [← hff]; exact hfx
            rw [List.filter_cons, List.filter_cons, ite_eq_right hfx, ite_eq_right hfy_neg]
            exact ih hrest
/-- Find congruence over observation-equal lists: both sides miss, or both
hit elements with equal observations (the node identities may differ in
unobserved fields). -/
private theorem Xc_find_obs {l l' : List (Node × Nat)}
    (h : l.map Xc_obs = l'.map Xc_obs) (f : Nat × Int × Nat × List Nat → Bool) :
    (∃ b b', (l.find? fun q => f (Xc_obs q)) = some b ∧
      (l'.find? fun q => f (Xc_obs q)) = some b' ∧ Xc_obs b = Xc_obs b') ∨
    ((l.find? fun q => f (Xc_obs q)) = none ∧
      (l'.find? fun q => f (Xc_obs q)) = none) := by
  induction l generalizing l' with
  | nil =>
      cases l' with
      | nil => exact Or.inr ⟨rfl, rfl⟩
      | cons y ys => simp at h
  | cons x xs ih =>
      cases l' with
      | nil => simp at h
      | cons y ys =>
          rw [List.map_cons, List.map_cons, List.cons.injEq] at h
          obtain ⟨hxy, hrest⟩ := h
          have hff : f (Xc_obs x) = f (Xc_obs y) := by rw [hxy]
          by_cases hfx : f (Xc_obs x) = true
          · have hfy : f (Xc_obs y) = true := hff ▸ hfx
            rw [List.find?_cons, List.find?_cons, hfx, hfy]
            exact Or.inl ⟨x, y, rfl, rfl, hxy⟩
          · have hfx' : f (Xc_obs x) = false := by
              cases hz : f (Xc_obs x) with
              | true => exact absurd hz hfx
              | false => rfl
            have hfy' : f (Xc_obs y) = false := by
              cases hz : f (Xc_obs y) with
              | true => rw [hz] at hff; exact absurd hff hfx
              | false => rfl
            rw [List.find?_cons, List.find?_cons, hfx', hfy']
            exact ih hrest

/-- Empty lists have equal observations iff both are empty. -/
private theorem Xc_isEmpty_of_map_eq {l l' : List (Node × Nat)}
    (h : l.map Xc_obs = l'.map Xc_obs) : l.isEmpty = l'.isEmpty := by
  have hlen : l.length = l'.length := by
    have hcon := congrArg List.length h
    simpa only [List.length_map] using hcon
  cases l with
  | nil => cases l' with | nil => rfl | cons _ _ => simp at hlen
  | cons _ _ => cases l' with | nil => simp at hlen | cons _ _ => rfl

/-- Flat-map congruence over observation-equal lists. -/
private theorem Xc_flatMap_obs {t t' : List (Node × Nat)}
    (h : t.map Xc_obs = t'.map Xc_obs)
    (F F' : Node × Nat → List Edge)
    (hF : ∀ a a', Xc_obs a = Xc_obs a' → F a = F' a') :
    t.flatMap F = t'.flatMap F' := by
  induction t generalizing t' with
  | nil => cases t' with | nil => rfl | cons _ _ => simp at h
  | cons x xs ih =>
      cases t' with
      | nil => simp at h
      | cons y ys =>
          rw [List.map_cons, List.map_cons, List.cons.injEq] at h
          obtain ⟨hxy, hrest⟩ := h
          rw [List.flatMap_cons, List.flatMap_cons, hF x y hxy, ih hrest]
/-- Per-top constraint edges, factored out of `Compound.constraints`: the
bottom lookup, member/children filters, nested/leaf edges, and the
empty-test, all over explicit node lists. -/
private def Xc_topEdges (ns tops : List (Node × Nat)) (top : Node × Nat) : List Edge :=
  match ns.find? (fun q => q.1.border == 2 && q.1.decl == top.1.decl) with
  | none => []
  | some bottom =>
    if (ns.filter fun q => q.1.border == 0 && q.1.clusterPath.contains top.1.decl).isEmpty &&
      (tops.filter fun q => q.1.clusterPath.dropLast == top.1.clusterPath).isEmpty
    then [⟨top.2, bottom.2, 1, 0, false⟩]
    else (ns.filter fun q => q.1.border == 0 && q.1.clusterPath.contains top.1.decl).flatMap
        (fun member => [⟨top.2, member.2, 1, 0, false⟩, ⟨member.2, bottom.2, 1, 0, false⟩]) ++
      (tops.filter fun q => q.1.clusterPath.dropLast == top.1.clusterPath).flatMap
        (fun child => match ns.find? (fun q => q.1.border == 2 && q.1.decl == child.1.decl) with
          | none => []
          | some childBottom =>
            [⟨top.2, child.2, 1, 0, false⟩, ⟨childBottom.2, bottom.2, 1, 0, false⟩])

/-- Per-top edges agree on observation-equal tops. -/
private theorem Xc_topEdges_congr {ns ns' tops tops' : List (Node × Nat)}
    (hns : ns.map Xc_obs = ns'.map Xc_obs)
    (htops : tops.map Xc_obs = tops'.map Xc_obs)
    {a a' : Node × Nat} (ha : Xc_obs a = Xc_obs a') :
    Xc_topEdges ns tops a = Xc_topEdges ns' tops' a' := by
  have ha2 : a.2 = a'.2 := congrArg (·.1) ha
  have had : a.1.decl = a'.1.decl := by simpa [Xc_obs] using congrArg (·.2.2.1) ha
  have hap : a.1.clusterPath = a'.1.clusterPath := by
    simpa [Xc_obs] using congrArg (·.2.2.2) ha
  unfold Xc_topEdges
  rw [← had, ← hap]
  have hfind := Xc_find_obs hns
    (fun o : Nat × Int × Nat × List Nat => o.2.1 == 2 && o.2.2.1 == a.1.decl)
  simp only [Xc_obs] at hfind
  rcases hfind with ⟨b, b', hb, hb', hobsb⟩ | ⟨hn, hn'⟩
  · rw [hb, hb']
    dsimp only
    have hb2 : b.2 = b'.2 := congrArg (·.1) hobsb
    have hmem_map : ((ns.filter fun q =>
        q.1.border == 0 && q.1.clusterPath.contains a.1.decl).map Xc_obs) =
        ((ns'.filter fun q =>
          q.1.border == 0 && q.1.clusterPath.contains a.1.decl).map Xc_obs) := by
      simpa [Xc_obs] using Xc_filter_obs_map hns
        (fun o : Nat × Int × Nat × List Nat => o.2.1 == 0 && o.2.2.2.contains a.1.decl)
    have hchild_map : ((tops.filter fun q =>
        q.1.clusterPath.dropLast == a.1.clusterPath).map Xc_obs) =
        ((tops'.filter fun q =>
          q.1.clusterPath.dropLast == a.1.clusterPath).map Xc_obs) := by
      simpa [Xc_obs] using Xc_filter_obs_map htops
        (fun o : Nat × Int × Nat × List Nat => o.2.2.2.dropLast == a.1.clusterPath)
    have hmem_empty := Xc_isEmpty_of_map_eq hmem_map
    have hchild_empty := Xc_isEmpty_of_map_eq hchild_map
    rw [hmem_empty, hchild_empty]
    congr 1
    · rw [ha2, hb2]
    · have hleaves : (ns.filter fun q =>
            q.1.border == 0 && q.1.clusterPath.contains a.1.decl).flatMap
            (fun member => [Edge.mk a.2 member.2 1 0 false,
              Edge.mk member.2 b.2 1 0 false]) =
            (ns'.filter fun q =>
              q.1.border == 0 && q.1.clusterPath.contains a.1.decl).flatMap
            (fun member => [Edge.mk a'.2 member.2 1 0 false,
              Edge.mk member.2 b'.2 1 0 false]) := by
        apply Xc_flatMap_obs hmem_map
        intro m m' hm
        have hm2 : m.2 = m'.2 := congrArg (·.1) hm
        rw [ha2, hb2, hm2]
      have hnested : (tops.filter fun q =>
            q.1.clusterPath.dropLast == a.1.clusterPath).flatMap
            (fun child => match ns.find? (fun q =>
              q.1.border == 2 && q.1.decl == child.1.decl) with
            | none => []
            | some childBottom => [Edge.mk a.2 child.2 1 0 false,
              Edge.mk childBottom.2 b.2 1 0 false]) =
            (tops'.filter fun q =>
              q.1.clusterPath.dropLast == a.1.clusterPath).flatMap
            (fun child => match ns'.find? (fun q =>
              q.1.border == 2 && q.1.decl == child.1.decl) with
            | none => []
            | some childBottom => [Edge.mk a'.2 child.2 1 0 false,
              Edge.mk childBottom.2 b'.2 1 0 false]) := by
        apply Xc_flatMap_obs hchild_map
        intro c c' hc
        have hc2 : c.2 = c'.2 := congrArg (·.1) hc
        have hcd : c.1.decl = c'.1.decl := by
          simpa [Xc_obs] using congrArg (·.2.2.1) hc
        rw [← hcd]
        have hnfind := Xc_find_obs hns
          (fun o : Nat × Int × Nat × List Nat => o.2.1 == 2 && o.2.2.1 == c.1.decl)
        simp only [Xc_obs] at hnfind
        rcases hnfind with ⟨cb, cb', hcb, hcb', hobscb⟩ | ⟨hcn, hcn'⟩
        · rw [hcb, hcb']
          dsimp only
          have hcb2 : cb.2 = cb'.2 := congrArg (·.1) hobscb
          rw [ha2, hc2, hcb2, hb2]
        · rw [hcn, hcn']
      rw [hleaves, hnested]
  · rw [hn, hn']
/-- `exactGraph` preserves constraint edges: only border, declaration, and
cluster-path observations flow into `Compound.constraints`. -/
private theorem Xc_constraints_eq {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g0 g : Graph}
    (h : exactGraph P exactIds inp o measured g0 = .ok g) :
    Compound.constraints g = Compound.constraints g0 := by
  have hobs := Xc_zip_obs_eq h
  have htops : ((g.nodes.zipIdx.filter fun q => q.1.border == -2).map Xc_obs) =
      ((g0.nodes.zipIdx.filter fun q => q.1.border == -2).map Xc_obs) := by
    simpa [Xc_obs] using Xc_filter_obs_map hobs
      (fun o : Nat × Int × Nat × List Nat => o.2.1 == -2)
  have hperTop : ∀ a a', Xc_obs a = Xc_obs a' →
      Xc_topEdges g.nodes.zipIdx
        (g.nodes.zipIdx.filter fun q => q.1.border == -2) a =
      Xc_topEdges g0.nodes.zipIdx
        (g0.nodes.zipIdx.filter fun q => q.1.border == -2) a' :=
    fun a a' ha => Xc_topEdges_congr hobs htops ha
  calc Compound.constraints g
      = (g.nodes.zipIdx.filter fun q => q.1.border == -2).flatMap
        (Xc_topEdges g.nodes.zipIdx
          (g.nodes.zipIdx.filter fun q => q.1.border == -2)) := rfl
    _ = (g0.nodes.zipIdx.filter fun q => q.1.border == -2).flatMap
        (Xc_topEdges g0.nodes.zipIdx
          (g0.nodes.zipIdx.filter fun q => q.1.border == -2)) :=
        Xc_flatMap_obs htops _ _ hperTop
    _ = Compound.constraints g0 := rfl

/-- `exactGraph` preserves components: edges, node count, and constraints are
untouched, and `components` is computed from exactly those. -/
private theorem Xc_components_eq {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g0 g : Graph}
    (h : exactGraph P exactIds inp o measured g0 = .ok g) :
    components g = components g0 := by
  have he : g.edges = g0.edges := exactGraph_edges h
  have hlen : g.nodes.length = g0.nodes.length := exactGraph_length h
  have hc : Compound.constraints g = Compound.constraints g0 := Xc_constraints_eq h
  unfold components
  rw [he, hc, hlen]
/-- Reverse key lookup through `exactGraph` (local copy of the private
`X_node_key_rev` of `ExactFlatC5.lean`): every exact-graph node comes from the
measured-graph node at the same index with the same key fields. -/
private theorem Xc_node_key_rev {P : Params} {exactIds : List String} {inp : Input}
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

/-- Component lookup at the position of a member (local copy of the private
`X_comp_idxOf_lookup` of `ExactFlatC5.lean`). -/
private theorem Xc_comp_idxOf_lookup {comp : List Nat} {x : Nat} (hmem : x ∈ comp) :
    comp[comp.idxOf x]? = some x :=
  (List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem)).trans
    (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)))

/-- The exact bottom-marker dump box plus boundary holds: anchor selection on
the measured graph (transferred to the exact graph by node-key and component
preservation), the `X_BottomBoundary` row, and the flat-port span transported
through the top-title entry — replaying `bottom_dump_box_boundary`. -/
theorem X_BottomMarkerDump_holds (exactIds : List String)
    (hbottom : X_BottomBoundary exactIds)
    (hanchor : GroupAnchorSelection) : X_BottomMarkerDump exactIds := by
  intro inp o res execution hwf hfp _hbottom _hanchor packed hpacked c q hselected
    candidate run labels orderOptions hrun loops area hpart pos w hpos n hn hb2 s hs hgrp
    hcomp px hspan
  have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hlines : execution.lines.length = inp.boxes.length := by
    have hle := execution.lines_eq
    unfold boxLines at hle
    have hlen := (mapM_getElem? _ _ _ hle).1
    simpa [List.length_zipIdx] using hlen
  have hanchorRes := hanchor execution.graph0_eq hlines
  obtain ⟨n0, hn0, hnb0, hnap0, hnd0⟩ := Xc_node_key_rev execution.graph_eq hn
  have hb2' : n0.border = 2 := hnb0.trans hb2
  have hposW : w = Compound.bottomIndex (preparedBoxes inp) n.decl := by
    have hw := hanchorRes.1 hn0 hb2'
    rw [hnd0] at hw
    exact hw
  have hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == s.id) = false := by
    obtain ⟨pbox, hpb, hpg, _, _, _⟩ :=
      measuredGraph_bottom_origin execution.graph0_eq (List.mem_of_getElem? hn0) hb2'
    have hlook := preparedBoxes_lookup hs
    have hpb' : (preparedBoxes inp)[n.decl]? = some pbox := by
      have hpb0 : (preparedBoxes inp)[n0.decl]? = some pbox := by
        simpa [preparedBoxes] using hpb
      rw [hnd0] at hpb0
      exact hpb0
    rw [hlook] at hpb'
    cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == s.id) with
    | true =>
        simp only [hf, ↓reduceIte] at hpb'
        have hcon : ({ s with role := .node } : ModelBox) = pbox :=
          Option.some.inj hpb'
        rw [← hcon] at hpg
        simp at hpg
    | false => rfl
  obtain ⟨top, comp, hmem, hntop, htopB, htopDecl, hjIn, hbotIn⟩ :=
    hanchorRes.2 hs hgrp hfixed
  obtain ⟨topX, htopX, htopB', htopnap, htopnd⟩ :=
    exactGraph_node_key execution.graph_eq hntop
  have hwIn : w ∈ q.1.1 := List.mem_of_getElem? hpos
  have hbotIn' : w ∈ comp := by rw [hposW]; exact hbotIn
  have hmemX : comp ∈ components execution.graph := by
    rw [Xc_components_eq execution.graph_eq]
    exact hmem
  have hcompEq : comp = q.1.1 :=
    components_shared_member_eq hmemX hcomp hbotIn' hwIn
  have hjIn' : n.decl ∈ q.1.1 := by rw [← hcompEq]; exact hjIn
  have hposTop := Xc_comp_idxOf_lookup hjIn'
  have hcgNode : (componentCandidate execution.graph q.1.1 candidate).nodes.getD pos
      default = n := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.getD_eq_getElem?_getD, List.getElem?_map, hpos,
      Option.map_some, Option.getD_some]
    rw [hn]
    rfl
  have hcgTop : (componentCandidate execution.graph q.1.1 candidate).nodes.getD
      (q.1.1.idxOf n.decl) default = topX := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.getD_eq_getElem?_getD, List.getElem?_map, hposTop,
      Option.map_some, Option.getD_some]
    rw [htopX]
    rfl
  have hbound :=
    hbottom execution.graph0_eq execution.graph_eq hlines hwf hfp hcomp hrun (v := pos)
      (t := q.1.1.idxOf n.decl) (px := px)
      (by rw [hcgNode]; exact hb2)
      (by rw [hcgTop]; exact htopB'.trans htopB)
      (by rw [hcgNode, hcgTop]; exact (htopnd.trans htopDecl).symm)
      hspan
  have hentry := X_chosen_part_frame_entry hpart hposTop
  rw [Xc_neg_eq_zero_sub] at hentry
  have hlookup := Xc_part_entry_box_lookup_of_box_ids_nodupX execution hids packed
    hpacked hselected hentry hs
  rw [shiftRect_pack_normalize] at hlookup
  refine ⟨Box.mk s.id s.role.id _ s.parent s.exclusive, hlookup, ?_⟩
  exact (onBoundary_shift _ _ _ _).mpr ((onBoundary_orient _ _ _ _).mpr
    ((onBoundary_shift _ _ _ _).mpr hbound))
/-- Exact sizing preserves node count (mirror of `sizeProperPorts_length`). -/
private theorem Xc_sizeProperPortsX_length (P : Params) (exact : List Nat)
    (source : Proper) :
    (sizeProperPortsX P exact source).nodes.length = source.nodes.length := by
  simp [sizeProperPortsX]

/-- Exact title-reservation rank alignment (mirror of
`titleReservations_node_rank_alignment` over `sizeProperPortsX`). -/
private theorem Xc_titleReservations_node_rank_alignment (P : Params)
    {exact : List Nat} {source : Proper}
    (h : source.nodes.length = source.rank.length) :
    (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length := by
  rw [titleReservations_nodes]
  simp only [List.length_append, List.length_map, Xc_sizeProperPortsX_length]
  have hrank : (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ (titleNodes (sizeProperPortsX P exact source)).map
        (fun entry => rk source.rank entry.2) := by
    unfold titleReservations titleNodes sizeProperPortsX
    rfl
  rw [hrank]
  simp only [List.length_append, List.length_map]
  omega

/-- Exact run record bundle: coordinate equation, node keys, length alignment,
and labeled node records — the `componentRunX` counterpart of
`componentRun_coordinate_source_alignment` plus the record transport. -/
private theorem Xc_run_records {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∃ labeled : Proper, coordinateGraphX P exact labeled = run.coordinateProper ∧
      NodeKeys cg labeled ∧ labeled.nodes.length = labeled.rank.length ∧
      (titleReservations (sizeProperPortsX P exact labeled)).nodes.length =
        (titleReservations (sizeProperPortsX P exact labeled)).rank.length ∧
      (∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
        labeled.nodes[index]? = some ⟨node, false, none, false⟩) := by
  obtain ⟨_, _, labeled, _, hn, hl, hc, _, _, _, _, _, _, _⟩ := componentRunX_spec h
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  exact ⟨labeled, hc, addLabelNodes_keys _ _ _ (normalize_keys hn) hl,
    haligned, Xc_titleReservations_node_rank_alignment P haligned,
    fun index node hnode =>
      addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl⟩

/-- Exact sizing node origin (local copy of `X_sizeProperPorts_node_origin` of
`ExactFlatC5Rank.lean`). -/
private theorem Xc_sizeProperPortsX_node_origin (P : Params) (exact : List Nat)
    (source : Proper) {index : Nat} {node : ProperNode}
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

/-- Exact titled marker record (mirror of `titled_marker_record` over
`sizeProperPortsX`). -/
private theorem Xc_titled_marker_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode}
    (hnode : source.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2) :
    (titleReservations (sizeProperPortsX P exact source)).nodes[index]? =
      some (titleF node) := by
  have hnonplain : node.node.border ≠ 0 := by
    rcases hborder with hborder | hborder <;> omega
  have hsized : (sizeProperPortsX P exact source).nodes[index]? = some node := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hnode, Option.map_some,
      Nat.zero_add]
    simp [hnonplain]
  rw [titleReservations_nodes, List.getElem?_append_left (by
    simp only [List.length_map, Xc_sizeProperPortsX_length]
    exact (List.getElem?_eq_some_iff.mp hnode).1)]
  simp only [List.getElem?_map, hsized, Option.map_some]

/-- Exact coordinate-graph marker record (mirror of
`coordinateGraph_marker_record` over `coordinateGraphX`). -/
private theorem Xc_coordinateGraphX_marker_record {P : Params} {exact : List Nat}
    {source : Proper} {index : Nat} {node : ProperNode}
    (hnode : source.nodes[index]? = some node)
    (hborder : node.node.border = -2 ∨ node.node.border = 2)
    (hdummy : node.dummy = false) :
    (coordinateGraphX P exact source).nodes[index]? = some (clearF (titleF node)) := by
  have htitled := Xc_titled_marker_record (P := P) (exact := exact) hnode hborder
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
/-- Exact proxy interval (mirror of `componentRun_proxy_interval` over
`componentRunX`). -/
private theorem Xc_proxy_interval {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
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

/-- The executed record of an exact `-2` top proxy keeps the coordinate
record's cluster path (mirror of `group_top_proper_clusterPath`). -/
private theorem Xc_proper_clusterPath {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = -2) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath := by
  obtain ⟨_, span, _, _, hproper, _, _⟩ :=
    Xc_proxy_interval hrun hcoord (Or.inl hb)
  exact ⟨{ coord with node := { coord.node with w := span.hi - span.lo } }, hproper, rfl⟩

/-- The executed exact `run.proper` rank equals the coordinate rank (mirror of
`componentRun_rank_eq` / `group_top_rank_eq_coordinate`). -/
private theorem Xc_rank_eq {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) (i : Nat) :
    rk run.proper.rank i = rk run.coordinateProper.rank i := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec hrun
  have hdropRank : run.proper.rank = q0.rank := by
    rw [← hdrop]
    exact OrderImpl.dropSynthetic_rank _
  rw [hdropRank, (proxyWidths_rel hproxy).2.1]

/-- Exact original nodes are covered (mirror of
`componentRun_original_nodes_covered`). -/
private theorem Xc_original_nodes_covered {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run) :
    ∀ i, i < cg.nodes.length → i < run.proper.nodes.length := by
  obtain ⟨ranks, p0, labeled, q, hn, hl, hcoord, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
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
      Xc_sizeProperPortsX_length]
    omega
  have hplen := (proxyWidths_rel hproxy).2.2.1
  intro i hi
  rw [← hdrop]
  change i < q.nodes.length
  omega
/-- The explicit marker coordinate has height zero (title reserves no height
for `±2` borders; clearing preserves it). -/
private theorem Xc_coord_marker_height {nd : Node}
    (hborder : nd.border = -2 ∨ nd.border = 2) :
    (clearF (titleF ⟨nd, false, none, false⟩)).node.h = 0 := by
  have h1 : (titleF ⟨nd, false, none, false⟩).node.h = 0 :=
    (titleF_keys _).2.2.2 hborder
  have h2 : (clearF (titleF ⟨nd, false, none, false⟩)).node.h =
      (titleF ⟨nd, false, none, false⟩).node.h := (clearF_keys _).2.2.2
  rw [h2]; exact h1



/-- The coordinate-graph record of an exact `-2` graph node (mirror of
`group_top_coordinate_record` over `componentRunX`). -/
private theorem Xc_group_top_coordinate_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : cg.nodes[v]? = some nd) (hgroup : nd.border = -2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = -2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
  obtain ⟨labeled, hc, _, _, _, hnodeRec⟩ := Xc_run_records hrun
  have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hnodeRec v nd hnode
  have hmarker := Xc_coordinateGraphX_marker_record (P := P) (exact := exact)
    hrec (Or.inl hgroup) rfl
  rw [hc] at hmarker
  refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_, ?_⟩
  · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [hb, (titleF_keys _).2.1]
    exact hgroup
  · exact (clearF_keys _).1.trans (titleF_keys _).1
  · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
  · exact Xc_coord_marker_height (Or.inl hgroup)
private theorem Xc_straightPort_lo_aux {source target lo hi : Int} (hle : lo ≤ hi) :
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

private theorem Xc_straightPort_hi_aux {source target lo hi : Int} (hle : lo ≤ hi) :
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

private theorem Xc_straightSpanOf_column_mem {ctx : StraightenCtx} {routing : Routing} {i : Nat}
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
              exact Xc_straightPort_lo_aux hle
            have hhiCx : cx ≤ hi := by
              rw [← hSP]
              exact Xc_straightPort_hi_aux hle
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

private theorem Xc_bool_of_not_true {b : Bool} (h : (!b) = true) : b = false := by
  cases hb : b with
  | true =>
    simp only [hb] at h
    cases h
  | false => rfl

private theorem Xc_straightRealNode_exists {p : Proper} {v : Nat}
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
    exact ⟨n, rfl, Xc_bool_of_not_true hd, Xc_bool_of_not_true hl, hbord⟩




private theorem Xc_installed_run_of_mem {exactIds : List String} {inp : Input} {o : Options}
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

private theorem Xc_XBbs_coordinateGraph0_lookup (P : Params) (exact : List Nat)
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
    Xc_sizeProperPortsX_length P exact p
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

private theorem Xc_XBbs_coordinateGraph_lookup (P : Params) (exact : List Nat)
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
  rcases Xc_XBbs_coordinateGraph0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
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

private theorem Xc_installed_proper_below {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
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
  rcases Xc_XBbs_coordinateGraph_lookup P exact labeled hpc with ⟨m, hm, hdPc, _, _, _⟩ | ⟨_, hbS⟩
    | ⟨_, _, _, _, _, hbT, _⟩
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

private theorem Xc_installed_proper_cg_node {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
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
  rcases Xc_XBbs_coordinateGraph_lookup P exact labeled hpc with ⟨m, hm, hdPc, hbPc, _, _⟩ | ⟨_, hbS⟩
    | ⟨_, _, _, _, _, hbT, _⟩
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

private theorem Xc_installed_comp_nodes_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  show (comp.map fun w => g.nodes.getD w default).length = comp.length
  simp

private theorem Xc_installed_place_rects_lengthX (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run 0 labels loops).rects.length = cg.nodes.length := by
  unfold placeComponentExact
  dsimp only
  simp only [List.length_map, List.length_range]


private theorem Xc_installed_fold_rects_sizeX (P : Params) (exactIds : List String) (inp : Input)
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
    rw [Xc_installed_fold_rects_sizeX P exactIds inp o graph labels comps next out hrest]
    exact (layoutComponentX_sizes hnext).1.symm

private theorem Xc_installed_mapM_ok_length {err α β : Type} (f : α → Except err β) :
    ∀ (l : List α) (out : List β), l.mapM f = Except.ok out → out.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro out h
    change Except.ok [] = Except.ok out at h
    injection h with hout
    subst out
    rfl
  | cons a l ih =>
    intro out h
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | error err =>
      rw [ha] at h
      change Except.error err = Except.ok out at h
      cases h
    | ok b =>
      cases hxs : l.mapM f with
      | error err =>
        rw [ha, hxs] at h
        change Except.error err = Except.ok out at h
        cases h
      | ok xs =>
        rw [ha, hxs] at h
        change Except.ok (b :: xs) = Except.ok out at h
        injection h with hout
        subst out
        exact congrArg Nat.succ (ih xs hxs)

private theorem Xc_installed_lines_lenX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  simp only [boxLines] at h
  calc execution.lines.length = (inp.boxes.zipIdx).length :=
        Xc_installed_mapM_ok_length _ _ _ h
    _ = inp.boxes.length := List.length_zipIdx

private theorem Xc_installed_graph_markedX {exactIds : List String} {inp : Input} {o : Options}
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
      have h0' := Xc_installed_mapM_ok_length _ _ _ hn0
      rwa [List.length_zipIdx] at h0'
    have h1 : nodes.length = nodes0.length := by
      have h1' := Xc_installed_mapM_ok_length _ _ _ hnodes
      rwa [List.length_zipIdx, List.length_map] at h1'
    rw [h1]
    exact h0

private theorem Xc_installed_markNodes_split (boxes : List ModelBox) (pad : Int)
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

private theorem Xc_installed_key_lt_boxesX {exactIds : List String} {inp : Input} {o : Options}
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
  obtain ⟨n, hnCg, hnBorder⟩ := Xc_installed_proper_cg_node hrun hv hd hb
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
  obtain ⟨N, hgraph, hNlen⟩ := Xc_installed_graph_markedX execution
  have hlines := Xc_installed_lines_lenX execution
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
  obtain ⟨nd0, hnd0, hnb0, _, _⟩ := Xc_node_key_rev execution.graph_eq hgetExact
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
    Xc_installed_markNodes_split _ _ _ N
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

/-- The exact chosen-part row holds, modulo the three uniform single-stage
residuals: the run-level port attachment (`X_RunAttach`), the part-level
dump-box identification (`X_DumpLookup`), and the bottom-marker dump box
plus boundary (`X_BottomMarkerDump`). The proof replays
`SceneExecution.chosen_part_group_c5_alias` over the exact run: chain
identification and head-side ports are proved here (`X_componentRun_chain_endpoints`,
`X_flat_head_port_on_ys`), the scene emission is proved here
(`X_chosen_part_route_entry`), and each side consumes its `EndpointAnchor`
through the residuals. The four `X_` row facts are consumed as hypotheses
(`_hrank` into the run attachment, `_hbottom`/`_hport`/`_hanchor` into the
marker dump); the `WellFormed`/`framedParents`/box-id premises their deferred
proofs need are not bound by `X_ChosenPart` (which is why the three narrow
stage residuals stay open — see each definition). -/
theorem x_chosenPart_holds (exactIds : List String)
    (hattach : X_RunAttach exactIds) : X_ChosenPart exactIds := by
  intro inp o res execution hwf hfp hrank hbottom hport hanchor packed hpacked c q hselected
    candidate run loops area hrun hloops hpart i edge hedge hne mroute hrouteD hF hT
  have hlookup : X_DumpLookup exactIds := X_DumpLookup_holds exactIds
  have hmarker : X_BottomMarkerDump exactIds :=
    X_BottomMarkerDump_holds exactIds hbottom hanchor
  have hlines : execution.lines.length = inp.boxes.length := by
    have hle := execution.lines_eq
    unfold boxLines at hle
    have hlen := (mapM_getElem? _ _ _ hle).1
    simpa [List.length_zipIdx] using hlen
  have hi : i < (componentCandidate execution.graph q.1.1 candidate).edges.length :=
    (List.getElem?_eq_some_iff.mp hedge).1
  have he : (componentCandidate execution.graph q.1.1 candidate).edges[i] = edge :=
    (List.getElem?_eq_some_iff.mp hedge).2
  have hdeclEq : edge.decl =
      (componentCandidate execution.graph q.1.1 candidate).edges[i].decl :=
    congrArg Edge.decl he |>.symm
  have hnd : (((componentCandidate execution.graph q.1.1 candidate).edges.map
      (·.decl))).Nodup :=
    componentCandidate_decls_nodup execution.graph q.1.1 candidate
      (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
  have hloopEdge : ∀ l ∈ loops, l.1 ≠ edge.decl :=
    componentLoops_excludes_ordinary_decl hloops hnd hedge hne
  have hloopCg : ∀ l ∈ loops,
      l.1 ≠ ((componentCandidate execution.graph q.1.1 candidate).edges[i]).decl :=
    fun l hl hcon => hloopEdge l hl (hcon.trans hdeclEq.symm)
  have hcomp : q.1.1 ∈ components execution.graph := by
    have hqin : q.1 ∈ execution.componentsAcc.parts :=
      List.mem_of_getElem? (zip_getElem?_left hselected)
    have hmap : q.1.1 ∈ execution.componentsAcc.parts.map
        (fun part : List Nat × Part => part.1) :=
      List.mem_map_of_mem hqin
    rw [(actual_components_parts_geometryX (by rfl) execution.components_eq).1] at hmap
    exact hmap
  obtain ⟨first, last, hfirst, hlast, htail, hhead⟩ :=
    X_componentRun_chain_endpoints hrun hedge hne
  obtain ⟨rt, start, finish, hget, _horig, _hplaced, hstart, hfinish, hports⟩ :=
    hattach execution.graph0_eq execution.graph_eq hlines hwf hfp hcomp candidate hrun
      hi hfirst hlast 0 loops hloopCg
      execution.params.canvasMargin o.direction execution.packedAcc.canvasH q.2.x q.2.y
  obtain ⟨mroute0, native, hmodelRoute, hnative, horiginal, hscene⟩ :=
    X_chosen_part_route_entry execution packed hpacked hselected hrun hpart hedge hloopEdge
  have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hsuff : res.scene.routes[edge.decl]? =
      some (Route.mk mroute0.id mroute0.fromId mroute0.toId mroute0.orthogonal
        (native.points.map (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY))) →
      ∃ (out : Route) (start finish : Point) (fromBox toBox : Box),
        res.scene.routes[edge.decl]? = some out ∧
        out.points.head? = some start ∧ out.points.getLast? = some finish ∧
        res.scene.layoutDump.box? out.fromId = some fromBox ∧
        res.scene.layoutDump.box? out.toId = some toBox ∧
        Validator.onBoundary start fromBox.rect ∧
        Validator.onBoundary finish toBox.rect := by
    intro hscene0
    {
  have hsame : native = rt := (Option.some.inj (hget.symm.trans hnative)).symm
  subst hsame
  have hmodelEq : mroute = mroute0 :=
    (Option.some.inj (hmodelRoute.symm.trans hrouteD)).symm
  subst hmodelEq
  rw [htail, hhead] at hports
  have hcondEq : (((componentCandidate execution.graph q.1.1 candidate).edges.map
      (·.reversed)).getD i false) = edge.reversed := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hedge, Option.map_some,
      Option.getD_some]
  cases hr : edge.reversed
  · simp only [hcondEq, hr] at hports
    have horigT : edge.original.tail = edge.tail := by simp [Edge.original, hr]
    have horigH : edge.original.head = edge.head := by simp [Edge.original, hr]
    obtain ⟨wF, hposFo, hsideF⟩ := hF
    have hposF : q.1.1[edge.tail]? = some wF := by rw [← horigT]; exact hposFo
    obtain ⟨wT, hposTo, hsideT⟩ := hT
    have hposTt : q.1.1[edge.head]? = some wT := by rw [← horigH]; exact hposTo
    have hfromOut : ∃ fromBox : Box,
        res.scene.layoutDump.box? mroute.fromId = some fromBox ∧
        Validator.onBoundary (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY
          start) fromBox.rect := by
      rcases hsideF with ⟨sF, hsFw, hidF⟩ | ⟨nF, hnF, hb2F, sF, hsF, hgrpF, hidF⟩
      · have hbox := hlookup execution hwf packed hpacked hselected hpart hposF hsFw
        refine ⟨Box.mk sF.id sF.role.id _ sF.parent sF.exclusive, ?_, hports.1⟩
        have hidF' : sF.id = mroute.fromId := hidF
        rw [show mroute.fromId = sF.id from hidF'.symm]
        exact hbox
      · have hcgNodeF : (componentCandidate execution.graph q.1.1 candidate).nodes.getD
            (RouteImpl.edgeAt run.proper first).tail default = nF := by
          rw [htail, componentCandidate_nodes]
          simp only [componentGraph, List.getD_eq_getElem?_getD, List.getElem?_map, hposF,
            Option.map_some, Option.getD_some]
          rw [hnF]
          rfl
        obtain ⟨rt', pxF, hrt', hx0, hx1, hlastF, hheadF⟩ :=
          hport hrun hi hfirst (by rw [hcgNodeF]; exact hb2F)
        have hrtEq : rt' = native := Option.some.inj (hrt'.symm.trans hnative)
        rw [hrtEq, htail] at hheadF
        rw [htail] at hx0 hx1
        have hheadF' := hheadF (hcondEq.trans hr)
        have hstartF : start = ⟨pxF, run.ys.getD edge.tail 0⟩ :=
          Option.some.inj (hstart.symm.trans hheadF')
        obtain ⟨bF, hbFlookup, hbFbound⟩ :=
          hmarker execution hwf hfp hbottom hanchor packed hpacked hselected hrun hpart
            hposF hnF hb2F hsF hgrpF hcomp ⟨hx0, hx1⟩
        refine ⟨bF, ?_, ?_⟩
        · have hidF' : sF.id = mroute.fromId := hidF
          rw [show mroute.fromId = sF.id from hidF'.symm]
          exact hbFlookup
        · rw [hstartF]
          exact hbFbound
    have htoOut : ∃ toBox : Box,
        res.scene.layoutDump.box? mroute.toId = some toBox ∧
        Validator.onBoundary (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY
          finish) toBox.rect := by
      rcases hsideT with ⟨sT, hsTw, hidT⟩ | ⟨nT, hnT, hb2T, sT, hsT, hgrpT, hidT⟩
      · have hbox := hlookup execution hwf packed hpacked hselected hpart hposTt hsTw
        refine ⟨Box.mk sT.id sT.role.id _ sT.parent sT.exclusive, ?_, hports.2⟩
        have hidT' : sT.id = mroute.toId := hidT
        rw [show mroute.toId = sT.id from hidT'.symm]
        exact hbox
      · obtain ⟨qxT, hy0, hy1, hheadT, hlastT⟩ :=
          X_flat_head_port_on_ys hrun hi hfirst hlast hnative
        rw [hhead] at hheadT hlastT hy0 hy1
        have hlastT' := hlastT (hcondEq.trans hr)
        have hfinishT : finish = ⟨qxT, run.ys.getD edge.head 0⟩ :=
          Option.some.inj (hfinish.symm.trans hlastT')
        obtain ⟨bT, hbTlookup, hbTbound⟩ :=
          hmarker execution hwf hfp hbottom hanchor packed hpacked hselected hrun hpart
            hposTt hnT hb2T hsT hgrpT hcomp ⟨hy0, hy1⟩
        refine ⟨bT, ?_, ?_⟩
        · have hidT' : sT.id = mroute.toId := hidT
          rw [show mroute.toId = sT.id from hidT'.symm]
          exact hbTlookup
        · rw [hfinishT]
          exact hbTbound
    obtain ⟨fromBox, hfromLookup, hfromBound⟩ := hfromOut
    obtain ⟨toBox, htoLookup, htoBound⟩ := htoOut
    refine ⟨Route.mk mroute.id mroute.fromId mroute.toId mroute.orthogonal
        (native.points.map (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY)),
      _, _, fromBox, toBox, hscene0, ?_, ?_, hfromLookup, htoLookup, hfromBound, htoBound⟩
    · simp only [List.head?_map, hstart, Option.map_some]
    · simp only [List.getLast?_map, hfinish, Option.map_some]
  · simp only [hcondEq, hr] at hports
    have horigT : edge.original.tail = edge.head := by simp [Edge.original, hr]
    obtain ⟨wF, hposFo, hsideF⟩ := hF
    have hposF : q.1.1[edge.head]? = some wF := by rw [← horigT]; exact hposFo
    obtain ⟨wT, hposTo, hsideT⟩ := hT
    have horigH : edge.original.head = edge.tail := by simp [Edge.original, hr]
    have hposTt : q.1.1[edge.tail]? = some wT := by rw [← horigH]; exact hposTo
    have hfromOut : ∃ fromBox : Box,
        res.scene.layoutDump.box? mroute.fromId = some fromBox ∧
        Validator.onBoundary (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY
          start) fromBox.rect := by
      rcases hsideF with ⟨sF, hsFw, hidF⟩ | ⟨nF, hnF, hb2F, sF, hsF, hgrpF, hidF⟩
      · have hbox := hlookup execution hwf packed hpacked hselected hpart hposF hsFw
        refine ⟨Box.mk sF.id sF.role.id _ sF.parent sF.exclusive, ?_, hports.1⟩
        have hidF' : sF.id = mroute.fromId := hidF
        rw [show mroute.fromId = sF.id from hidF'.symm]
        exact hbox
      · obtain ⟨qxT, hy0, hy1, hheadT, hlastT⟩ :=
          X_flat_head_port_on_ys hrun hi hfirst hlast hnative
        rw [hhead] at hheadT hy0 hy1
        have hheadT' := hheadT (hcondEq.trans hr)
        have hstartF : start = ⟨qxT, run.ys.getD edge.head 0⟩ :=
          Option.some.inj (hstart.symm.trans hheadT')
        obtain ⟨bF, hbFlookup, hbFbound⟩ :=
          hmarker execution hwf hfp hbottom hanchor packed hpacked hselected hrun hpart
            hposF hnF hb2F hsF hgrpF hcomp ⟨hy0, hy1⟩
        refine ⟨bF, ?_, ?_⟩
        · have hidF' : sF.id = mroute.fromId := hidF
          rw [show mroute.fromId = sF.id from hidF'.symm]
          exact hbFlookup
        · rw [hstartF]
          exact hbFbound
    have htoOut : ∃ toBox : Box,
        res.scene.layoutDump.box? mroute.toId = some toBox ∧
        Validator.onBoundary (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY
          finish) toBox.rect := by
      rcases hsideT with ⟨sT, hsTw, hidT⟩ | ⟨nT, hnT, hb2T, sT, hsT, hgrpT, hidT⟩
      · have hbox := hlookup execution hwf packed hpacked hselected hpart hposTt hsTw
        refine ⟨Box.mk sT.id sT.role.id _ sT.parent sT.exclusive, ?_, hports.2⟩
        have hidT' : sT.id = mroute.toId := hidT
        rw [show mroute.toId = sT.id from hidT'.symm]
        exact hbox
      · have hcgNodeT : (componentCandidate execution.graph q.1.1 candidate).nodes.getD
            (RouteImpl.edgeAt run.proper first).tail default = nT := by
          rw [htail, componentCandidate_nodes]
          simp only [componentGraph, List.getD_eq_getElem?_getD, List.getElem?_map, hposTt,
            Option.map_some, Option.getD_some]
          rw [hnT]
          rfl
        obtain ⟨rt', pxF, hrt', hx0, hx1, hlastF, hheadF⟩ :=
          hport hrun hi hfirst (by rw [hcgNodeT]; exact hb2T)
        have hrtEq : rt' = native := Option.some.inj (hrt'.symm.trans hnative)
        rw [hrtEq, htail] at hlastF
        rw [htail] at hx0 hx1
        have hlastF' := hlastF (hcondEq.trans hr)
        have hfinishT : finish = ⟨pxF, run.ys.getD edge.tail 0⟩ :=
          Option.some.inj (hfinish.symm.trans hlastF')
        obtain ⟨bT, hbTlookup, hbTbound⟩ :=
          hmarker execution hwf hfp hbottom hanchor packed hpacked hselected hrun hpart
            hposTt hnT hb2T hsT hgrpT hcomp ⟨hx0, hx1⟩
        refine ⟨bT, ?_, ?_⟩
        · have hidT' : sT.id = mroute.toId := hidT
          rw [show mroute.toId = sT.id from hidT'.symm]
          exact hbTlookup
        · rw [hfinishT]
          exact hbTbound
    obtain ⟨fromBox, hfromLookup, hfromBound⟩ := hfromOut
    obtain ⟨toBox, htoLookup, htoBound⟩ := htoOut
    refine ⟨Route.mk mroute.id mroute.fromId mroute.toId mroute.orthogonal
        (native.points.map (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY)),
      _, _, fromBox, toBox, hscene0, ?_, ?_, hfromLookup, htoLookup, hfromBound, htoBound⟩
    · simp only [List.head?_map, hstart, Option.map_some]
    · simp only [List.getLast?_map, hfinish, Option.map_some]
    }
  simp only at hscene
  rcases hscene with hscene | _hcorr
  · exact hsuff hscene
  -- Corridor case is second: resplit the corridor route via route_cases.
  case inr =>
    obtain ⟨_pts, _hcor, _hrouteC⟩ := _hcorr
    obtain ⟨_x, _y₀, _y₁, _hlt, _hptsEq⟩ := _hcor
    have _hk' : edge.decl < inp.routes.length :=
      (List.getElem?_eq_some_iff.mp hrouteD).1
    have _hstraight := sceneOf_routes_getElem? execution.params inp o execution.lines
      execution.straightAcc execution.measured edge.decl _hk'
    rw [← execution.scene_eq] at _hstraight
    rw [ExactStraighten.straight_canvasH execution] at _hstraight
    have _hgetD : execution.straightAcc.routes.getD edge.decl [] = _pts :=
      ExactStraighten.straight_points_of_scene execution _hrouteC
    have hpts : execution.straightAcc.routes[edge.decl]? = some _pts := by
      have _hne : _pts ≠ [] := by
        rw [_hptsEq]
        intro _hcon
        simp at _hcon
      have _hgd : (execution.straightAcc.routes[edge.decl]?.getD []) = _pts := by
        have _h := _hgetD
        rw [Array.getD_eq_getD_getElem?] at _h
        exact _h
      cases _ho : execution.straightAcc.routes[edge.decl]? with
      | none =>
        simp only [_ho, Option.getD_none] at _hgd
        exact absurd _hgd.symm _hne
      | some _v =>
        simp only [_ho, Option.getD_some] at _hgd
        exact congrArg Option.some _hgd
    rcases ExactStraighten.route_cases execution X_componentRun_normalized_source hpts with _hpackedPts | hinst
    · -- (P) packed corridor: the packed route equals the corridor points, so the
      -- placed-points bridge turns _hrouteC into the first-disjunct form reused via hsuff.
      have _heP := (List.getElem?_eq_some_iff.mp hedge).2
      have _hgetP := X_placeComponentExact_route_entry_of_producer hrun 0 loops i hi hloopCg
      have _hpartRoutes : q.1.2.routes =
          (placeComponentExact execution.params (componentCandidate execution.graph q.1.1 candidate)
            run 0 execution.measured loops).routes := by
        rw [hpart]
      rw [← _hpartRoutes] at _hgetP
      have _hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
        rw [_hpartRoutes]
        exact ExactStraighten.placeComponentExact_routes_decls_nodup execution.params
          (componentCandidate execution.graph q.1.1 candidate) run 0
          execution.measured loops hnd
      have _hrouteSize : edge.decl < execution.componentsAcc.routes.size := by
        rw [← packAcc_routes_size execution.packed_eq]
        exact (Array.getElem?_eq_some_iff.mp _hpackedPts).1
      have _hpackedRoute := ExactStraighten.actual_components_packAcc_routes_getD
        (by rfl) execution.components_eq (exactGraph_decls_nodup execution.graph0_eq execution.graph_eq)
        packed execution.packed_eq hpacked c q hselected i _ _ [] _hgetP _hpartNodup (by rw [_heP]; exact _hrouteSize)
      have _hnativeGet := (List.getElem?_eq_some_iff.mp hnative).2
      have _hmodelEq : inp.routes[edge.decl]'_hk' = mroute0 :=
        Option.some.inj ((List.getElem?_eq_getElem _hk').symm.trans hmodelRoute)
      have _hbridge : execution.packedAcc.routes.getD edge.decl [] =
          execution.straightAcc.routes.getD edge.decl [] := by
        rw [_hgetD, Array.getD_eq_getD_getElem?, _hpackedPts, Option.getD_some]
      have _hneg : -(placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
          run execution.measured loops).minY =
          0 - (placeBoundsX execution.params (componentCandidate execution.graph q.1.1 candidate)
          run execution.measured loops).minY := by omega
      rw [_heP, _hbridge] at _hpackedRoute
      rw [_hneg] at _hpackedRoute
      rw [_hmodelEq] at _hstraight
      rw [_hpackedRoute, routePointTransport_eq, _hnativeGet] at _hstraight
      exact hsuff _hstraight
    · obtain ⟨tailKey, headKey, tailRect, headRect, span,
        _hEdgeTailLt, _hEdgeHeadLt, htailLt, hheadLt, hKeyT, hKeyH,
        htailRect, hheadRect, h0tail, h0head,
        _htxT, _htwT, _htxH, _htwH, hxT1, hxT2, hxH1, hxH2, hy0eq, hy1eq, hptsEq⟩ :=
        execution.installed_part_edge_rects hinst hselected hedge rfl hrun hpart
      have hptsEq2 : _pts = [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩] := by
        rw [hptsEq]
        rfl
      have hmEq : mroute = mroute0 :=
        (Option.some.inj (hmodelRoute.symm.trans hrouteD)).symm
      have hkeys : ∃ sF sT : ModelBox, inp.boxes[tailKey]? = some sF ∧ sF.id = mroute.fromId ∧
        inp.boxes[headKey]? = some sT ∧ sT.id = mroute.toId := by
        have hidsEq := execution.installed_part_edge_key_ids hinst hselected hedge rfl hrun hpart (route := mroute) hrouteD htailLt hheadLt hKeyT hKeyH
        obtain ⟨hsFid, hsTid⟩ := hidsEq
        have hsourceTail : inp.boxes[tailKey]? = some (inp.boxes[tailKey]'htailLt) :=
          List.getElem?_eq_getElem htailLt
        have hsourceHead : inp.boxes[headKey]? = some (inp.boxes[headKey]'hheadLt) :=
          List.getElem?_eq_getElem hheadLt
        exact ⟨_, _, hsourceTail, hsFid, hsourceHead, hsTid⟩
      obtain ⟨sF, sT, hsourceTail, hsFid, hsourceHead, hsTid⟩ := hkeys
      have htailGetD : execution.packedAcc.rects.getD tailKey default = tailRect := by
        simp only [Array.getD_eq_getD_getElem?, htailRect, Option.getD_some]
      have hheadGetD : execution.packedAcc.rects.getD headKey default = headRect := by
        simp only [Array.getD_eq_getD_getElem?, hheadRect, Option.getD_some]
      have hlookupTail := Xc_source_box_lookup_of_box_ids_nodupX execution hids hsourceTail
      have hlookupHead := Xc_source_box_lookup_of_box_ids_nodupX execution hids hsourceHead
      rw [htailGetD] at hlookupTail
      rw [hheadGetD] at hlookupHead
      have hsFid0 : sF.id = mroute0.fromId := by
        rw [hmEq] at hsFid; exact hsFid
      have hsTid0 : sT.id = mroute0.toId := by
        rw [hmEq] at hsTid; exact hsTid
      have hb := corridor_onBoundary_acc h0tail h0head ⟨hxT1, hxT2⟩ ⟨hxH1, hxH2⟩ hy0eq hy1eq
      have hbScene := corridor_onBoundary_scene (margin := execution.params.canvasMargin)
        (d := o.direction) (h := execution.packedAcc.canvasH) hb
      have hptsMap : (_pts.map fun p => shiftPoint execution.params.canvasMargin
        execution.params.canvasMargin
        (orientPoint o.direction execution.packedAcc.canvasH p)) =
        [(shiftPoint execution.params.canvasMargin execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH ⟨span.column, span.top⟩)),
         (shiftPoint execution.params.canvasMargin execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH ⟨span.column, span.bottom⟩))] := by
        rw [hptsEq2]
        simp only [List.map_cons, List.map_nil]
      refine ⟨Route.mk mroute0.id mroute0.fromId mroute0.toId mroute0.orthogonal
        (_pts.map fun p => shiftPoint execution.params.canvasMargin
          execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH p)),
        (shiftPoint execution.params.canvasMargin execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH ⟨span.column, span.top⟩)),
        (shiftPoint execution.params.canvasMargin execution.params.canvasMargin
          (orientPoint o.direction execution.packedAcc.canvasH ⟨span.column, span.bottom⟩)),
        { id := sF.id, role := sF.role.id,
          rect :=
            shiftRect execution.params.canvasMargin execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH tailRect),
          parent := sF.parent, exclusive := sF.exclusive },
        { id := sT.id, role := sT.role.id,
          rect :=
            shiftRect execution.params.canvasMargin execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH headRect),
          parent := sT.parent, exclusive := sT.exclusive },
        _hrouteC, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hptsMap]; rfl
      · rw [hptsMap]; rfl
      · rw [← hsFid0]; exact hlookupTail
      · rw [← hsTid0]; exact hlookupHead
      · exact hbScene.1
      · exact hbScene.2
end PipelineImpl
end Layered
end Elegant


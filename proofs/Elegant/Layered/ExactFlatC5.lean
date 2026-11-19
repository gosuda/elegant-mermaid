import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.FamilyC5B
import Elegant.Layered.FamilyC5Measured
import Elegant.Layered.FlatGroupEndpointsProof
import Elegant.Layered.GroupAnchorFactsProof
import Elegant.Layered.GroupAnchors
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.FrameClearanceFacts
set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact flat C5: `FlatC5B (layoutX exactIds)`.

The probe `wip/Probe/ExactFlatC5Probe.lean` executes `layoutX ["hub"]` on a
well-formed framed-parents input whose exact hub has fixed width `100` with
`10` incident routes (`width / portGap = 100 / 512 < 1`, ten times over the
nominal port capacity) and reports `c5 = true` with every route endpoint on
its box boundary (hub ports at `20831, 20840, ..., 20912`, all inside hub
rect `x = 20822, w = 100`). No port-capacity guard is needed: `portCoord`
places port `j` of `n` at `x - w / 2 + fdiv ((j + 1) * w) (n + 1)`, which lies
in `[x - w / 2, x + w / 2]` for every `0 <= j < n` however small `w` is, so an
exact box that skips `sizeProperPortsX` widening still carries every port on
its top/bottom edge.

Proof shape: `flatC5B_layoutX_of_endpointsX` reduces the target to the
execution seam `FlatGroupEndpointsX` (mirroring `flatC5B_of_endpoints`);
`layoutX_ids` and `route_component_sourceX` are proved by replaying the plain
proofs against `SceneExecutionX` (the scene assembly `sceneOf`/`packAcc` is
shared, only the graph/run phases differ); the anchor row reuses the proved
plain `groupAnchorSelection` on `execution.graph0_eq`. The four remaining
rows are residual defs, each about one exact-pipeline phase and each consumed
by `flatGroupEndpointsX`: the executed port row, the bottom-boundary row, the
rank-closure row, and the per-edge emission assembly (which covers self-loop
edges as well, so the assembly needs no case split). -/

/-- Exact id preservation: a successful `layoutX` keeps the box and route id
lists, by the same `sceneOf` projection the plain `layout_ids` uses. -/
theorem layoutX_ids {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res) :
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
    res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  unfold layoutX at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have h := Except.ok.inj h
    subst h
    simp only [sceneOf, List.map_map]
    exact ⟨zipIdx_map_comp (·.id) inp.boxes 0, zipIdx_map_comp (·.id) inp.routes 0⟩

/-- The exact graph covers every route index: edges are untouched by
`exactGraph`, so the measured decl range transfers verbatim. -/
theorem exactGraph_decl_rangeX {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {g0 g : Graph} (h0 : measuredGraph P inp o lines = .ok g0)
    (h : exactGraph P exactIds inp o measured g0 = .ok g) :
    g.edges.map (·.decl) = List.range' 0 inp.routes.length := by
  rw [exactGraph_edges h, measuredGraph_decl_range h0]

/-- Exact route-component source: every input route index resolves through the
exact graph to a selected component, an exact run, exact loops, and a placed
part, replaying `SceneExecution.route_component_source` with
`actual_components_parts_geometryX` and `componentRunX_route_of_index`. -/
theorem SceneExecutionX.route_component_sourceX {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} (hkey : key < inp.routes.length) :
    ∃ (packed : Pack.State) (c : Nat) (q : (List Nat × Part) × Rect)
      (candidate : Nat) (run : Run) (loops : List (Nat × LoopPlacement)) (area : Int)
      (i : Nat) (edge : Edge),
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
      (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q ∧
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph q.1.1 candidate) execution.measured
        (candidateOrder candidate) = .ok run ∧
      componentLoops execution.params
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        = .ok loops ∧
      q.1.2 = { placeComponentExact execution.params
        (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
        loops with area := area } ∧
      (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge ∧
      edge.decl = key := by
  have hdecl : key ∈ execution.graph.edges.map (·.decl) := by
    rw [exactGraph_decl_rangeX execution.graph0_eq execution.graph_eq]
    exact List.mem_range'.mpr ⟨key, hkey, by omega⟩
  obtain ⟨globalEdge, hglobalEdge, hglobalDecl⟩ := List.mem_map.mp hdecl
  have hglobalBounds := sceneExecutionX_edges_bounded execution globalEdge
    (List.mem_append_left _ hglobalEdge)
  obtain ⟨component, hcomponent, htail⟩ :=
    components_cover hglobalBounds.1 (sceneExecutionX_edges_bounded execution)
  obtain ⟨hparts, hall⟩ := actual_components_parts_geometryX (by rfl)
    execution.components_eq
  have hcomponentPart : component ∈ execution.componentsAcc.parts.map (·.1) := by
    rw [hparts]
    exact hcomponent
  obtain ⟨part, hpartMember, hpartComponent⟩ := List.mem_map.mp hcomponentPart
  obtain ⟨candidate, _, run, loops, area, _, _, _, hrun, hloops, hpart⟩ :=
    hall part hpartMember
  have htailPart : globalEdge.tail ∈ part.1 := by
    simpa only [hpartComponent] using htail
  have hrawDecl : globalEdge.decl ∈ (componentGraph execution.graph part.1).edges.map (·.decl) := by
    unfold componentGraph
    dsimp only
    apply List.mem_map.mpr
    refine ⟨Edge.mk (part.1.idxOf globalEdge.tail) (part.1.idxOf globalEdge.head)
      globalEdge.minLen globalEdge.decl globalEdge.reversed, ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨globalEdge, List.mem_filter.mpr
      ⟨hglobalEdge, List.contains_iff_mem.mpr htailPart⟩, rfl⟩
  rw [← componentCandidate_decls execution.graph part.1 candidate] at hrawDecl
  obtain ⟨edge, hedgeMember, hedgeDecl⟩ := List.mem_map.mp hrawDecl
  obtain ⟨i, hedge⟩ := List.mem_iff_getElem?.mp hedgeMember
  obtain ⟨packed, hpacked, _⟩ := packAcc_components_disjoint execution.packed_eq
  obtain ⟨c, hpartIndex⟩ := List.mem_iff_getElem?.mp hpartMember
  have hc := (List.getElem?_eq_some_iff.mp hpartIndex).1
  have hpackedCount : packed.boxes.length = execution.componentsAcc.parts.length := by
    simpa only [List.length_map] using Pack.pack_count hpacked
  have hpositionBound : c < packed.boxes.length := by omega
  let position := packed.boxes[c]'hpositionBound
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
      some (part, position) := List.getElem?_zip_eq_some.mpr
    ⟨hpartIndex, List.getElem?_eq_getElem hpositionBound⟩
  exact ⟨packed, c, (part, position), candidate, run, loops, area, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hedgeDecl.trans hglobalDecl⟩


/-- The flat endpoint seam for the exact pipeline: every successful exact
execution on a well-formed framed-parents input satisfies the measured
group-endpoint invariant. This mirrors `FlatGroupEndpoints`, with
`SceneExecutionX` in place of `SceneExecution`. -/
def FlatGroupEndpointsX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult},
    WellFormed (inputModel inp o) → framedParents inp = true →
    SceneExecutionX exactIds inp o res → GroupEndpointInvariantMeasured inp res.scene

/-- Reduction: the endpoint seam plus id preservation give `FlatC5B` for
`layoutX`, mirroring `flatC5B_of_endpoints`. -/
theorem flatC5B_layoutX_of_endpointsX {exactIds : List String}
    (hflat : FlatGroupEndpointsX exactIds) : FlatC5B (layoutX exactIds) := by
  intro inp o res hwf hfp hb
  obtain ⟨execution⟩ := layoutX_sceneExecution hb
  have hids := layoutX_ids hb
  exact ⟨hids.1, hids.2, hflat hwf hfp execution⟩

/-- Residual, exact executed port row: for a successful `componentRunX` whose
chain-tail endpoint is a `border = 2` bottom marker, the emitted route's
tail-side point is the flat port `⟨px, run.ys v⟩` with `px` inside the
marker's box span. This is the one-phase exact counterpart of
`GroupTailPortOnYs`. It holds for executed exact layouts because the port
x-coordinate still comes from `portCoord`, which divides the (possibly small)
exact width by the port count and therefore stays inside the box span, and
because `sizeProperPortsX`/`coordinateGraphX` preserve the zero-height
transfer that puts the tail point at `boxRect.y + boxRect.h = run.ys v`. -/
def X_TailPort (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run →
    ∀ {i : Nat} (_hi : i < cg.edges.length) {first : Nat}
      (_hfirst : (RouteImpl.edgesOf run.proper i).head? = some first),
      (cg.nodes.getD (RouteImpl.edgeAt run.proper first).tail default).border = 2 →
      ∃ (rt : EdgeRoute) (px : Int),
        run.routes[i]? = some rt ∧
        (RouteImpl.boxRect run.proper run.xs run.ys
            (RouteImpl.edgeAt run.proper first).tail).x ≤ px ∧
        px ≤ (RouteImpl.boxRect run.proper run.xs run.ys
            (RouteImpl.edgeAt run.proper first).tail).x +
          (RouteImpl.boxRect run.proper run.xs run.ys
            (RouteImpl.edgeAt run.proper first).tail).w ∧
        ((cg.edges.map (·.reversed)).getD i false = true →
          rt.points.getLast? = some ⟨px,
            run.ys.getD (RouteImpl.edgeAt run.proper first).tail 0⟩) ∧
        ((cg.edges.map (·.reversed)).getD i false = false →
          rt.points.head? = some ⟨px,
            run.ys.getD (RouteImpl.edgeAt run.proper first).tail 0⟩)

/-- Residual, exact bottom-boundary row: a route port of a `border = 2` bottom
marker lies on the frame of its paired `border = -2` top marker in an
executed exact run. This is the one-phase exact counterpart of
`GroupBottomBoundaryFacts`, stated over the measured graph plus the exact
graph equation. It holds for executed exact layouts because `reserveExactRanks`
shifts each rank's `ys`/`top` entries uniformly, so the port point and the top
frame move together and the boundary relation is preserved. -/
def X_BottomBoundary (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {v t : Nat} {px : Int},
    ((componentCandidate graph comp candidate).nodes.getD v default).border = 2 →
    ((componentCandidate graph comp candidate).nodes.getD t default).border = -2 →
    ((componentCandidate graph comp candidate).nodes.getD v default).decl =
      ((componentCandidate graph comp candidate).nodes.getD t default).decl →
    (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w →
    Validator.onBoundary ⟨px, run.ys.getD v 0⟩
      (frameRect P (componentCandidate graph comp candidate) run t)

/-- Residual, exact rank-closure row: every executed exact node whose cluster
path contains a `-2` group top's declaration ranks at or below the top. This
is the one-phase exact counterpart of `GroupTopSubtreeRankProper`. It holds
for executed exact layouts because ranking consumes only borders, decls,
cluster paths, and edges, all of which `exactGraph` preserves
(`exactGraph_node_key`, `exactGraph_edges`), so the exact ranking graph has
the same closure as the measured one. -/
def X_TopRank (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph0 graph : Graph}
    {measured : List MeasuredLabel},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {v : Nat} {nd : Node},
    (componentCandidate graph comp candidate).nodes[v]? = some nd →
    nd.border = -2 →
    v < (componentCandidate graph comp candidate).nodes.length →
    ∀ {i : Nat}, i < run.proper.nodes.length →
    (run.proper.nodes.getD i default).node.clusterPath.contains nd.decl = true →
    rk run.proper.rank v ≤ rk run.proper.rank i

/-- Residual, exact per-edge anchor resolution: the endpoints of every proper
candidate edge of the exact graph resolve either to the input box carrying
the endpoint id or to the synthetic `border = 2` bottom marker of the group
box carrying it. This mirrors `SceneExecution.edge_endpoint_anchors` with the
exact graph in place of the measured graph. It holds for executed exact
layouts because `exactGraph` leaves the edge list identical
(`exactGraph_edges`) and preserves every node's decl, border, and cluster
path (`exactGraph_node_key`), so candidate construction and the alias-edge
identification resolve exactly as in the plain pipeline. -/
def X_EdgeAnchors (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (_hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      = .ok loops)
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    {i : Nat} {edge : Edge}
    (_hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (_hne : edge.tail ≠ edge.head),
    ∃ mroute : ModelRoute,
      inp.routes[edge.decl]? = some mroute ∧
      EndpointAnchor inp execution.graph q.1.1 edge.original.tail mroute true ∧
      EndpointAnchor inp execution.graph q.1.1 edge.original.head mroute false
/-- Residual, exact per-edge emission assembly: for one selected exact
component, one exact run, and one ordinary (non-self-loop) candidate edge,
the scene route emitted at the edge's decl attaches both endpoints to the
boundary of its endpoint dump boxes. This mirrors
`SceneExecution.chosen_part_group_c5_alias`, taking the exact row facts as
premises. Self-loop edges take a separate loop-row path. It holds for
executed exact layouts because port x-coordinates stay inside exact spans
(`portCoord` divides by the port count), `ys` shifts move boxes and route
endpoints together, and the anchor rows supply the same dump-box lookups as
in the plain pipeline. -/
def X_ChosenPart (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hrank : X_TopRank exactIds) (_hbottom : X_BottomBoundary exactIds)
    (_hport : X_TailPort exactIds) (_hanchor : GroupAnchorSelection)
    (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (_hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      = .ok loops)
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    {i : Nat} {edge : Edge}
    (_hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (_hne : edge.tail ≠ edge.head),
    {mroute : ModelRoute} → (_hrouteD : inp.routes[edge.decl]? = some mroute) →
    (_hF : EndpointAnchor inp execution.graph q.1.1 edge.original.tail mroute true) →
    (_hT : EndpointAnchor inp execution.graph q.1.1 edge.original.head mroute false) →
    ∃ (out : Route) (start finish : Point) (fromBox toBox : Box),
      res.scene.routes[edge.decl]? = some out ∧
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect

/-- Reverse key lookup through `exactGraph`: every exact-graph node comes
from the measured-graph node at the same index with the same key fields. -/
private theorem X_node_key_rev {P : Params} {exactIds : List String} {inp : Input}
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

/-- Endpoint case split on prepared boxes (copy of the private
`endpoint_cases_local` of `FlatGroupEndpointsProof.lean`). -/
private theorem X_endpoint_cases {boxes : List ModelBox} (s : Bool) (i j : Nat) :
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

/-- Component lookup at the position of a member (copy of the private
`comp_idxOf_lookup` of `FlatGroupEndpointsProof.lean`). -/
private theorem X_comp_idxOf_lookup {comp : List Nat} {x : Nat} (hmem : x ∈ comp) :
    comp[comp.idxOf x]? = some x :=
  (List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem)).trans
    (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)))

/-- Exact candidate edges resolve to model identity: replay of
`componentCandidate_model_endpoint_source` with the measured equation on
`graph0`; the global edge transfers through `exactGraph_edges` and the
semantic source is graph-agnostic. -/
theorem X_candidate_model_endpoint_source
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel} {graph0 graph : Graph} {exactIds : List String}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {component : List Nat} {candidate : Nat} {edge : Edge}
    (hedge : edge ∈ (componentCandidate graph component candidate).edges) :
    ∃ index route raw source target,
      inp.routes[index]? = some route ∧ edgeOf inp route index = .ok raw ∧
      edge.decl = index ∧
      inp.boxes[raw.tail]? = some source ∧ source.id = route.fromId ∧
      inp.boxes[raw.head]? = some target ∧ target.id = route.toId ∧
      let prepared := inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
        else box
      let aliased := Compound.aliasEdge prepared raw
      edge.original = { aliased with
        tail := component.idxOf aliased.tail, head := component.idxOf aliased.head } := by
  obtain ⟨globalEdge, hglobal, _, hsemantic⟩ :=
    componentCandidate_semantic_source hedge
  have hglobal0 : globalEdge ∈ graph0.edges := by
    rw [exactGraph_edges hgraphX] at hglobal
    exact hglobal
  obtain ⟨index, route, raw, hroute, hraw, halias⟩ :=
    measuredGraph_edge_source hgraph0 hglobal0
  obtain ⟨hdecl, hreversed, source, target, hsource, hsourceId, htarget, htargetId⟩ :=
    edgeOf_semantic_endpoints hraw
  have hglobalReversed : globalEdge.reversed = false := by
    rw [halias]; exact hreversed
  have horiginal : globalEdge.original = globalEdge := by
    cases globalEdge with
    | mk tail head minLen decl reversed =>
      cases hglobalReversed
      rfl
  have hdecl' : edge.decl = index := by
    calc
      edge.decl = globalEdge.decl := by
        simpa only [Edge.original_decl] using congrArg Edge.decl hsemantic
      _ = raw.decl := by rw [halias]; rfl
      _ = index := hdecl
  refine ⟨index, route, raw, source, target, hroute, hraw, hdecl',
    hsource, hsourceId, htarget, htargetId, ?_⟩
  dsimp only
  rw [horiginal, halias] at hsemantic
  exact hsemantic

/-- Transport an endpoint witness across key-equal nodes: only `decl` and
`border` are observed. -/
private theorem X_endpointWitness_transport {inp : Input} {r : ModelRoute}
    {isFrom : Bool} {v : Nat} {n n0 : Node}
    (hkd : n.decl = n0.decl) (hkb : n.border = n0.border)
    (h : endpointWitness inp r isFrom v n0) : endpointWitness inp r isFrom v n := by
  unfold endpointWitness at h ⊢
  obtain ⟨b, hb, hidb, hside⟩ := h
  refine ⟨b, by rwa [hkd], hidb, ?_⟩
  rcases hside with ⟨hb0, hr⟩ | ⟨hbb, hr⟩
  · exact Or.inl ⟨by rwa [hkb], hr⟩
  · rcases hbb with h2 | h2
    · exact Or.inr ⟨Or.inl (by rwa [hkb]), hr⟩
    · exact Or.inr ⟨Or.inr (by rwa [hkb]), hr⟩

/-- Bottom-node enumeration (copy of the private `bottomNodesOf` of
`GroupAnchors.lean`). -/
private def X_bottomNodesOf (full sub : List ModelBox) (off : Nat) : List Node :=
  (sub.zipIdx off).filterMap fun q =>
    if q.1.role == .group then
      some {
        decl := q.2, w := 0, h := 0
        clusterPath := Compound.path full q.1 ++ [q.2], border := 2 }
    else none

/-- Position/identity of enumerated bottom nodes (copy of the private
`bottomNodesOf_getElem?_decl` of `GroupAnchors.lean`). -/
private theorem X_bottomNodesOf_getElem?_decl {full sub : List ModelBox} {off k : Nat}
    {x : Node} (hx : (X_bottomNodesOf full sub off)[k]? = some x) :
    ∃ d g, sub[d]? = some g ∧ g.role = .group ∧ x.decl = d + off ∧
      ((sub.take d).filter fun b => b.role == .group).length = k := by
  induction sub generalizing off k with
  | nil => simp [X_bottomNodesOf] at hx
  | cons b bs ih =>
    unfold X_bottomNodesOf at hx
    rw [List.zipIdx_cons] at hx
    by_cases hb : b.role = .group
    · have hbeq : (b.role == .group) = true := beq_iff_eq.mpr hb
      simp only [hbeq, ↓reduceIte, List.filterMap_cons] at hx
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨0, b, List.getElem?_cons_zero, hb, by simp, by simp⟩
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨d, g, hdg, hgg, hdecl, hcount⟩ := ih hx
        refine ⟨d + 1, g, ?_, hgg, ?_, ?_⟩
        · simpa using hdg
        · have : d + 1 + off = d + (off + 1) := by omega
          rw [this]; exact hdecl
        · have htake : ((b :: bs).take (d + 1)).filter
              (fun b => b.role == .group) =
            b :: (bs.take d).filter (fun b => b.role == .group) := by
            rw [List.take_succ_cons]
            simp [hb]
          rw [htake, List.length_cons, hcount]
    · have hbf : (b.role == .group) = false := by
        cases hz : (b.role == .group) with
        | true => exact absurd (beq_iff_eq.mp hz) hb
        | false => rfl
      simp only [hbf, Bool.false_eq_true, ↓reduceIte, List.filterMap_cons] at hx
      obtain ⟨d, g, hdg, hgg, hdecl, hcount⟩ := ih hx
      refine ⟨d + 1, g, ?_, hgg, ?_, ?_⟩
      · simpa using hdg
      · have : d + 1 + off = d + (off + 1) := by omega
        rw [this]; exact hdecl
      · have htake : ((b :: bs).take (d + 1)).filter
            (fun b => b.role == .group) =
            (bs.take d).filter (fun b => b.role == .group) := by
            rw [List.take_succ_cons]
            have hbf2 : (b.role == .group) = false := hbf
            simp only [hbf2, Bool.false_eq_true, ↓reduceIte, List.filter_cons]
        rw [htake, hcount]

/-- Counting monotone take fact (copy of the private `countP_take_add_one` of
`GroupAnchors.lean`). -/
private theorem X_countP_take_add_one {α : Type} (p : α → Bool)
    {l : List α} {i n : Nat} (hn : n ≠ 0) (hi : i < l.length) (hpi : p l[i] = true) :
    (l.take i).countP p + 1 ≤ (l.take (i + n)).countP p := by
  have hsplit : (l.take (i + n)).countP p =
      (l.take i).countP p + ((l.drop i).take n).countP p := by
    rw [List.take_add, List.countP_append]
  rw [hsplit]
  have hwindow : l[i] ∈ (l.drop i).take n := by
    have h1 : (l.drop i)[0]? = some l[i] := by
      rw [List.getElem?_drop, Nat.add_zero]
      exact List.getElem?_eq_getElem hi
    have h2 : ((l.drop i).take n)[0]? = (l.drop i)[0]? := by
      rw [List.getElem?_take]
      simp [Nat.pos_of_ne_zero hn]
    have h0 : ((l.drop i).take n)[0]? = some l[i] := by rw [h2, h1]
    exact List.mem_of_getElem? h0
  have hge : 1 ≤ (((l.drop i).take n).filter p).length := by
    have hmem : p l[i] = true := hpi
    apply List.length_pos_of_mem
    exact List.mem_filter.mpr ⟨hwindow, hmem⟩
  simp only [List.countP_eq_length_filter]
  omega

/-- The bottom node at `Compound.bottomIndex boxes i` declares `i` (copy of
the private `bottom_node_decl` of `GroupAnchors.lean`). -/
private theorem X_bottom_node_decl {boxes : List ModelBox} {pad : Int}
    {titles : List (Int × Int)} {nodes : List Node} (hlen : nodes.length = boxes.length)
    {i j : Nat} {x : Node} {b : ModelBox}
    (hj : j = boxes.length + ((boxes.take i).filter fun b => b.role == .group).length)
    (hx : (Compound.markNodes boxes pad titles nodes)[j]? = some x)
    (hbi : boxes[i]? = some b) (hb : b.role = .group) :
    x.decl = i := by
  rw [markNodes_eq] at hx
  have htopLen : (nodes.zipIdx.map (markOne boxes pad titles)).length = nodes.length := by
    simp [List.length_map, List.length_zipIdx]
  have hjge : (nodes.zipIdx.map (markOne boxes pad titles)).length ≤ j := by
    rw [htopLen, hlen]; omega
  rw [List.getElem?_append_right hjge] at hx
  have hk : j - (nodes.zipIdx.map (markOne boxes pad titles)).length =
      ((boxes.take i).filter fun b => b.role == .group).length := by omega
  rw [hk] at hx
  have hme : markExtras boxes = X_bottomNodesOf boxes boxes 0 := rfl
  rw [hme] at hx
  obtain ⟨d, g, hdg, hgg, hdecl, hcount⟩ := X_bottomNodesOf_getElem?_decl hx
  have hi : i < boxes.length := (List.getElem?_eq_some_iff.mp hbi).1
  have hcntI : ((boxes.take i).filter fun b => b.role == .group).length =
      j - (nodes.zipIdx.map (markOne boxes pad titles)).length := by omega
  have hidi : i = d := by
    rcases Nat.lt_trichotomy i d with hlt | heq | hgt
    · have hbdi : (fun b => b.role == .group) b = true := beq_iff_eq.mpr hb
      have hmono := X_countP_take_add_one (p := fun b => b.role == .group)
        (l := boxes) (i := i) (n := d - i) (Nat.sub_ne_zero_of_lt hlt)
        (by omega) (by
          obtain ⟨_, heq⟩ := List.getElem_of_getElem? hbi
          rw [heq]; exact hbdi)
      have hrewrite : i + (d - i) = d := by omega
      rw [hrewrite, List.countP_eq_length_filter,
        List.countP_eq_length_filter] at hmono
      omega
    · exact heq
    · have hdi : d < boxes.length := (List.getElem?_eq_some_iff.mp hdg).1
      have hgid : (fun b => b.role == .group) g = true := beq_iff_eq.mpr hgg
      have hmono := X_countP_take_add_one (p := fun b => b.role == .group)
        (l := boxes) (i := d) (n := i - d) (Nat.sub_ne_zero_of_lt hgt)
        (by omega) (by
          obtain ⟨_, heq⟩ := List.getElem_of_getElem? hdg
          rw [heq]; exact hgid)
      have hrewrite : d + (i - d) = i := by omega
      rw [hrewrite, List.countP_eq_length_filter,
        List.countP_eq_length_filter] at hmono
      omega
  subst hidi
  simpa using hdecl

/-- Exact node-identity witness (measured-side proof of the private
`model_node_witness` of `GroupAnchors.lean`, run on the prepared node `n0`;
callers transport the conclusion across `X_node_key_rev`). -/
private theorem X_model_node_witness_aux {inp : Input} {r : ModelRoute} (isFrom : Bool)
    {prepared : List ModelBox} {pad : Int} {titles : List (Int × Int)}
    {nodes0 : List Node} {g0 : Graph}
    (hg0 : g0.nodes = nodes0)
    (hlen0 : nodes0.length = prepared.length)
    (hmeta : ∀ (i : Nat) (n : Node), nodes0[i]? = some n → n.decl = i ∧ n.border = 0)
    {j : Nat} {src : ModelBox} (hsrc : inp.boxes[j]? = some src)
    (hbp : prepared[j]? =
      some (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        { src with role := .node } else src))
    (hid : src.id = (if isFrom then r.fromId else r.toId))
    {v : Nat} {n0 : Node}
    (hnode : (Compound.prepare prepared pad titles g0).nodes[v]? = some n0)
    (hvj : v = j) :
    endpointWitness inp r isFrom v n0 := by
  have hjp : j < prepared.length := by
    have := (List.getElem?_eq_some_iff.mp hbp).1
    omega
  have hjn : j < nodes0.length := by rw [hlen0]; exact hjp
  have hi : j < g0.nodes.length := by rw [hg0]; exact hjn
  have hmetaJ := hmeta j (nodes0[j]'hjn) (List.getElem?_eq_getElem hjn)
  have hnodeJ : (Compound.prepare prepared pad titles g0).nodes[j]? = some n0 := by
    rw [← hvj]; exact hnode
  cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) with
  | true =>
    rw [hf] at hbp
    simp only [↓reduceIte] at hbp
    have hbox : prepared[j]? = some { src with role := .node } := hbp
    have hng : ({ src with role := .node } : ModelBox).role ≠ .group := by
      intro hcon; cases hcon
    have hrec := Compound.prepare_plain_node_record prepared pad titles g0 hi
      hbox hng
    have hj0 : g0.nodes[j]'hi = nodes0[j]'hjn := by
      have h1 : g0.nodes[j]? = some (g0.nodes[j]'hi) := List.getElem?_eq_getElem hi
      have h2 : g0.nodes[j]? = some (nodes0[j]'hjn) := by
        rw [hg0]; exact List.getElem?_eq_getElem hjn
      exact Option.some.inj (h1.symm.trans h2)
    have hnEq : n0 = { g0.nodes[j]'hi with
        clusterPath := Compound.path prepared { src with role := .node } } :=
      Option.some.inj (hnodeJ.symm.trans hrec)
    subst hnEq
    refine ⟨src, ?_, hid, Or.inl ⟨by rw [hj0]; exact hmetaJ.2, Or.inr hf⟩⟩
    show inp.boxes[(g0.nodes[j]'hi).decl]? = some src
    rw [hj0, hmetaJ.1]
    exact hsrc
  | false =>
    rw [hf] at hbp
    cases hs : src.role with
    | node =>
      have hbox : prepared[j]? = some src := hbp
      have hng : src.role ≠ .group := by
        rw [hs]; intro hcon; cases hcon
      have hrec := Compound.prepare_plain_node_record prepared pad titles g0 hi
        hbox hng
      have hj0 : g0.nodes[j]'hi = nodes0[j]'hjn := by
        have h1 : g0.nodes[j]? = some (g0.nodes[j]'hi) := List.getElem?_eq_getElem hi
        have h2 : g0.nodes[j]? = some (nodes0[j]'hjn) := by
          rw [hg0]; exact List.getElem?_eq_getElem hjn
        exact Option.some.inj (h1.symm.trans h2)
      have hnEq : n0 = { g0.nodes[j]'hi with
          clusterPath := Compound.path prepared src } :=
        Option.some.inj (hnodeJ.symm.trans hrec)
      subst hnEq
      refine ⟨src, ?_, hid, Or.inl ⟨by rw [hj0]; exact hmetaJ.2, Or.inl hs⟩⟩
      show inp.boxes[(g0.nodes[j]'hi).decl]? = some src
      rw [hj0, hmetaJ.1]
      exact hsrc
    | group =>
      have hbox : prepared[j]? = some src := hbp
      have hrec := Compound.prepare_group_title_record prepared pad titles g0 hi
        hbox hs
      have hj0 : g0.nodes[j]'hi = nodes0[j]'hjn := by
        have h1 : g0.nodes[j]? = some (g0.nodes[j]'hi) := List.getElem?_eq_getElem hi
        have h2 : g0.nodes[j]? = some (nodes0[j]'hjn) := by
          rw [hg0]; exact List.getElem?_eq_getElem hjn
        exact Option.some.inj (h1.symm.trans h2)
      have hnEq : n0 = { g0.nodes[j]'hi with
          clusterPath := Compound.path prepared src ++ [j], border := -2,
          w := (titles.getD j (0, 0)).1,
          h := if (g0.nodes[j]'hi).loopExtent == 0 then (titles.getD j (0, 0)).2 + pad
               else max ((titles.getD j (0, 0)).2 + pad) (g0.nodes[j]'hi).h } :=
        Option.some.inj (hnodeJ.symm.trans hrec)
      subst hnEq
      refine ⟨src, ?_, hid, Or.inr ⟨Or.inl rfl, hs⟩⟩
      show inp.boxes[(g0.nodes[j]'hi).decl]? = some src
      rw [hj0, hmetaJ.1]
      exact hsrc

/-- Exact bottom-identity witness (measured-side proof of the private
`model_bottom_witness` of `GroupAnchors.lean`). -/
private theorem X_model_bottom_witness_aux {inp : Input} {r : ModelRoute} (isFrom : Bool)
    {prepared : List ModelBox} {pad : Int} {titles : List (Int × Int)}
    {nodes0 : List Node}
    (hlen0 : nodes0.length = prepared.length)
    {j : Nat} {src : ModelBox} (hsrc : inp.boxes[j]? = some src)
    (hbp : prepared[j]? =
      some (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        { src with role := .node } else src))
    (hbpg : (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
      { src with role := .node } else src).role = .group)
    (hid : src.id = (if isFrom then r.fromId else r.toId))
    {v : Nat} {n0 : Node}
    (hnode' : (Compound.markNodes prepared pad titles nodes0)[v]? = some n0)
    (hvj : v = Compound.bottomIndex prepared j) :
    endpointWitness inp r isFrom v n0 := by
  have hfFalse : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false := by
    cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) with
    | true =>
      rw [hf] at hbpg
      simp only [↓reduceIte] at hbpg
      exact absurd hbpg (by intro hcon; cases hcon)
    | false => rfl
  have hpbEq : (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
      { src with role := .node } else src) = src := by
    rw [hfFalse]; simp
  have hsrole : src.role = .group := by rw [← hpbEq]; exact hbpg
  have hbpj : prepared[j]? = some src := by rw [hpbEq] at hbp; exact hbp
  have hvGe : nodes0.length ≤ v := by
    rw [hvj, hlen0]
    unfold Compound.bottomIndex
    omega
  obtain ⟨hb2, _, _, _, _⟩ :=
    Compound.markNodes_getElem?_bottom prepared pad titles nodes0 v hvGe hnode'
  have hdeclEq : n0.decl = j := by
    rw [hvj] at hnode'
    exact X_bottom_node_decl hlen0 rfl hnode' hbpj hsrole
  refine ⟨src, by rw [hdeclEq]; exact hsrc, hid, Or.inr ⟨Or.inr hb2, hsrole⟩⟩

/-- Exact alias identification (counterpart of `GroupAnchorsAlias` for the
exact pipeline): every endpoint of a proper exact candidate edge resolves
through the measured alias identification. The run premises are carried
unused, exactly as in the plain proof. -/
def X_GroupAnchorsAlias (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult},
    ∀ (execution : SceneExecutionX exactIds inp o res) (packed : Pack.State),
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed) →
    ∀ {c : Nat} {q : (List Nat × Part) × Rect},
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q) →
    ∀ {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int},
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run) →
    (_hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      = .ok loops) →
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area }) →
    ∀ {i : Nat} {edge : Edge},
    (_hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge) →
    (_hne : edge.tail ≠ edge.head) →
    ∃ (r : ModelRoute), inp.routes[edge.decl]? = some r ∧
      ∀ (pos : Nat) (v : Nat) (n : Node),
        q.1.1[pos]? = some v →
        execution.graph.nodes[v]? = some n →
        if pos = edge.original.tail then endpointWitness inp r true v n
          else if pos = edge.original.head then endpointWitness inp r false v n
            else True

/-- Exact alias identification holds, by replaying `groupAnchorsAlias_holds`
with the measured equation on `graph0`, edge transfer through
`exactGraph_edges`, and per-node key transfer through `X_node_key_rev`. -/
theorem X_groupAnchorsAlias_holds (exactIds : List String) :
    X_GroupAnchorsAlias exactIds := by
  intro inp o res execution packed _hpack c q hq candidate run loops area hrun
    hloops _hqplace i edge hedge _hne
  have hedges : edge ∈ (componentCandidate execution.graph q.1.1 candidate).edges :=
    List.mem_of_getElem? hedge
  obtain ⟨routeIndex, route, raw, source, target, hrouteIdx, hedgeroute, hdecl,
    hrawsource, hsourceId, hrawtarget, htargetId, _hsem⟩ :=
    X_candidate_model_endpoint_source execution.graph0_eq execution.graph_eq hedges
  obtain ⟨hpartsMap, _⟩ :=
    actual_components_parts_geometryX (by rfl) execution.components_eq
  obtain ⟨hqin, _⟩ := List.of_mem_zip (List.mem_of_getElem? hq)
  have hcompIn : q.1.1 ∈ components execution.graph := by
    have hmap : q.1.1 ∈
        execution.componentsAcc.parts.map (fun part : List Nat × Part => part.1) :=
      List.mem_map_of_mem hqin
    rw [hpartsMap] at hmap
    exact hmap
  obtain ⟨nodes0, edges0, titles0, hprepared0, hnodeLen0, hmetadata0⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have hle := execution.lines_eq
    unfold boxLines at hle
    have := (mapM_getElem? _ _ _ hle).1
    simpa [List.length_zipIdx] using this
  have hlen0 : nodes0.length = (preparedBoxes inp).length := by
    rw [hnodeLen0, hlinesLen, preparedBoxes, List.length_map]
  obtain ⟨gEdge, hgEdge, hgTailMem, hsemG⟩ := componentCandidate_semantic_source hedges
  have hgEdge0 : gEdge ∈ execution.graph0.edges := by
    have h := hgEdge
    rw [exactGraph_edges execution.graph_eq] at h
    exact h
  obtain ⟨index2, route2, raw2, hr2Route, hr2EdgeOf, hgeAlias⟩ :=
    measuredGraph_edge_source execution.graph0_eq hgEdge0
  obtain ⟨h2Decl, h2Rev, _, _, _, _⟩ := edgeOf_semantic_endpoints hr2EdgeOf
  have hgeRev : gEdge.reversed = false := by rw [hgeAlias]; exact h2Rev
  have hgeOrig : gEdge.original = gEdge := by
    cases gEdge with
    | mk _ _ _ _ rev => cases hgeRev; rfl
  have hgeDeclIdx : edge.decl = index2 := by
    have h1 : edge.decl = gEdge.decl := by
      have h := congrArg Edge.decl hsemG
      simpa only [Edge.original_decl] using h
    rw [h1, hgeAlias, Compound.aliasEdge_decl, h2Decl]
  have hidx2 : index2 = routeIndex := hgeDeclIdx.symm.trans hdecl
  have hroute2Eq : route2 = route := by
    rw [hidx2] at hr2Route
    exact Option.some.inj (hr2Route.symm.trans hrouteIdx)
  rw [hroute2Eq, hidx2] at hr2EdgeOf
  have hrawEq : raw2 = raw := Except.ok.inj (hr2EdgeOf.symm.trans hedgeroute)
  rw [hrawEq] at hgeAlias
  have hgTailMem2 : (aliasEdgeOf inp raw).tail ∈ q.1.1 := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgTailMem
  have hbdAll := sceneExecutionX_edges_bounded execution
  obtain ⟨comp', hcomp'In, hgTailC, hgHeadC⟩ :=
    components_edge_endpoints hbdAll
      (List.mem_append.mpr (Or.inl hgEdge))
  have hgTailC' : (aliasEdgeOf inp raw).tail ∈ comp' := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgTailC
  have hcompEq : comp' = q.1.1 :=
    components_shared_member_eq hcomp'In hcompIn hgTailC' hgTailMem2
  have hgHeadMem : (aliasEdgeOf inp raw).head ∈ q.1.1 := by
    rw [← hcompEq]
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgHeadC
  have hlookupT : q.1.1[q.1.1.idxOf (aliasEdgeOf inp raw).tail]? =
      some (aliasEdgeOf inp raw).tail := by
    have hlt : q.1.1.idxOf (aliasEdgeOf inp raw).tail < q.1.1.length :=
      List.idxOf_lt_length_of_mem hgTailMem2
    rw [List.getElem?_eq_getElem hlt]
    exact congrArg some (List.getElem_idxOf hlt)
  have hlookupH : q.1.1[q.1.1.idxOf (aliasEdgeOf inp raw).head]? =
      some (aliasEdgeOf inp raw).head := by
    have hlt : q.1.1.idxOf (aliasEdgeOf inp raw).head < q.1.1.length :=
      List.idxOf_lt_length_of_mem hgHeadMem
    rw [List.getElem?_eq_getElem hlt]
    exact congrArg some (List.getElem_idxOf hlt)
  have hsemTail : edge.original.tail = q.1.1.idxOf (aliasEdgeOf inp raw).tail := by
    have h := congrArg Edge.tail hsemG
    rw [hgeOrig, hgeAlias] at h
    exact h
  have hsemHead : edge.original.head = q.1.1.idxOf (aliasEdgeOf inp raw).head := by
    have h := congrArg Edge.head hsemG
    rw [hgeOrig, hgeAlias] at h
    exact h
  refine ⟨route, by rw [hdecl]; exact hrouteIdx, ?_⟩
  intro pos v n hpos hnode
  obtain ⟨n0, hn0, hnb0, hnap0, hnd0⟩ := X_node_key_rev execution.graph_eq hnode
  have hkd : n.decl = n0.decl := hnd0.symm
  have hkb : n.border = n0.border := hnb0.symm
  have hG : (⟨nodes0, edges0, execution.params.slot⟩ : Graph).nodes = nodes0 := rfl
  have hnodeP : (Compound.prepare (preparedBoxes inp) execution.params.clusterPad
      titles0 (⟨nodes0, edges0, execution.params.slot⟩ : Graph)).nodes[v]? = some n0 := by
    have h2 := hn0
    rw [hprepared0] at h2
    exact h2
  have hnodeM : (Compound.markNodes (preparedBoxes inp) execution.params.clusterPad
      titles0 nodes0)[v]? = some n0 := by
    have h2 := hnodeP
    rw [Compound.prepare_nodes] at h2
    exact h2
  by_cases hpT : pos = edge.original.tail
  · rw [ite_eq_left hpT]
    rw [hpT, hsemTail] at hpos
    have hvEq : v = (aliasEdgeOf inp raw).tail :=
      Option.some.inj (hpos.symm.trans hlookupT)
    subst hvEq
    rcases X_endpoint_cases (boxes := preparedBoxes inp) true raw.tail raw.head
      with hflat | ⟨hbot, hgrp⟩
    · refine X_endpointWitness_transport hkd hkb ?_
      refine X_model_node_witness_aux true hG hlen0 hmetadata0 hrawsource
        (preparedBoxes_lookup hrawsource) hsourceId hnodeP ?_
      rw [show (aliasEdgeOf inp raw).tail =
          Compound.endpoint (preparedBoxes inp) true raw.tail raw.head from rfl]
      exact hflat
    · refine X_endpointWitness_transport hkd hkb ?_
      refine X_model_bottom_witness_aux true hlen0 hrawsource
        (preparedBoxes_lookup hrawsource)
        (hgrp _ (preparedBoxes_lookup hrawsource)) hsourceId hnodeM ?_
      rw [show (aliasEdgeOf inp raw).tail =
          Compound.endpoint (preparedBoxes inp) true raw.tail raw.head from rfl]
      exact hbot
  · rw [ite_eq_right hpT]
    by_cases hpH : pos = edge.original.head
    · rw [ite_eq_left hpH]
      rw [hpH, hsemHead] at hpos
      have hvEq : v = (aliasEdgeOf inp raw).head :=
        Option.some.inj (hpos.symm.trans hlookupH)
      subst hvEq
      rcases X_endpoint_cases (boxes := preparedBoxes inp) false raw.head raw.tail
        with hflatH | ⟨hbotH, hgrpH⟩
      · refine X_endpointWitness_transport hkd hkb ?_
        refine X_model_node_witness_aux false hG hlen0 hmetadata0 hrawtarget
          (preparedBoxes_lookup hrawtarget) htargetId hnodeP ?_
        rw [show (aliasEdgeOf inp raw).head =
            Compound.endpoint (preparedBoxes inp) false raw.head raw.tail from rfl]
        exact hflatH
      · refine X_endpointWitness_transport hkd hkb ?_
        refine X_model_bottom_witness_aux false hlen0 hrawtarget
          (preparedBoxes_lookup hrawtarget)
          (hgrpH _ (preparedBoxes_lookup hrawtarget)) htargetId hnodeM ?_
        rw [show (aliasEdgeOf inp raw).head =
            Compound.endpoint (preparedBoxes inp) false raw.head raw.tail from rfl]
        exact hbotH
    · rw [ite_eq_right hpH]
      exact True.intro

/-- Residual, exact per-edge self-loop row: for one selected exact component,
one exact run, and one self-loop candidate edge, the scene route emitted at
the edge's decl attaches both endpoints to the boundary of its endpoint dump
boxes, with endpoint boxes supplied from the model route. This is the
one-phase exact counterpart of the self-loop half of `flatGroupEndpoints`
(`flat_self_route_ids` plus `self_routes_c5_of_box_ids_nodup`). It holds for
executed exact layouts because self-loop geometry runs through the exact loop
placements (`Loops.exactExtent`), which the exact graph sizes to the fixed
box. -/
def X_SelfRoutes (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (_hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      = .ok loops)
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    {i : Nat} {edge : Edge}
    (_hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (_hself : edge.tail = edge.head)
    {mroute : ModelRoute} (_hrouteD : inp.routes[edge.decl]? = some mroute),
    ∃ source ∈ inp.boxes, ∃ target ∈ inp.boxes,
      source.id = mroute.fromId ∧ target.id = mroute.toId ∧
      ∃ (out : Route) (start finish : Point) (fromBox toBox : Box),
        res.scene.routes[edge.decl]? = some out ∧
        out.points.head? = some start ∧ out.points.getLast? = some finish ∧
        res.scene.layoutDump.box? out.fromId = some fromBox ∧
        res.scene.layoutDump.box? out.toId = some toBox ∧
        Validator.onBoundary start fromBox.rect ∧
        Validator.onBoundary finish toBox.rect

/-- The exact anchor resolution holds, by replaying
`SceneExecution.edge_endpoint_anchors` with the measured equation on
`graph0`, edge transfer through `exactGraph_edges`, the exact alias
identification, and per-node key transfer. -/
theorem X_edge_anchors_holds (exactIds : List String) :
    X_EdgeAnchors exactIds := by
  intro inp o res execution packed _hpack c q _hsel candidate run loops area
    _hr _hl _hp i edge _he hne
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have hle := execution.lines_eq
    unfold boxLines at hle
    have hlen := (mapM_getElem? _ _ _ hle).1
    simpa [List.length_zipIdx] using hlen
  have hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? =
      some edge := _he
  have hedges : edge ∈ (componentCandidate execution.graph q.1.1 candidate).edges :=
    List.mem_of_getElem? hedge
  obtain ⟨index, mroute, raw, source, target, hroute, hrawOf, hdeclIdx,
    hrawsource, hsourceId, hrawtarget, htargetId, _⟩ :=
    X_candidate_model_endpoint_source execution.graph0_eq execution.graph_eq hedges
  obtain ⟨gEdge, hgEdge, hgTailMem, hsemG⟩ := componentCandidate_semantic_source hedges
  have hgEdge0 : gEdge ∈ execution.graph0.edges := by
    have h := hgEdge
    rw [exactGraph_edges execution.graph_eq] at h
    exact h
  obtain ⟨index2, mroute2, raw2, hr2Route, hr2EdgeOf, hgeAlias⟩ :=
    measuredGraph_edge_source execution.graph0_eq hgEdge0
  obtain ⟨h2Decl, h2Rev, _, _, _, _⟩ := edgeOf_semantic_endpoints hr2EdgeOf
  have hgeRev : gEdge.reversed = false := by rw [hgeAlias]; exact h2Rev
  have hgeOrig : gEdge.original = gEdge := by
    cases gEdge with
    | mk _ _ _ _ rev => cases hgeRev; rfl
  have hgeDeclIdx : edge.decl = index2 := by
    have h1 : edge.decl = gEdge.decl := by
      have h := congrArg Edge.decl hsemG
      simpa only [Edge.original_decl] using h
    rw [h1, hgeAlias, Compound.aliasEdge_decl, h2Decl]
  have hidx2 : index2 = index := hgeDeclIdx.symm.trans hdeclIdx
  rw [hidx2] at hr2Route
  have hroute2EQ : mroute2 = mroute :=
    Option.some.inj (hr2Route.symm.trans hroute)
  rw [hidx2, hroute2EQ] at hr2EdgeOf
  have hrawEq : raw2 = raw := Except.ok.inj (hr2EdgeOf.symm.trans hrawOf)
  rw [hrawEq] at hgeAlias
  have hbd : ∀ e ∈ execution.graph.edges ++ Compound.constraints execution.graph,
      e.tail < execution.graph.nodes.length ∧
        e.head < execution.graph.nodes.length :=
    sceneExecutionX_edges_bounded execution
  obtain ⟨comp', hcomp'In, hgTailC, hgHeadC⟩ :=
    components_edge_endpoints hbd (List.mem_append.mpr (Or.inl hgEdge))
  obtain ⟨hpartsMap, _⟩ :=
    actual_components_parts_geometryX (by rfl) execution.components_eq
  have hcompIn : q.1.1 ∈ components execution.graph := by
    have hqin : q.1 ∈ execution.componentsAcc.parts :=
      List.mem_of_getElem? (zip_getElem?_left _hsel)
    have hmap : q.1.1 ∈
        execution.componentsAcc.parts.map (fun part : List Nat × Part => part.1) :=
      List.mem_map_of_mem hqin
    rw [hpartsMap] at hmap
    exact hmap
  have hcompEq : comp' = q.1.1 :=
    components_shared_member_eq hcomp'In hcompIn
      (by simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgTailC)
      (by simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgTailMem)
  have hgHeadMem : gEdge.head ∈ q.1.1 := by
    rw [← hcompEq]
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgHeadC
  have hgTailMem' : (aliasEdgeOf inp raw).tail ∈ q.1.1 := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgTailMem
  have hgHeadMem' : (aliasEdgeOf inp raw).head ∈ q.1.1 := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgHeadMem
  have hsemTail : edge.original.tail = q.1.1.idxOf (aliasEdgeOf inp raw).tail := by
    have h := congrArg Edge.tail hsemG
    rw [hgeOrig, hgeAlias] at h
    exact h
  have hsemHead : edge.original.head = q.1.1.idxOf (aliasEdgeOf inp raw).head := by
    have h := congrArg Edge.head hsemG
    rw [hgeOrig, hgeAlias] at h
    exact h
  have hposT : q.1.1[edge.original.tail]? = some (aliasEdgeOf inp raw).tail := by
    rw [hsemTail]; exact X_comp_idxOf_lookup hgTailMem'
  have hposH : q.1.1[edge.original.head]? = some (aliasEdgeOf inp raw).head := by
    rw [hsemHead]; exact X_comp_idxOf_lookup hgHeadMem'
  have hltT : (aliasEdgeOf inp raw).tail < execution.graph.nodes.length := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using
      (sceneExecutionX_edges_bounded execution gEdge
        (List.mem_append.mpr (Or.inl hgEdge))).1
  have hltH : (aliasEdgeOf inp raw).head < execution.graph.nodes.length := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using
      (sceneExecutionX_edges_bounded execution gEdge
        (List.mem_append.mpr (Or.inl hgEdge))).2
  obtain ⟨nodes0, edges0, titles0, hprepared0, hnodeLen0, _⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hlen0 : nodes0.length = (preparedBoxes inp).length := by
    rw [hnodeLen0, hlinesLen, preparedBoxes, List.length_map]
  have hnTex : ∃ nT : Node,
      execution.graph.nodes[(aliasEdgeOf inp raw).tail]? = some nT := by
    rw [List.getElem?_eq_getElem hltT]
    exact ⟨_, rfl⟩
  have hnHex : ∃ nH : Node,
      execution.graph.nodes[(aliasEdgeOf inp raw).head]? = some nH := by
    rw [List.getElem?_eq_getElem hltH]
    exact ⟨_, rfl⟩
  obtain ⟨nT, hnT⟩ := hnTex
  obtain ⟨nH, hnH⟩ := hnHex
  obtain ⟨nT0, hnT0, hnbT0, _, hndT0⟩ := X_node_key_rev execution.graph_eq hnT
  obtain ⟨nH0, hnH0, hnbH0, _, hndH0⟩ := X_node_key_rev execution.graph_eq hnH
  have hmarkT : (Compound.markNodes (preparedBoxes inp) execution.params.clusterPad
      titles0 nodes0)[(aliasEdgeOf inp raw).tail]? = some nT0 := by
    have h2 := hnT0
    rw [hprepared0, Compound.prepare_nodes] at h2
    exact h2
  have hmarkH : (Compound.markNodes (preparedBoxes inp) execution.params.clusterPad
      titles0 nodes0)[(aliasEdgeOf inp raw).head]? = some nH0 := by
    have h2 := hnH0
    rw [hprepared0, Compound.prepare_nodes] at h2
    exact h2
  obtain ⟨r, hrouteR, hwit⟩ := X_groupAnchorsAlias_holds exactIds execution packed
    _hpack _hsel _hr _hl _hp hedge hne
  have hroute' : inp.routes[edge.decl]? = some mroute := by rw [hdeclIdx]; exact hroute
  have hrEq : mroute = r := (Option.some.inj (hrouteR.symm.trans hroute')).symm
  subst hrEq
  have horigNE : edge.original.tail ≠ edge.original.head := by
    cases hr : edge.reversed with
    | true => simpa [Edge.original, hr] using fun h => hne h.symm
    | false => simpa [Edge.original, hr] using hne
  have hwitT0 := hwit edge.original.tail (aliasEdgeOf inp raw).tail nT hposT hnT
  have hwitT : endpointWitness inp mroute true (aliasEdgeOf inp raw).tail nT := by
    split at hwitT0
    · exact hwitT0
    · rename_i hcon; exact absurd rfl hcon
  have hwitH0 := hwit edge.original.head (aliasEdgeOf inp raw).head nH hposH hnH
  have hwitH : endpointWitness inp mroute false (aliasEdgeOf inp raw).head nH := by
    split at hwitH0
    · rename_i hcon; exact absurd hcon (fun h => horigNE h.symm)
    · split at hwitH0
      · exact hwitH0
      · rename_i hcon; exact absurd rfl hcon
  obtain ⟨bT, hbT, hidT, hclsT⟩ := hwitT
  obtain ⟨bH, hbH, hidH, hclsH⟩ := hwitH
  have hTailEq : (aliasEdgeOf inp raw).tail =
      Compound.endpoint (preparedBoxes inp) true raw.tail raw.head := rfl
  have hHeadEq : (aliasEdgeOf inp raw).head =
      Compound.endpoint (preparedBoxes inp) false raw.head raw.tail := rfl
  refine ⟨mroute, hroute', ?_, ?_⟩
  · rcases X_endpoint_cases (boxes := preparedBoxes inp) true raw.tail raw.head
      with hflatT | ⟨hbotT, hgrpT⟩
    · refine ⟨raw.tail, ?_, Or.inl ⟨source, hrawsource, hsourceId⟩⟩
      rw [hposT, hTailEq, hflatT]
    · have hge : nodes0.length ≤ (aliasEdgeOf inp raw).tail := by
        rw [hlen0, hTailEq, hbotT]
        unfold Compound.bottomIndex
        omega
      obtain ⟨hb2, _, _, _, _⟩ :=
        Compound.markNodes_getElem?_bottom (preparedBoxes inp)
          execution.params.clusterPad titles0 nodes0 _ hge hmarkT
      have hrole : bT.role = .group := by
        rcases hclsT with ⟨hb0, _⟩ | ⟨-, hgrp⟩
        · have hnbT : nT.border = 2 := hnbT0.symm.trans hb2
          omega
        · exact hgrp
      exact ⟨(aliasEdgeOf inp raw).tail, hposT,
        Or.inr ⟨nT, hnT, hnbT0.symm.trans hb2, bT, hbT, hrole, hidT⟩⟩
  · rcases X_endpoint_cases (boxes := preparedBoxes inp) false raw.head raw.tail
      with hflatH | ⟨hbotH, hgrpH⟩
    · refine ⟨raw.head, ?_, Or.inl ⟨target, hrawtarget, htargetId⟩⟩
      rw [hposH, hHeadEq, hflatH]
    · have hge : nodes0.length ≤ (aliasEdgeOf inp raw).head := by
        rw [hlen0, hHeadEq, hbotH]
        unfold Compound.bottomIndex
        omega
      obtain ⟨hb2, _, _, _, _⟩ :=
        Compound.markNodes_getElem?_bottom (preparedBoxes inp)
          execution.params.clusterPad titles0 nodes0 _ hge hmarkH
      have hrole : bH.role = .group := by
        rcases hclsH with ⟨hb0, _⟩ | ⟨-, hgrp⟩
        · have hnbH : nH.border = 2 := hnbH0.symm.trans hb2
          omega
        · exact hgrp
      exact ⟨(aliasEdgeOf inp raw).head, hposH,
        Or.inr ⟨nH, hnH, hnbH0.symm.trans hb2, bH, hbH, hrole, hidH⟩⟩

/-- Exact flat endpoint assembly: from the residual rows, every scene route of
a successful exact execution satisfies the measured group-endpoint invariant,
mirroring `flatGroupEndpoints` (ordinary edges via anchors plus emission
assembly, self-loop edges via the loop row). -/
theorem flatGroupEndpointsX {exactIds : List String}
    (hrank : X_TopRank exactIds) (hbottom : X_BottomBoundary exactIds)
    (hport : X_TailPort exactIds)
    (hassem : X_ChosenPart exactIds)
    (hself : X_SelfRoutes exactIds) : FlatGroupEndpointsX exactIds := by
  intro inp o res hwf hfp execution
  have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hlines : execution.lines.length = inp.boxes.length := by
    have hle := execution.lines_eq
    unfold boxLines at hle
    have hlen := (mapM_getElem? _ _ _ hle).1
    simpa [List.length_zipIdx] using hlen
  intro out hout
  obtain ⟨key, houtIndex⟩ := List.mem_iff_getElem?.mp hout
  have hlength : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    simp only [sceneOf, List.length_map, List.length_zipIdx]
  have hkey : key < inp.routes.length := by
    rw [← hlength]
    exact (List.getElem?_eq_some_iff.mp houtIndex).1
  have hmodel : inp.routes[key]? = some (inp.routes[key]'hkey) :=
    List.getElem?_eq_getElem hkey
  have hscene := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.packedAcc execution.measured key hkey
  rw [← execution.scene_eq] at hscene
  have houtRecord := Option.some.inj (houtIndex.symm.trans hscene)
  obtain ⟨packed, c, q, candidate, run, loops, area, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdeclEq⟩ :=
    execution.route_component_sourceX hkey
  have hrouteKey : inp.routes[edge.decl]? = some (inp.routes[key]'hkey) := by
    rw [hdeclEq]
    exact hmodel
  by_cases hne : edge.tail = edge.head
  · obtain ⟨sourceBox, hsourceMem, targetBox, htargetMem, hsidF, hsidT,
      out', start, finish, fromBox, toBox, hemitted, h1, h2, h3, h4, h5, h6⟩ :=
      hself execution packed hpacked hselected hrun hloops hpart hedge hne hrouteKey
    rw [hdeclEq] at hemitted
    have hsame : out' = out := Option.some.inj (hemitted.symm.trans houtIndex)
    subst hsame
    have houtFrom : out'.fromId = (inp.routes[key]'hkey).fromId :=
      congrArg Route.fromId houtRecord
    have houtTo : out'.toId = (inp.routes[key]'hkey).toId :=
      congrArg Route.toId houtRecord
    exact ⟨sourceBox, hsourceMem, targetBox, htargetMem,
      hsidF.trans houtFrom.symm, hsidT.trans houtTo.symm,
      start, finish, fromBox, toBox, h1, h2, h3, h4, h5, h6⟩
  · obtain ⟨mroute, hrouteD, hFa, hTa⟩ :=
      X_edge_anchors_holds exactIds execution packed hpacked hselected hrun hloops hpart hedge hne
    have hmk : mroute = inp.routes[key]'hkey :=
      Option.some.inj (hrouteD.symm.trans hrouteKey)
    obtain ⟨sourceBox, hsourceMem, hsourceId⟩ :
        ∃ sb : ModelBox, sb ∈ inp.boxes ∧ sb.id = (inp.routes[key]'hkey).fromId := by
      obtain ⟨wF, _, hsideF⟩ := hFa
      rcases hsideF with ⟨sF, hsFw, hidF⟩ | ⟨nF, _, _, sF, hsF, _, hidF⟩
      · refine ⟨sF, List.mem_of_getElem? hsFw, ?_⟩
        rw [hmk] at hidF
        exact hidF
      · refine ⟨sF, List.mem_of_getElem? hsF, ?_⟩
        rw [hmk] at hidF
        exact hidF
    obtain ⟨targetBox, htargetMem, htargetId⟩ :
        ∃ tb : ModelBox, tb ∈ inp.boxes ∧ tb.id = (inp.routes[key]'hkey).toId := by
      obtain ⟨wT, _, hsideT⟩ := hTa
      rcases hsideT with ⟨sT, hsTw, hidT⟩ | ⟨nT, _, _, sT, hsT, _, hidT⟩
      · refine ⟨sT, List.mem_of_getElem? hsTw, ?_⟩
        rw [hmk] at hidT
        exact hidT
      · refine ⟨sT, List.mem_of_getElem? hsT, ?_⟩
        rw [hmk] at hidT
        exact hidT
    obtain ⟨out', start, finish, fromBox, toBox, hemitted, h1, h2, h3, h4, h5, h6⟩ :=
      hassem execution hrank hbottom hport groupAnchorSelection packed hpacked
        hselected hrun hloops hpart hedge hne hrouteD hFa hTa
    rw [hdeclEq] at hemitted
    have hsame : out' = out := Option.some.inj (hemitted.symm.trans houtIndex)
    subst hsame
    have houtFrom : out'.fromId = (inp.routes[key]'hkey).fromId :=
      congrArg Route.fromId houtRecord
    have houtTo : out'.toId = (inp.routes[key]'hkey).toId :=
      congrArg Route.toId houtRecord
    exact ⟨sourceBox, hsourceMem, targetBox, htargetMem,
      hsourceId.trans houtFrom.symm, htargetId.trans houtTo.symm,
      start, finish, fromBox, toBox, h1, h2, h3, h4, h5, h6⟩

/-- Flat C5 for the exact pipeline: every successful `layoutX` preserves box
and route ids and attaches every route endpoint to its dump-box boundary. -/
theorem flatC5B_layoutX (exactIds : List String)
    (hrank : X_TopRank exactIds) (hbottom : X_BottomBoundary exactIds)
    (hport : X_TailPort exactIds)
    (hassem : X_ChosenPart exactIds) (hself : X_SelfRoutes exactIds) :
    FlatC5B (layoutX exactIds) :=
  flatC5B_layoutX_of_endpointsX
    (flatGroupEndpointsX hrank hbottom hport hassem hself)
end PipelineImpl
end Layered
end Elegant

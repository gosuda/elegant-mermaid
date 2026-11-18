import Elegant.Layered.FamilyC5Measured
import Elegant.Layered.GroupAttachSeamFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! ### Residual seams for the flat group-endpoint proof

`FlatGroupEndpoints` is the flat C5 seam: every route of a successful flat
`layout` of a well-formed framed input attaches both endpoints to the boundary
of its endpoint dump boxes.  `SceneExecution.group_endpoint_source_invariant_measured`
proves it from the refuted `GroupAnchors`; this file re-proves it from the true
identification `GroupAnchorsAlias` (`groupAnchorsAlias_holds`).

Four one-phase facts stay open as named residuals; each is consumed below.

* `GroupTopSubtreeRankProper` (`GroupTopRank.lean`) yields `GroupAttachMeasured`
  (`groupAttachMeasured_of_rank`): the boundary half for plain and top-proxy
  endpoints, i.e. the group attach geometry of the ranking phase.
* `GroupBottomBoundaryFacts` (`FamilyC5Measured.lean`): the bottom boundary
  row; a route port of a `border = 2` bottom marker lies on the frame of its
  paired `border = -2` top marker.
* `GroupAnchorSelection` (below): the measured-graph anchor row; bottom
  markers sit at the `bottomIndex` of their own declaration, and a group's top
  title node and bottom marker share one union-find component.
* `GroupTailPortOnYs` (below): the executed port row; the tail-side route
  point of a bottom-marker endpoint is the flat port `⟨px, run.ys v⟩`. -/

/-- Residual, measured-graph anchor selection: in a measured graph every
`border = 2` node is the synthetic bottom marker placed at the `bottomIndex`
of its own declaration, and for every group box the top title node at the
box's own index carries `border = -2` and that declaration while top and
bottom marker lie in one reported component.  This is a statement about node
records, ids and component construction only. -/
def GroupAnchorSelection : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    (∀ {v : Nat} {n : Node}, graph.nodes[v]? = some n → n.border = 2 →
      v = Compound.bottomIndex (preparedBoxes inp) n.decl) ∧
    ∀ {j : Nat} {src : ModelBox},
      inp.boxes[j]? = some src → src.role = .group →
      ∃ (top : Node) (comp : List Nat) (_ : comp ∈ components graph),
        graph.nodes[j]? = some top ∧ top.border = -2 ∧ top.decl = j ∧
          j ∈ comp ∧ Compound.bottomIndex (preparedBoxes inp) j ∈ comp

/-- Residual, executed tail port: for a successful `componentRun` whose
chain-tail endpoint is a `border = 2` bottom marker, the emitted route's
tail-side point is the flat port `⟨px, run.ys v⟩` with `px` inside the
marker's box span.  This is the `nodeH = 0` collapse of the two stored port
forms of `route_endpoints_on_ports`; only the tail side needs it, because the
head-side point already sits at `boxRect.y = run.ys`. -/
def GroupTailPortOnYs : Prop :=
  ∀ {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions},
    componentRun P cg labels orderOptions = .ok run →
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

/-! ### Small lookup helpers -/

/-- Local copy of the private `endpoint_cases` of `GroupAnchors.lean`. -/
private theorem endpoint_cases_local {boxes : List ModelBox} (s : Bool) (i j : Nat) :
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

/-- Component lookup at the position of a member. -/
private theorem comp_idxOf_lookup {comp : List Nat} {x : Nat} (hmem : x ∈ comp) :
    comp[comp.idxOf x]? = some x :=
  (List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem)).trans
    (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)))

/-- On a duplicate-free component, `idxOf` is injective. -/
private theorem comp_idxOf_injective {comp : List Nat}
    {x y : Nat} (hx : x ∈ comp) (hy : y ∈ comp)
    (h : comp.idxOf x = comp.idxOf y) : x = y := by
  have e0 : comp[comp.idxOf x]? = comp[comp.idxOf y]? := by rw [h]
  have eL : comp[comp.idxOf x]? = some x := comp_idxOf_lookup hx
  have eR : comp[comp.idxOf y]? = some y := comp_idxOf_lookup hy
  exact Option.some.inj (eL.symm.trans (e0.trans eR))
/-- `bottomIndex` is strictly increasing past a group box. -/
private theorem flat_bottomIndex_lt {boxes : List ModelBox} {i j : Nat}
    (hij : i < j) (hi : i < boxes.length)
    (hg : (boxes[i]'hi).role == .group) :
    Compound.bottomIndex boxes i < Compound.bottomIndex boxes j := by
  have h1 : (boxes.take j).take i ++ (boxes.take j).drop i = boxes.take j :=
    List.take_append_drop i (boxes.take j)
  have h2 : (boxes.take j).take i = boxes.take i := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)]
  have h3 := congrArg (List.filter (fun box : ModelBox => box.role == .group)) h1
  rw [List.filter_append, h2] at h3
  have hmem : boxes[i]'hi ∈ (boxes.take j).drop i := by
    have h0 : ((boxes.take j).drop i)[0]? = some (boxes[i]'hi) := by
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_take, ite_eq_left hij,
        List.getElem?_eq_getElem hi]
    exact List.mem_of_getElem? h0
  have hfilter : 0 < (((boxes.take j).drop i).filter
      (fun box : ModelBox => box.role == .group)).length := by
    apply List.length_pos_of_mem
    exact List.mem_filter.mpr ⟨hmem, hg⟩
  have h4 := congrArg (fun l => l.length) h3
  rw [List.length_append] at h4
  unfold Compound.bottomIndex
  omega

/-- Two group-box indices with the same `bottomIndex` coincide. -/
private theorem flat_bottomIndex_injective {boxes : List ModelBox} {i j : Nat}
    {bi bj : ModelBox} (hbi : boxes[i]? = some bi) (hbj : boxes[j]? = some bj)
    (hgi : bi.role == .group) (hgj : bj.role == .group)
    (h : Compound.bottomIndex boxes i = Compound.bottomIndex boxes j) : i = j := by
  obtain ⟨hi, hie⟩ := List.getElem_of_getElem? hbi
  obtain ⟨hj, hje⟩ := List.getElem_of_getElem? hbj
  rw [← hie] at hgi
  rw [← hje] at hgj
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (flat_bottomIndex_lt hlt hi hgi))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (flat_bottomIndex_lt hgt hj hgj))

/-- A proper self edge of a measured candidate graph carries a model route
whose two endpoint ids coincide: the aliased endpoints can only coincide when
the raw `edgeOf` endpoints do, and those resolve to the same model box. -/
private theorem flat_self_route_ids {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat}
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate graph comp candidate).edges[i]? = some edge)
    (hself : edge.tail = edge.head) :
    ∃ route : ModelRoute, inp.routes[edge.decl]? = some route ∧
      route.fromId = route.toId ∧
      ∃ src : ModelBox, src ∈ inp.boxes ∧ src.id = route.fromId := by
  have hedges : edge ∈ (componentCandidate graph comp candidate).edges :=
    List.mem_of_getElem? hedge
  obtain ⟨index, route, raw, source, target, hroute, hrawOf, hdeclIdx,
    hrawsource, hsourceId, hrawtarget, htargetId, _⟩ :=
    componentCandidate_model_endpoint_source hgraph hedges
  obtain ⟨gEdge, hgEdge, hgTailMem, hsemG⟩ :=
    componentCandidate_semantic_source hedges
  obtain ⟨index2, route2, raw2, hr2Route, hr2EdgeOf, hgeAlias⟩ :=
    measuredGraph_edge_source hgraph hgEdge
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
  have hroute2Eq : route2 = route :=
    Option.some.inj (hr2Route.symm.trans hroute)
  rw [hidx2, hroute2Eq] at hr2EdgeOf
  have hrawEq : raw2 = raw := Except.ok.inj (hr2EdgeOf.symm.trans hrawOf)
  rw [hrawEq] at hgeAlias
  have hbd : ∀ e ∈ graph.edges ++ Compound.constraints graph,
      e.tail < graph.nodes.length ∧ e.head < graph.nodes.length := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact measuredGraph_edges_bounded hgraph hlines e he
    · exact constraints_bounded graph e he
  obtain ⟨comp', hcomp'In, hgTailC, hgHeadC⟩ :=
    components_edge_endpoints hbd (List.mem_append.mpr (Or.inl hgEdge))
  have hcompEq : comp' = comp :=
    components_shared_member_eq hcomp'In hcomp hgTailC hgTailMem
  have hgHeadMem : gEdge.head ∈ comp := by rw [← hcompEq]; exact hgHeadC
  have hgTailMem' : (aliasEdgeOf inp raw).tail ∈ comp := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgTailMem
  have hgHeadMem' : (aliasEdgeOf inp raw).head ∈ comp := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgHeadMem
  have hsemTail : edge.original.tail = comp.idxOf (aliasEdgeOf inp raw).tail := by
    have h := congrArg Edge.tail hsemG
    rw [hgeOrig, hgeAlias] at h
    exact h
  have hsemHead : edge.original.head = comp.idxOf (aliasEdgeOf inp raw).head := by
    have h := congrArg Edge.head hsemG
    rw [hgeOrig, hgeAlias] at h
    exact h
  have horig : edge.original.tail = edge.original.head := by
    cases hr : edge.reversed with
    | true => simp [Edge.original, hr, hself]
    | false => simp [Edge.original, hr, hself]
  have haliased : (aliasEdgeOf inp raw).tail = (aliasEdgeOf inp raw).head :=
    comp_idxOf_injective hgTailMem' hgHeadMem'
      (by rw [← hsemTail, ← hsemHead, horig])
  have hT : (aliasEdgeOf inp raw).tail =
      Compound.endpoint (preparedBoxes inp) true raw.tail raw.head := rfl
  have hH : (aliasEdgeOf inp raw).head =
      Compound.endpoint (preparedBoxes inp) false raw.head raw.tail := rfl
  rcases endpoint_cases_local (boxes := preparedBoxes inp) true raw.tail raw.head
    with hflatT | ⟨hbotT, hgrpT⟩
  · rcases endpoint_cases_local (boxes := preparedBoxes inp) false raw.head raw.tail
      with hflatH | ⟨hbotH, hgrpH⟩
    · rw [hT, hflatT, hH, hflatH] at haliased
      refine ⟨route, by rw [hdeclIdx]; exact hroute, ?_, ?_⟩
      have hst : source = target := by
        rw [haliased] at hrawsource
        exact Option.some.inj (hrawsource.symm.trans hrawtarget)
      · exact hsourceId.symm.trans (by rw [hst]; exact htargetId)
      · exact ⟨source, List.mem_of_getElem? hrawsource, hsourceId⟩
    · rw [hT, hflatT, hH, hbotH] at haliased
      have hlt : raw.tail < (preparedBoxes inp).length := by
        simpa [preparedBoxes, List.length_map] using
          (List.getElem?_eq_some_iff.mp hrawsource).1
      have hge : (preparedBoxes inp).length ≤ Compound.bottomIndex
          (preparedBoxes inp) raw.head := by
        unfold Compound.bottomIndex; omega
      omega
  · rcases endpoint_cases_local (boxes := preparedBoxes inp) false raw.head raw.tail
      with hflatH | ⟨hbotH, hgrpH⟩
    · rw [hT, hbotT, hH, hflatH] at haliased
      have hlt : raw.head < (preparedBoxes inp).length := by
        simpa [preparedBoxes, List.length_map] using
          (List.getElem?_eq_some_iff.mp hrawtarget).1
      have hge : (preparedBoxes inp).length ≤ Compound.bottomIndex
          (preparedBoxes inp) raw.tail := by
        unfold Compound.bottomIndex; omega
      omega
    · rw [hT, hbotT, hH, hbotH] at haliased
      have hsame : raw.tail = raw.head :=
        flat_bottomIndex_injective (preparedBoxes_lookup hrawsource)
          (preparedBoxes_lookup hrawtarget)
          (by simp [hgrpT _ (preparedBoxes_lookup hrawsource)])
          (by simp [hgrpH _ (preparedBoxes_lookup hrawtarget)]) haliased
      refine ⟨route, by rw [hdeclIdx]; exact hroute, ?_, ?_⟩
      have hst : source = target := by
        rw [hsame] at hrawsource
        exact Option.some.inj (hrawsource.symm.trans hrawtarget)
      · exact hsourceId.symm.trans (by rw [hst]; exact htargetId)
      · exact ⟨source, List.mem_of_getElem? hrawsource, hsourceId⟩

/-- One endpoint of a candidate edge resolved to model identity: either the
component entry names the input box carrying the endpoint id, or it names the
synthetic `border = 2` bottom marker of the group box carrying it. -/
def EndpointAnchor (inp : Input) (graph : Graph) (comp : List Nat) (pos : Nat)
    (route : ModelRoute) (isFrom : Bool) : Prop :=
  ∃ w : Nat, comp[pos]? = some w ∧
    ((∃ s : ModelBox, inp.boxes[w]? = some s ∧
        s.id = (if isFrom then route.fromId else route.toId)) ∨
      (∃ n : Node, graph.nodes[w]? = some n ∧ n.border = 2 ∧
        ∃ s : ModelBox, inp.boxes[n.decl]? = some s ∧ s.role = .group ∧
          s.id = (if isFrom then route.fromId else route.toId)))

/-- The endpoints of every proper candidate edge resolve through the alias
identification `GroupAnchorsAlias`: the flat case names the raw `edgeOf`
endpoint box directly, the aliased case names the bottom marker, whose
`endpointWitness` (from `groupAnchorsAlias_holds`) supplies the group box at
the marker's declaration. -/
private theorem SceneExecution.edge_endpoint_anchors
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∃ mroute : ModelRoute,
      inp.routes[edge.decl]? = some mroute ∧
      EndpointAnchor inp execution.graph q.1.1 edge.original.tail mroute true ∧
      EndpointAnchor inp execution.graph q.1.1 edge.original.head mroute false := by
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have hle := execution.lines_eq
    unfold boxLines at hle
    have hlen := (mapM_getElem? _ _ _ hle).1
    simpa [List.length_zipIdx] using hlen
  have hedges : edge ∈ (componentCandidate execution.graph q.1.1 candidate).edges :=
    List.mem_of_getElem? hedge
  obtain ⟨index, mroute, raw, source, target, hroute, hrawOf, hdeclIdx,
    hrawsource, hsourceId, hrawtarget, htargetId, _⟩ :=
    componentCandidate_model_endpoint_source execution.graph_eq hedges
  obtain ⟨gEdge, hgEdge, hgTailMem, hsemG⟩ :=
    componentCandidate_semantic_source hedges
  obtain ⟨index2, mroute2, raw2, hr2Route, hr2EdgeOf, hgeAlias⟩ :=
    measuredGraph_edge_source execution.graph_eq hgEdge
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
      e.head < execution.graph.nodes.length := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact measuredGraph_edges_bounded execution.graph_eq hlinesLen e he
    · exact constraints_bounded execution.graph e he
  obtain ⟨comp', hcomp'In, hgTailC, hgHeadC⟩ :=
    components_edge_endpoints hbd (List.mem_append.mpr (Or.inl hgEdge))
  have hpartsMap : execution.componentsAcc.parts.map
      (fun part : List Nat × Part => part.1) = components execution.graph :=
    (actual_components_parts (by rfl) execution.components_eq).1
  have hcompIn : q.1.1 ∈ components execution.graph := by
    have hqin : q.1 ∈ execution.componentsAcc.parts :=
      List.mem_of_getElem? (zip_getElem?_left hselected)
    have hmap : q.1.1 ∈
        execution.componentsAcc.parts.map (fun part : List Nat × Part => part.1) :=
      List.mem_map_of_mem hqin
    rw [hpartsMap] at hmap
    exact hmap
  have hcompEq : comp' = q.1.1 :=
    components_shared_member_eq hcomp'In hcompIn hgTailC hgTailMem
  have hgHeadMem : gEdge.head ∈ q.1.1 := by rw [← hcompEq]; exact hgHeadC
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
    rw [hsemTail]; exact comp_idxOf_lookup hgTailMem'
  have hposH : q.1.1[edge.original.head]? = some (aliasEdgeOf inp raw).head := by
    rw [hsemHead]; exact comp_idxOf_lookup hgHeadMem'
  have hltT : (aliasEdgeOf inp raw).tail < execution.graph.nodes.length := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using
      (measuredGraph_edges_bounded execution.graph_eq hlinesLen gEdge hgEdge).1
  have hltH : (aliasEdgeOf inp raw).head < execution.graph.nodes.length := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using
      (measuredGraph_edges_bounded execution.graph_eq hlinesLen gEdge hgEdge).2
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
  obtain ⟨r, hrouteR, hwit⟩ :=
    groupAnchorsAlias_holds (inp := inp) (o := o) (res := res) execution packed hpacked
      (c := c) (q := q) hselected (candidate := candidate) (run := run) (loops := loops)
      (area := area) hrun hloops hpart (i := i) (edge := edge) hedge hne
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
  obtain ⟨nodes0, edges0, titles, hprepared, hnodeLen, _hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph_eq
  have hlen0 : nodes0.length = (preparedBoxes inp).length := by
    rw [hnodeLen, hlinesLen, preparedBoxes, List.length_map]
  have hgraphNodes : execution.graph.nodes =
      Compound.markNodes (preparedBoxes inp) execution.params.clusterPad titles nodes0 := by
    rw [hprepared]
    exact Compound.prepare_nodes _ _ _ _
  refine ⟨mroute, hroute', ?_, ?_⟩
  · rcases endpoint_cases_local (boxes := preparedBoxes inp) true raw.tail raw.head
      with hflatT | ⟨hbotT, hgrpT⟩
    · refine ⟨raw.tail, ?_, Or.inl ⟨source, hrawsource, hsourceId⟩⟩
      rw [hposT, hTailEq, hflatT]
    · have hge : nodes0.length ≤ (aliasEdgeOf inp raw).tail := by
        rw [hlen0, hTailEq, hbotT]
        unfold Compound.bottomIndex
        omega
      have hnT' : (Compound.markNodes (preparedBoxes inp)
          execution.params.clusterPad titles nodes0)[(aliasEdgeOf inp raw).tail]? =
          some nT := by rw [← hgraphNodes]; exact hnT
      obtain ⟨hb2, _, _, _, _⟩ :=
        Compound.markNodes_getElem?_bottom (preparedBoxes inp)
          execution.params.clusterPad titles nodes0 _ hge hnT'
      have hrole : bT.role = .group := by
        rcases hclsT with ⟨hb0, _⟩ | ⟨-, hgrp⟩
        · omega
        · exact hgrp
      exact ⟨(aliasEdgeOf inp raw).tail, hposT,
        Or.inr ⟨nT, hnT, hb2, bT, hbT, hrole, hidT⟩⟩
  · rcases endpoint_cases_local (boxes := preparedBoxes inp) false raw.head raw.tail
      with hflatH | ⟨hbotH, hgrpH⟩
    · refine ⟨raw.head, ?_, Or.inl ⟨target, hrawtarget, htargetId⟩⟩
      rw [hposH, hHeadEq, hflatH]
    · have hge : nodes0.length ≤ (aliasEdgeOf inp raw).head := by
        rw [hlen0, hHeadEq, hbotH]
        unfold Compound.bottomIndex
        omega
      have hnH' : (Compound.markNodes (preparedBoxes inp)
          execution.params.clusterPad titles nodes0)[(aliasEdgeOf inp raw).head]? =
          some nH := by rw [← hgraphNodes]; exact hnH
      obtain ⟨hb2, _, _, _, _⟩ :=
        Compound.markNodes_getElem?_bottom (preparedBoxes inp)
          execution.params.clusterPad titles nodes0 _ hge hnH'
      have hrole : bH.role = .group := by
        rcases hclsH with ⟨hb0, _⟩ | ⟨-, hgrp⟩
        · omega
        · exact hgrp
      exact ⟨(aliasEdgeOf inp raw).head, hposH,
        Or.inr ⟨nH, hnH, hb2, bH, hbH, hrole, hidH⟩⟩

/-- The dump box of an aligned endpoint: the component entry at the endpoint's
own position carries the input box, and the packed rect lookup transports the
frame rectangle of that position. -/
private theorem aligned_dump_box {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {pos key : Nat} (hkey : q.1.1[pos]? = some key)
    {s : ModelBox} (hsource : inp.boxes[key]? = some s) :
    res.scene.layoutDump.box? s.id =
      some (Box.mk s.id s.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (shiftRect (q.2.x - (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run
                execution.measured loops).minX)
              (q.2.y - (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run
                execution.measured loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run pos))))
        s.parent s.exclusive) := by
  have hentry := chosen_part_frame_entry hpart hkey
  have hlookup := execution.part_entry_box_lookup_of_box_ids_nodup hids packed hpacked
    hselected hentry hsource
  rw [shiftRect_pack_normalize] at hlookup
  exact hlookup

/-- The dump box and boundary of a bottom-marker endpoint: the group's top
title node lies in the same component (the anchor-selection residual), its
entry supplies the group's dump box, and the bottom-boundary residual puts
the flat port point on that entry's frame, transported to scene coordinates. -/
private theorem bottom_dump_box_boundary {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    (hanchor : GroupAnchorSelection) (hbottom : GroupBottomBoundaryFacts)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {q : (List Nat × Part) × Rect}
    (hcompIn : q.1.1 ∈ components execution.graph)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) labels orderOptions = .ok run)
    {loops : List (Nat × LoopPlacement)} {area : Int}
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {pos w : Nat} (hpos : q.1.1[pos]? = some w)
    {n : Node} (hn : execution.graph.nodes[w]? = some n) (hb2 : n.border = 2)
    {s : ModelBox} (hs : inp.boxes[n.decl]? = some s) (hgrp : s.role = .group)
    {px : Int}
    (hspan : (RouteImpl.boxRect run.proper run.xs run.ys pos).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys pos).x +
        (RouteImpl.boxRect run.proper run.xs run.ys pos).w) :
    ∃ b : Box,
      res.scene.layoutDump.box? s.id = some b ∧
      Validator.onBoundary (routePointTransport execution.params.canvasMargin
        o.direction execution.packedAcc.canvasH q.2.x q.2.y
        (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
          run execution.measured loops).minX
        (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
          run execution.measured loops).minY
        ⟨px, run.ys.getD pos 0⟩) b.rect := by
  have hanchorRes := hanchor execution.graph_eq
  have hposW : w = Compound.bottomIndex (preparedBoxes inp) n.decl :=
    hanchorRes.1 hn hb2
  obtain ⟨top, comp, hmem, hntop, htopB, htopDecl, hjIn, hbotIn⟩ :=
    hanchorRes.2 hs hgrp
  have hwIn : w ∈ q.1.1 := List.mem_of_getElem? hpos
  have hbotIn' : w ∈ comp := by rw [hposW]; exact hbotIn
  have hcompEq : comp = q.1.1 :=
    components_shared_member_eq hmem hcompIn hbotIn' hwIn
  have hjIn' : n.decl ∈ q.1.1 := by rw [← hcompEq]; exact hjIn
  have hposTop := comp_idxOf_lookup hjIn'
  have hcgNode : (componentCandidate execution.graph q.1.1 candidate).nodes.getD pos
      default = n := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.getD_eq_getElem?_getD, List.getElem?_map, hpos,
      Option.map_some, Option.getD_some]
    rw [hn]
    rfl
  have hcgTop : (componentCandidate execution.graph q.1.1 candidate).nodes.getD
      (q.1.1.idxOf n.decl) default = top := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.getD_eq_getElem?_getD, List.getElem?_map, hposTop,
      Option.map_some, Option.getD_some]
    rw [hntop]
    rfl
  have hlines : execution.lines.length = inp.boxes.length := by
    have hle := execution.lines_eq
    unfold boxLines at hle
    have hlen := (mapM_getElem? _ _ _ hle).1
    simpa [List.length_zipIdx] using hlen
  have hbound :=
    hbottom execution.graph_eq hlines hwf hfp hcompIn hrun (v := pos)
      (t := q.1.1.idxOf n.decl) (px := px)
      (by rw [hcgNode]; exact hb2)
      (by rw [hcgTop]; exact htopB)
      (by rw [hcgNode, hcgTop]; exact htopDecl.symm)
      hspan
  have hentry := chosen_part_frame_entry hpart hposTop
  have hlookup := execution.part_entry_box_lookup_of_box_ids_nodup hids packed hpacked
    hselected hentry hs
  rw [shiftRect_pack_normalize] at hlookup
  refine ⟨Box.mk s.id s.role.id _ s.parent s.exclusive, hlookup, ?_⟩
  exact (onBoundary_shift _ _ _ _).mpr ((onBoundary_orient _ _ _ _).mpr
    ((onBoundary_shift _ _ _ _).mpr hbound))

/-- The head-side route point of a `border = 2` endpoint is the flat port
`⟨qx, run.ys v⟩`: both stored port forms of `route_endpoints_on_ports` place
the head-side point at `boxRect.y`, and `boxRect.y = yAt = run.ys`. -/
private theorem flat_head_port_on_ys
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
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
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouting, _, _, _, hroutes⟩ :=
    componentRun_spec hrun
  obtain ⟨rt', hrt', horiginal, _⟩ := componentRun_route_of_index hrun hi
  have hrtEq : rt = rt' := Option.some.inj (hrt.symm.trans hrt')
  subst hrtEq
  have hm : rt ∈ run.routes := List.mem_iff_getElem?.mpr ⟨i, hrt⟩
  have hfirst' : (RouteImpl.edgesOf run.proper rt.original).head? = some first := by
    rw [horiginal]; exact hfirst
  have hlast' : (RouteImpl.edgesOf run.proper rt.original).getLast? = some last := by
    rw [horiginal]; exact hlast
  obtain ⟨px, qx, _, _, hpx0, hpx1, hqx0, hqx1, hend⟩ :=
    route_endpoints_on_ports hrouting hroutes rt hm first last hfirst' hlast'
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

/-- The flat C5 assembly for one proper candidate edge: the emitted scene
route attaches both endpoints to the boundary of its endpoint dump boxes.
Each side consumes its `EndpointAnchor`: the aligned side reads its dump box
from its own component entry and its boundary from the measured group
attachment fact, the bottom-marker side reads the group's dump box from the
top title entry and its boundary from the bottom-boundary residual applied to
the flat port point. -/
theorem SceneExecution.chosen_part_group_c5_alias
    {inp : Input} {o : Options} {res : FamilyResult}
    (hattach : GroupAttachMeasured) (hbottom : GroupBottomBoundaryFacts)
    (hport : GroupTailPortOnYs) (hanchor : GroupAnchorSelection)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (execution : SceneExecution inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head)
    {mroute : ModelRoute} (hrouteD : inp.routes[edge.decl]? = some mroute)
    (hF : EndpointAnchor inp execution.graph q.1.1 edge.original.tail mroute true)
    (hT : EndpointAnchor inp execution.graph q.1.1 edge.original.head mroute false) :
    ∃ (out : Route) (start finish : Point) (fromBox toBox : Box),
      res.scene.routes[edge.decl]? = some out ∧
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧
      Validator.onBoundary finish toBox.rect := by
  have hlines : execution.lines.length = inp.boxes.length := by
    have hle := execution.lines_eq
    unfold boxLines at hle
    have hlen := (mapM_getElem? _ _ _ hle).1
    simpa [List.length_zipIdx] using hlen
  have hcomp : q.1.1 ∈ components execution.graph := by
    have hqin : q.1 ∈ execution.componentsAcc.parts :=
      List.mem_of_getElem? (zip_getElem?_left hselected)
    have hmap : q.1.1 ∈
        execution.componentsAcc.parts.map (fun part : List Nat × Part => part.1) :=
      List.mem_map_of_mem hqin
    rw [(actual_components_parts (by rfl) execution.components_eq).1] at hmap
    exact hmap
  have hattachAt : GroupAttachAt execution.params
      (componentCandidate execution.graph q.1.1 candidate) :=
    hattach execution.graph_eq hlines hwf hfp hcomp candidate
  have hnd : ((componentCandidate execution.graph q.1.1 candidate).edges.map
      (·.decl)).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate
  have hP := checkedParams_valid execution.checked
  have hshape : CgShape (componentCandidate execution.graph q.1.1 candidate) :=
    componentCandidate_shape
      (components_nodup execution.graph q.1.1 hcomp)
      (measuredGraph_shape execution.graph_eq) candidate
  obtain ⟨first, last, hfirst, hlast, htail, hhead⟩ :=
    componentRun_chain_endpoints hP hnd hshape hrun hedge hne
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have hdeclEq : ((componentCandidate execution.graph q.1.1 candidate).edges[i]'hi).decl =
      edge.decl :=
    congrArg Edge.decl
      (Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hedge))
  have hlo : ∀ l ∈ loops,
      l.1 ≠ ((componentCandidate execution.graph q.1.1 candidate).edges[i]'hi).decl := by
    intro l hl
    rw [hdeclEq]
    exact componentLoops_excludes_ordinary_decl hloops hnd hedge hne l hl
  obtain ⟨rt, start, finish, hget, hor, hplaced, hstart, hfinish, hports⟩ :=
    hattachAt hrun hi hfirst hlast 0 loops (fun l hl => hlo l hl)
      execution.params.canvasMargin o.direction execution.packedAcc.canvasH q.2.x q.2.y
  obtain ⟨mroute0, native, hmodelRoute, hnative, horiginal, hscene⟩ :=
    execution.chosen_part_route_entry packed hpacked hselected hrun hpart hedge
      (fun l hl => by
        rw [← hdeclEq]
        exact hlo l hl)
  have hsame : native = rt := (Option.some.inj (hget.symm.trans hnative)).symm
  subst hsame
  have hmodelEq : mroute = mroute0 :=
    (Option.some.inj (hmodelRoute.symm.trans hrouteD)).symm
  subst hmodelEq
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hedge, Option.map_some,
    Option.getD_some, htail, hhead] at hports
  have hcondEq : ((componentCandidate execution.graph q.1.1 candidate).edges.map
      (·.reversed)).getD i false = edge.reversed := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hedge, Option.map_some,
      Option.getD_some]
  cases hr : edge.reversed
  · simp only [hr] at hports
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
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY
          start) fromBox.rect := by
      rcases hsideF with ⟨sF, hsFw, hidF⟩ | ⟨nF, hnF, hb2F, sF, hsF, hgrpF, hidF⟩
      · have hbox := aligned_dump_box (c := c) (q := q) execution hids packed hpacked hselected
          (candidate := candidate) (run := run) (loops := loops) (area := area) hpart hposF hsFw
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
        have hstartF : start = ⟨pxF,
            run.ys.getD edge.tail 0⟩ := Option.some.inj (hstart.symm.trans hheadF')
        obtain ⟨bF, hbFlookup, hbFbound⟩ :=
          bottom_dump_box_boundary (q := q) execution hids hanchor hbottom hwf hfp hcomp
            packed hpacked
            (c := c) hselected (candidate := candidate) (run := run)
            (labels := execution.measured) (orderOptions := candidateOrder candidate) hrun
            (loops := loops) (area := area) hpart hposF (n := nF) hnF hb2F (s := sF) hsF
            hgrpF (px := pxF) ⟨hx0, hx1⟩
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
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY
          finish) toBox.rect := by
      rcases hsideT with ⟨sT, hsTw, hidT⟩ | ⟨nT, hnT, hb2T, sT, hsT, hgrpT, hidT⟩
      · have hbox := aligned_dump_box (c := c) (q := q) execution hids packed hpacked hselected
          (candidate := candidate) (run := run) (loops := loops) (area := area) hpart hposTt hsTw
        refine ⟨Box.mk sT.id sT.role.id _ sT.parent sT.exclusive, ?_, hports.2⟩
        have hidT' : sT.id = mroute.toId := hidT
        rw [show mroute.toId = sT.id from hidT'.symm]
        exact hbox
      · obtain ⟨qxT, hy0, hy1, hheadT, hlastT⟩ :=
          flat_head_port_on_ys hrun hi hfirst hlast hnative
        rw [hhead] at hlastT hy0 hy1
        have hlastT' := hlastT (hcondEq.trans hr)
        have hfinishT : finish = ⟨qxT,
            run.ys.getD edge.head 0⟩ := Option.some.inj (hfinish.symm.trans hlastT')
        obtain ⟨bT, hbTlookup, hbTbound⟩ :=
          bottom_dump_box_boundary (q := q) execution hids hanchor hbottom hwf hfp hcomp
            packed hpacked
            (c := c) hselected (candidate := candidate) (run := run)
            (labels := execution.measured) (orderOptions := candidateOrder candidate) hrun
            (loops := loops) (area := area) hpart hposTt (n := nT) hnT hb2T (s := sT) hsT
            hgrpT (px := qxT) ⟨hy0, hy1⟩
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
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY)),
      _, _, fromBox, toBox, hscene, ?_, ?_, hfromLookup, htoLookup, hfromBound, htoBound⟩
    · simp only [List.head?_map, hstart, Option.map_some]
    · simp only [List.getLast?_map, hfinish, Option.map_some]
  · simp only [hr] at hports
    have horigT : edge.original.tail = edge.head := by simp [Edge.original, hr]
    have horigH : edge.original.head = edge.tail := by simp [Edge.original, hr]
    obtain ⟨wF, hposFo, hsideF⟩ := hF
    have hposF : q.1.1[edge.head]? = some wF := by rw [← horigT]; exact hposFo
    obtain ⟨wT, hposTo, hsideT⟩ := hT
    have hposTt : q.1.1[edge.tail]? = some wT := by rw [← horigH]; exact hposTo
    have hfromOut : ∃ fromBox : Box,
        res.scene.layoutDump.box? mroute.fromId = some fromBox ∧
        Validator.onBoundary (routePointTransport execution.params.canvasMargin o.direction
          execution.packedAcc.canvasH q.2.x q.2.y
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY
          start) fromBox.rect := by
      rcases hsideF with ⟨sF, hsFw, hidF⟩ | ⟨nF, hnF, hb2F, sF, hsF, hgrpF, hidF⟩
      · have hbox := aligned_dump_box (c := c) (q := q) execution hids packed hpacked hselected
          (candidate := candidate) (run := run) (loops := loops) (area := area) hpart hposF hsFw
        refine ⟨Box.mk sF.id sF.role.id _ sF.parent sF.exclusive, ?_, hports.1⟩
        have hidF' : sF.id = mroute.fromId := hidF
        rw [show mroute.fromId = sF.id from hidF'.symm]
        exact hbox
      · obtain ⟨qxT, hy0, hy1, hheadT, hlastT⟩ :=
          flat_head_port_on_ys hrun hi hfirst hlast hnative
        rw [hhead] at hheadT hy0 hy1
        have hheadT' := hheadT (hcondEq.trans hr)
        have hstartF : start = ⟨qxT,
            run.ys.getD edge.head 0⟩ := Option.some.inj (hstart.symm.trans hheadT')
        obtain ⟨bF, hbFlookup, hbFbound⟩ :=
          bottom_dump_box_boundary (q := q) execution hids hanchor hbottom hwf hfp hcomp
            packed hpacked
            (c := c) hselected (candidate := candidate) (run := run)
            (labels := execution.measured) (orderOptions := candidateOrder candidate) hrun
            (loops := loops) (area := area) hpart hposF (n := nF) hnF hb2F (s := sF) hsF
            hgrpF (px := qxT) ⟨hy0, hy1⟩
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
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY
          finish) toBox.rect := by
      rcases hsideT with ⟨sT, hsTw, hidT⟩ | ⟨nT, hnT, hb2T, sT, hsT, hgrpT, hidT⟩
      · have hbox := aligned_dump_box (c := c) (q := q) execution hids packed hpacked hselected
          (candidate := candidate) (run := run) (loops := loops) (area := area) hpart hposTt hsTw
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
        have hfinishT : finish = ⟨pxF,
            run.ys.getD edge.tail 0⟩ := Option.some.inj (hfinish.symm.trans hlastF')
        obtain ⟨bT, hbTlookup, hbTbound⟩ :=
          bottom_dump_box_boundary (q := q) execution hids hanchor hbottom hwf hfp hcomp
            packed hpacked
            (c := c) hselected (candidate := candidate) (run := run)
            (labels := execution.measured) (orderOptions := candidateOrder candidate) hrun
            (loops := loops) (area := area) hpart hposTt (n := nT) hnT hb2T (s := sT) hsT
            hgrpT (px := pxF) ⟨hx0, hx1⟩
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
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY)),
      _, _, fromBox, toBox, hscene, ?_, ?_, hfromLookup, htoLookup, hfromBound, htoBound⟩
    · simp only [List.head?_map, hstart, Option.map_some]
    · simp only [List.getLast?_map, hfinish, Option.map_some]

/-- The flat endpoint seam `FlatGroupEndpoints`, reduced to four named one-phase
residuals: the executed rank closure (which yields the measured group
attachment via `groupAttachMeasured_of_rank`), the bottom boundary row, the
anchor selection row, and the tail port row.  Every other obligation — the
self-loop identification, the alias anchor resolution, the per-side dump box
lookups, the scene route emission, and the point/rect transport — is proved
here without assumptions. -/
theorem flatGroupEndpoints
    (hrank : GroupTopSubtreeRankProper)
    (hbottom : GroupBottomBoundaryFacts)
    (hport : GroupTailPortOnYs)
    (hanchor : GroupAnchorSelection) : FlatGroupEndpoints := by
  have hattach : GroupAttachMeasured := groupAttachMeasured_of_rank hrank
  intro inp o res hwf hfp execution
  have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hlines : execution.lines.length = inp.boxes.length := by
    have hle := execution.lines_eq
    unfold boxLines at hle
    have hlen := (mapM_getElem? _ _ _ hle).1
    simpa [List.length_zipIdx] using hlen
  have hcompAll : ∀ q ∈ execution.componentsAcc.parts,
      q.1 ∈ components execution.graph := by
    intro q hq
    have hmap : q.1 ∈
        execution.componentsAcc.parts.map (fun part : List Nat × Part => part.1) :=
      List.mem_map_of_mem hq
    rw [(actual_components_parts (by rfl) execution.components_eq).1] at hmap
    exact hmap
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
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ :=
    execution.route_component_source hkey
  by_cases hself : edge.tail = edge.head
  · obtain ⟨mroute, hrouteD, hselfIds, src, hsrcMem, hsrcId⟩ :=
      flat_self_route_ids execution.graph_eq hlines
        (comp := q.1.1) (hcompAll q.1 (List.mem_of_getElem? (zip_getElem?_left hselected)))
        (candidate := candidate) (i := i) (edge := edge) hedge hself
    have hrouteKey : inp.routes[edge.decl]? = some mroute := hrouteD
    rw [hdecl] at hrouteKey
    have hmk : mroute = inp.routes[key]'hkey :=
      Option.some.inj (hrouteKey.symm.trans hmodel)
    have hselfId : out.fromId = out.toId := by
      have h1 : out.fromId = (inp.routes[key]'hkey).fromId :=
        congrArg Route.fromId houtRecord
      have h2 : out.toId = (inp.routes[key]'hkey).toId :=
        congrArg Route.toId houtRecord
      rw [h1, h2, ← hmk]
      exact hselfIds
    obtain ⟨start, finish, fromBox, toBox, h1, h2, h3, h4, h5, h6⟩ :=
      execution.self_routes_c5_of_box_ids_nodup hids hout hselfId
    refine ⟨src, hsrcMem, src, hsrcMem, ?_, ?_, start, finish, fromBox, toBox,
      h1, h2, h3, h4, h5, h6⟩
    · have h1' : out.fromId = (inp.routes[key]'hkey).fromId :=
        congrArg Route.fromId houtRecord
      rw [h1', ← hmk]
      exact hsrcId
    · have h2' : out.toId = (inp.routes[key]'hkey).toId :=
        congrArg Route.toId houtRecord
      rw [h2', ← hmk]
      exact hselfIds ▸ hsrcId
  · obtain ⟨mroute, hrouteD, hFa, hTa⟩ :=
      execution.edge_endpoint_anchors packed hpacked (c := c) (q := q) hselected
        (candidate := candidate) (run := run) (loops := loops) (area := area)
        hrun hloops hpart (i := i) (edge := edge) hedge hself
    have hrouteKey : inp.routes[edge.decl]? = some mroute := hrouteD
    rw [hdecl] at hrouteKey
    have hmk : mroute = inp.routes[key]'hkey :=
      Option.some.inj (hrouteKey.symm.trans hmodel)
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
      execution.chosen_part_group_c5_alias hattach hbottom hport hanchor hwf hfp hids
        packed hpacked (c := c) (q := q) hselected (candidate := candidate) (run := run)
        (loops := loops) (area := area) hrun hloops hpart (i := i) (edge := edge) hedge
        hself hrouteD hFa hTa
    rw [hdecl] at hemitted
    have hsame : out' = out := Option.some.inj (hemitted.symm.trans houtIndex)
    subst hsame
    have houtFrom : out'.fromId = (inp.routes[key]'hkey).fromId :=
      congrArg Route.fromId houtRecord
    have houtTo : out'.toId = (inp.routes[key]'hkey).toId :=
      congrArg Route.toId houtRecord
    exact ⟨sourceBox, hsourceMem, targetBox, htargetMem, hsourceId.trans houtFrom.symm,
      htargetId.trans houtTo.symm, start, finish, fromBox, toBox, h1, h2, h3, h4, h5, h6⟩

end Elegant.Layered.PipelineImpl

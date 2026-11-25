import Elegant.Layered.RegionC5TerminalTransport
import Elegant.Layered.RegionC5PlainBoundary
import Elegant.Layered.RegionBaseExecutedValidity
import Lean

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

elab "c5ChainEnds%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionGroupEndpointProof
    `Elegant.Layered.PipelineImpl.rgeChainEndpointsR))

elab "c5RankSource%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionC5PlainBoundary
    `Elegant.Layered.PipelineImpl.rpbRankEdgeOrigMem))

elab "c5CandidateSource%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionC5PlainBoundary
    `Elegant.Layered.PipelineImpl.rpbCandEdgeOrig))

elab "c5AliasCases%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.GroupAnchors
    `Elegant.Layered.PipelineImpl.endpoint_cases))

elab "c5BottomDecl%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.GroupAnchors
    `Elegant.Layered.PipelineImpl.bottom_node_decl))

private theorem componentKey {comp : List Nat} {k : Nat} (hk : k ∈ comp) :
    comp[comp.idxOf k]? = some k :=
  (List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hk)).trans
    (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem hk)))

theorem c5NativeRouteOrigin {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    {used : Option RegionSpec} {comp : List Nat} {index : Nat} {cg : Graph} {run : Run}
    (hc : comp ∈ components e.graph)
    (hrun : componentRunR e.params (exactDecls exactIds inp) used inp
      (componentCandidateR used e.graph comp index) e.measured (candidateOrder index) = .ok (cg, run))
    {i : Nat} {edge : Edge} (he : cg.edges[i]? = some edge) :
    ∃ route raw, inp.routes[edge.decl]? = some route ∧ edgeOf inp route edge.decl = .ok raw ∧
      comp[edge.original.tail]? = some (aliasEdgeOf inp raw).tail ∧
      comp[edge.original.head]? = some (aliasEdgeOf inp raw).head ∧
      (aliasEdgeOf inp raw).tail < e.graph.nodes.length ∧
      (aliasEdgeOf inp raw).head < e.graph.nodes.length := by
  obtain ⟨candidateEdge, hcandidateEdge, hsemantic, hdecl⟩ :=
    c5RankSource% hrun (List.mem_of_getElem? he)
  obtain ⟨gEdge, hg, htail, hlocal, hcdecl⟩ := c5CandidateSource% hcandidateEdge
  have hg0 : gEdge ∈ e.graph0.edges := by rwa [exactGraph_edges e.graph_eq] at hg
  obtain ⟨key, route, raw, hroute, hraw, halias⟩ := measuredGraph_edge_source e.graph0_eq hg0
  have hrawk := (edgeOf_semantic_endpoints hraw).1
  have hnoRev := (edgeOf_semantic_endpoints hraw).2.1
  change gEdge = aliasEdgeOf inp raw at halias
  have hd : edge.decl = key := by
    rw [hdecl, hcdecl, halias]
    exact hrawk
  have hgRev : gEdge.reversed = false := by rw [halias]; exact hnoRev
  have hgOrig : gEdge.original = gEdge := by
    cases gEdge with
    | mk _ _ _ _ r => cases hgRev; rfl
  have hsource := hsemantic.trans hlocal
  rw [hgOrig] at hsource
  have ht : edge.original.tail = comp.idxOf gEdge.tail := congrArg Edge.tail hsource
  have hh : edge.original.head = comp.idxOf gEdge.head := congrArg Edge.head hsource
  have hbound := sceneExecutionR_edges_boundedR e
  have heMem := List.mem_append_left (Compound.constraints e.graph) hg
  have hbounds := hbound gEdge heMem
  obtain ⟨other, ho, hot, hoh⟩ := components_edge_endpoints hbound heMem
  have heq := components_shared_member_eq ho hc hot htail
  subst other
  refine ⟨route, raw, by rwa [hd], by rwa [hd], ?_, ?_, ?_, ?_⟩
  · rw [ht, show (aliasEdgeOf inp raw).tail = gEdge.tail from (congrArg Edge.tail halias).symm]
    exact componentKey htail
  · rw [hh, show (aliasEdgeOf inp raw).head = gEdge.head from (congrArg Edge.head halias).symm]
    exact componentKey hoh
  · exact halias ▸ hbounds.1
  · exact halias ▸ hbounds.2

theorem c5NativeAliasTerminalNode {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) {front : Bool} {key other : Nat}
    {box : ModelBox} (hbox : inp.boxes[key]? = some box)
    {n : Node} (hn : e.graph.nodes[Compound.endpoint (preparedBoxes inp) front key other]? = some n) :
    n.decl = key ∧ ((n.border = 0 ∧ Compound.endpoint (preparedBoxes inp) front key other = key) ∨
      n.border = -2 ∨ n.border = 2) := by
  let prepared := preparedBoxes inp
  let anchor := Compound.endpoint prepared front key other
  change e.graph.nodes[anchor]? = some n at hn
  have ha : anchor < e.graph0.nodes.length := by
    rw [← exactGraph_length e.graph_eq]
    exact (List.getElem?_eq_some_iff.mp hn).1
  obtain ⟨n', hn', hborder, _, hdecl⟩ := exactGraph_node_key e.graph_eq (List.getElem?_eq_getElem ha)
  have he := Option.some.inj (hn'.symm.trans hn)
  rw [he] at hborder hdecl
  obtain ⟨nodes, _, titles, hprepared, hlen, hmetadata⟩ := measuredGraph_prepared_source e.graph0_eq
  have hlen' : nodes.length = prepared.length := by
    rw [hlen, boxLines_length e.lines_eq]
    exact (List.length_map ..).symm
  have hm : (Compound.markNodes prepared e.params.clusterPad titles nodes)[anchor]? =
      some (e.graph0.nodes[anchor]'ha) := by
    have hlookup := congrArg (fun g : Graph => g.nodes[anchor]?) hprepared
    change e.graph0.nodes[anchor]? =
      (Compound.markNodes prepared e.params.clusterPad titles nodes)[anchor]? at hlookup
    exact hlookup.symm.trans (List.getElem?_eq_getElem ha)
  rcases c5AliasCases% (boxes := prepared) front key other with heq | ⟨heq, hg⟩
  · change anchor = key at heq
    have hb := (List.getElem?_eq_some_iff.mp hbox).1
    have hb' : key < nodes.length := by
      rw [hlen, boxLines_length e.lines_eq]
      exact hb
    have hp := preparedBoxes_lookup hbox
    let b := if inp.fixedSizes.any (fun p => p.1 == box.id) then { box with role := .node } else box
    change prepared[key]? = some b at hp
    have hmeta := hmetadata key nodes[key] (List.getElem?_eq_getElem hb')
    have hm' : (Compound.markNodes prepared e.params.clusterPad titles nodes)[key]? =
        some (e.graph0.nodes[anchor]'ha) := by simpa only [heq] using hm
    cases hr : b.role with
    | node =>
      have hng : b.role ≠ .group := by simp [hr]
      have hrec := Compound.prepare_plain_node_record prepared e.params.clusterPad titles
        ({ nodes := nodes, edges := [], slot := 0 } : Graph) hb' hp hng
      rw [Compound.prepare_nodes] at hrec
      have hvalue := Option.some.inj (hm'.symm.trans hrec)
      exact ⟨hdecl.trans ((congrArg Node.decl hvalue).trans hmeta.1),
        Or.inl ⟨hborder.trans ((congrArg Node.border hvalue).trans hmeta.2), heq⟩⟩
    | group =>
      have hrec := Compound.markNodes_getElem?_group prepared e.params.clusterPad titles nodes hb' hp hr
      have hvalue := Option.some.inj (hm'.symm.trans hrec)
      exact ⟨hdecl.trans ((congrArg Node.decl hvalue).trans hmeta.1),
        Or.inr (Or.inl (hborder.trans (congrArg Node.border hvalue)))⟩
  · change anchor = Compound.bottomIndex prepared key at heq
    have hp := preparedBoxes_lookup hbox
    have hd := c5BottomDecl% hlen' heq hm hp (hg _ hp)
    have hge : nodes.length ≤ anchor := by
      rw [hlen', heq, Compound.bottomIndex]
      omega
    have hb := (Compound.markNodes_getElem?_bottom prepared e.params.clusterPad titles nodes
      anchor hge hm).1
    exact ⟨hdecl.trans hd, Or.inr (Or.inr (hborder.trans hb))⟩

private theorem aliasTerminal {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    {used : Option RegionSpec} {comp : List Nat} {index : Nat} {cg : Graph} {run : Run}
    (hc : comp ∈ components e.graph)
    (hrun : componentRunR e.params (exactDecls exactIds inp) used inp
      (componentCandidateR used e.graph comp index) e.measured (candidateOrder index) = .ok (cg, run))
    {v key other : Nat} {front : Bool} {box : ModelBox}
    (hkey : comp[v]? = some (Compound.endpoint (preparedBoxes inp) front key other))
    (hbound : Compound.endpoint (preparedBoxes inp) front key other < e.graph.nodes.length)
    (hbox : inp.boxes[key]? = some box) :
    ((cg.nodes.getD v default).border = 0 ∧ comp[v]? = some key) ∨
      ∃ top, SelectedC5SemanticGroupTerminal cg v top ∧ comp[top]? = some key := by
  let anchor := Compound.endpoint (preparedBoxes inp) front key other
  have hg : e.graph.nodes[anchor]? = some (e.graph.nodes[anchor]'hbound) := List.getElem?_eq_getElem hbound
  let n := e.graph.nodes[anchor]'hbound
  have hnode := component_node_lookupR (spec := used) (cand := index) hkey hg
  have hh : cg.nodes[v]? = some n := by rw [c5TransportRunNodes hrun]; exact hnode
  obtain ⟨hd, htag⟩ := c5NativeAliasTerminalNode e hbox hg
  rcases htag with ⟨hplain, heq⟩ | htop | hbottom
  · refine Or.inl ⟨?_, by rw [← heq]; exact hkey⟩
    rw [List.getD_eq_getElem?_getD, hh, Option.getD_some]
    change (e.graph.nodes[anchor]'hbound).border = 0
    exact hplain
  · obtain ⟨htopKey, _⟩ := c5TransportGroupFrameSource e hrun hh htop
    exact Or.inr ⟨v, ⟨n, n, hh, hh, htop, Or.inl ⟨rfl, htop⟩, rfl⟩, by rwa [hd] at htopKey⟩
  · have hh' : (componentCandidate e.graph comp index).nodes[v]? = some n := by
      rwa [c5TransportRunNodes hrun, c5TransportCandidateNodes] at hh
    obtain ⟨p, hp⟩ := X_componentRun_cg_top_of_bottom e.graph0_eq e.graph_eq
      (boxLines_length e.lines_eq) hc hh' hbottom
    have hk : p.1.border = -2 ∧ p.1.clusterPath = n.clusterPath := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some hp
    have hp' : (componentCandidate e.graph comp index).nodes[p.2]? = some p.1 :=
      List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hp)
    have hpc : cg.nodes[p.2]? = some p.1 := by
      rw [c5TransportRunNodes hrun, c5TransportCandidateNodes]
      exact hp'
    obtain ⟨_, _, htopPath⟩ := X_cg_group_box e.graph0_eq e.graph_eq hp' hk.1
    obtain ⟨_, _, hbotPath⟩ := X_cg_bottom_box e.graph0_eq e.graph_eq hh' hbottom
    have hpDecl : p.1.decl = n.decl := by
      have hlast := congrArg List.getLast? hk.2
      simpa [htopPath, hbotPath] using hlast
    obtain ⟨htopKey, _⟩ := c5TransportGroupFrameSource e hrun hpc hk.1
    exact Or.inr ⟨p.2, ⟨n, p.1, hh, hpc, hk.1, Or.inr hbottom, hpDecl.symm⟩,
      by rwa [hpDecl, hd] at htopKey⟩

def EmittedC5Boundary (scene : Scene) (out : Route) : Prop :=
  ∃ (start finish : Point) (fromBox toBox : Box),
    out.points.head? = some start ∧ out.points.getLast? = some finish ∧
    scene.layoutDump.box? out.fromId = some fromBox ∧
    scene.layoutDump.box? out.toId = some toBox ∧
    Validator.onBoundary start fromBox.rect ∧ Validator.onBoundary finish toBox.rect

private theorem runLayersOk {P : Params} {exact : List Nat} {used : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {order : OrderOptions}
    (hrun : componentRunR P exact used inp cg labels order = .ok (cg', run)) :
    RouteImpl.layersOk run.proper run.layers = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
  rcases stages.hLanes with ⟨_, hl⟩ | ⟨_, hl⟩
  · exact (RouteImpl.routeWithLanes_geometry hl).1
  · exact (rcbRouteWithLanesR_geometry hl).1

/-- All non-loop native routes in an actually selected active component satisfy both
    endpoint clauses, including mixed plain/group and reversed group/group routes. -/
theorem regionC5SelectedActiveOrdinaryEndpoints
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      e.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (e.componentsAcc.parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (e.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {rm : ComponentRegions}
    (hregion : newComponentRegions (selectedC5TerminalSpec idSets e.params o e.lines)
      e.params inp (componentGraph e.graph q.1.1) = .ok (some rm)) :
    ∃ s index chosen cg run loops area,
      selectedC5TerminalSpec idSets e.params o e.lines = some s ∧
      Portfolio.portfolio o.thoroughness (componentTrialR e.params exactIds (some s)
        inp o e.graph q.1.1 e.measured) = .ok chosen ∧ chosen.value = (cg, run) ∧
      componentRunR e.params (exactDecls exactIds inp) (some s) inp
        (componentCandidateR (some s) e.graph q.1.1 index) e.measured
        (candidateOrder index) = .ok (cg, run) ∧
      componentLoops e.params cg run e.measured = .ok loops ∧
      q.1.2 = { placeComponentExact e.params cg run 0 e.measured loops with area := area } ∧
      ∀ {i : Nat} {edge : Edge}, cg.edges[i]? = some edge → edge.tail ≠ edge.head →
        ∀ {out : Route}, res.scene.routes[edge.decl]? = some out →
          EmittedC5Boundary res.scene out := by
  obtain ⟨s, index, chosen, cg, run, loops, area, hs, hport, hvalue, hrun, hloops, hplace, hgroups⟩ :=
    regionC5ChosenActiveEmittedGroupTerminals e hwf hfp hpack hselected hregion
  refine ⟨s, index, chosen, cg, run, loops, area, hs, hport, hvalue, hrun, hloops, hplace, ?_⟩
  intro i edge hedge hne out hout
  obtain ⟨hkeys, _⟩ := actual_components_parts_geometryR (by rfl) e.components_eq
  have hc : q.1.1 ∈ components e.graph := by
    rw [← hkeys]
    exact List.mem_map_of_mem (List.mem_of_getElem? (zip_getElem?_left hselected))
  obtain ⟨native, raw, hnative, hraw, htailKey, hheadKey, htailBound, hheadBound⟩ :=
    c5NativeRouteOrigin e hc hrun hedge
  obtain ⟨_, _, source, target, hsource, hsourceId, htarget, htargetId⟩ :=
    edgeOf_semantic_endpoints hraw
  have hbound := (List.getElem?_eq_some_iff.mp hnative).1
  have hemit := sceneOf_routes_getElem? e.params inp o e.lines e.packedAcc e.measured edge.decl hbound
  rw [← e.scene_eq] at hemit
  have ho := Option.some.inj (hout.symm.trans hemit)
  have hfrom : out.fromId = native.fromId := by
    rw [← (List.getElem?_eq_some_iff.mp hnative).2]
    exact congrArg Route.fromId ho
  have hto : out.toId = native.toId := by
    rw [← (List.getElem?_eq_some_iff.mp hnative).2]
    exact congrArg Route.toId ho
  have hfromId : source.id = out.fromId := hsourceId.trans hfrom.symm
  have htoId : target.id = out.toId := htargetId.trans hto.symm
  obtain ⟨first, last, hf, hl, ht, hh⟩ := c5ChainEnds% hrun hedge hne
  obtain ⟨out', hout', hgroupTail, hgroupHead⟩ := hgroups hedge hne hf hl
  have heq : out' = out := Option.some.inj (hout'.symm.trans hout)
  subst out'
  let tail := (RouteImpl.edgeAt run.proper first).tail
  let head := (RouteImpl.edgeAt run.proper last).head
  let hRect := RouteImpl.boxRect run.proper run.xs run.ys head
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have he := (List.getElem?_eq_some_iff.mp hedge).2
  obtain ⟨rt, px, qx, hrt, hpx₀, hpx₁, hqx₀, hqx₁, hends⟩ := regionRunPortEndpointsR hrun hi hf hl
  have hrev : (cg.edges.map (·.reversed)).getD i false = edge.reversed := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hedge, Option.map_some, Option.getD_some]
  rw [hrev] at hends
  have hnd : (cg.edges.map Edge.decl).Nodup := by
    rw [componentRunR_edges_declsR hrun, c5TransportCandidateDecls]
    exact componentGraph_decls_nodup _ _ (exactGraph_decls_nodup e.graph0_eq e.graph_eq)
  have hnoLoop : ∀ l ∈ loops, l.1 ≠ (cg.edges[i]).decl := by
    simpa only [he] using componentLoops_excludes_ordinary_decl hloops hnd hedge hne
  let bounds := placeBoundsX e.params cg run e.measured loops
  let moved := shiftPoint (0 - bounds.minX) (-bounds.minY)
  have hlocal : q.1.2.routes[i]? = some (edge.decl, rt.points.map moved) := by
    have hp := rcbPlaceEntryR hrun 0 loops i hi hnoLoop
    rw [(List.getElem?_eq_some_iff.mp hrt).2, he] at hp
    rw [hplace]
    exact hp
  obtain ⟨_, hdim, _, _, hbounds⟩ := RouteImpl.layersOk_spec (runLayersOk hrun)
  have htf : tail < run.proper.nodes.length :=
    (hbounds first (RouteImpl.mem_edgesOf (RouteImpl.mem_of_head' hf))).1
  have hhf : head < run.proper.nodes.length :=
    (hbounds last (RouteImpl.mem_edgesOf (List.mem_of_getLast? hl))).2.1
  have htHeight := (hdim _ htf).2
  have hhHeight := (hdim _ hhf).2
  have tailPoint : c5EndpointPoint (!edge.reversed) rt.points =
      some ⟨px, RouteImpl.tailPortY run.proper run.ys tail⟩ := by
    by_cases hr : edge.reversed = true
    · rw [ite_eq_left hr] at hends
      rw [hr]
      exact hends.2
    · rw [ite_eq_right hr] at hends
      have hf' : edge.reversed = false := Bool.eq_false_iff.mpr hr
      rw [hf']
      exact hends.1
  have headPoint : c5EndpointPoint edge.reversed rt.points = some ⟨qx, hRect.y⟩ := by
    by_cases hr : edge.reversed = true
    · rw [ite_eq_left hr] at hends
      rw [hr]
      exact hends.1
    · rw [ite_eq_right hr] at hends
      have hf' : edge.reversed = false := Bool.eq_false_iff.mpr hr
      rw [hf']
      exact hends.2
  have tailPlain (hzero : (cg.nodes.getD tail default).border = 0) :
      Validator.onBoundary ⟨px, RouteImpl.tailPortY run.proper run.ys tail⟩
        (frameRect e.params cg run tail) := by
    rw [plain_frame_eq_boxRect e.params cg run tail htf (by omega)]
    unfold RouteImpl.tailPortY
    by_cases htag : RouteImpl.frameKind run.proper tail = -2
    · simp only [Validator.onBoundary, RouteImpl.boxRect, htag, ↓reduceIte]
      exact ⟨hpx₀, hpx₁, by omega, by omega, Or.inr (Or.inr (Or.inl True.intro))⟩
    · simp only [Validator.onBoundary, RouteImpl.boxRect, htag, ↓reduceIte]
      exact ⟨hpx₀, hpx₁, by omega, by omega, Or.inr (Or.inr (Or.inr True.intro))⟩
  have headPlain (hzero : (cg.nodes.getD head default).border = 0) :
      Validator.onBoundary ⟨qx, hRect.y⟩ (frameRect e.params cg run head) := by
    rw [plain_frame_eq_boxRect e.params cg run head hhf (by omega)]
    simp only [Validator.onBoundary, hRect, RouteImpl.boxRect]
    exact ⟨hqx₀, hqx₁, by omega, by omega, Or.inr (Or.inr (Or.inl True.intro))⟩
  have emitPlain {v key : Nat} {box : ModelBox} {front : Bool} {p : Point}
      (hkey : q.1.1[v]? = some key) (hbox : inp.boxes[key]? = some box)
      (hp : c5EndpointPoint front rt.points = some p)
      (hb : Validator.onBoundary p (frameRect e.params cg run v)) :
      ∃ p' box', c5EndpointPoint front out.points = some p' ∧
        res.scene.layoutDump.box? box.id = some box' ∧ Validator.onBoundary p' box'.rect := by
    have hv : v < cg.nodes.length := by
      rw [c5TransportRunNodes hrun, c5TransportCandidateNodes, componentCandidate_nodes]
      simpa only [componentGraph, List.length_map] using (List.getElem?_eq_some_iff.mp hkey).1
    exact c5TransportEndpoint e hwf hpack hselected hout hlocal
      (c5TransportPlacedFrameEntry hplace hv hkey) hbox
      (front := front) (p := moved p) (by rw [c5EndpointPoint_map, hp] <;> rfl)
      ((onBoundary_shift _ _ _ _).mpr hb)
  have tailEmit {key : Nat} {box : ModelBox} (hbox : inp.boxes[key]? = some box)
      (witness : ((cg.nodes.getD tail default).border = 0 ∧ q.1.1[tail]? = some key) ∨
        ∃ top, SelectedC5SemanticGroupTerminal cg tail top ∧ q.1.1[top]? = some key) :
      ∃ p' box', c5EndpointPoint (!edge.reversed) out.points = some p' ∧
        res.scene.layoutDump.box? box.id = some box' ∧ Validator.onBoundary p' box'.rect := by
    rcases witness with ⟨hzero, hkey⟩ | ⟨top, hm, hkey⟩
    · exact emitPlain hkey hbox tailPoint (tailPlain hzero)
    · obtain ⟨key', box', p, frame, hkey', hbox', hpoint, hlookup, hb⟩ := hgroupTail top hm
      have hk : key' = key := Option.some.inj (hkey'.symm.trans hkey)
      subst key'
      have hb' : box' = box := Option.some.inj (hbox'.symm.trans hbox)
      exact ⟨p, frame, hpoint, hb' ▸ hlookup, hb⟩
  have headEmit {key : Nat} {box : ModelBox} (hbox : inp.boxes[key]? = some box)
      (witness : ((cg.nodes.getD head default).border = 0 ∧ q.1.1[head]? = some key) ∨
        ∃ top, SelectedC5SemanticGroupTerminal cg head top ∧ q.1.1[top]? = some key) :
      ∃ p' box', c5EndpointPoint edge.reversed out.points = some p' ∧
        res.scene.layoutDump.box? box.id = some box' ∧ Validator.onBoundary p' box'.rect := by
    rcases witness with ⟨hzero, hkey⟩ | ⟨top, hm, hkey⟩
    · exact emitPlain hkey hbox headPoint (headPlain hzero)
    · obtain ⟨key', box', p, frame, hkey', hbox', hpoint, hlookup, hb⟩ := hgroupHead top hm
      have hk : key' = key := Option.some.inj (hkey'.symm.trans hkey)
      subst key'
      have hb' : box' = box := Option.some.inj (hbox'.symm.trans hbox)
      exact ⟨p, frame, hpoint, hb' ▸ hlookup, hb⟩
  have hsourceAnchor := aliasTerminal e hc hrun (front := true) (other := raw.head)
    htailKey htailBound hsource
  have htargetAnchor := aliasTerminal e hc hrun (front := false) (other := raw.tail)
    hheadKey hheadBound htarget
  change tail = edge.tail at ht
  change head = edge.head at hh
  cases hr : edge.reversed with
  | false =>
    simp only [Edge.original, hr, Bool.false_eq_true, ↓reduceIte] at hsourceAnchor htargetAnchor
    obtain ⟨start, fromBox, hstart, hfrom, hsb⟩ := tailEmit hsource (ht ▸ hsourceAnchor)
    obtain ⟨finish, toBox, hfinish, hto, htb⟩ := headEmit htarget (hh ▸ htargetAnchor)
    exact ⟨start, finish, fromBox, toBox, by simpa [c5EndpointPoint, hr] using hstart,
      by simpa [c5EndpointPoint, hr] using hfinish, hfromId ▸ hfrom, htoId ▸ hto, hsb, htb⟩
  | true =>
    simp only [Edge.original, hr, ↓reduceIte] at hsourceAnchor htargetAnchor
    obtain ⟨start, fromBox, hstart, hfrom, hsb⟩ := headEmit hsource (hh ▸ hsourceAnchor)
    obtain ⟨finish, toBox, hfinish, hto, htb⟩ := tailEmit htarget (ht ▸ htargetAnchor)
    exact ⟨start, finish, fromBox, toBox, by simpa [c5EndpointPoint, hr] using hstart,
      by simpa [c5EndpointPoint, hr] using hfinish, hfromId ▸ hfrom, htoId ▸ hto, hsb, htb⟩

/-- Scene-level C5 for the actual active part owning a non-self route's source
    declaration. The key and owning component premises are execution data. -/
theorem regionC5ActiveBoundaryForOrdinaryOwnedRoute
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      e.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (e.componentsAcc.parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (e.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {rm : ComponentRegions}
    (hregion : newComponentRegions (selectedC5TerminalSpec idSets e.params o e.lines)
      e.params inp (componentGraph e.graph q.1.1) = .ok (some rm))
    {key : Nat} {out : Route} (hout : res.scene.routes[key]? = some out)
    (hkey : key ∈ (componentGraph e.graph q.1.1).edges.map (·.decl))
    (hne : out.fromId ≠ out.toId) : EmittedC5Boundary res.scene out := by
  obtain ⟨s, index, _, cg, run, _, _, _, _, _, hrun, _, _, hordinary⟩ :=
    regionC5SelectedActiveOrdinaryEndpoints e hwf hfp hpack hselected hregion
  rw [← c5TransportCandidateDecls (some s) e.graph q.1.1 index,
    ← componentRunR_edges_declsR hrun] at hkey
  obtain ⟨edge, hedge, hdecl⟩ := List.mem_map.mp hkey
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hedge
  rw [← hdecl] at hout
  apply hordinary hi _ hout
  intro hself
  obtain ⟨hparts, _⟩ := actual_components_parts_geometryR (by rfl) e.components_eq
  have hc : q.1.1 ∈ components e.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem (List.mem_of_getElem? (zip_getElem?_left hselected))
  obtain ⟨native, raw, hn, hraw, ht, hh, hbt, _⟩ := c5NativeRouteOrigin e hc hrun hi
  obtain ⟨_, _, source, target, hs, hsid, htgt, htid⟩ := edgeOf_semantic_endpoints hraw
  have horig : edge.original.tail = edge.original.head := by
    by_cases hr : edge.reversed = true
    · rw [Edge.original, ite_eq_left hr]
      exact hself.symm
    · rw [Edge.original, ite_eq_right hr]
      exact hself
  rw [horig] at ht
  have halias : (aliasEdgeOf inp raw).tail = (aliasEdgeOf inp raw).head :=
    Option.some.inj (ht.symm.trans hh)
  let node := e.graph.nodes[(aliasEdgeOf inp raw).tail]'hbt
  have hnode : e.graph.nodes[(aliasEdgeOf inp raw).tail]? = some node :=
    List.getElem?_eq_getElem hbt
  have hnode' : e.graph.nodes[(aliasEdgeOf inp raw).head]? = some node := by
    rw [← halias]
    exact hnode
  have hsd := (c5NativeAliasTerminalNode e (front := true) (other := raw.head) hs hnode).1
  have htd := (c5NativeAliasTerminalNode e (front := false) (other := raw.tail) htgt hnode').1
  have hkeys : raw.tail = raw.head := hsd.symm.trans htd
  rw [hkeys] at hs
  have hsame := Option.some.inj (hs.symm.trans htgt)
  have hid : native.fromId = native.toId := hsid.symm.trans ((congrArg ModelBox.id hsame).trans htid)
  have hb := (List.getElem?_eq_some_iff.mp hn).1
  have hemit := sceneOf_routes_getElem? e.params inp o e.lines e.packedAcc e.measured edge.decl hb
  rw [← e.scene_eq] at hemit
  have heq := Option.some.inj (hout.symm.trans hemit)
  have h : inp.routes[edge.decl].fromId = inp.routes[edge.decl].toId := by
    rw [(List.getElem?_eq_some_iff.mp hn).2]
    exact hid
  exact hne ((congrArg Route.fromId heq).trans (h.trans (congrArg Route.toId heq).symm))

/-- A non-self scene route satisfies the entire C5 conclusion, or its owning
    part used the exact fallback. A successful active run elsewhere is not a
    witness that this route used the region router. -/
theorem regionC5OrdinaryRouteBoundary_or_owningFallback
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {out : Route} (hout : out ∈ res.scene.routes) (hne : out.fromId ≠ out.toId) :
    EmittedC5Boundary res.scene out ∨
      ∃ (key : Nat) (part : List Nat × Part),
        res.scene.routes[key]? = some out ∧ part ∈ e.componentsAcc.parts ∧
        key ∈ (componentGraph e.graph part.1).edges.map (·.decl) ∧
        newComponentRegions (selectedC5TerminalSpec idSets e.params o e.lines)
          e.params inp (componentGraph e.graph part.1) = .ok none := by
  obtain ⟨key, hout⟩ := List.mem_iff_getElem?.mp hout
  have hlen : res.scene.routes.length = inp.routes.length := by
    rw [e.scene_eq]
    exact sceneOf_routes_length e.params inp o e.lines e.packedAcc e.measured
  have hkey : key < inp.routes.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hout).1
  obtain ⟨packed, c, q, index, run, loops, area, used, cg, i, edge,
    hpack, hsel, hrun, hloops, hplace, hedge, hdecl⟩ := rgeRouteSourceR e hkey
  have howned : key ∈ (componentGraph e.graph q.1.1).edges.map (·.decl) := by
    rw [← c5TransportCandidateDecls used e.graph q.1.1 index, ← componentRunR_edges_declsR hrun,
      ← hdecl]
    exact List.mem_map_of_mem (List.mem_of_getElem? hedge)
  have hmem : q.1 ∈ e.componentsAcc.parts := List.mem_of_getElem? (zip_getElem?_left hsel)
  obtain ⟨_, hall⟩ := actual_components_parts_geometryR (by rfl) e.components_eq
  have hgeom : ActualPartGeometryR e.params exactIds
      (selectedC5TerminalSpec idSets e.params o e.lines) inp o e.graph e.measured q.1 :=
    hall q.1 hmem
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨rs, hr, _⟩, _, _, _⟩ := hgeom
  cases rs with
  | none => exact Or.inr ⟨key, q.1, hout, hmem, howned, hr⟩
  | some rm =>
    exact Or.inl (regionC5ActiveBoundaryForOrdinaryOwnedRoute e hwf hfp hpack hsel hr hout howned hne)

end Elegant.Layered.PipelineImpl

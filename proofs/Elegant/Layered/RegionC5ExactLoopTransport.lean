import Elegant.Layered.RegionC5NativeEndpoints
import Elegant.Layered.ExactFlatC5SelfRoutes

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

elab "c5ExactLoopEntry%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.ExactFlatC5SelfRoutes
    `Elegant.Layered.PipelineImpl.X_componentLoops_emitted_self_edgeX))

private theorem selfAlias (bs : List ModelBox) (front : Bool) (v : Nat) :
    Compound.endpoint bs front v v = v := by
  cases h : bs[v]? <;> simp [Compound.endpoint, h]

/-- Transport a selected self-loop through the native exact-loop constructor. This
    applies whether the selected component is active or locally fell back. -/
theorem regionC5SelectedExactLoopEndpoints
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    {packed : Pack.State}
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      e.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (e.componentsAcc.parts.map fun part => ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (e.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {used : Option RegionSpec} {index i : Nat} {cg : Graph} {run : Run}
    {loops : List (Nat × LoopPlacement)} {area : Int} {edge : Edge} {out : Route}
    (hrun : componentRunR e.params (exactDecls exactIds inp) used inp
      (componentCandidateR used e.graph q.1.1 index) e.measured (candidateOrder index) = .ok (cg, run))
    (hloops : componentLoops e.params cg run e.measured = .ok loops)
    (hplace : q.1.2 = { placeComponentExact e.params cg run 0 e.measured loops with area := area })
    (hedge : cg.edges[i]? = some edge) (hself : edge.tail = edge.head)
    (hexact : run.exact.contains edge.tail = true)
    (hout : res.scene.routes[edge.decl]? = some out) : EmittedC5Boundary res.scene out := by
  obtain ⟨hparts, _⟩ := actual_components_parts_geometryR (by rfl) e.components_eq
  have hc : q.1.1 ∈ components e.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem (List.mem_of_getElem? (zip_getElem?_left hselected))
  obtain ⟨native, raw, hnative, hraw, ht, hh, hbt, _⟩ := c5NativeRouteOrigin e hc hrun hedge
  obtain ⟨_, _, source, target, hsource, hsourceId, htarget, htargetId⟩ := edgeOf_semantic_endpoints hraw
  have htail : edge.original.tail = edge.tail := by
    by_cases hr : edge.reversed = true
    · rw [Edge.original, ite_eq_left hr]
      exact hself.symm
    · rw [Edge.original, ite_eq_right hr]
  have hhead : edge.original.head = edge.tail := by
    by_cases hr : edge.reversed = true
    · rw [Edge.original, ite_eq_left hr]
    · rw [Edge.original, ite_eq_right hr]
      exact hself.symm
  rw [htail] at ht
  rw [hhead] at hh
  have halias : (aliasEdgeOf inp raw).tail = (aliasEdgeOf inp raw).head :=
    Option.some.inj (ht.symm.trans hh)
  let node := e.graph.nodes[(aliasEdgeOf inp raw).tail]'hbt
  have hnode : e.graph.nodes[(aliasEdgeOf inp raw).tail]? = some node := List.getElem?_eq_getElem hbt
  have hnode' : e.graph.nodes[(aliasEdgeOf inp raw).head]? = some node := by
    rw [← halias]
    exact hnode
  have hsd := (c5NativeAliasTerminalNode e (front := true) (other := raw.head) hsource hnode).1
  have htd := (c5NativeAliasTerminalNode e (front := false) (other := raw.tail) htarget hnode').1
  have hkeys : raw.tail = raw.head := hsd.symm.trans htd
  have ha : (aliasEdgeOf inp raw).tail = raw.tail := by
    change Compound.endpoint (preparedBoxes inp) true raw.tail raw.head = raw.tail
    rw [← hkeys]
    exact selfAlias _ true _
  rw [ha] at ht
  have hsame : source = target := Option.some.inj ((hkeys ▸ hsource).symm.trans htarget)
  have hb := (List.getElem?_eq_some_iff.mp hnative).1
  have hemit := sceneOf_routes_getElem? e.params inp o e.lines e.packedAcc e.measured edge.decl hb
  rw [← e.scene_eq] at hemit
  have heq := Option.some.inj (hout.symm.trans hemit)
  have hfrom : out.fromId = source.id := by
    rw [hsourceId, ← (List.getElem?_eq_some_iff.mp hnative).2]
    exact congrArg Route.fromId heq
  have hto : out.toId = source.id := by
    rw [hsame, htargetId, ← (List.getElem?_eq_some_iff.mp hnative).2]
    exact congrArg Route.toId heq
  have hv : edge.tail < cg.nodes.length := by
    rw [c5TransportRunNodes hrun, c5TransportCandidateNodes, componentCandidate_nodes]
    simpa only [componentGraph, List.length_map] using (List.getElem?_eq_some_iff.mp ht).1
  obtain ⟨entry, hm, _, hdecl, hentry⟩ := c5ExactLoopEntry% hloops hedge hv hself 0
  obtain ⟨v, _, placements, hp, loopEdge, hzip, hloopDecl, htail', _⟩ := componentLoops_entry_origin hloops hm
  have hloopMem : loopEdge ∈ cg.edges := (List.mem_filter.mp (List.of_mem_zip hzip).1).1
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hloopMem
  have hnd : (cg.edges.map Edge.decl).Nodup := by
    rw [componentRunR_edges_declsR hrun, c5TransportCandidateDecls]
    exact componentGraph_decls_nodup _ _ (exactGraph_decls_nodup e.graph0_eq e.graph_eq)
  have hi : i < (cg.edges.map Edge.decl).length := by
    simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hedge).1
  have hmap : (cg.edges.map Edge.decl)[i]? = (cg.edges.map Edge.decl)[j]? := by
    simp only [List.getElem?_map, hedge, hj, Option.map_some]
    exact congrArg some (hdecl.symm.trans hloopDecl)
  have hij := (hnd.getElem?_inj hi).mp hmap
  subst j
  have hsameEdge : loopEdge = edge := Option.some.inj (hj.symm.trans hedge)
  subst loopEdge
  subst v
  rw [hexact, ite_eq_left rfl] at hp
  obtain ⟨start, finish, hs, hf, hsb, hfb⟩ := Loops.exactLoops_boundary hp (List.of_mem_zip hzip).2
  let bounds := placeBoundsX e.params cg run e.measured loops
  let move := shiftPoint (0 - bounds.minX) (-bounds.minY)
  have hlocal : q.1.2.routes[i]? = some (edge.decl, entry.2.points.map move) := by
    rw [hplace]
    exact hentry
  have hrect := c5TransportPlacedFrameEntry hplace hv ht
  obtain ⟨s, fromBox, hps, hbs, hfs⟩ := c5TransportEndpoint e hwf hpack hselected hout hlocal hrect
    hsource (front := true) (p := move start)
    (by
      rw [c5EndpointPoint_map]
      change Option.map move entry.2.points.head? = _
      rw [hs] <;> rfl)
    ((onBoundary_shift _ _ _ _).mpr hsb)
  obtain ⟨f, toBox, hpf, hbf, hff⟩ := c5TransportEndpoint e hwf hpack hselected hout hlocal hrect
    hsource (front := false) (p := move finish)
    (by
      rw [c5EndpointPoint_map]
      change Option.map move entry.2.points.getLast? = _
      rw [hf] <;> rfl)
    ((onBoundary_shift _ _ _ _).mpr hfb)
  exact ⟨s, f, fromBox, toBox, hps, hpf, hfrom.symm ▸ hbs, hto.symm ▸ hbf, hfs, hff⟩

end Elegant.Layered.PipelineImpl

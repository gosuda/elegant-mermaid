import Elegant.Layered.RegionC5NonexactLoopHeight
import Elegant.Layered.RegionC5LoopOnlyCutover

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem nonexactLoopSelfAlias (bs : List ModelBox) (front : Bool) (v : Nat) :
    Compound.endpoint bs front v v = v := by
  cases h : bs[v]? <;> simp [Compound.endpoint, h]

theorem regionC5SelectedNonexactLoop_boundary {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res) (hwf : WellFormed (inputModel inp o))
    {out : Route} (h : R5_SelectedLoopR e out false) : EmittedC5Boundary res.scene out := by
  obtain ⟨packed, c, q, candidate, run, loops, area, used, cg, i, edge,
    hpack, hselected, hchosen, hresolved, hrun, hloops, hplace, hedge, hself, hnonexact, hout⟩ := h
  have hpart := zip_getElem?_left hselected
  obtain ⟨hparts, _⟩ := actual_components_parts_geometryR (by rfl) e.components_eq
  have hc : q.1.1 ∈ components e.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem (List.mem_of_getElem? hpart)
  let s : R6_SelectedLoopPartR e c q.1 :=
    ⟨candidate, used, cg, run, loops, area, hpart, hc, hchosen, hresolved, hrun, hloops, hplace⟩
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
    exact nonexactLoopSelfAlias _ true _
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
  obtain ⟨entry, _, hfind, _, hentry⟩ := c5ExactLoopEntry% hloops hedge hv hself 0
  obtain ⟨_, start, finish, hs, hf, hsb, hfb⟩ := s.nonexactLoopBoundary hedge hfind ht hsource hnonexact
  let bounds := placeBoundsX e.params cg run e.measured loops
  let move := shiftPoint (0 - bounds.minX) (-bounds.minY)
  have hlocal : q.1.2.routes[i]? = some (edge.decl, entry.2.points.map move) := by
    rw [hplace]
    exact hentry
  have hrect := c5TransportPlacedFrameEntry hplace hv ht
  obtain ⟨start', fromBox, hps, hbs, hfs⟩ := c5TransportEndpoint e hwf hpack hselected hout hlocal hrect
    hsource (front := true) (p := move start)
    (by
      rw [c5EndpointPoint_map]
      change Option.map move entry.2.points.head? = _
      rw [hs] <;> rfl)
    ((onBoundary_shift _ _ _ _).mpr hsb)
  obtain ⟨finish', toBox, hpf, hbf, hff⟩ := c5TransportEndpoint e hwf hpack hselected hout hlocal hrect
    hsource (front := false) (p := move finish)
    (by
      rw [c5EndpointPoint_map]
      change Option.map move entry.2.points.getLast? = _
      rw [hf] <;> rfl)
    ((onBoundary_shift _ _ _ _).mpr hfb)
  exact ⟨start', finish', fromBox, toBox, hps, hpf, hfrom.symm ▸ hbs, hto.symm ▸ hbf, hfs, hff⟩

theorem r_activeBoundarySelectedNonexactLoopResidual_closed (exactIds : List String)
    (idSets : List (String × List String)) :
    R_ActiveBoundarySelectedNonexactLoopResidual exactIds idSets := by
  intro inp o res e hwf _ _ out _ h
  exact regionC5SelectedNonexactLoop_boundary e hwf h.2.1

theorem r_activeBoundaryR_closed (exactIds : List String)
    (idSets : List (String × List String)) : R_ActiveBoundaryR exactIds idSets :=
  (r_activeBoundaryR_iff_selectedNonexactLoopResidual exactIds idSets).mpr
    (r_activeBoundarySelectedNonexactLoopResidual_closed exactIds idSets)

end Elegant.Layered.PipelineImpl

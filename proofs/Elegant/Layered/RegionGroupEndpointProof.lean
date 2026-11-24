import Elegant.Layered.RegionC5Boundary
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.RegionActualParts
import Elegant.Layered.RegionRunChainFacts
import Elegant.Layered.RegionCrossCoordsMetadata
import Elegant.Layered.GroupEndpointC5

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region C5 group endpoints

The `gteCycle` witness in `proofs/wip/Probe/RegionGroupEndpointTProbe.lean`
exposed a reversed group edge whose target was inside its frame. The router
used the reserved height of a top marker instead of its semantic height.
The route now uses the semantic tail port for that endpoint.

`R_GroupMarkerFactsR` states the remaining run-level attachment facts for
non-reversed nonloop edges and group self-loops. It does not prove the
unrestricted scene-level group-endpoint boundary property. -/
/-- Run-level attachment facts for region group endpoints. -/
def R_GroupMarkerFactsR : Prop :=
  ∀ {P : Params} {exact : List Nat} {spec : Option RegionSpec} {inp : Input} {o : Options}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (_hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)),
    WellFormed (inputModel inp o) → framedParents inp = true →
    (∀ {i : Nat} {edge : Edge} (_hedge : cg'.edges[i]? = some edge),
      edge.tail ≠ edge.head →
      (cg'.edges.map (·.reversed)).getD i false = false →
      ∃ vt vh : Nat,
        (∃ first : Nat, (RouteImpl.edgesOf run.proper i).head? = some first ∧
          (RouteImpl.edgeAt run.proper first).tail = vt) ∧
        (∃ last : Nat, (RouteImpl.edgesOf run.proper i).getLast? = some last ∧
          (RouteImpl.edgeAt run.proper last).head = vh) ∧
        vt < run.proper.nodes.length ∧ vh < run.proper.nodes.length ∧
        ∃ rt : EdgeRoute,
          run.routes[i]? = some rt ∧
          ∃ start finish : Point,
            rt.points.head? = some start ∧ rt.points.getLast? = some finish ∧
            Validator.onBoundary start (frameRect P cg' run vt) ∧
            Validator.onBoundary finish (frameRect P cg' run vh)) ∧
    (∀ {loops : List (Nat × LoopPlacement)}
      (_hloops : componentLoops P cg' run labels = .ok loops),
      ∀ {i : Nat} {edge : Edge} (_hedge : cg'.edges[i]? = some edge),
      edge.tail = edge.head →
      ((cg'.nodes.getD edge.tail default).border = -2 ∨
        (cg'.nodes.getD edge.tail default).border = 2) →
      ∃ q ∈ loops, q.1 = edge.decl ∧
        ∃ start finish : Point,
          q.2.points.head? = some start ∧ q.2.points.getLast? = some finish ∧
          Validator.onBoundary start (frameRect P cg' run edge.tail) ∧
          Validator.onBoundary finish (frameRect P cg' run edge.tail))

/-- Peel helper (prefixed copy: `bind_ok` is private in every module). -/
private theorem rgeBind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β} (h : x.bind f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Exact placement writes one rectangle per candidate node (copy of
`rapPlacedRects_getR`, private to `RegionActualParts.lean`). -/
private theorem rgePlacedRectsGetR {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)}
    {cursor : Int} {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponentExact P cg run cursor labels loops).rects[i]? =
      some (shiftRect (cursor - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponentExact placeBoundsX
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- The region candidate keeps the component length (copy of
`rapCandidateR_nodes_lengthR`, private to `RegionActualParts.lean`). -/
private theorem rgeCandidateRLengthR (spec' : Option RegionSpec) (g : Graph)
    (comp : List Nat) (index : Nat) :
    (componentCandidateR spec' g comp index).nodes.length = comp.length := by
  cases spec' with
  | none =>
    show (componentCandidate g comp index).nodes.length = comp.length
    rw [componentCandidate_nodes]
    show (comp.map fun v => g.nodes.getD v default).length = comp.length
    exact List.length_map ..
  | some _ =>
    unfold componentCandidateR componentGraph
    dsimp only
    exact List.length_map ..

/-- The region run keeps the candidate nodes (via `componentRunR_specR`:
`none` gives `cg' = cg`, `some` via `rankEquivalentR_nodes_eq`). -/
private theorem rgeRunNodesEqR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    cg'.nodes = cg.nodes := by
  obtain ⟨rs, _, _, _, _, _, _, _, _, _, _, _, _, _, hRs, hRank, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := componentRunR_specR h
  rcases hRank with ⟨rr, hrsNone, _, _, hcgEq, _⟩ | ⟨rm, _, hrank⟩
  · subst hrsNone
    rw [hcgEq]
  · exact rankEquivalentR_nodes_eq hrank


/-- A mapped zip-indexed list keeps every declaration when each mapped edge does. -/
private theorem rge_map_decl_of_mem (l : List Edge) (n : Nat)
    (f : Edge × Nat → Edge)
    (hf : ∀ q ∈ l.zipIdx n, (f q).decl = q.1.decl) :
    (((l.zipIdx n).map f).map (·.decl) = l.map (·.decl)) := by
  induction l generalizing n with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    have htail := ih (n + 1) (fun q hq => hf q (List.mem_cons_of_mem (e, n) hq))
    rw [htail]
    have hhead := hf (e, n) (by simp)
    simpa using congrArg (fun d => d :: rest.map (·.decl)) hhead

/-- The region candidate preserves edge declarations: `none` via
`componentCandidate_decls`, `some` via the copied induction with the flag
function (premise by `split <;> rfl`), chained via `List.map_map` and
`Edge.original_decl`. -/
private theorem rgeCandidateRDeclsR (spec' : Option RegionSpec) (g : Graph)
    (comp : List Nat) (index : Nat) :
    (componentCandidateR spec' g comp index).edges.map (·.decl) =
      (componentGraph g comp).edges.map (·.decl) := by
  cases spec' with
  | none => exact componentCandidate_decls g comp index
  | some _ =>
    unfold componentCandidateR
    dsimp only
    let raw := componentGraph g comp
    let sourceEdges := raw.edges.map Edge.original
    let flags := if index == 2 then groupGreedyFlags
      ({ raw with edges := sourceEdges } : Graph)
      else List.replicate sourceEdges.length false
    have hzip : ((sourceEdges.zipIdx.map fun q =>
        if flags.getD q.2 false then
          { q.1 with tail := q.1.head, head := q.1.tail, reversed := true }
        else q.1).map (·.decl)) = sourceEdges.map (·.decl) :=
      rge_map_decl_of_mem sourceEdges 0 _ (fun q _ => by split <;> rfl)
    have horig : (sourceEdges.map (·.decl)) = raw.edges.map (·.decl) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro e _
      exact Edge.original_decl e
    rw [hzip, horig]

/-- `Edge.original` is idempotent (copy of the private
`original_idempotent` of `ExecutedPortsFacts.lean`). -/
private theorem rge_original_idempotent (edge : Edge) :
    edge.original.original = edge.original := by
  cases hr : edge.reversed <;> simp [Edge.original, hr]

/-- `Edge.original` commutes with node remapping, stated with explicit
constructors to avoid structure-update syntax (the update form is used only
in already-compiled files). -/
private theorem rge_original_remap (edge : Edge) (f : Nat → Nat) :
    (Edge.mk (f edge.tail) (f edge.head) edge.minLen edge.decl
        edge.reversed).original =
      Edge.mk (f edge.original.tail) (f edge.original.head)
        edge.original.minLen edge.original.decl edge.original.reversed := by
  cases edge with
  | mk t h m d r => cases r <;> rfl

/-- An `original` node is never reversed (both `Edge.original` branches clear
the flag). -/
private theorem rge_original_reversed_false (edge : Edge) :
    (edge.original).reversed = false := by
  cases h : edge.reversed <;> simp [Edge.original, h]

/-- Index lookup on a member (copy of the private `comp_idxOf_lookup` of
`FlatGroupEndpointsProof.lean`). -/
private theorem rge_comp_idxOf_lookup {comp : List Nat} {x : Nat}
    (hmem : x ∈ comp) :
    comp[comp.idxOf x]? = some x :=
  (List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem)).trans
    (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)))

/-- The prepared alias is the identity on plain endpoints (copy of the
private `prepared_alias_of_effective_node_roles` of `ExecutedPortsFacts.lean`). -/
private theorem rge_prepared_alias_of_effective_node_roles
    {inp : Input} {raw : Edge} {source target : ModelBox}
    (hsource : inp.boxes[raw.tail]? = some source)
    (htarget : inp.boxes[raw.head]? = some target)
    (hs : source.role = .node ∨
      inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = true)
    (ht : target.role = .node ∨
      inp.fixedSizes.any (fun fixed => fixed.1 == target.id) = true) :
    Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box) raw = raw := by
  cases hsf : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) <;>
    cases htf : inp.fixedSizes.any (fun fixed => fixed.1 == target.id) <;>
      rcases hs with hs | hs <;> rcases ht with ht | ht <;>
        simp [Compound.aliasEdge, Compound.endpoint, List.getElem?_map,
          hsource, htarget, hsf, htf, hs, ht] at *

/-- The prepared alias is the identity on plain endpoints (copy of the
private `prepared_alias_of_node_roles` of `ExecutedPortsFacts.lean`). -/
private theorem rge_prepared_alias_of_node_roles
    {inp : Input} {raw : Edge} {source target : ModelBox}
    (hsource : inp.boxes[raw.tail]? = some source)
    (htarget : inp.boxes[raw.head]? = some target)
    (hs : source.role = .node) (ht : target.role = .node) :
    Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
      else box) raw = raw := by
  exact rge_prepared_alias_of_effective_node_roles hsource htarget
    (Or.inl hs) (Or.inl ht)

/-- Region title-node rewiring for metadata transfer (copy of private
`rfc4TitleRF` of `RegionFlatC4.lean`). -/
private def rgeTitleRF (node : ProperNode) : ProperNode :=
  if node.node.border == -2 || node.node.border == 2 then
    { node with node := { node.node with w := 0, h := 0 } } else node

/-- Dummy preservation of the rewiring (copy of private
`rfc4TitleRF_dummy`). -/
private theorem rgeTitleRF_dummy (n : ProperNode) :
    (rgeTitleRF n).dummy = n.dummy := by
  unfold rgeTitleRF
  split <;> rfl

/-- Nodes of the region title reservation (copy of private
`rfc4TitleReservationsR_nodes`). -/
private theorem rgeTitleReservationsR_nodes (titles : List (Int × Int))
    (pad : Int) (p : Proper) :
    (titleReservationsR titles pad p).nodes = p.nodes.map rgeTitleRF ++
      (p.nodes.zipIdx.filter fun q => q.1.node.border == -2).map fun q => { q.1 with node := { q.1.node with border := 3, loopExtent := 0, h := (titles.getD q.1.node.decl (0, 0)).2 + pad } } := rfl

/-- Edges of the region title reservation (copy of private
`rfc4TitleReservationsR_edges`). -/
private theorem rgeTitleReservationsR_edges (titles : List (Int × Int))
    (pad : Int) (p : Proper) :
    (titleReservationsR titles pad p).edges = p.edges := rfl

/-- Region executed nodes are real, no-spec case: replay of
`X_componentRun_source_isReal` over `componentRunR_specR` (the coordinate
graph is `coordinateGraphX` via `coordinateGraphR_none`). -/
private theorem rgeIsRealR_none {P : Params} {exact : List Nat} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunR P exact none inp cg labels orderOptions = .ok (cg', run))
    {v : Nat} {node : Node} (hnode : cg.nodes[v]? = some node) :
    RouteImpl.IsReal run.proper v := by
  have hnode' : cg'.nodes[v]? = some node := by
    have heq := rgeRunNodesEqR hrun
    rw [heq]
    exact hnode
  obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
    reserved, placedProper, q0, yt, ysMid, hs⟩ := componentRunR_specR hrun
  obtain ⟨hRs, hRank, hNorm, hLabels, hCoord, hMin, hOrd, hLabelWidths, hPlaced,
    hProxy, hDrop, hLanes, hYt, hYsMid, hReserve, hRoutes, hRouting, hCoordProper,
    hCoordYs, hBudget, hExact⟩ := hs
  have hrs : rs = none := by
    have h := (newComponentRegions_none P inp cg).symm.trans hRs
    simpa using (Except.ok.inj h).symm
  rcases hPlaced with ⟨_, _, _, _, hPeq⟩ | ⟨rm, m, hrsSome, _, _⟩
  · have hc : coordinateGraphX P exact labeled = run.coordinateProper := by
      rw [hCoordProper, hPeq, ← hCoord, coordinateGraphR_none]
    have hnormalized := normalize_node_record hNorm hnode'
    have hlabeled := addLabelNodes_untouched_node hLabels hnormalized rfl
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
    obtain ⟨out, hout, hod, _, _⟩ := (proxyWidths_rel hProxy).2.2.2.2.1 v _
      (by rw [← hCoordProper]; exact hcoordinate')
    have hfinal : run.proper.nodes[v]? = some out := by
      rw [← hDrop]
      exact hout
    intro nd hnd
    have heq := Option.some.inj (hnd.symm.trans hfinal)
    subst nd
    exact hod.trans (hmd.trans (hcd.trans (hbd.trans (htd.trans hsd))))
  · exact absurd hrsSome (by rw [hrs]; simp)

/-- Region executed nodes are real, some-spec case: same chain with the
region title reservations; the cross-coordinate step uses the proved
`rfc4CrossCoordsR_metadata_holds`. -/
private theorem rgeIsRealR_some {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} (s : RegionSpec)
    (hspec : spec = some s)
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {v : Nat} {node : Node} (hnode : cg.nodes[v]? = some node) :
    RouteImpl.IsReal run.proper v := by
  subst hspec
  have hnode' : cg'.nodes[v]? = some node := by
    have heq := rgeRunNodesEqR hrun
    rw [heq]
    exact hnode
  obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
    reserved, placedProper, q0, yt, ysMid, hs⟩ := componentRunR_specR hrun
  obtain ⟨hRs, hRank, hNorm, hLabels, hCoord, hMin, hOrd, hLabelWidths, hPlaced,
    hProxy, hDrop, hLanes, hYt, hYsMid, hReserve, hRoutes, hRouting, hCoordProper,
    hCoordYs, hBudget, hExact⟩ := hs
  have hnormalized := normalize_node_record hNorm hnode'
  have hlabeled := addLabelNodes_untouched_node hLabels hnormalized rfl
  have hsized : Metadata.NodeMetadata labeled (sizeProperPortsX P exact labeled) := by
    apply Metadata.nodeMetadata_of_lookup_maps
    intro index
    have hk := congrArg (Option.map (fun t : Bool × Int × List Nat => t.1))
      (sizeProperPortsX_key P exact labeled index)
    simpa only [Option.map_map, Function.comp_def] using hk
  have htitled : Metadata.NodeMetadata (sizeProperPortsX P exact labeled)
      (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled)) :=
    Metadata.nodeMetadata_map_append rgeTitleRF rgeTitleRF_dummy _
      (rgeTitleReservationsR_nodes _ _ _)
  have hbordered := Metadata.nodeMetadata_borderExtension
    (OrderImpl.addClusterBorders_metadata (titleReservationsR s.titles P.clusterPad
      (sizeProperPortsX P exact labeled)) P.clusterBorderW)
  have hcleared : Metadata.NodeMetadata
      (OrderImpl.addClusterBorders (titleReservationsR s.titles P.clusterPad
        (sizeProperPortsX P exact labeled)) P.clusterBorderW)
      (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservationsR s.titles P.clusterPad
          (sizeProperPortsX P exact labeled)) P.clusterBorderW)) :=
    Metadata.nodeMetadata_map clearF (fun nd => (clearF_keys nd).1)
      (clearProxyExtents_nodes _)
  obtain ⟨sized, hs, hsd⟩ := hsized v _ hlabeled
  obtain ⟨titled, ht, htd⟩ := htitled v _ hs
  obtain ⟨bordered, hb, hbd⟩ := hbordered v _ ht
  obtain ⟨cleared, hclear, hcd⟩ := hcleared v _ hb
  obtain ⟨coordinate, hcoordinate, hmd⟩ := materialize_exists _ hclear
  have hcoord : pCoord.nodes[v]? = some coordinate := by
    have hpc : pCoord = materializeDummyPaths (clearProxyExtents
      (OrderImpl.addClusterBorders (titleReservationsR s.titles P.clusterPad
        (sizeProperPortsX P exact labeled)) P.clusterBorderW)) := by
      rw [← hCoord]
      rfl
    rw [hpc]
    exact hcoordinate
  rcases hPlaced with ⟨_, _, _, _, hPeq⟩ | ⟨rm, m, _, _, hcrossRun⟩
  · have hplaced : placedProper.nodes[v]? = some coordinate := by
      rw [hPeq]
      exact hcoord
    obtain ⟨out, hout, hod, _, _⟩ := (proxyWidths_rel hProxy).2.2.2.2.1 v _ hplaced
    have hfinal : run.proper.nodes[v]? = some out := by
      rw [← hDrop]
      exact hout
    intro nd hnd
    have heq := Option.some.inj (hnd.symm.trans hfinal)
    subst nd
    exact hod.trans (hmd.trans (hcd.trans (hbd.trans (htd.trans hsd))))
  · obtain ⟨pnd, hpnd, hpdd⟩ :=
      rfc4CrossCoordsR_metadata_holds hcrossRun v _ hcoord
    obtain ⟨out, hout, hod, _, _⟩ := (proxyWidths_rel hProxy).2.2.2.2.1 v _ hpnd
    have hfinal : run.proper.nodes[v]? = some out := by
      rw [← hDrop]
      exact hout
    intro nd hnd
    have heq := Option.some.inj (hnd.symm.trans hfinal)
    subst nd
    exact hod.trans (hpdd.trans (hmd.trans (hcd.trans (hbd.trans (htd.trans hsd)))))

/-- Region executed nodes are real: dispatcher over the spec. -/
theorem rgeIsRealR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {v : Nat} {node : Node} (hnode : cg.nodes[v]? = some node) :
    RouteImpl.IsReal run.proper v := by
  cases spec with
  | none => exact rgeIsRealR_none hrun hnode
  | some s => exact rgeIsRealR_some s rfl hrun hnode

/-- Region runs keep a well-shaped proper graph: dispatcher over the spec
(the `some` arm uses the proved cross-coords row). -/
private theorem rgeProperShapeR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    RouteImpl.ProperShape run.proper := by
  cases spec with
  | none => exact componentRunR_properShape_noneR hrun
  | some s => exact componentRunR_properShape_someR rfc4CrossCoordsR_metadata_holds s rfl hrun

/-- First-edge lookup along a real-headed chain (copy of the private
`real_tail_first` of `ExecutedPortsFacts.lean`). -/
private theorem rge_real_tail_first {p : Proper} {v : Nat}
    (hv : RouteImpl.IsReal p v) :
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
    · obtain ⟨first, hfirst, htail⟩ := rge_real_tail_first hv (b :: rest)
        hc.2 e hm ht
      have hbf : b = first := Option.some.inj hfirst
      have hb : (RouteImpl.edgeAt p b).tail = v := by
        simpa only [hbf] using htail
      obtain ⟨_, _, _, nd, hnd, hdummy⟩ := hc.1
      have hreal := hv nd (by rw [← hb]; exact hnd)
      rw [hreal] at hdummy
      contradiction

/-- Last-edge lookup along a real-headed chain (copy of the private
`real_head_last` of `ExecutedPortsFacts.lean`). -/
private theorem rge_real_head_last {p : Proper} {v : Nat}
    (hv : RouteImpl.IsReal p v) :
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
    · obtain ⟨last, hlast, hhead⟩ := rge_real_head_last hv (b :: rest)
        hc.2 e hm ht
      exact ⟨last, by simpa only [List.getLast?_cons_cons] using hlast, hhead⟩

/-- Edge-index lookup from a record (copy of the private `mem_edgesOf_of_record`
of `ExecutedPortsFacts.lean`). -/
private theorem rge_mem_edgesOf_of_record {p : Proper} {i : Nat}
    {edge : ProperEdge} (hm : edge ∈ p.edges) (ho : edge.original = i) :
    ∃ k ∈ RouteImpl.edgesOf p i, RouteImpl.edgeAt p k = edge := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
  have hb := (List.getElem?_eq_some_iff.mp hk).1
  have hrecord : RouteImpl.edgeAt p k = edge := by
    simp only [RouteImpl.edgeAt, List.getD_eq_getElem?_getD, hk,
      Option.getD_some]
  refine ⟨k, ?_, hrecord⟩
  apply List.mem_filter.mpr
  exact ⟨List.mem_range.mpr hb, by simp only [hrecord, ho, beq_self_eq_true]⟩

/-- Region-run semantic chains cover every rewritten-graph edge (replay of
`X_componentRun_semantic_node_chain` over `rcbNormalizedSourceR`). -/
private theorem rgeSemanticChainR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {i : Nat} {edge : Edge} (hedge : cg'.edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∃ chain : List Nat,
      run.proper.chains[i]? = some chain ∧ 2 ≤ chain.length ∧
      chain.head? = some edge.tail ∧ chain.getLast? = some edge.head ∧
      ∀ (j : Nat) (hj : j < chain.length) (hj1 : j + 1 < chain.length),
        ∃ properEdge ∈ run.proper.edges,
          properEdge.original = i ∧ properEdge.decl = edge.decl ∧
          properEdge.tail = chain[j] ∧ properEdge.head = chain[j + 1] := by
  obtain ⟨ranks, normalized, hn, he, hc⟩ := rcbNormalizedSourceR hrun
  have hchain := (normalize_ok hn).2.2 i (List.getElem?_eq_some_iff.mp hedge).1 edge hedge
  change NormalizeImpl.ChainFact cg'.edges normalized (edge, i) normalized.chains[i]? at hchain
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

/-- Region-run chains expose their endpoints (replay of
`X_componentRun_chain_endpoints` over the region semantic chain, region
`IsReal` and `ProperShape`). -/
private theorem rgeChainEndpointsR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {i : Nat} {edge : Edge} (hedge : cg'.edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∃ first last,
      (RouteImpl.edgesOf run.proper i).head? = some first ∧
      (RouteImpl.edgesOf run.proper i).getLast? = some last ∧
      (RouteImpl.edgeAt run.proper first).tail = edge.tail ∧
      (RouteImpl.edgeAt run.proper last).head = edge.head := by
  obtain ⟨chain, hchain, hlen, hhead, hlast, hsegments⟩ :=
    rgeSemanticChainR hrun hedge hne
  obtain ⟨ranks, normalized, hn, _, _⟩ := rcbNormalizedSourceR hrun
  have hwf := (normalize_node_rank_alignment hn).2
  have hbounds := RankImpl.wellformed_spec hwf edge (List.mem_of_getElem? hedge)
  have htailReal : RouteImpl.IsReal run.proper edge.tail :=
    rgeIsRealR hrun
      (by rw [← rgeRunNodesEqR hrun]; exact List.getElem?_eq_getElem hbounds.1)
  have hheadReal : RouteImpl.IsReal run.proper edge.head :=
    rgeIsRealR hrun
      (by rw [← rgeRunNodesEqR hrun]; exact List.getElem?_eq_getElem hbounds.2.1)
  have hproper := (rgeProperShapeR hrun) i
  obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp hhead
  obtain ⟨firstEdge, hfirstMem, hfirstOriginal, _, hfirstTail, _⟩ :=
    hsegments 0 (by omega) (by omega)
  obtain ⟨firstIndex, hfirstIndex, hfirstRecord⟩ :=
    rge_mem_edgesOf_of_record hfirstMem hfirstOriginal
  have hfirstValue : (RouteImpl.edgeAt run.proper firstIndex).tail = edge.tail := by
    rw [hfirstRecord]
    exact hfirstTail
  obtain ⟨first, hfirst, hfirstTail⟩ :=
    rge_real_tail_first htailReal _ hproper firstIndex hfirstIndex hfirstValue
  obtain ⟨lastEdge, hlastMem, hlastOriginal, _, _, hlastHead⟩ :=
    hsegments ((edge.tail :: rest).length - 2) (by omega) (by omega)
  obtain ⟨lastIndex, hlastIndex, hlastRecord⟩ :=
    rge_mem_edgesOf_of_record hlastMem hlastOriginal
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
    rge_real_head_last hheadReal _ hproper lastIndex hlastIndex hlastValue'
  exact ⟨first, last, hfirst, hlast, hfirstTail, hlastHead⟩

/-- Region route-component source: every input route index resolves through
the exact graph to a selected component, a region run, loops, and a placed
part (replay of `SceneExecution.route_component_source` with
`actual_components_parts_geometryR`). -/
theorem rgeRouteSourceR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {key : Nat} (hkey : key < inp.routes.length) :
    ∃ (packed : Pack.State) (c : Nat) (q : (List Nat × Part) × Rect)
      (candidate : Nat) (run : Run) (loops : List (Nat × LoopPlacement))
      (area : Int) (spec' : Option RegionSpec) (cg : Graph)
      (i : Nat) (edge : Edge),
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
      (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q ∧
      componentRunR execution.params (exactDecls exactIds inp) spec' inp
        (componentCandidateR spec' execution.graph q.1.1 candidate)
        execution.measured (candidateOrder candidate) = .ok (cg, run) ∧
      componentLoops execution.params cg run execution.measured = .ok loops ∧
      q.1.2 = { placeComponentExact execution.params cg run 0
        execution.measured loops with area := area } ∧
      cg.edges[i]? = some edge ∧ edge.decl = key := by
  have hdecl : key ∈ execution.graph.edges.map (·.decl) := by
    rw [exactGraph_decl_rangeX execution.graph0_eq execution.graph_eq]
    exact List.mem_range'.mpr ⟨key, hkey, by omega⟩
  obtain ⟨globalEdge, hglobalEdge, hglobalDecl⟩ := List.mem_map.mp hdecl
  have hglobalBounds := sceneExecutionR_edges_boundedR execution globalEdge
    (List.mem_append_left _ hglobalEdge)
  obtain ⟨component, hcomponent, htail⟩ :=
    components_cover hglobalBounds.1 (sceneExecutionR_edges_boundedR execution)
  obtain ⟨hparts, hall⟩ := actual_components_parts_geometryR (by rfl)
    execution.components_eq
  have hcomponentPart : component ∈ execution.componentsAcc.parts.map (·.1) := by
    rw [hparts]
    exact hcomponent
  obtain ⟨part, hpartMember, hpartComponent⟩ := List.mem_map.mp hcomponentPart
  obtain ⟨candidate, _, cg, run, loops, area, spec', _, _, _, _, hrun,
    hloops, hpartdef⟩ := hall part hpartMember
  have htailPart : globalEdge.tail ∈ part.1 := by
    simpa only [hpartComponent] using htail
  have hrawDecl : globalEdge.decl ∈
      (componentGraph execution.graph part.1).edges.map (·.decl) := by
    unfold componentGraph
    dsimp only
    apply List.mem_map.mpr
    refine ⟨Edge.mk (part.1.idxOf globalEdge.tail)
      (part.1.idxOf globalEdge.head) globalEdge.minLen globalEdge.decl
      globalEdge.reversed, ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨globalEdge, List.mem_filter.mpr
      ⟨hglobalEdge, List.contains_iff_mem.mpr htailPart⟩, rfl⟩
  have hcandDecl : globalEdge.decl ∈ (componentCandidateR spec'
      execution.graph part.1 candidate).edges.map (·.decl) := by
    rw [rgeCandidateRDeclsR]
    exact hrawDecl
  have hrankDecl : globalEdge.decl ∈ cg.edges.map (·.decl) := by
    rw [componentRunR_edges_declsR hrun]
    exact hcandDecl
  rw [hglobalDecl] at hrankDecl
  obtain ⟨edge, hedgeMember, hedgeDecl⟩ := List.mem_map.mp hrankDecl
  obtain ⟨i, hedge⟩ := List.mem_iff_getElem?.mp hedgeMember
  obtain ⟨packed, hpacked, _⟩ := packAcc_components_disjoint execution.packed_eq
  obtain ⟨c, hpartIndex⟩ := List.mem_iff_getElem?.mp hpartMember
  have hc := (List.getElem?_eq_some_iff.mp hpartIndex).1
  have hpackedCount : packed.boxes.length =
      execution.componentsAcc.parts.length := by
    simpa only [List.length_map] using Pack.pack_count hpacked
  have hpositionBound : c < packed.boxes.length := by omega
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
      some (part, packed.boxes[c]'hpositionBound) :=
    List.getElem?_zip_eq_some.mpr
      ⟨hpartIndex, List.getElem?_eq_getElem hpositionBound⟩
  exact ⟨packed, c, (part, packed.boxes[c]'hpositionBound), candidate, run,
    loops, area, spec', cg, i, edge, hpacked, hselected, hrun, hloops,
    hpartdef, hedge, hedgeDecl⟩

/-- Region scene-box lookup from box ids (copy of
`Xc_source_box_lookup_of_box_ids_nodupX` via `boxes_eq_mapR`). -/
private theorem rgeSourceBoxLookupR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
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
    rw [execution.boxes_eq_mapR]
    simp only [List.getElem?_map, List.getElem?_zipIdx, hsource,
      Option.map_some, Nat.zero_add]
    rfl
  have hids : (res.scene.boxes.map (·.id)) = inp.boxes.map (·.id) := by
    rw [execution.boxes_eq_mapR, List.map_map]
    exact zipIdx_map_comp (·.id) inp.boxes 0
  have hnodup : (res.scene.boxes.map (·.id)).Nodup := by
    rw [hids]
    exact hboxIds
  change res.scene.boxes.find? (fun candidate => candidate.id == source.id) = some box
  exact Assembly.keyed_lookup_eq (·.id) res.scene.boxes hnodup box
    (List.mem_of_getElem? hbox)

/-- Region part-entry dump lookup (copy of
`Xc_part_entry_box_lookup_of_box_ids_nodupX` via `actual_components_packed_rect_valueR`). -/
private theorem rgePartEntryDumpR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
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
    execution.components_rects_sizeR
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [hsize]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hrect := actual_components_packed_rect_valueR (by rfl)
    execution.components_eq execution.packed_eq packed hpacked
    hselected hentry hkeysize default
  have hlookup := rgeSourceBoxLookupR execution hids hsource
  rw [hrect] at hlookup
  exact hlookup

end PipelineImpl
end Layered
end Elegant

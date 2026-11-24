import Elegant.Layered.ExactFlatC6WProof
import Elegant.Layered.ExactFlatC6Proof
import Elegant.Layered.ExactFlatC6KeysPathsProof
import Elegant.Layered.ExactRunPathGroupsProof
import Elegant.Layered.ExactFlatC7ExclusiveKey
import Elegant.Layered.ExactFlatC7
import Elegant.Layered.ExactFlatC5ChosenPart
import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.RouteScopeClearance
import Elegant.Layered.RunStagePathFacts
import Elegant.Layered.PartSeparation
import Elegant.Layered.RouteTransport
import Elegant.Layered.ComponentCoverage

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact flat C6 bridge and chain, W form (in progress).

The route-scope bridge `x6_routeScopeBridgeW_holds` recovers the packed
placement of an exclusive scene box. Same-part boxes come from real run
nodes with declarations outside every proper-node cluster path; other-part
boxes are contained in their own transported shelf.

`x6_scopedW_holds` proves that run route endpoints land inside the scene
route scope, using `X6_chainEndpointKeysW_holds`. It supplies the
endpoint-identity step in the chain case.

Exact-run replay infrastructure:
* The private `x6bc_` lemmas cover declaration preservation, part/component
  alignment, candidate endpoint bounds, self-loop emission, frame entries,
  reverse key lookup, and node-role border transport.

The chain case (`X6_ChainCaseW`) remains open in this file. The bridge uses
closed shelf containment, not shelf positivity. Positivity without the
fixed-size premise fails on `twoZero` in `ExactFlatC6ShelfBorderProof`.

Probe evidence (`proofs/wip/Probe/X6RouteBridgeTProbe.lean`, eight executed
inputs: flat/nested/self-loop with sane fixed sizes, empty group, census
`twoZero`, two-part degenerate, wide fixed, ill-formed):
* `bridge=true` (run-level bridge ID content) on all eight (the `ill` case
  vacuously).
* `chain=true` (scene-level miss) on all eight.
* `shelf=false` exactly on `zero` and `twoPart` (the degenerate parts),
  `fit=true` there (no labels own the fixed boxes), so a fit-conditioned
  shelf is still false and is not used; the missing piece is part positivity.
-/
/-- `sizeProperPortsX` keeps declarations (prefixed copy of the private
`X_sizeProperPortsX_decl` in `ExactFlatC7ExclusiveKey`). -/
private theorem x6bc_sizeX_decl {P : Params} {exact : List Nat} {p : Proper}
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (sizeProperPortsX P exact p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧ qn.node.clusterPath = nd.node.clusterPath := by
  unfold sizeProperPortsX
  simp only [List.getElem?_map, List.getElem?_zipIdx, hv, Option.map_some]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩ <;> split <;> rfl

/-- The exact coordinate graph keeps every prefix declaration and path
(prefixed copy of the private `X_coordinateGraphX_decl_prefix`). -/
private theorem x6bc_coordX_decl_prefix {P : Params} {exact : List Nat} {p : Proper}
    {v : Nat} {nd : ProperNode} (hv : p.nodes[v]? = some nd) :
    ∃ qn : ProperNode, (coordinateGraphX P exact p).nodes[v]? = some qn ∧
      qn.node.decl = nd.node.decl ∧ qn.dummy = nd.dummy ∧
      qn.node.border = nd.node.border ∧
      (nd.dummy = false → qn.node.clusterPath = nd.node.clusterPath) := by
  unfold coordinateGraphX at ⊢
  obtain ⟨s1, hs1, hdecl1, hdum1, hbord1, hpath1⟩ := x6bc_sizeX_decl hv
  obtain ⟨t1, ht1, hdecl2, hdum2, hbord2, hpath2⟩ := titleReservations_decl hs1
  obtain ⟨c1, hc1, hdecl3, hdum3, hbord3, hpath3⟩ :=
    addClusterBorders_decl (w := P.clusterBorderW) ht1
  obtain ⟨e1, he1, hdecl4, hdum4, hbord4, hpath4⟩ := clearProxyExtents_decl hc1
  obtain ⟨m1, hm1, hdecl5, hdum5, hbord5⟩ := materialize_decl he1
  refine ⟨m1, hm1, ?_, ?_, ?_, ?_⟩
  · exact hdecl5.trans (hdecl4.trans (hdecl3.trans (hdecl2.trans hdecl1)))
  · exact hdum5.trans (hdum4.trans (hdum3.trans (hdum2.trans hdum1)))
  · exact hbord5.trans (hbord4.trans (hbord3.trans (hbord2.trans hbord1)))
  · intro hnd
    have he1dum : e1.dummy = false := by
      have h1 : s1.dummy = nd.dummy := hdum1
      have h2 : t1.dummy = s1.dummy := hdum2
      have h3 : c1.dummy = t1.dummy := hdum3
      have h4 : e1.dummy = c1.dummy := hdum4
      rw [h4, h3, h2, h1, hnd]
    have hme : m1.node.clusterPath = e1.node.clusterPath := by
      have hlookup : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some e1 := he1
      unfold materializeDummyPaths at hm1
      simp only [List.getElem?_map, List.getElem?_zipIdx, hlookup,
        Option.map_some] at hm1
      have hF : e1.dummy = false := he1dum
      simp only [hF, Bool.false_eq_true, ↓reduceIte] at hm1
      have heq := Option.some.inj hm1
      rw [heq]
    rw [hme, hpath4, hpath3, hpath2, hpath1]

/-- Every original candidate node survives the exact run with its declaration
(prefixed copy of the private `X_runDeclOfCandidate`). -/
private theorem x6bc_runDeclOfCandidate {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {n : Node} (hn : cg.nodes[v]? = some n) :
    ∃ out : ProperNode, run.proper.nodes[v]? = some out ∧ out.node.decl = n.decl := by
  obtain ⟨_, p0, labeled, q0, hn0, hl0, hcoord, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨pn0, hpn0, hdecl0, _, _, _⟩ := normalize_decl_prefix hn0 hn
  obtain ⟨pn1, hpn1, hdecl1, _, _, _⟩ := addLabelNodes_decl _ _ _ hl0 hpn0
  obtain ⟨pn2, hpn2, hdecl2, _, _, _⟩ := x6bc_coordX_decl_prefix hpn1
  have hpn2c : run.coordinateProper.nodes[v]? = some pn2 := by
    rw [← hcoord]
    exact hpn2
  obtain ⟨pn3, hpn3, hdecl3, _, _, _⟩ := proxyWidths_decl_path hproxy hpn2c
  have hpn3q : q0.nodes[v]? = some pn3 := hpn3
  obtain ⟨pn4, hpn4, hdecl4, _, _, _⟩ := dropSynthetic_decl (p := q0) hpn3q
  have hpn4r : run.proper.nodes[v]? = some pn4 := by
    rw [← hdrop]
    exact hpn4
  exact ⟨pn4, hpn4r, hdecl4.trans (hdecl3.trans (hdecl2.trans (hdecl1.trans hdecl0)))⟩


/-- A model endpoint box of a real edge lies in the dump scope of any scene
route with the same endpoints (prefixed copy of the private `boxIdInScope`). -/
private theorem x6bc_boxIdInScope {inp : Input} {res : FamilyResult}
    {route₀ : ModelRoute} {index : Nat} {raw : Edge}
    (hraw : edgeOf inp route₀ index = .ok raw)
    {route : Route} (hfrom : route.fromId = route₀.fromId) (hto : route.toId = route₀.toId)
    {D : Nat} (hD : D = raw.tail ∨ D = raw.head)
    {b : ModelBox} (hb : inp.boxes[D]? = some b) :
    b.id ∈ LayoutDump.routeScope res.scene.layoutDump route := by
  obtain ⟨_, _, source, target, hsource, hsourceId, htarget, htargetId⟩ :=
    edgeOf_semantic_endpoints hraw
  rcases hD with rfl | rfl
  · have heq : b = source := Option.some.inj (hb.symm.trans hsource)
    rw [heq, hsourceId, ← hfrom]
    simp [LayoutDump.routeScope]
  · have heq : b = target := Option.some.inj (hb.symm.trans htarget)
    rw [heq, htargetId, ← hto]
    simp [LayoutDump.routeScope]

/-- Run route endpoints land inside the scene route scope, over executed
exact runs (replay of `runRouteEndpointIdsScoped_of_keys` through the exact
chain/model lemmas and the closed chain keys). -/
private theorem x6bc_scopedW {exactIds : List String}
    (hkeys : X6_ChainEndpointKeysW exactIds)
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (hcomp : comp ∈ components execution.graph)
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (i : Nat) (edge : Edge) (native : EdgeRoute) (route : Route)
    (hedge : (componentCandidate execution.graph comp candidate).edges[i]? = some edge)
    (hnative : run.routes[i]? = some native)
    (horiginal : native.original = i)
    (hkeyedge : res.scene.routes[edge.decl]? = some route)
    (i₀ i₁ : Nat)
    (hfirst : (RouteImpl.edgesOf run.proper native.original).head? = some i₀)
    (hlast : (RouteImpl.edgesOf run.proper native.original).getLast? = some i₁) :
    (∀ b₀ : ModelBox,
      inp.boxes[RouteImpl.nodeDecl run.proper (RouteImpl.edgeAt run.proper i₀).tail]? =
        some b₀ →
      b₀.id ∈ LayoutDump.routeScope res.scene.layoutDump route) ∧
    (∀ b₁ : ModelBox,
      inp.boxes[RouteImpl.nodeDecl run.proper (RouteImpl.edgeAt run.proper i₁).head]? =
        some b₁ →
      b₁.id ∈ LayoutDump.routeScope res.scene.layoutDump route) := by
  obtain ⟨tailKey, headKey, index, route₀, raw, nT, nH,
    hcompT, hcompH, hnT, hnH, hdeclT, hdeclH, hroute₀, hraw, hdeclIdx⟩ :=
    hkeys execution hwf hfp comp candidate run hcomp hrun i edge native hnative
      horiginal hedge i₀ i₁ hfirst hlast
  have hcandT : (componentCandidate execution.graph comp candidate).nodes[(RouteImpl.edgeAt run.proper i₀).tail]? = some nT :=
    candidate_node_of_part_key hcompT hnT
  have hcandH : (componentCandidate execution.graph comp candidate).nodes[(RouteImpl.edgeAt run.proper i₁).head]? = some nH :=
    candidate_node_of_part_key hcompH hnH
  obtain ⟨outT, houtT, hdecl2T⟩ := x6bc_runDeclOfCandidate hrun hcandT
  obtain ⟨outH, houtH, hdecl2H⟩ := x6bc_runDeclOfCandidate hrun hcandH
  have hndT : RouteImpl.nodeDecl run.proper (RouteImpl.edgeAt run.proper i₀).tail = outT.node.decl := by
    unfold RouteImpl.nodeDecl
    simp only [houtT]
  have hndH : RouteImpl.nodeDecl run.proper (RouteImpl.edgeAt run.proper i₁).head = outH.node.decl := by
    unfold RouteImpl.nodeDecl
    simp only [houtH]
  have hk : index < inp.routes.length := (List.getElem?_eq_some_iff.mp hroute₀).1
  have hsceneT : res.scene.routes[index]? = some route := by
    rw [← hdeclIdx]; exact hkeyedge
  have hse := execution.scene_eq
  rw [hse] at hsceneT
  have hget := sceneOf_routes_getElem? execution.params inp o execution.lines execution.packedAcc execution.measured index hk
  have hmap := congrArg (Option.map Route.fromId) (hget.symm.trans hsceneT)
  have hmapT := congrArg (Option.map Route.toId) (hget.symm.trans hsceneT)
  simp only [Option.map_some, Option.some.injEq] at hmap hmapT
  have hmod : inp.routes[index] = route₀ := (List.getElem?_eq_some_iff.mp hroute₀).2
  have hfrom : route.fromId = route₀.fromId := hmap.symm.trans (congrArg ModelRoute.fromId hmod)
  have hto : route.toId = route₀.toId := hmapT.symm.trans (congrArg ModelRoute.toId hmod)
  constructor
  · intro b₀ hb₀
    rw [hndT, hdecl2T] at hb₀
    rcases hdeclT with hT | hT
    · exact x6bc_boxIdInScope hraw hfrom hto (Or.inl hT) hb₀
    · exact x6bc_boxIdInScope hraw hfrom hto (Or.inr hT) hb₀
  · intro b₁ hb₁
    rw [hndH, hdecl2H] at hb₁
    rcases hdeclH with hH | hH
    · exact x6bc_boxIdInScope hraw hfrom hto (Or.inl hH) hb₁
    · exact x6bc_boxIdInScope hraw hfrom hto (Or.inr hH) hb₁

/-- Exact emitted self edge (prefixed copy of the private
`X_componentLoops_emitted_self_edgeX` over `placeComponentExact`). -/
private theorem x6bc_loops_emitted_self_edgeX
    {P : Params} {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {loops : List (Nat × LoopPlacement)}
    (hloops : componentLoops P cg run labels = .ok loops)
    {i : Nat} {edge : Edge} (hedge : cg.edges[i]? = some edge)
    (hv : edge.tail < cg.nodes.length) (hself : edge.tail = edge.head)
    (cursor : Int) :
    ∃ q ∈ loops,
      loops.find? (fun loop => loop.1 == edge.decl) = some q ∧ q.1 = edge.decl ∧
      (placeComponentExact P cg run cursor labels loops).routes[i]? =
        some (edge.decl, q.2.points.map
          (shiftPoint (cursor - (placeBoundsX P cg run labels loops).minX)
            (-(placeBoundsX P cg run labels loops).minY))) := by
  obtain ⟨placement, hplacement⟩ := componentLoops_entry_of_self_edge hloops
    (List.mem_of_getElem? hedge) hv hself
  cases hfind : loops.find? (fun loop => loop.1 == edge.decl) with
  | none =>
    have hn := List.find?_eq_none.mp hfind (edge.decl, placement) hplacement
    simp only [beq_self_eq_true, not_true_eq_false] at hn
  | some q =>
    have hq := List.mem_of_find?_eq_some hfind
    have hdecl : q.1 = edge.decl := by
      simpa only [beq_iff_eq] using List.find?_some hfind
    refine ⟨q, hq, rfl, hdecl, ?_⟩
    unfold placeComponentExact placeBoundsX
    dsimp only
    simp only [List.getElem?_map, zipIdx_getElem?, hedge, Option.map_some,
      hfind, Option.getD_some]

/-- Local re-proof of the private `ComponentCoverage.componentCandidate_nodes_length`:
a candidate graph has exactly the component's nodes. -/
private theorem x6bc_candidate_nodes_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- Endpoint projections of the pristine form of an edge. -/
private theorem x6bc_edge_original_tail (e : Edge) :
    e.original.tail = if e.reversed then e.head else e.tail := by
  unfold Edge.original
  cases h : e.reversed <;> simp

/-- Endpoint projections of the pristine form of an edge. -/
private theorem x6bc_edge_original_head (e : Edge) :
    e.original.head = if e.reversed then e.tail else e.head := by
  unfold Edge.original
  cases h : e.reversed <;> simp

/-- Every edge of a component candidate keeps both endpoints below the
candidate's node count (prefixed copy of the private
`candidate_edge_endpoints_bounded`). -/
private theorem x6bc_edge_endpoints_bounded (g : Graph) (comp : List Nat) (index : Nat)
    (hcomp : comp ∈ components g)
    (hbd : ∀ e ∈ g.edges ++ Compound.constraints g,
      e.tail < g.nodes.length ∧ e.head < g.nodes.length)
    {edge : Edge} (hedge : edge ∈ (componentCandidate g comp index).edges) :
    edge.tail < (componentCandidate g comp index).nodes.length ∧
      edge.head < (componentCandidate g comp index).nodes.length := by
  have hlen : (componentCandidate g comp index).nodes.length = comp.length :=
    x6bc_candidate_nodes_length g comp index
  have hmem : edge.original ∈ (componentCandidate g comp index).edges.map Edge.original :=
    List.mem_map_of_mem hedge
  rw [componentCandidate_semantic_edges g comp index] at hmem
  obtain ⟨e₁, he₁, heq⟩ := List.mem_map.mp hmem
  have he₁mem : e₁ ∈ (componentGraph g comp).edges := he₁
  change e₁ ∈ ((g.edges.filter fun e => comp.contains e.tail).map fun e =>
    { e with tail := comp.idxOf e.tail, head := comp.idxOf e.head }) at he₁mem
  obtain ⟨e₀, he₀filter, he₁def⟩ := List.mem_map.mp he₁mem
  obtain ⟨he₀mem, he₀tail⟩ := List.mem_filter.mp he₀filter
  have he₀tailmem : e₀.tail ∈ comp := List.contains_iff_mem.mp he₀tail
  obtain ⟨comp', hcomp'mem, htail', hhead'⟩ :=
    components_edge_endpoints hbd (List.mem_append_left _ he₀mem)
  have hsame : comp = comp' :=
    components_shared_member_eq hcomp hcomp'mem he₀tailmem htail'
  have he₁tail : e₁.tail = comp.idxOf e₀.tail := congrArg Edge.tail he₁def.symm
  have he₁head : e₁.head = comp.idxOf e₀.head := congrArg Edge.head he₁def.symm
  have htailLt : comp.idxOf e₀.tail < comp.length := List.idxOf_lt_length_of_mem he₀tailmem
  have hheadLt : comp.idxOf e₀.head < comp.length :=
    List.idxOf_lt_length_of_mem (hsame ▸ hhead')
  have he₁tailLt : e₁.tail < comp.length := by rw [he₁tail]; exact htailLt
  have he₁headLt : e₁.head < comp.length := by rw [he₁head]; exact hheadLt
  have ht := congrArg Edge.tail heq
  have hh := congrArg Edge.head heq
  rw [x6bc_edge_original_tail e₁, x6bc_edge_original_tail edge] at ht
  rw [x6bc_edge_original_head e₁, x6bc_edge_original_head edge] at hh
  rw [hlen]
  cases h₁ : e₁.reversed <;> cases h₂ : edge.reversed <;>
    simp only [h₁, h₂, Bool.false_eq_true, ↓reduceIte] at ht hh <;>
    constructor <;> omega

/-- Routes of an exact-placed component cover the candidate edge decls
(prefixed copy of the private `X_placeComponentExact_routes_decls`). -/
private theorem x6bc_routes_decls (P : Params) (cg : Graph) (run : Run)
    (cursor : Int) (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run cursor labels loops).routes.map (·.1) =
      cg.edges.map (·.decl) := by
  unfold placeComponentExact
  dsimp only
  rw [List.map_map]
  exact zipIdx_map_comp (·.decl) cg.edges 0

/-- The component of the selected part is the component whose run placed it
(replay of the private `part_component_aligned` over `componentRunX`). -/
private theorem x6bc_part_aligned {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {comp : List Nat} {candidate : Nat} {run : Run}
    {loops : List (Nat × LoopPlacement)} {area : Int}
    (hcomp : comp ∈ components execution.graph)
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured
      = .ok loops)
    (hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph comp candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph comp candidate).edges[i]? = some edge) :
    comp = q.1.1 := by
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hparts, hall⟩ :=
    actual_components_parts_geometryX hempty execution.components_eq
  have hq1mem : q.1 ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? (zip_getElem?_left hselected)
  have hq1comp : q.1.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hq1mem
  obtain ⟨index₀, _, run₀, loops₀, area₀, _, _, _, hrun₀, hloops₀, hpart₀⟩ :=
    hall q.1 hq1mem
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have hedgemem : edge ∈ (componentCandidate execution.graph comp candidate).edges :=
    List.mem_of_getElem? hedge
  have hbounds := x6bc_edge_endpoints_bounded execution.graph comp candidate hcomp
    (sceneExecutionX_edges_bounded execution) hedgemem
  have hgnodup : (execution.graph.edges.map (·.decl)).Nodup := by
    rw [exactGraph_edges execution.graph_eq]
    exact measuredGraph_decls_nodup execution.graph0_eq
  have hdecls :=
    componentCandidate_decls_nodup execution.graph comp candidate hgnodup
  have hemitted :
      ∃ pts : List Point,
        (edge.decl, pts) ∈
          (placeComponentExact execution.params
            (componentCandidate execution.graph comp candidate) run 0 execution.measured
            loops).routes := by
    by_cases hself : edge.tail = edge.head
    · obtain ⟨_, _, _, _, hemittedRoutes⟩ :=
        x6bc_loops_emitted_self_edgeX hloops hedge hbounds.1 hself 0
      exact ⟨_, List.mem_of_getElem? hemittedRoutes⟩
    · have hedgeIdx :
          ((componentCandidate execution.graph comp candidate).edges)[i]? =
            some ((componentCandidate execution.graph comp candidate).edges[i]) :=
        List.getElem?_eq_getElem hi
      have hloop : ∀ l ∈ loops,
          l.1 ≠ ((componentCandidate execution.graph comp candidate).edges[i]).decl :=
        componentLoops_excludes_ordinary_decl hloops hdecls hedgeIdx
          (by rw [(List.getElem?_eq_some_iff.mp hedge).2]; exact hself)
      have hemittedRoutes :=
        X_placeComponentExact_route_entry_of_producer hrun 0 loops i hi hloop
      rw [show ((componentCandidate execution.graph comp candidate).edges[i]).decl = edge.decl
        by rw [(List.getElem?_eq_some_iff.mp hedge).2]] at hemittedRoutes
      exact ⟨_, List.mem_of_getElem? hemittedRoutes⟩
  have hroutesComp : q.1.2.routes =
      (placeComponentExact execution.params
        (componentCandidate execution.graph comp candidate) run 0 execution.measured
        loops).routes := by rw [hpart]
  have hroutesOwn : q.1.2.routes =
      (placeComponentExact execution.params
        (componentCandidate execution.graph q.1.1 index₀) run₀ 0 execution.measured
        loops₀).routes := by rw [hpart₀]
  obtain ⟨pts, hpts⟩ := hemitted
  rw [← hroutesComp, hroutesOwn] at hpts
  have hkey : edge.decl ∈ (componentCandidate execution.graph q.1.1 index₀).edges.map
      (·.decl) := by
    rw [← x6bc_routes_decls execution.params
      (componentCandidate execution.graph q.1.1 index₀) run₀ 0 execution.measured loops₀]
    exact List.mem_map_of_mem hpts
  obtain ⟨e₁, he₁mem, he₁decl⟩ := List.mem_map.mp hkey
  obtain ⟨source₁, hs1mem, htail₁, hsem₁⟩ :=
    componentCandidate_semantic_source he₁mem
  obtain ⟨source₂, hs2mem, htail₂, hsem₂⟩ :=
    componentCandidate_semantic_source hedgemem
  have hd₁ : e₁.original.decl = source₁.original.decl := by rw [hsem₁]
  have hd₂ : edge.original.decl = source₂.original.decl := by rw [hsem₂]
  have hdeclEq : source₁.decl = source₂.decl := by
    have h₁ := Edge.original_decl e₁
    have h₂ := Edge.original_decl edge
    have h₃ := Edge.original_decl source₁
    have h₄ := Edge.original_decl source₂
    omega
  obtain ⟨j₁, hj₁⟩ := List.mem_iff_getElem?.mp hs1mem
  obtain ⟨j₂, hj₂⟩ := List.mem_iff_getElem?.mp hs2mem
  have hsamePos : j₁ = j₂ := by
    refine (hgnodup.getElem?_inj ?_).mp ?_
    · simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hj₁).1
    · have m₁ : (execution.graph.edges.map (·.decl))[j₁]? = some source₁.decl := by
        simp only [List.getElem?_map, hj₁, Option.map_some]
      have m₂ : (execution.graph.edges.map (·.decl))[j₂]? = some source₂.decl := by
        simp only [List.getElem?_map, hj₂, Option.map_some]
      rw [show (execution.graph.edges.map (·.decl))[j₁]? = some source₁.decl by
          simp only [List.getElem?_map, hj₁, Option.map_some],
        show (execution.graph.edges.map (·.decl))[j₂]? = some source₂.decl by
          simp only [List.getElem?_map, hj₂, Option.map_some]]
      exact congrArg some hdeclEq
  have hsource : source₁ = source₂ := by
    have hj : execution.graph.edges[j₁]? = execution.graph.edges[j₂]? := by
      rw [hsamePos]
    rw [hj₁, hj₂] at hj
    exact Option.some.inj hj
  have htail₂' : source₁.tail ∈ comp := by rw [hsource]; exact htail₂
  exact (components_shared_member_eq (a := q.1.1) (b := comp) hq1comp hcomp htail₁ htail₂').symm

/-- Exact frame entry (prefixed copy of the private `X_chosen_part_frame_entry`). -/
private theorem x6bc_frame_entry
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

/-- Reverse key lookup through `exactGraph` (prefixed copy of the private
`X_cg_key_rev`). -/
private theorem x6bc_cg_key_rev {P : Params} {exactIds : List String} {inp : Input}
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

/-- A node-role box keeps a non-`-2` border through the exact candidate
(measured-graph role fact transported across `exactGraph`). -/
private theorem x6bc_candidate_not_top {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {component : List Nat} {candidate v key : Nat} {source : ModelBox}
    (hkey : component[v]? = some key)
    (hsource : inp.boxes[key]? = some source)
    (hs : source.role = .node) :
    ((componentCandidate execution.graph component candidate).nodes.getD v default).border ≠
      -2 := by
  have hvlt : v < (componentCandidate execution.graph component candidate).nodes.length := by
    rw [x6bc_candidate_nodes_length]
    exact (List.getElem?_eq_some_iff.mp hkey).1
  have hnd : (componentCandidate execution.graph component candidate).nodes[v]? =
      some (execution.graph.nodes.getD key default) := by
    rw [componentCandidate_nodes]
    have hmap : (componentGraph execution.graph component).nodes =
        component.map (fun k => execution.graph.nodes.getD k default) := rfl
    rw [hmap, List.getElem?_map, hkey, Option.map_some]
  have hkeylen : key < execution.graph.nodes.length :=
    sceneExecutionX_graph_len execution (List.getElem?_eq_some_iff.mp hsource).1
  have hgnode : execution.graph.nodes[key]? =
      some (execution.graph.nodes.getD key default) := by
    have hsome : execution.graph.nodes[key]? =
        some (execution.graph.nodes[key]'hkeylen) := List.getElem?_eq_getElem hkeylen
    rw [List.getD_eq_getElem?_getD, hsome, Option.getD_some]
  obtain ⟨nd0, hnd0, hbord, _, _⟩ := x6bc_cg_key_rev execution.graph_eq hgnode
  have hcand0 : (componentCandidate execution.graph0 component candidate).nodes[v]? =
      some nd0 :=
    component_node_lookupX hkey hnd0
  have hgetD0 : (componentCandidate execution.graph0 component candidate).nodes.getD v
      default = nd0 := by
    rw [List.getD_eq_getElem?_getD, hcand0, Option.getD_some]
  have hnt := componentCandidate_node_role_not_top (candidate := candidate)
    execution.graph0_eq hkey hsource hs
  rw [hgetD0] at hnt
  have hgoal : (componentCandidate execution.graph component candidate).nodes.getD v
      default = execution.graph.nodes.getD key default := by
    rw [List.getD_eq_getElem?_getD, hnd, Option.getD_some]
  rw [hgoal]
  exact hbord ▸ hnt

/-- Run route endpoints land inside the scene route scope, over executed exact
runs, unconditionally: the closed chain keys (`X6_chainEndpointKeysW_holds`)
feed the replayed `runRouteEndpointIdsScoped_of_keys`. The chain same-part
branch consumes this for the endpoint-identity step. -/
theorem x6_scopedW_holds (exactIds : List String)
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (hcomp : comp ∈ components execution.graph)
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (i : Nat) (edge : Edge) (native : EdgeRoute) (route : Route)
    (hedge : (componentCandidate execution.graph comp candidate).edges[i]? = some edge)
    (hnative : run.routes[i]? = some native)
    (horiginal : native.original = i)
    (hkeyedge : res.scene.routes[edge.decl]? = some route)
    (i₀ i₁ : Nat)
    (hfirst : (RouteImpl.edgesOf run.proper native.original).head? = some i₀)
    (hlast : (RouteImpl.edgesOf run.proper native.original).getLast? = some i₁) :
    (∀ b₀ : ModelBox,
      inp.boxes[RouteImpl.nodeDecl run.proper (RouteImpl.edgeAt run.proper i₀).tail]? =
        some b₀ →
      b₀.id ∈ LayoutDump.routeScope res.scene.layoutDump route) ∧
    (∀ b₁ : ModelBox,
      inp.boxes[RouteImpl.nodeDecl run.proper (RouteImpl.edgeAt run.proper i₁).head]? =
        some b₁ →
      b₁.id ∈ LayoutDump.routeScope res.scene.layoutDump route) :=
  x6bc_scopedW (X6_chainEndpointKeysW_holds exactIds) execution hwf hfp comp candidate
    run hcomp hrun i edge native route hedge hnative horiginal hkeyedge i₀ i₁ hfirst
    hlast

/-- Recover the scene box from the route's exact component run or from a
different packed shelf. Cluster paths contain only group declarations, so
their exclusion here does not require the route-scope premise. -/
theorem x6_routeScopeBridgeW_holds (exactIds : List String) :
    X6_RouteScopeBridgeW exactIds := by
  intro inp o res execution hwf hfp packed hpacked comp candidate run loops area c q
    hcomp hrun hloops hpart hselected i edge hedge _route box _hroute hboxmem hex _hscope
  have halign : comp = q.1.1 :=
    x6bc_part_aligned execution packed hpacked hselected hcomp hrun hloops hpart hedge
  subst comp
  obtain ⟨key, hbox⟩ := List.mem_iff_getElem?.mp hboxmem
  obtain ⟨source, hsource, _, _, hexcl, hboxrect⟩ := sceneBox_source_rectX execution hbox
  have hkeylen := (List.getElem?_eq_some_iff.mp hsource).1
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact hkeylen
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  by_cases hmem : key ∈ q.1.1
  · obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
    have hvlen : v < (componentCandidate execution.graph q.1.1 candidate).nodes.length := by
      rw [x6bc_candidate_nodes_length]
      exact (List.getElem?_eq_some_iff.mp hv).1
    have hgraphlen := sceneExecutionX_graph_len execution hkeylen
    have hnode := List.getElem?_eq_getElem hgraphlen
    have hreal := X_componentRun_source_isReal hrun (component_node_lookupX hv hnode)
    have hdecl := x_exclusiveRunNodeDecl_holds exactIds inp o res execution q.1.1
      candidate run hcomp hrun v key source hv hsource
    have hnotgroup : source.role ≠ .group := by
      intro hgroup
      obtain ⟨_, _, _, _, _, _, hgroups⟩ := (wellFormed_iff (inputModel inp o)).mp hwf
      have hfalse := hgroups source (List.mem_of_getElem? hsource) hgroup
      have htrue := hexcl.symm.trans hex
      rw [hfalse] at htrue
      exact Bool.noConfusion htrue
    have hpath (u : Nat) : RouteImpl.nodeDecl run.proper v ∉
        ((run.proper.nodes[u]?).map (·.node.clusterPath)).getD [] := by
      rw [hdecl]
      intro hmempath
      cases hnodeAt : run.proper.nodes[u]? with
      | none => simp [hnodeAt] at hmempath
      | some node =>
        simp only [hnodeAt, Option.map_some, Option.getD_some] at hmempath
        exact hnotgroup (X6_runPathGroupsW_holds exactIds execution hwf hfp
          q.1.1 candidate run hcomp hrun u node hnodeAt key hmempath source hsource)
    have hentry := x6bc_frame_entry hpart hv
    have hval := actual_components_packed_rect_valueX hempty execution.components_eq
      execution.packed_eq packed hpacked hselected hentry hkeysize default
    refine ⟨v, Or.inl ⟨hvlen, hreal, ?_, ?_⟩⟩
    · intro _rt _hrt i₀ i₁ _hfirst _hlast _htail _hhead
      exact ⟨hpath (RouteImpl.edgeAt run.proper i₀).tail,
        hpath (RouteImpl.edgeAt run.proper i₁).head⟩
    · simp only [hboxrect, hval, Int.zero_sub]
  · obtain ⟨other, hother, ⟨entryKey, rect⟩, hentry, hentryKey⟩ :=
      sceneExecutionX_parts_entry execution hkeylen
    change entryKey = key at hentryKey
    subst entryKey
    obtain ⟨c', hc'⟩ := List.mem_iff_getElem?.mp hother
    have hshelfLen := part_packed_box_lenX execution packed hpacked hc'
    let shelf := packed.boxes[c']'hshelfLen
    have hshelf : packed.boxes[c']? = some shelf := List.getElem?_eq_getElem hshelfLen
    have hselected' : (execution.componentsAcc.parts.zip packed.boxes)[c']? =
        some (other, shelf) :=
      List.getElem?_zip_eq_some.mpr ⟨hc', hshelf⟩
    have hne : c' ≠ c := by
      intro hcEq
      have hq : execution.componentsAcc.parts[c']? = some q.1 := by
        rw [hcEq]
        exact zip_getElem?_left hselected
      have heq : other = q.1 := Option.some.inj (hc'.symm.trans hq)
      apply hmem
      rw [← heq]
      exact (List.of_mem_zip hentry).1
    obtain ⟨pos, hpos⟩ := List.mem_iff_getElem?.mp hentry
    have hval := actual_components_packed_rect_valueX hempty execution.components_eq
      execution.packed_eq packed hpacked hselected' hpos hkeysize default
    have hwithin :=
      (X_partsSeparated_holds (exactIds := exactIds) (inp := inp) (o := o) (res := res)
        execution packed c' other shelf hpacked hc' hshelf).2 rect (List.of_mem_zip hentry).2
    have hshelfRect (r : Rect) : shiftRect r.x r.y ⟨0, 0, r.w, r.h⟩ = r := by
      cases r
      simp [shiftRect]
    rw [hshelfRect] at hwithin
    refine ⟨0, Or.inr ⟨c', shelf, hne, hshelf, ?_⟩⟩
    rw [hboxrect, hval]
    exact hwithin

end PipelineImpl
end Layered
end Elegant

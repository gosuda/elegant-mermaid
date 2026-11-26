import Elegant.Layered.FlatC6ScopeBridgeProof
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.RouteTransport

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Flat C6 scope residuals: id-level facts of one executed component run

This module discharges the three id-level residuals used by
`Elegant.Layered.FlatC6ScopeBridgeProof`:

* `ExclusiveRunNodeDecl`: the declaration of a node of an executed component
  run is the key of its model source box.
* `RunRouteEndpointIdsScoped`: the endpoint nodes of the run route behind a
  scene route carry model-box ids inside that scene route's dump scope.
* `RoutePartShelfPositive`: the packed shelf of a part that has an edge has
  positive width and height.

Each proof is conditional on one narrow single-phase residual that is
strictly simpler than its goal, mentions only execution equations, and is
true of every successful flat execution:

* `ProperDeclPreserved` (run phase only, no boxes or geometry): proper node
  declarations follow candidate declarations through normalization, label
  insertion, coordinate preparation, proxy widths, and synthetic-edge removal.
  Every phase only widens nodes, zeroes frame reservations, appends new
  nodes, or rewrites cluster paths; none touches `node.decl` of retained
  indices.
* `ProperChainEndpointKeys` (run-to-model id transport, no scene or dump):
  the first/last proper edges of a run route sit at the candidate edge
  endpoints, the component positions resolve to global keys whose graph
  nodes carry the model endpoint declarations, and the candidate edge
  links to its model route.  Self-loop originals contribute no proper
  edges (`normalizeEdge` appends an empty chain), so the statement is
  vacuous for them.
* `PartPositiveContent` (placement phase only, no pack or dump): a placed
  part with a route entry has a positive-width rect and either a
  positive-height rect or route points with distinct y.  Width comes from a
  plain node (`node_min_w` in both profiles) or a group top (borders of
  width `cluster_border_w` in both profiles are always added and always
  belong to the top frame); height comes from a plain node, a titled group,
  or the vertical span of a chain/loop route (rank steps are positive by
  `Params.Valid`, loop placements span `2 * slot`).
-/

/-- Narrow residual R1 (run phase only): proper node declarations follow
candidate declarations for every retained index. -/
def ProperDeclPreserved (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ (v : Nat) (node : Node),
      (componentCandidate execution.graph comp candidate).nodes[v]? = some node →
      ∃ out : ProperNode, run.proper.nodes[v]? = some out ∧ out.node.decl = node.decl

/-- Narrow residual R2 (run-to-model id transport): the first/last proper
edges of a run route resolve to global keys whose graph nodes carry the
model endpoint declarations, with the candidate edge linked to its model
route.  No scene boxes, routes, or dump scopes appear. -/
def ProperChainEndpointKeys (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ (i : Nat) (edge : Edge) (native : EdgeRoute),
      (_hnative : run.routes[i]? = some native) →
      (_horig : native.original = i) →
      (componentCandidate execution.graph comp candidate).edges[i]? = some edge →
      ∀ (i₀ i₁ : Nat),
        (RouteImpl.edgesOf run.proper native.original).head? = some i₀ →
        (RouteImpl.edgesOf run.proper native.original).getLast? = some i₁ →
        ∃ (tailKey headKey index : Nat) (route₀ : ModelRoute) (raw : Edge)
          (nT nH : Node),
          comp[(RouteImpl.edgeAt run.proper i₀).tail]? = some tailKey ∧
          comp[(RouteImpl.edgeAt run.proper i₁).head]? = some headKey ∧
          execution.graph.nodes[tailKey]? = some nT ∧
          execution.graph.nodes[headKey]? = some nH ∧
          (nT.decl = raw.tail ∨ nT.decl = raw.head) ∧
          (nH.decl = raw.tail ∨ nH.decl = raw.head) ∧
          inp.routes[index]? = some route₀ ∧
          edgeOf inp route₀ index = .ok raw ∧
          edge.decl = index

/-- Narrow residual R3 (placement phase only): a placed part with a route
entry has a positive-width rect and either a positive-height rect or
route points with distinct y. -/
def PartPositiveContent (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res)
    {part : List Nat × Part} (_hpart : part ∈ execution.componentsAcc.parts)
    (_hroutes : part.2.routes ≠ []),
    (∃ r : Rect, r ∈ part.2.rects ∧ 0 < r.w) ∧
    ((∃ r : Rect, r ∈ part.2.rects ∧ 0 < r.h) ∨
      (∃ pts : List Point, ∃ p₁ p₂ : Point,
        (∃ decl : Nat, (decl, pts) ∈ part.2.routes) ∧
        p₁ ∈ pts ∧ p₂ ∈ pts ∧ p₁.y ≠ p₂.y))

/-- The graph node behind a model box carries that box index as its
declaration, in both the group and the plain case. -/
private theorem graphNodeDeclOfBox {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source) :
    ∃ node : Node, execution.graph.nodes[key]? = some node ∧ node.decl = key := by
  by_cases h : source.role = .group ∧
      inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false
  · obtain ⟨hrole, hfixed⟩ := h
    obtain ⟨node, hn, _, hdecl⟩ :=
      execution.nonfixed_group_graph_node hsource hrole hfixed
    exact ⟨node, hn, hdecl⟩
  · have hplain : ¬ (source.role = .group ∧
        inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false) := h
    obtain ⟨node, hn, _, _, hdecl⟩ :=
      execution.plain_graph_node hsource hplain
    exact ⟨node, hn, hdecl⟩

/-- A model endpoint box of a real edge lies in the dump scope of any scene
route with the same endpoints. -/
private theorem boxIdInScope {inp : Input} {res : FamilyResult}
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

/-- Residual 1: node declarations transport from the model box through the
graph, the candidate, and the run. -/
theorem exclusiveRunNodeDecl_of_preserved {inp : Input} {o : Options} {res : FamilyResult}
    (hpreserved : ProperDeclPreserved inp o res) :
    ExclusiveRunNodeDecl inp o res := by
  intro execution comp candidate run hcomp hrun v key source hcompv hsource
  obtain ⟨node, hnode, hdecl⟩ := graphNodeDeclOfBox execution hsource
  have hcand : (componentCandidate execution.graph comp candidate).nodes[v]? = some node :=
    candidate_node_of_part_key hcompv hnode
  obtain ⟨out, hout, hdecl2⟩ :=
    hpreserved execution comp candidate run hcomp hrun v node hcand
  have hnd : RouteImpl.nodeDecl run.proper v = out.node.decl := by
    unfold RouteImpl.nodeDecl
    simp only [hout]
  rw [hnd, hdecl2, hdecl]

/-- Residual 2: run route endpoints land inside the scene route scope. -/
theorem runRouteEndpointIdsScoped_of_keys {inp : Input} {o : Options} {res : FamilyResult}
    (hpreserved : ProperDeclPreserved inp o res)
    (hkeys : ProperChainEndpointKeys inp o res) :
    RunRouteEndpointIdsScoped inp o res := by
  intro execution comp candidate run hcomp hrun i edge native route hedge hnative hnativeOrig hkeyedge i₀ i₁ hfirst hlast
  obtain ⟨tailKey, headKey, index, route₀, raw, nT, nH,
    hcompT, hcompH, hnT, hnH, hdeclT, hdeclH, hroute₀, hraw, hdeclIdx⟩ :=
    hkeys execution comp candidate run hcomp hrun i edge native hnative hnativeOrig hedge i₀ i₁ hfirst hlast
  have hcandT : (componentCandidate execution.graph comp candidate).nodes[(RouteImpl.edgeAt run.proper i₀).tail]? = some nT :=
    candidate_node_of_part_key hcompT hnT
  have hcandH : (componentCandidate execution.graph comp candidate).nodes[(RouteImpl.edgeAt run.proper i₁).head]? = some nH :=
    candidate_node_of_part_key hcompH hnH
  obtain ⟨outT, houtT, hdecl2T⟩ :=
    hpreserved execution comp candidate run hcomp hrun _ nT hcandT
  obtain ⟨outH, houtH, hdecl2H⟩ :=
    hpreserved execution comp candidate run hcomp hrun _ nH hcandH
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
  have hget := sceneOf_routes_getElem? execution.params inp o execution.lines execution.straightAcc execution.measured index hk
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
    · exact boxIdInScope hraw hfrom hto (Or.inl hT) hb₀
    · exact boxIdInScope hraw hfrom hto (Or.inr hT) hb₀
  · intro b₁ hb₁
    rw [hndH, hdecl2H] at hb₁
    rcases hdeclH with hH | hH
    · exact boxIdInScope hraw hfrom hto (Or.inl hH) hb₁
    · exact boxIdInScope hraw hfrom hto (Or.inr hH) hb₁

/-- Residual 3: the shelf of a part with an edge is positive in both axes. -/
theorem routePartShelfPositive_of_content {inp : Input} {o : Options} {res : FamilyResult}
    (hcontent : PartPositiveContent inp o res) :
    RoutePartShelfPositive inp o res := by
  intro execution packed hpacked c q hselected candidate _i edge hedge
  have hpart : q.1 ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? (zip_getElem?_left hselected)
  obtain ⟨cand₀, run₀, loops₀, area₀, _, hrun₀, hplace₀⟩ :=
    execution_part_run execution hpart
  have hdeclmem : edge.decl ∈ ((componentCandidate execution.graph q.1.1 candidate).edges.map (·.decl)) :=
    List.mem_map_of_mem (List.mem_of_getElem? hedge)
  rw [componentCandidate_decls] at hdeclmem
  obtain ⟨i₀, e₀, hedge₀, _hdecl₀⟩ :=
    componentCandidate_decl_edge (g := execution.graph) (comp := q.1.1) (index := cand₀) hdeclmem
  have hroutesNE : q.1.2.routes ≠ [] := by
    have hi : i₀ < (componentCandidate execution.graph q.1.1 cand₀).edges.length :=
      (List.getElem?_eq_some_iff.mp hedge₀).1
    have hlen := placeComponent_routes_length execution.params (componentCandidate execution.graph q.1.1 cand₀) run₀ 0 execution.measured loops₀
    have hlenpos : 0 < q.1.2.routes.length := by
      rw [hplace₀]
      show 0 < (placeComponent execution.params (componentCandidate execution.graph q.1.1 cand₀) run₀ 0 execution.measured loops₀).routes.length
      omega
    intro hnil
    have h0 := congrArg List.length hnil
    simp only [List.length_nil] at h0
    omega
  obtain ⟨⟨wrect, hwmem, hwpos⟩, hH⟩ := hcontent execution hpart hroutesNE
  obtain ⟨_, _, hrects, _, hroutesB, _⟩ := execution.components_parts_bounded q.1 hpart
  have hposW : 0 < q.1.2.width := by
    obtain ⟨hx0, hxw, _, _, _, _⟩ := hrects wrect hwmem
    omega
  have hposH : 0 < q.1.2.height := by
    rcases hH with ⟨hrect, hrmem, hhpos⟩ | ⟨pts, p₁, p₂, ⟨decl, hdeclmem⟩, hp₁, hp₂, hne⟩
    · obtain ⟨_, _, _, hyh, _, _⟩ := hrects hrect hrmem
      omega
    · obtain ⟨_, _, hy01, hyh1⟩ := hroutesB (decl, pts) hdeclmem p₁ hp₁
      obtain ⟨_, _, hy02, hyh2⟩ := hroutesB (decl, pts) hdeclmem p₂ hp₂
      omega
  have hmemc : execution.componentsAcc.parts[c]? = some q.1 :=
    zip_getElem?_left hselected
  obtain ⟨_, hshelfC⟩ := List.getElem?_zip_eq_some.mp hselected
  have h1 := congrArg (fun l : List (Int × Int) => l[c]?) (Pack.pack_dimensions hpacked)
  simp only [Pack.dimensions, List.getElem?_map, hshelfC, hmemc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨hBw, hBh⟩ := h1
  have hshelfT : shelfRectT execution packed c = shiftRect execution.params.canvasMargin execution.params.canvasMargin (orientRect o.direction execution.packedAcc.canvasH q.2) := by
    unfold shelfRectT
    rw [hshelfC, Option.getD_some]
  have hgoal : 0 < (shelfRectT execution packed c).w ∧ 0 < (shelfRectT execution packed c).h := by
    rw [hshelfT, shiftRect_dims, orientRect_dims, hBw, hBh]
    exact ⟨hposW, hposH⟩
  exact hgoal

end PipelineImpl
end Layered
end Elegant

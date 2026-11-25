import Elegant.Layered.FlatC6LoopProof
import Elegant.Layered.RecursiveCallContext

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Frame-level route clearance for a fixed group, flat layout

For one executed flat `layout` (a `SceneExecution`), the located frame of a
fixed-size group-role box is a plain graph node (`border = 0`) of the
parent run: fixed sizes are rewritten to node role by `measuredGraph`
(`measuredGraph_fixed_loop_reservation`), so the exclusive-flag step of the
flat C6 bridge is replaced by the fixed-size node facts
(`SceneExecution.fixed_candidate_node_border_zero`). The run-level
avoidance (`componentRun_route_avoids_nodes`) is stated by `IsReal` graph
node rather than by the dump `exclusive` flag, so it applies to the frame;
only the run-to-scene bridge and the endpoint/scope exclusions need the
frame in place of the exclusive box.

Proved here, from the named seams:

* `FrameRunBridge`: the frame analog of `RouteScopeBridge` (same-part real
  node with `border = 0`, or other-part shelf containment). The cluster-path
  payload of `RouteScopeBridge` is dropped: the run-level lemma consumed
  below takes no cluster-path premises.
* `flatFrameChainMiss` / `flatFrameLoopMiss`: chain and self-loop scene
  routes miss the frame, from the bridge, the endpoint-id seams
  (`ExclusiveRunNodeDecl`, `RunRouteEndpointIdsScoped`), and the loop seams.
* `flat_frame_clear`: the flat frame-clear conclusion, splitting on the
  executed edge (chain vs self-loop) like `flat_c6_core`.
* `parentInput_group_fixedEntry`: the fixed-size entry the bridge needs,
  proved from the executed call context.

Residuals left for the recursion lift: `ExpandChildFrameGeometry` and
`ExpandChildFrameChildGeometry` (the per-expansion frame step, mirroring
`ExpandChildC6Geometry` with the frame in place of the exclusive box),
`ExpandChildFrameRecursion` (the lifted conclusion), and
`ExpandChildFrameScopeOutside` (endpoint inequality implies scope
exclusion). Part (b) needs are listed at the end, without proof.
-/

/-! ## Copied private helpers (renamed `frameRun*`) -/

/-- Local re-proof: a candidate graph has exactly the component's nodes. -/
private theorem frameRun_candidate_nodes_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- Endpoint projections of the pristine form of an edge. -/
private theorem frameRun_edge_original_tail (e : Edge) :
    e.original.tail = if e.reversed then e.head else e.tail := by
  unfold Edge.original
  cases h : e.reversed <;> simp

/-- Endpoint projections of the pristine form of an edge. -/
private theorem frameRun_edge_original_head (e : Edge) :
    e.original.head = if e.reversed then e.tail else e.head := by
  unfold Edge.original
  cases h : e.reversed <;> simp

/-- Every edge of a component candidate keeps both endpoints below the
candidate's node count. -/
private theorem frameRun_candidate_edge_endpoints_bounded (g : Graph) (comp : List Nat) (index : Nat)
    (hcomp : comp ∈ components g)
    (hbd : ∀ e ∈ g.edges ++ Compound.constraints g,
      e.tail < g.nodes.length ∧ e.head < g.nodes.length)
    {edge : Edge} (hedge : edge ∈ (componentCandidate g comp index).edges) :
    edge.tail < (componentCandidate g comp index).nodes.length ∧
      edge.head < (componentCandidate g comp index).nodes.length := by
  have hlen : (componentCandidate g comp index).nodes.length = comp.length :=
    frameRun_candidate_nodes_length g comp index
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
  have htailLt : e₁.tail < comp.length := by rw [he₁tail]; exact List.idxOf_lt_length_of_mem he₀tailmem
  have hheadLt : e₁.head < comp.length := by
    rw [he₁head]; exact List.idxOf_lt_length_of_mem (hsame ▸ hhead')
  have ht := congrArg Edge.tail heq
  have hh := congrArg Edge.head heq
  rw [frameRun_edge_original_tail e₁, frameRun_edge_original_tail edge] at ht
  rw [frameRun_edge_original_head e₁, frameRun_edge_original_head edge] at hh
  rw [hlen]
  cases h₁ : e₁.reversed <;> cases h₂ : edge.reversed <;>
    simp only [h₁, h₂, Bool.false_eq_true, ↓reduceIte] at ht hh <;>
    constructor <;> omega

/-- The component of the selected part is the component whose run placed it. -/
private theorem frameRun_part_component_aligned
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
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
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured = .ok loops)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph comp candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph comp candidate).edges[i]? = some edge) :
    comp = q.1.1 := by
  obtain ⟨hparts, hall⟩ :=
    actual_components_parts_geometry (by rfl) execution.components_eq
  have hq1mem : q.1 ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? (zip_getElem?_left hselected)
  have hq1comp : q.1.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hq1mem
  obtain ⟨index₀, chosen₀, run₀, loops₀, area₀, _, _, _, hrun₀, hloops₀, hpart₀⟩ :=
    hall q.1 hq1mem
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have hedgemem : edge ∈ (componentCandidate execution.graph comp candidate).edges :=
    List.mem_of_getElem? hedge
  have hbounds := frameRun_candidate_edge_endpoints_bounded execution.graph comp candidate hcomp
    (sceneExecution_edges_bounded execution) hedgemem
  have hdecls := componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq comp candidate
  have hemitted :
      ∃ pts : List Point,
        (edge.decl, pts) ∈
          (placeComponent execution.params
            (componentCandidate execution.graph comp candidate) run 0 execution.measured
            loops).routes := by
    by_cases hself : edge.tail = edge.head
    · obtain ⟨_, _, _, _, hemittedRoutes⟩ :=
        componentLoops_emitted_self_edge hloops hedge hbounds.1 hself 0
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
        placeComponent_route_entry_of_producer hrun 0 loops i hi hloop
      rw [show ((componentCandidate execution.graph comp candidate).edges[i]).decl = edge.decl
          by rw [(List.getElem?_eq_some_iff.mp hedge).2]] at hemittedRoutes
      exact ⟨_, List.mem_of_getElem? hemittedRoutes⟩
  have hroutesComp : q.1.2.routes =
      (placeComponent execution.params
        (componentCandidate execution.graph comp candidate) run 0 execution.measured
        loops).routes := by rw [hpart]
  have hroutesOwn : q.1.2.routes =
      (placeComponent execution.params
        (componentCandidate execution.graph q.1.1 index₀) run₀ 0 execution.measured
        loops₀).routes := by rw [hpart₀]
  obtain ⟨pts, hpts⟩ := hemitted
  rw [← hroutesComp, hroutesOwn] at hpts
  have hkey : edge.decl ∈ (componentCandidate execution.graph q.1.1 index₀).edges.map
      (·.decl) := by
    rw [← placeComponent_routes_decls execution.params
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
  have hgnodup := measuredGraph_decls_nodup execution.graph_eq
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

/-- Indexed form of list-zip membership. -/
private theorem frameRun_mem_zip_getElem? {α β : Type} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : (a, b) ∈ l₁.zip l₂) :
    ∃ i : Nat, l₁[i]? = some a ∧ l₂[i]? = some b := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at h
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨0, rfl, rfl⟩
      · obtain ⟨i, h1, h2⟩ := ih h
        exact ⟨i + 1, by simpa using h1, by simpa using h2⟩

/-- Point-transport composition along a shelf origin. -/
private theorem frameRun_shiftPoint_compose (dx dy nx ny : Int) (p : Point) :
    shiftPoint dx dy (shiftPoint (0 - nx) (0 - ny) p) = shiftPoint (dx - nx) (dy - ny) p := by
  cases p
  simp only [shiftPoint, Point.mk.injEq]
  constructor <;> omega

/-- A segment between two points of a closed shelf rect misses the interior of
any rect the disjoint partner shelf contains. -/
private theorem frameRun_segMisses_of_shelf {S B R : Rect} {p q : Point}
    (hd : Disjoint S B) (hposS : 0 < S.w ∧ 0 < S.h) (hposB : 0 < B.w ∧ 0 < B.h)
    (hp : pointInRect S p) (hq : pointInRect S q)
    (hsub : B.Contained R) : Polyline.segMisses p q R := by
  have hsep : S.x + S.w ≤ B.x ∨ B.x + B.w ≤ S.x ∨ S.y + S.h ≤ B.y ∨
      B.y + B.h ≤ S.y := by
    apply Classical.byContradiction
    intro hcon
    have h1 : ¬(S.x + S.w ≤ B.x) := fun h => hcon (Or.inl h)
    have h2 : ¬(B.x + B.w ≤ S.x) := fun h => hcon (Or.inr (Or.inl h))
    have h3 : ¬(S.y + S.h ≤ B.y) := fun h => hcon (Or.inr (Or.inr (Or.inl h)))
    have h4 : ¬(B.y + B.h ≤ S.y) := fun h => hcon (Or.inr (Or.inr (Or.inr h)))
    exact hd ⟨by omega, by omega⟩
  unfold Polyline.segMisses at ⊢
  unfold pointInRect at hp hq
  unfold Rect.Contained at hsub
  rcases hsep with hx | hx | hy | hy
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))

/-- Whole-polyline version of `frameRun_segMisses_of_shelf`. -/
private theorem frameRun_allSegsMiss_of_shelves {S B R : Rect} : ∀ {points : List Point},
    Disjoint S B → (∀ p ∈ points, pointInRect S p) →
    (0 < S.w ∧ 0 < S.h) → (0 < B.w ∧ 0 < B.h) → B.Contained R →
    Polyline.allSegsMiss points R := by
  intro points
  induction points with
  | nil => intro _ _ _ _ _; exact True.intro
  | cons p ps ih =>
    intro hd hpts hposS hposB hsub
    cases ps with
    | nil => exact True.intro
    | cons p' ps' =>
      exact ⟨frameRun_segMisses_of_shelf hd hposS hposB (hpts p List.mem_cons_self)
        (hpts p' (List.mem_cons_of_mem _ List.mem_cons_self)) hsub,
        ih hd (fun x hx => hpts x (List.mem_cons_of_mem _ hx)) hposS hposB hsub⟩

/-- Segment version for the loop shelf argument (explicit rect arguments). -/
private theorem frameRun_segMisses_of_shelf_l (S B R : Rect) {p q : Point}
    (hd : Disjoint S B) (hposS : 0 < S.w ∧ 0 < S.h) (hposB : 0 < B.w ∧ 0 < B.h)
    (hp : pointInRect S p) (hq : pointInRect S q)
    (hsub : B.Contained R) : Polyline.segMisses p q R := by
  have hsep : S.x + S.w ≤ B.x ∨ B.x + B.w ≤ S.x ∨ S.y + S.h ≤ B.y ∨
      B.y + B.h ≤ S.y := by
    apply Classical.byContradiction
    intro hcon
    have h1 : ¬(S.x + S.w ≤ B.x) := fun h => hcon (Or.inl h)
    have h2 : ¬(B.x + B.w ≤ S.x) := fun h => hcon (Or.inr (Or.inl h))
    have h3 : ¬(S.y + S.h ≤ B.y) := fun h => hcon (Or.inr (Or.inr (Or.inl h)))
    have h4 : ¬(B.y + B.h ≤ S.y) := fun h => hcon (Or.inr (Or.inr (Or.inr h)))
    exact hd ⟨by omega, by omega⟩
  unfold Polyline.segMisses at ⊢
  unfold pointInRect at hp hq
  unfold Rect.Contained at hsub
  rcases hsep with hx | hx | hy | hy
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))

/-- Whole-polyline version of `frameRun_segMisses_of_shelf_l`. -/
private theorem frameRun_allSegsMiss_of_shelves_l (S B R : Rect) : ∀ {points : List Point},
    Disjoint S B → (∀ p ∈ points, pointInRect S p) →
    (0 < S.w ∧ 0 < S.h) → (0 < B.w ∧ 0 < B.h) → B.Contained R →
    Polyline.allSegsMiss points R := by
  intro points
  induction points with
  | nil => intro _ _ _ _ _; exact True.intro
  | cons p ps ih =>
    intro hd hpts hposS hposB hsub
    cases ps with
    | nil => exact True.intro
    | cons p' ps' =>
      exact ⟨frameRun_segMisses_of_shelf_l S B R hd hposS hposB (hpts p List.mem_cons_self)
        (hpts p' (List.mem_cons_of_mem _ List.mem_cons_self)) hsub,
        ih hd (fun x hx => hpts x (List.mem_cons_of_mem _ hx)) hposS hposB hsub⟩

/-- Folded routes list size (needed by the loop route-point transport). -/
private theorem frameRun_components_fold_routes_size (P : Params) (inp : Input) (o : Options)
    (graph : Graph) (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
    comps.foldlM (fun acc comp => layoutComponent P inp o graph acc comp labels) start = .ok out →
    out.routes.size = start.routes.size
  | [], start, out, h => by
    have he : start = out := Except.ok.inj h
    rw [he]
  | comp :: comps, start, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨next, hnext, hrest⟩ := bind_ok h
    rw [frameRun_components_fold_routes_size P inp o graph labels comps next out hrest]
    exact (layoutComponent_sizes hnext).2.1.symm

/-- The scene route of a loop placement, transported to the scene. -/
private theorem frameRun_scene_loop_route_points {inp : Input} {o : Options} {res : FamilyResult}
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
    (_hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hbounds : edge.tail < (componentCandidate execution.graph q.1.1 candidate).nodes.length)
    (hself : edge.tail = edge.head)
    {loop : Nat × LoopPlacement}
    (hfound : loops.find? (fun l => l.1 == edge.decl) = some loop) :
    ∃ route : ModelRoute, inp.routes[edge.decl]? = some route ∧
      res.scene.routes[edge.decl]? =
        some (Route.mk route.id route.fromId route.toId route.orthogonal
          (loop.2.points.map (routePointTransport execution.params.canvasMargin o.direction
            execution.packedAcc.canvasH q.2.x q.2.y
            (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX
            (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY))) := by
  let cg := componentCandidate execution.graph q.1.1 candidate
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have he := (List.getElem?_eq_some_iff.mp hedge).2
  have hk : (cg.edges[i]).decl < inp.routes.length :=
    componentCandidate_edge_index_decl_lt execution.graph_eq q.1.1 candidate hi
  have hsize : execution.componentsAcc.routes.size = inp.routes.length := by
    have h := frameRun_components_fold_routes_size execution.params inp o execution.graph
      execution.measured _ _ _ execution.components_eq
    simpa only [Array.size_replicate] using h
  have hrouteSize : edge.decl < execution.componentsAcc.routes.size := by
    rw [hsize]
    simpa only [cg, he] using hk
  have hpartRoutes : q.1.2.routes =
      (placeComponent execution.params cg run 0 execution.measured loops).routes := by
    rw [hpart]
  obtain ⟨qq, _hqqmem, hqfind, _hqdecl, hget_pC⟩ :=
    componentLoops_emitted_self_edge (cg := cg) hloops hedge hbounds hself 0
  have hqeq : qq = loop := Option.some.inj (hqfind.symm.trans hfound)
  subst hqeq
  rw [← hpartRoutes] at hget_pC
  have hnd : (cg.edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate
  have hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
    rw [hpartRoutes]
    exact placeComponent_routes_decls_nodup execution.params cg run 0 execution.measured
      loops hnd
  have hpackedRoute := Elegant.Layered.actual_components_packAcc_routes_getD
    (by rfl) execution.components_eq (measuredGraph_decls_nodup execution.graph_eq)
    packed execution.packed_eq hpacked c q hselected i _ _ [] hget_pC hpartNodup hrouteSize
  have hkdecl : edge.decl < inp.routes.length := by simpa only [cg, he] using hk
  have hk'' : edge.decl < inp.routes.length := hkdecl
  have hscene := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.packedAcc execution.measured edge.decl hkdecl
  rw [← execution.scene_eq] at hscene
  rw [hpackedRoute] at hscene
  rw [routePointTransport_eq] at hscene
  refine ⟨(inp.routes[edge.decl]'hk''), List.getElem?_eq_getElem hk'', ?_⟩
  exact hscene

/-! ## Split residuals (moved here from `ExpandChildParentRouteClearProof`) -/

/-- Residual (a): a parent route out of the frame's scope (neither endpoint
is the group) misses the frame rectangle. Strictly simpler than the combined
residual: the attached conjunct and the inner-rect quantifier are gone. The
remaining content is router-level: the group is a fixed-size real node of
the parent run, and `componentRun_route_avoids_nodes` is stated by `IsReal`
node rather than by the dump `exclusive` flag. -/
def ExpandChildParentRouteFrameClear (group : ModelBox) (parent : FamilyResult) : Prop :=
  ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pr ∈ parent.scene.routes, pr.fromId ≠ group.id → pr.toId ≠ group.id →
      ¬ Polyline.hitsRect pr.points frame.rect

/-- Residual (b): a parent route attached to the frame (an endpoint is the
group) misses every rectangle strictly inside the frame. Strictly simpler
than the combined residual: the out-of-scope conjunct is gone. The
remaining content is endpoint attachment: the route meets the frame on its
`C5` boundary port with the stub exterior facing outward. -/
def ExpandChildParentRouteAttachedClear (group : ModelBox) (parent : FamilyResult) : Prop :=
  ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pr ∈ parent.scene.routes, (pr.fromId = group.id ∨ pr.toId = group.id) →
      ∀ (r : Rect), frame.rect.StrictInside r →
        ¬ Polyline.hitsRect pr.points r

/-! ## Frame run bridge -/

/-- The frame analog of `RouteScopeBridge`: for a successful flat execution,
the scene box with the group's id (outside the dump route scope) either is
the transported `frameRect` of a real node of the route's own component run
(with `border = 0`, from the fixed-size entry), or lies inside the
transported shelf of a different packed part. The cluster-path payload of
`RouteScopeBridge` is dropped: the run-level lemma consumed below
(`componentRun_route_avoids_nodes`) takes no cluster-path premises. -/
def FrameRunBridge (pinp : Input) (o : Options) (pres : FamilyResult) (group : ModelBox) : Prop :=
  ∀ (execution : SceneExecution pinp o pres)
    (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {comp : List Nat} {candidate : Nat} {run : Run}
    {loops : List (Nat × LoopPlacement)} {area : Int}
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hcomp : comp ∈ components execution.graph)
    (_hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (_hloops : componentLoops execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured = .ok loops)
    (_hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph comp candidate) run 0 execution.measured loops
      with area := area })
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {i : Nat} {edge : Edge}
    (_hedge : (componentCandidate execution.graph comp candidate).edges[i]? = some edge)
    {route : Route} {box : Box}
    (_hroute : pres.scene.routes[edge.decl]? = some route)
    (_hboxmem : box ∈ pres.scene.boxes)
    (_hframe : box.id = group.id)
    (_hscope : group.id ∉ LayoutDump.routeScope pres.scene.layoutDump route),
    (∃ v key : Nat, ∃ src : ModelBox,
      q.1.1[v]? = some key ∧
      pinp.boxes[key]? = some src ∧
      src.id = group.id ∧
      v < (componentCandidate execution.graph comp candidate).nodes.length ∧
      RouteImpl.IsReal run.proper v ∧
      ((componentCandidate execution.graph comp candidate).nodes.getD v default).border = 0 ∧
      box.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBounds execution.params
                (componentCandidate execution.graph comp candidate) run
                execution.measured loops).minX)
              (0 - (placeBounds execution.params
                (componentCandidate execution.graph comp candidate) run
                execution.measured loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph comp candidate) run v)))))
    ∨
    ∃ c' : Nat, ∃ r' : Rect, c' ≠ c ∧ packed.boxes[c']? = some r' ∧
      (shelfRectT execution packed c').Contained box.rect

/-- The bridge from the fixed-size entry: the frame box maps to the
`border = 0` run node of the fixed group (`fixed_candidate_node_border_zero`
via `measuredGraph_fixed_loop_reservation`); the other-part case is the
shelf separation of `PartSeparation`. -/
theorem frameRunBridge {pinp : Input} {o : Options} {pres : FamilyResult} {group : ModelBox}
    (hfixed : ∀ {b : Box}, b ∈ pres.scene.boxes → b.id = group.id →
      ∃ entry : String × Size,
        pinp.fixedSizes.find? (fun fixed => fixed.1 == b.id) = some entry) :
    FrameRunBridge pinp o pres group := by
  intro execution packed hpacked comp candidate run loops area c q hcomp hrun hloops hpart
    hselected i edge hedge route box hroute hboxmem hframe hscope
  have hb0 := hboxmem
  have halign : comp = q.1.1 :=
    frameRun_part_component_aligned execution packed hpacked hselected hcomp hrun hloops hpart hedge
  subst halign
  rw [execution.boxes_eq_map] at hboxmem
  obtain ⟨pair, hpair, hboxeq⟩ := List.mem_map.mp hboxmem
  have hsource : pinp.boxes[pair.2]? = some pair.1 := List.mem_zipIdx_iff_getElem?.mp hpair
  have hkeylen : pair.2 < pinp.boxes.length := (List.getElem?_eq_some_iff.mp hsource).1
  have hkeysize : pair.2 < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact hkeylen
  have hq1mem : q.1 ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? (zip_getElem?_left hselected)
  have hparts := (actual_components_parts_geometry (by rfl) execution.components_eq).1
  have hq1comp : q.1.1 ∈ components execution.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hq1mem
  have hboxrect : box.rect =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD pair.2 default)) := by
    rw [← hboxeq]
  by_cases hmem : pair.2 ∈ q.1.1
  · obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
    have hvlen : v < (componentCandidate execution.graph q.1.1 candidate).nodes.length := by
      rw [frameRun_candidate_nodes_length]
      exact (List.getElem?_eq_some_iff.mp hv).1
    have hentry := chosen_part_frame_entry hpart hv
    dsimp only at hentry
    have hval := actual_components_packed_rect_value (by rfl) execution.components_eq
      execution.packed_eq packed hpacked hselected hentry hkeysize default
    have hgraphlen : pair.2 < execution.graph.nodes.length :=
      sceneExecution_graph_len execution hkeylen
    have hgraphnode : execution.graph.nodes[pair.2]? =
        some (execution.graph.nodes[pair.2]'hgraphlen) := List.getElem?_eq_getElem hgraphlen
    have hreal := componentRun_source_isReal hrun (candidate_node_of_part_key hv hgraphnode)
    obtain ⟨entry, hentryFixed⟩ := hfixed hb0 hframe
    have hentry' : pinp.fixedSizes.find? (fun fixed => fixed.1 == pair.1.id) = some entry := by
      have hpid : pair.1.id = box.id := congrArg Box.id hboxeq
      rw [hpid]
      exact hentryFixed
    have hcompv : q.1.1[v]'((List.getElem?_eq_some_iff.mp hv).1) = pair.2 :=
      (List.getElem?_eq_some_iff.mp hv).2
    have hsource' : pinp.boxes[q.1.1[v]'((List.getElem?_eq_some_iff.mp hv).1)]? = some pair.1 := by
      rw [hcompv]; exact hsource
    have hvlen' : v < q.1.1.length := (List.getElem?_eq_some_iff.mp hv).1
    obtain ⟨node, hnode, hborder0⟩ :=
      execution.fixed_candidate_node_border_zero q.1.1 candidate v hvlen' hsource' hentry'
    have hgetD : (componentCandidate execution.graph q.1.1 candidate).nodes.getD v default =
        node := by
      simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
    have hsrcId : pair.1.id = group.id := by
      have hpid : pair.1.id = box.id := congrArg Box.id hboxeq
      rw [hpid]
      exact hframe
    refine Or.inl ⟨v, pair.2, pair.1, hv, hsource, hsrcId, hvlen, hreal, ?_, ?_⟩
    · rw [hgetD]
      exact hborder0
    · exact hboxrect.trans (congrArg (fun r => shiftRect execution.params.canvasMargin
        execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH r)) hval)
  · obtain ⟨part', hpart'mem, entry, hentrymem, hentrykey⟩ :=
      sceneExecution_parts_entry execution hkeylen
    obtain ⟨v', hv'key, hv'rect⟩ := frameRun_mem_zip_getElem? hentrymem
    have hkeymem' : pair.2 ∈ part'.1 := by
      rw [← hentrykey]
      exact (List.of_mem_zip hentrymem).1
    rw [hentrykey] at hv'key
    obtain ⟨c', hc'get⟩ := List.mem_iff_getElem?.mp hpart'mem
    have hc'len : c' < packed.boxes.length := by
      rw [Pack.pack_count hpacked]
      simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hc'get).1
    have hshelf : packed.boxes[c']? = some (packed.boxes[c']'hc'len) :=
      List.getElem?_eq_getElem hc'len
    have hselected' : (execution.componentsAcc.parts.zip packed.boxes)[c']? =
        some (part', packed.boxes[c']'hc'len) :=
      List.getElem?_zip_eq_some.mpr ⟨hc'get, hshelf⟩
    have hframe' : part'.2.rects[v']? = some entry.2 := hv'rect
    have hentry2 : (part'.1.zip part'.2.rects)[v']? = some (pair.2, entry.2) :=
      List.getElem?_zip_eq_some.mpr ⟨hv'key, hframe'⟩
    have hval' := actual_components_packed_rect_value (by rfl) execution.components_eq
      execution.packed_eq packed hpacked hselected' hentry2 hkeysize default
    have hcont := part_rects_within_shelf hpacked hc'get hc'len entry.2
      (List.mem_of_getElem? hframe')
    have hc'ne : c' ≠ c := by
      intro heq
      have hqc : execution.componentsAcc.parts[c']? = some q.1 := by
        rw [heq]
        exact zip_getElem?_left hselected
      have hpe : part' = q.1 := Option.some.inj (hc'get.symm.trans hqc)
      exact hmem (hpe ▸ hkeymem')
    refine Or.inr ⟨c', packed.boxes[c']'hc'len, hc'ne, hshelf, ?_⟩
    rw [hboxrect, hval']
    simpa only [shelfRectT, partRectT, hshelf, Option.getD_some] using hcont

/-! ## Flat chain miss -/

/-- Chain-route case of the flat frame miss: the scene route is the
transported run route of the executed component, and the frame box is the
transported `frameRect` of the bridged real node (`FrameRunBridge`). The
run-level miss is `componentRun_route_avoids_nodes` (no cluster-path or
exclusive premises); the endpoint exclusions come from
`RunRouteEndpointIdsScoped` against the scope premise. The other-part case
is the shelf separation. -/
theorem flatFrameChainMiss {pinp : Input} {o : Options} {pres : FamilyResult} {group : ModelBox}
    (execution : SceneExecution pinp o pres)
    (hclear : FrameClearanceSeam pinp o pres)
    (hbridge : FrameRunBridge pinp o pres group)
    (hnodeDecl : ExclusiveRunNodeDecl pinp o pres)
    (hscoped : RunRouteEndpointIdsScoped pinp o pres)
    (hpos : RoutePartShelfPositive pinp o pres)
    {r : Route} {b : Box} (_hr : r ∈ pres.scene.routes) (hb : b ∈ pres.scene.boxes)
    (hframe : b.id = group.id)
    (hscope : group.id ∉ LayoutDump.routeScope pres.scene.layoutDump r)
    {key : Nat} (hkget : pres.scene.routes[key]? = some r) (_hkeylen : key < pinp.routes.length)
    {packed : Pack.State} {c : Nat} {q : (List Nat × Part) × Rect}
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)}
    {i : Nat} {edge : Edge} (area : Int)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hdecl : edge.decl = key)
    (hfound : loops.find? (fun l => l.1 == edge.decl) = none) :
    ¬ Polyline.hitsRect r.points b.rect := by
  have hq1comp : q.1.1 ∈ components execution.graph := by
    obtain ⟨hparts, _⟩ := actual_components_parts_geometry (by rfl) execution.components_eq
    rw [← hparts]
    exact List.mem_map_of_mem
      (List.mem_of_getElem? (zip_getElem?_left hselected))
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have hedgemem : edge ∈ (componentCandidate execution.graph q.1.1 candidate).edges :=
    List.mem_of_getElem? hedge
  have hbounds := frameRun_candidate_edge_endpoints_bounded execution.graph q.1.1 candidate hq1comp
    (sceneExecution_edges_bounded execution) hedgemem
  have hself : edge.tail ≠ edge.head := by
    intro hEq
    obtain ⟨placement, hplacement⟩ :=
      componentLoops_entry_of_self_edge hloops hedgemem hbounds.1 hEq
    exact (List.find?_eq_none.mp hfound (edge.decl, placement) hplacement) (by simp)
  have hloopen : ∀ l ∈ loops, l.1 ≠ edge.decl := by
    intro l hl he
    exact (List.find?_eq_none.mp hfound l hl) (by simp [he])
  obtain ⟨modelRoute, native, hmodelRoute, hnative, hnativeOrig, hroutes⟩ :=
    execution.chosen_part_route_entry packed hpacked hselected hrun hpart hedge hloopen
  dsimp only at hroutes
  have hkeyedge : pres.scene.routes[edge.decl]? = some r := by
    rw [hdecl]
    exact hkget
  have hreq : r = Route.mk modelRoute.id modelRoute.fromId modelRoute.toId
      modelRoute.orthogonal
      (native.points.map (routePointTransport execution.params.canvasMargin o.direction
        execution.packedAcc.canvasH q.2.x q.2.y
        (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
          run execution.measured loops).minX
        (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
          run execution.measured loops).minY)) :=
    Option.some.inj (hkeyedge.symm.trans hroutes)
  have hbridge' := hbridge execution packed hpacked hq1comp hrun hloops hpart hselected
    hedge hkeyedge hb hframe hscope
  cases hbridge' with
  | inl hleft =>
    obtain ⟨v, gkey, gsrc, hv, hsource, hsrcId, hvlen, hreal, hborder0, hbrect⟩ := hleft
    obtain ⟨chain, hchainget, hchainlen, _, _, hsegs⟩ :=
      componentRun_semantic_node_chain hrun hedge hself
    obtain ⟨properEdge, hPEmem, hPEorig, _, _, _⟩ := hsegs 0 (by omega) (by omega)
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hPEmem
    have hjlt : j < run.proper.edges.length := (List.getElem?_eq_some_iff.mp hj).1
    have hjedge : RouteImpl.edgeAt run.proper j = properEdge := by
      unfold RouteImpl.edgeAt
      rw [List.getD_eq_getElem?_getD, hj]
      rfl
    have hjmem : j ∈ RouteImpl.edgesOf run.proper i := by
      refine List.mem_filter.mpr ⟨List.mem_range.mpr hjlt, ?_⟩
      rw [hjedge]
      simp [hPEorig]
    cases h₀ : (RouteImpl.edgesOf run.proper i).head? with
    | none =>
      have hnil : RouteImpl.edgesOf run.proper i = [] := (List.head?_eq_none_iff).mp h₀
      rw [hnil] at hjmem
      exact absurd hjmem List.not_mem_nil
    | some i₀ =>
      cases h₁ : (RouteImpl.edgesOf run.proper i).getLast? with
      | none =>
        have hnil : RouteImpl.edgesOf run.proper i = [] := (List.getLast?_eq_none_iff).mp h₁
        rw [hnil] at hjmem
        exact absurd hjmem List.not_mem_nil
      | some i₁ =>
        have hfirst : (RouteImpl.edgesOf run.proper native.original).head? = some i₀ := by
          rw [hnativeOrig]; exact h₀
        have hlast : (RouteImpl.edgesOf run.proper native.original).getLast? = some i₁ := by
          rw [hnativeOrig]; exact h₁
        have hnd : RouteImpl.nodeDecl run.proper v = gkey :=
          hnodeDecl execution q.1.1 candidate run hq1comp hrun v gkey gsrc hv hsource
        have hscoping := hscoped execution q.1.1 candidate run hq1comp hrun i edge native r
          hedge hnative hnativeOrig hkeyedge i₀ i₁ hfirst hlast
        have hv0 : v ≠ (RouteImpl.edgeAt run.proper i₀).tail := by
          intro hev
          have hbx : pinp.boxes[RouteImpl.nodeDecl run.proper
              (RouteImpl.edgeAt run.proper i₀).tail]? = some gsrc := by
            have hshift : RouteImpl.nodeDecl run.proper
                (RouteImpl.edgeAt run.proper i₀).tail =
                RouteImpl.nodeDecl run.proper v := by rw [hev]
            rw [hshift, hnd]
            exact hsource
          have hmem2 : gsrc.id ∈ LayoutDump.routeScope pres.scene.layoutDump r :=
            hscoping.1 gsrc hbx
          rw [hsrcId] at hmem2
          exact hscope hmem2
        have hv1 : v ≠ (RouteImpl.edgeAt run.proper i₁).head := by
          intro hev
          have hbx : pinp.boxes[RouteImpl.nodeDecl run.proper
              (RouteImpl.edgeAt run.proper i₁).head]? = some gsrc := by
            have hshift : RouteImpl.nodeDecl run.proper
                (RouteImpl.edgeAt run.proper i₁).head =
                RouteImpl.nodeDecl run.proper v := by rw [hev]
            rw [hshift, hnd]
            exact hsource
          have hmem2 : gsrc.id ∈ LayoutDump.routeScope pres.scene.layoutDump r :=
            hscoping.2 gsrc hbx
          rw [hsrcId] at hmem2
          exact hscope hmem2
        have hne : ((componentCandidate execution.graph q.1.1 candidate).nodes.getD v
            default).border ≠ -2 := by
          rw [hborder0]
          decide
        have hclearRun : FrameClearance run.proper run.layers run.xs :=
          hclear execution q.1.1 candidate run (candidateOrder candidate) hq1comp hrun
        have hmissFlat : ¬ Polyline.hitsRect native.points
            (RouteImpl.boxRect run.proper run.xs run.ys v) :=
          componentRun_route_avoids_nodes (checkedParams_valid execution.checked)
            (componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate)
            (componentCandidate_shape (components_nodup execution.graph q.1.1 hq1comp)
              (measuredGraph_shape execution.graph_eq) candidate)
            hclearRun hrun native (List.mem_iff_getElem?.mpr ⟨i, hnative⟩) i₀ i₁ hfirst hlast
            v (componentRun_original_nodes_covered hrun v hvlen) hreal hv0 hv1
        have hmissT : ¬ Polyline.hitsRect
            (native.points.map (routePointTransport execution.params.canvasMargin o.direction
              execution.packedAcc.canvasH q.2.x q.2.y
              (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minX
              (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minY))
            (shiftRect execution.params.canvasMargin execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH
                (shiftRect (q.2.x - (placeBounds execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                    loops).minX)
                  (q.2.y - (placeBounds execution.params
                    (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                    loops).minY)
                  (RouteImpl.boxRect run.proper run.xs run.ys v)))) := by
          rw [← routePointTransport_eq, ← shiftRect_pack_normalize,
            not_hitsRect_shift_orient_iff, not_hitsRect_shift_iff, not_hitsRect_shift_iff]
          exact hmissFlat
        rw [congrArg Route.points hreq, hbrect, shiftRect_pack_normalize,
          plain_frame_eq_boxRect execution.params
            (componentCandidate execution.graph q.1.1 candidate) run v
            (componentRun_original_nodes_covered hrun v hvlen) hne]
        exact hmissT
  | inr hright =>
    obtain ⟨c', r', hne, hshelfget, hbIn⟩ := hright
    have hc'len : c' < packed.boxes.length :=
      (List.getElem?_eq_some_iff.mp hshelfget).1
    have hmemc : execution.componentsAcc.parts[c]? = some q.1 := zip_getElem?_left hselected
    have hclt : c < packed.boxes.length := by
      rw [Pack.pack_count hpacked]
      simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hmemc).1
    have hshelfC : packed.boxes[c]? = some q.2 := (List.getElem?_zip_eq_some.mp hselected).2
    have hloopen' : ∀ l ∈ loops,
        l.1 ≠ ((componentCandidate execution.graph q.1.1 candidate).edges[i]).decl := by
      intro l hl he
      exact hloopen l hl (by rw [he, (List.getElem?_eq_some_iff.mp hedge).2])
    have hplaced := placeComponent_route_entry_of_producer hrun 0 loops i hi hloopen'
    rw [show ((componentCandidate execution.graph q.1.1 candidate).edges[i]).decl = edge.decl
        by rw [(List.getElem?_eq_some_iff.mp hedge).2]] at hplaced
    rw [(List.getElem?_eq_some_iff.mp hnative).2] at hplaced
    have hrouteMem : (edge.decl, native.points.map
        (shiftPoint (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minX)
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minY))) ∈ q.1.2.routes := by
      rw [show q.1.2.routes =
          (placeComponent execution.params
            (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
            loops).routes from by rw [hpart]]
      exact List.mem_of_getElem? hplaced
    have hin := part_route_points_within_shelf hpacked hmemc hclt
    have hptsIn : ∀ p ∈ r.points, pointInRect (shelfRectT execution packed c) p := by
      intro p hp
      rw [congrArg Route.points hreq] at hp
      obtain ⟨p', hp'mem, hpeq⟩ := List.mem_map.mp hp
      have hp'in : shiftPoint
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minX)
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minY) p' ∈
          native.points.map (shiftPoint
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)) :=
        List.mem_map_of_mem hp'mem
      have hin' := hin _ hrouteMem _ hp'in
      have hconv : partPointT execution packed c (shiftPoint
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minX)
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minY) p') =
          routePointTransport execution.params.canvasMargin o.direction
            execution.packedAcc.canvasH q.2.x q.2.y
            (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX
            (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minY p' := by
        simp only [partPointT, routePointTransport, hshelfC, Option.getD_some,
          frameRun_shiftPoint_compose]
      rw [← hpeq, ← hconv]
      exact hin'
    intro hhit
    obtain ⟨hw, hh, hnm⟩ := hhit
    have hposS := hpos execution packed hpacked hselected hedge
    have hposB : 0 < (shelfRectT execution packed c').w ∧
        0 < (shelfRectT execution packed c').h := by
      have hbIn2 := hbIn
      unfold Rect.Contained at hbIn2
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hbIn2
      constructor <;> omega
    exact hnm (frameRun_allSegsMiss_of_shelves
      (partsShelvesDisjoint_of_pack hpacked c c' hclt hc'len (Ne.symm hne)) hptsIn hposS
        hposB hbIn)

/-! ## Flat loop miss -/

/-- Self-loop case of the flat frame miss: the scene route is the transported
loop placement, and the frame box is the transported `frameRect` of the
bridged real node. The run-level miss is
`componentLoops_route_misses_foreign_boxes`, with the reservation and
footprint-separation seams; the footprint side condition uses the bridged
`border = 0` (no `LoopForeignBoxBorderZero` needed). The other-part case is
the shelf separation. -/
theorem flatFrameLoopMiss {pinp : Input} {o : Options} {pres : FamilyResult} {group : ModelBox}
    (execution : SceneExecution pinp o pres)
    (hbridge : FrameRunBridge pinp o pres group)
    (hloopRes : ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat),
      comp ∈ components execution.graph →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopReservation (componentCandidate execution.graph comp candidate) run
        execution.measured v)
    (hloopSep : ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
        execution.measured v b)
    (hpos : RoutePartShelfPositive pinp o pres)
    {r : Route} {b : Box} (_hr : r ∈ pres.scene.routes) (hb : b ∈ pres.scene.boxes)
    (hframe : b.id = group.id)
    (hscope : group.id ∉ LayoutDump.routeScope pres.scene.layoutDump r)
    {key : Nat} (hkget : pres.scene.routes[key]? = some r) (_hkeylen : key < pinp.routes.length)
    {packed : Pack.State} {c : Nat} {q : (List Nat × Part) × Rect}
    {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)}
    {i : Nat} {edge : Edge} (area : Int)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    (hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge)
    (hdecl : edge.decl = key)
    {loop : Nat × LoopPlacement}
    (hfound : loops.find? (fun l => l.1 == edge.decl) = some loop) :
    ¬ Polyline.hitsRect r.points b.rect := by
  have hq1mem : q.1 ∈ execution.componentsAcc.parts := by
    have hmem : q ∈ execution.componentsAcc.parts.zip packed.boxes :=
      List.mem_of_getElem? hselected
    exact (List.of_mem_zip hmem).1
  have hq1comp : q.1.1 ∈ components execution.graph := by
    obtain ⟨hparts, _⟩ := actual_components_parts_geometry (by rfl) execution.components_eq
    rw [← hparts]
    exact List.mem_map_of_mem hq1mem
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have he := (List.getElem?_eq_some_iff.mp hedge).2
  have hedgemem : edge ∈ (componentCandidate execution.graph q.1.1 candidate).edges :=
    List.mem_of_getElem? hedge
  have hbounds := frameRun_candidate_edge_endpoints_bounded execution.graph q.1.1 candidate hq1comp
    (sceneExecution_edges_bounded execution) hedgemem
  have hself : edge.tail = edge.head := by
    apply Classical.byContradiction
    intro hne
    have hnd : ((componentCandidate execution.graph q.1.1 candidate).edges.map Edge.decl).Nodup :=
      componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate
    have hna := componentLoops_excludes_ordinary_decl hloops hnd hedge hne
    have hmem : loop ∈ loops := List.mem_of_find?_eq_some hfound
    have hloopdecl : loop.1 = edge.decl := by
      have h := List.find?_some hfound
      simpa only [beq_iff_eq] using h
    exact hna loop hmem hloopdecl
  obtain ⟨sroute, hsget, hsroute⟩ := frameRun_scene_loop_route_points execution packed hpacked
    hselected hrun hloops hpart hedge hbounds.1 hself hfound
  have hreq : r.points =
      loop.2.points.map (routePointTransport execution.params.canvasMargin o.direction
        execution.packedAcc.canvasH q.2.x q.2.y
        (placeBounds execution.params
          (componentCandidate execution.graph q.1.1 candidate) run execution.measured
          loops).minX
        (placeBounds execution.params
          (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        loops).minY) := by
    have h1 : pres.scene.routes[edge.decl]? = some r := by rw [hdecl]; exact hkget
    have h2 : pres.scene.routes[edge.decl]? =
        some (Route.mk sroute.id sroute.fromId sroute.toId sroute.orthogonal
          (loop.2.points.map (routePointTransport execution.params.canvasMargin o.direction
            execution.packedAcc.canvasH q.2.x q.2.y
            (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX
            (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minY))) := hsroute
    exact congrArg Route.points (Option.some.inj (h1.symm.trans h2))
  have hkeyedge : pres.scene.routes[edge.decl]? = some r := by
    rw [hdecl]; exact hkget
  have hbridge' := hbridge execution packed hpacked hq1comp hrun hloops hpart hselected
    hedge hkeyedge hb hframe hscope
  cases hbridge' with
  | inl hleft =>
    obtain ⟨v, _, _, _, _, _, _, hreal, hborder0, hbrect⟩ := hleft
    have hframeEq : frameRect execution.params
        (componentCandidate execution.graph q.1.1 candidate) run v =
        frameRect default (componentCandidate execution.graph q.1.1 candidate) run v := rfl
    obtain ⟨v₀, _hv₀, placements, hp, edge₀, hzip, _hdecl₀, htail, hhead⟩ :=
      componentLoops_entry_origin hloops (List.mem_of_find?_eq_some hfound)
    have hhex : run.exact = [] := componentRun_exact_nil hrun
    have hnotexact : ¬ v₀ ∈ run.exact := by rw [hhex]; simp
    have hcf : run.exact.contains v₀ = false := by rw [hhex]; rfl
    simp only [hcf, Bool.false_eq_true, ite_false] at hp
    have ⟨hslot, hres⟩ := hloopRes q.1.1 candidate run v₀ hq1comp hrun
    have hdisj : LoopFootprintSeparation
        (componentCandidate execution.graph q.1.1 candidate) run execution.measured v₀ v :=
      hloopSep q.1.1 candidate run v₀ v hq1comp hborder0 hrun
    have hmiss : ¬ Polyline.hitsRect loop.2.points
        (frameRect default (componentCandidate execution.graph q.1.1 candidate) run v) :=
      componentLoops_route_misses_foreign_boxes
        ⟨placements, hp, hzip, htail, hhead⟩ hnotexact hslot hres hdisj
    rw [hreq, hbrect, hframeEq, ← routePointTransport_eq]
    apply not_hitsRect_shift_orient
    apply not_hitsRect_shift
    exact not_hitsRect_shift _ _ _ _ hmiss
  | inr hright =>
    obtain ⟨c', r', hne, hshelfget, hbIn⟩ := hright
    have hc'len : c' < packed.boxes.length :=
      (List.getElem?_eq_some_iff.mp hshelfget).1
    have hmemc : execution.componentsAcc.parts[c]? = some q.1 := zip_getElem?_left hselected
    have hclt : c < packed.boxes.length := by
      rw [Pack.pack_count hpacked]
      simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hmemc).1
    have hshelfC : packed.boxes[c]? = some q.2 := (List.getElem?_zip_eq_some.mp hselected).2
    have hhb := hbounds.1
    obtain ⟨qq, _hqqmem, hqfind, _hqdecl, hget_pC⟩ :=
      componentLoops_emitted_self_edge hloops hedge hhb hself 0
    have hqeq : qq = loop := Option.some.inj (hqfind.symm.trans hfound)
    subst hqeq
    have hrouteMem : (edge.decl, qq.2.points.map
        (shiftPoint (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minX)
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minY))) ∈ q.1.2.routes := by
      rw [show q.1.2.routes =
          (placeComponent execution.params
            (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
            loops).routes from by rw [hpart]]
      exact List.mem_of_getElem? hget_pC
    have hin := part_route_points_within_shelf hpacked hmemc hclt
    have hptsIn : ∀ p ∈ r.points, pointInRect (shelfRectT execution packed c) p := by
      intro p hp
      rw [hreq] at hp
      obtain ⟨p', hp'mem, hpeq⟩ := List.mem_map.mp hp
      have hp'in : shiftPoint
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minX)
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minY) p' ∈
          qq.2.points.map (shiftPoint
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)) :=
        List.mem_map_of_mem hp'mem
      have hin' := hin _ hrouteMem _ hp'in
      have hconv : partPointT execution packed c (shiftPoint
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minX)
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minY) p') =
          routePointTransport execution.params.canvasMargin o.direction
            execution.packedAcc.canvasH q.2.x q.2.y
            (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX
            (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
            loops).minY p' := by
        simp only [partPointT, routePointTransport, hshelfC, Option.getD_some,
          frameRun_shiftPoint_compose]
      rw [← hpeq, ← hconv]
      exact hin'
    intro hhit
    obtain ⟨hw, hh, hnm⟩ := hhit
    have hposS := hpos execution packed hpacked hselected hedge
    have hposB : 0 < (shelfRectT execution packed c').w ∧
        0 < (shelfRectT execution packed c').h := by
      have hbIn2 := hbIn
      unfold Rect.Contained at hbIn2
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hbIn2
      constructor <;> omega
    exact hnm (frameRun_allSegsMiss_of_shelves_l _ _ _
      (partsShelvesDisjoint_of_pack hpacked c c' hclt hc'len (Ne.symm hne)) hptsIn hposS
        hposB hbIn)

/-! ## Flat frame clear -/

/-- The flat frame-clear conclusion: a scene route of a successful flat
layout misses the frame of the fixed group. Splits on the executed edge
(chain vs self-loop) like `flat_c6_core`, delegating to the two cases above. -/
theorem flat_frame_clear {pinp : Input} {o : Options} {pres : FamilyResult} {group : ModelBox}
    (execution : SceneExecution pinp o pres)
    (hclear : FrameClearanceSeam pinp o pres)
    (hbridge : FrameRunBridge pinp o pres group)
    (hnodeDecl : ExclusiveRunNodeDecl pinp o pres)
    (hscoped : RunRouteEndpointIdsScoped pinp o pres)
    (hloopRes : ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat),
      comp ∈ components execution.graph →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopReservation (componentCandidate execution.graph comp candidate) run
        execution.measured v)
    (hloopSep : ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
        execution.measured v b)
    (hpos : RoutePartShelfPositive pinp o pres)
    {r : Route} {b : Box} (hr : r ∈ pres.scene.routes) (hb : b ∈ pres.scene.boxes)
    (hframe : b.id = group.id)
    (hscope : group.id ∉ LayoutDump.routeScope pres.scene.layoutDump r) :
    ¬ Polyline.hitsRect r.points b.rect := by
  obtain ⟨key, hkget⟩ := List.mem_iff_getElem?.mp hr
  have hlen : pres.scene.routes.length = pinp.routes.length := by
    rw [execution.scene_eq]
    exact sceneOf_routes_length execution.params pinp o execution.lines
      execution.packedAcc execution.measured
  have hkey : key < pinp.routes.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hkget).1
  obtain ⟨packed, c, q, candidate, run, loops, area, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ :=
    execution.route_component_source hkey
  cases hfound : loops.find? (fun l => l.1 == edge.decl) with
  | none =>
    exact flatFrameChainMiss execution hclear hbridge hnodeDecl hscoped hpos
      hr hb hframe hscope hkget hkey area hpacked hselected hrun hloops hpart hedge hdecl hfound
  | some loop =>
    exact flatFrameLoopMiss execution hbridge hloopRes hloopSep hpos
      hr hb hframe hscope hkget hkey area hpacked hselected hrun hloops hpart hedge hdecl
      hfound

/-! ## Fixed entry for the parent call (proved) -/

/-- The fixed-size entry the bridge needs: the parent sub-input appends
`(group.id, childFrameSize ...)` to the (unchanged) fixed tables, and the
recursion only selects a non-fixed group, so the appended entry is the
unique match. -/
theorem parentInput_group_fixedEntry
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    ∃ entry : String × Size,
      (parentSubInput inp group P titleLines child).fixedSizes.find?
        (fun fixed => fixed.1 == group.id) = some entry := by
  obtain ⟨_, hfind, _, _, _, _⟩ := hctx
  have hpred := List.find?_some hfind
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨_, hnotfixed⟩ := hpred
  have hany : inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
    simpa using hnotfixed
  have hnone : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hany)
  have hfix : (parentSubInput inp group P titleLines child).fixedSizes =
      inp.fixedSizes ++ [(group.id, childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩)] := rfl
  refine ⟨(group.id, childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0)
      ((max 1 titleLines.length : Int) * P.lineH)
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩), ?_⟩
  rw [hfix, List.find?_append, hnone]
  simp

/-! ## Lift residuals -/

/-- Per-expansion frame step, frame located in the parent scene (the common
case: the expanded group is unrelated to the frame). Mirrors
`ExpandChildC6Geometry` with the frame in place of the exclusive box, plus
scope premises (the scope transport through the merged dump is the lift's
job, as `routeScope_subset` is for C6). The first conjunct is the cross-side
geometry: shifted child routes (confined to the expanded frame, disjoint
from the frame by the unrelated-frames result) miss the frame. The second
conjunct is the induction hypothesis shape for the parent side. -/
def ExpandChildFrameGeometry (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleHeight : Int) (parent child _result : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines →
    (∀ cr ∈ child.scene.routes,
        cr.fromId ≠ group.id → cr.toId ≠ group.id →
        group.id ∉ LayoutDump.routeScope child.scene.layoutDump cr →
        ¬ Polyline.hitsRect (cr.points.map (shiftPoint dx dy)) frame.rect) ∧
    (∀ pr ∈ parent.scene.routes,
        pr.fromId ≠ group.id → pr.toId ≠ group.id →
        group.id ∉ LayoutDump.routeScope parent.scene.layoutDump pr →
        ¬ Polyline.hitsRect pr.points frame.rect)

/-- Per-expansion frame step, frame located in the child scene (the ancestor
case: the expanded group strictly contains the fixed frame). Symmetric to
`ExpandChildFrameGeometry` with the sides swapped; the frame travels to the
merged scene shifted by `(dx, dy)`. The parent-side conjunct is the hard
cross-side geometry (parent routes miss the expanded frame, hence the inner
frame by monotonicity); the child-side conjunct is the induction hypothesis
shape. -/
def ExpandChildFrameChildGeometry (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleHeight : Int) (parent child _result : FamilyResult) : Prop :=
  ∀ (frame : Box) (titleLines : List Measure.Line) (dx dy : Int),
    child.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines →
    (∀ cr ∈ child.scene.routes,
        cr.fromId ≠ group.id → cr.toId ≠ group.id →
        group.id ∉ LayoutDump.routeScope child.scene.layoutDump cr →
        ¬ Polyline.hitsRect cr.points frame.rect) ∧
    (∀ pr ∈ parent.scene.routes,
        pr.fromId ≠ group.id → pr.toId ≠ group.id →
        group.id ∉ LayoutDump.routeScope parent.scene.layoutDump pr →
        ¬ Polyline.hitsRect pr.points (shiftRect dx dy frame.rect))

/-- The lifted conclusion for the executed parent call: the frame-level miss
holds under a scope premise. Follows, in the future induction mirroring
`layoutRecursive_c6_of_flat`, from the flat version (`flat_frame_clear` at
every `layout` leaf, via `layout_sceneExecution` and the bridge with
`parentInput_group_fixedEntry`) and the per-expansion steps above: the zero
case is flat; the succ case splits merged routes via `expandChild_routes_eq`
(child-embedded routes transport through the common shift, parent-verbatim
routes transport through unchanged ancestor chains) with scope carried by the
merged dump (`routeScope_subset`, `ancestors_mono`). -/
def ExpandChildFrameRecursion (_fuel : Nat) (_P : Params) (_inp : Input) (_o : Options)
    (group : ModelBox) (_titleLines : List Measure.Line) (_titleHeight : Int)
    (parent _child _res : FamilyResult) : Prop :=
  ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pr ∈ parent.scene.routes, pr.fromId ≠ group.id → pr.toId ≠ group.id →
      group.id ∉ LayoutDump.routeScope parent.scene.layoutDump pr →
      ¬ Polyline.hitsRect pr.points frame.rect

/-- Scope from endpoints for the executed parent call: a parent route whose
endpoints differ from the group id has the group id outside its dump route
scope. Pure id fact, no geometry. Proof route: dump ancestors are the input
parent chains (`SceneExecution.boxes_eq_map` preserves parents at the flat
leaves, `embedBox` transports preserve them through expansion), so group id
on an endpoint ancestor chain would put that endpoint inside the group
(`inside_of_ancestors`), contradicting the `selectInput` exclusion the
parent sub-input is built from. -/
def ExpandChildFrameScopeOutside (_fuel : Nat) (_P : Params) (_inp : Input) (_o : Options)
    (group : ModelBox) (_titleLines : List Measure.Line) (_titleHeight : Int)
    (parent _child _res : FamilyResult) : Prop :=
  ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pr ∈ parent.scene.routes, pr.fromId ≠ group.id → pr.toId ≠ group.id →
      group.id ∉ LayoutDump.routeScope parent.scene.layoutDump pr

/-! ## Part (b) needs (no proof)

The attached conjunct `ExpandChildParentRouteAttachedClear` needs exactly
these facts; none is proved here:

1. `C5` boundary port at the frame: the attached endpoint of the scene route
   lies `onBoundary` of the transported frame rect. At run level this is the
   ordinary/group attachment (`componentRun_ordinary_route_attachment` for
   plain endpoints, `GroupRouteAttachment.componentRun_group_route_attachment`
   for group top proxies), transported through packing and orientation like
   the chain case above. The frame is a `border = 0` node, so the plain
   endpoint form applies.
2. Outward-facing stub: the first (resp. last) segment of the attached route
   leaves the frame rect, i.e. the port stub exterior faces outward. This is
   the port-placement side of the same attachment lemmas (frameKind and stub
   geometry), not a clearance fact.
3. Middle-segment avoidance: the remaining segments miss the frame interior.
   The frame is the endpoint's own node, hence explicitly excluded from the
   run-level node avoidance; what is needed is the channel-placement bound
   (route middle segments run in reserved lanes outside all node rects of the
   executed run), applied to the frame node.
4. Strict-inside transport from the frame boundary to every strictly inside
   rect: proved (`routeClear_hitsRect_of_strictInside` in
   `ExpandChildParentRouteClearProof`), using that `hitsRect` counts only the
   open interior while the attachment touches at most the boundary.
-/

end Elegant.Layered.PipelineImpl

import Elegant.Layered.FlatC6Assembly
import Elegant.Layered.PartSeparation
import Elegant.Layered.ComponentCoverage

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Scope-bridge and chain-case proofs for the flat clause 6 seams

This module discharges two of the open seams assembled in
`Elegant.Layered.FlatC6Assembly`:

* `routeScopeBridge` proves `RouteScopeBridge`: an exclusive scene box outside
  the dump route scope is either the transported `frameRect` of a real node of
  the executing component run, or the content of a different packed part.
* `flatC6ChainCase` proves `FlatC6ChainCase`: the chain (non-self-loop) scene
  route never meets the interior of such a foreign exclusive box.

Both proofs ride on executed facts that already exist: the reverse scene box
lookup (`SceneExecution.boxes_eq_map`), the part/component fold
(`actual_components_parts_geometry`), the frame entry of a placed part
(`chosen_part_frame_entry`), the packed rect write
(`actual_components_packed_rect_value`), the part/shelf separation
(`Elegant.Layered.PartSeparation`), and the run-level clearance
(`componentRun_exclusive_clear`).

The named residuals below isolate the remaining id-level facts that no existing
lemma states; each speaks only about node ids of one executed component run,
carries no geometry, and is strictly weaker than the seams proved here. The
measured-graph provenance residual records the one transport step (plain-box
graph cluster paths are ancestor lists) that no existing lemma provides.
-/

/-- Local re-proof of the private `ComponentCoverage.componentCandidate_nodes_length`:
a candidate graph has exactly the component's nodes. -/
private theorem candidate_nodes_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- Endpoint projections of the pristine form of an edge. -/
private theorem edge_original_tail (e : Edge) :
    e.original.tail = if e.reversed then e.head else e.tail := by
  unfold Edge.original
  cases h : e.reversed <;> simp

/-- Endpoint projections of the pristine form of an edge. -/
private theorem edge_original_head (e : Edge) :
    e.original.head = if e.reversed then e.tail else e.head := by
  unfold Edge.original
  cases h : e.reversed <;> simp

/-- Every edge of a component candidate keeps both endpoints below the
candidate's node count: candidate edges are the component's edges renumbered
through `List.idxOf`, and both endpoints of a graph edge lie in one component. -/
private theorem candidate_edge_endpoints_bounded (g : Graph) (comp : List Nat) (index : Nat)
    (hcomp : comp ∈ components g)
    (hbd : ∀ e ∈ g.edges ++ Compound.constraints g,
      e.tail < g.nodes.length ∧ e.head < g.nodes.length)
    {edge : Edge} (hedge : edge ∈ (componentCandidate g comp index).edges) :
    edge.tail < (componentCandidate g comp index).nodes.length ∧
      edge.head < (componentCandidate g comp index).nodes.length := by
  have hlen : (componentCandidate g comp index).nodes.length = comp.length :=
    candidate_nodes_length g comp index
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
  rw [edge_original_tail e₁, edge_original_tail edge] at ht
  rw [edge_original_head e₁, edge_original_head edge] at hh
  rw [hlen]
  cases h₁ : e₁.reversed <;> cases h₂ : edge.reversed <;>
    simp only [h₁, h₂, Bool.false_eq_true, ↓reduceIte] at ht hh <;>
    constructor <;> omega

/-- The component of the selected part is the component whose run placed it:
whenever a component run that owns an edge places the very records of the part
packed at index `c`, that component is the part's own.  This is the id-level
consistency of the executed component fold: the part's route table is shared by
both placements, so both components own an edge with the same declaration, hence
the same graph edge, hence a common node. -/
private theorem part_component_aligned
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
  have hbounds := candidate_edge_endpoints_bounded execution.graph comp candidate hcomp
    (sceneExecution_edges_bounded execution) hedgemem
  have hdecls := componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq comp candidate
  -- the comp edge's declaration appears in the comp placement's route table
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
  -- the part's own placement shares that route table
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
private theorem mem_zip_getElem? {α β : Type} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
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

/-! ## Named residuals (id-level facts of one executed component run)

Each of the following defs states one executed fact about node ids of a single
component run. None of them carries geometry, and none implies (or renames)
`RouteScopeBridge` or `FlatC6ChainCase`; they are the remaining seams that the
run-level id transport does not yet provide. -/

/-- Residual: the declaration of a node of an executed component run is the key
of its model source box.  This is the id half of the run's node transport
(`componentRun` preserves node declarations through normalization and
ordering); geometry plays no role. -/
def ExclusiveRunNodeDecl (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ (v key : Nat) (source : ModelBox),
      comp[v]? = some key →
      inp.boxes[key]? = some source →
      RouteImpl.nodeDecl run.proper v = key

/-- Residual: the endpoint nodes of the run route that produces a scene route
carry model-box ids inside that scene route's dump scope.  Pure id statement
about one run route and the route scope list. -/
def RunRouteEndpointIdsScoped (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ (i : Nat) (edge : Edge) (native : EdgeRoute) (route : Route),
      (componentCandidate execution.graph comp candidate).edges[i]? = some edge →
      run.routes[i]? = some native →
      native.original = i →
      res.scene.routes[edge.decl]? = some route →
      ∀ i₀ i₁,
        (RouteImpl.edgesOf run.proper native.original).head? = some i₀ →
        (RouteImpl.edgesOf run.proper native.original).getLast? = some i₁ →
        (∀ b₀ : ModelBox,
          inp.boxes[RouteImpl.nodeDecl run.proper (RouteImpl.edgeAt run.proper i₀).tail]? =
            some b₀ →
          b₀.id ∈ LayoutDump.routeScope res.scene.layoutDump route) ∧
        (∀ b₁ : ModelBox,
          inp.boxes[RouteImpl.nodeDecl run.proper (RouteImpl.edgeAt run.proper i₁).head]? =
            some b₁ →
          b₁.id ∈ LayoutDump.routeScope res.scene.layoutDump route)

/-- Residual: for a well-formed framed input, the declaration of a node whose
model source box is exclusive never occurs in the cluster path of the endpoint
nodes of any route of the same executed run.  The bare id statement is false:
an exclusive group with an edge-bearing member puts the group's declaration
into the member's cluster path (`Compound.path`); the two leading premises
rule that counterexample out (`modelWellFormed` forbids exclusive groups,
`inputModel` copies `inp.boxes`, and `framedParents` forces every parent to be
a group, so an exclusive box is never a parent and cluster paths list only
ancestors).  Id statement only. -/
def ExclusiveDeclOutsideEndpointPaths (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  WellFormed (inputModel inp o) → framedParents inp = true →
  ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ (v key : Nat) (source : ModelBox),
      comp[v]? = some key →
      inp.boxes[key]? = some source →
      source.exclusive = true →
      ∀ rt ∈ run.routes, ∀ i₀ i₁,
        (RouteImpl.edgesOf run.proper rt.original).head? = some i₀ →
        (RouteImpl.edgesOf run.proper rt.original).getLast? = some i₁ →
        RouteImpl.nodeDecl run.proper v ∉
          ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₀).tail]?).map
            (·.node.clusterPath)).getD [] ∧
        RouteImpl.nodeDecl run.proper v ∉
          ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₁).head]?).map
            (·.node.clusterPath)).getD []

/-- Residual (measured-graph provenance): the cluster path stored for a plain
(non-group) box of an executed measured graph is the ancestor list
`Compound.path` of its source box.  This is the transport that `measuredGraph`
provides (per-index `clusterPath` assignment, preserved by `Compound.prepare`
for plain boxes since demotion keeps ids and parents); no existing lemma
states it, and the exclusive-declaration bridge needs it to turn "exclusive
boxes are never parents" into "exclusive declarations occur in no cluster
path".  True for executed layouts, strictly simpler than the bridge goal, and
pinned by the `SceneExecution` graph equation. -/
def MeasuredGraphClusterPathOfPlainNode (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (key : Nat) (box : ModelBox),
    inp.boxes[key]? = some box →
    box.role ≠ .group →
    ∀ (node : Node),
      execution.graph.nodes[key]? = some node →
      node.clusterPath = Compound.path inp.boxes box

/-- Residual (run-level cluster-path provenance): every index occurring in the
cluster path of a node of an executed component run's proper graph is the index
of a group-role box of the input.  Cluster paths are built by `Compound.prepare`
as `Compound.path` ancestor lists (plus the group box's own index for group
title/bottom nodes) and are preserved through normalization, labelling,
coordinate construction, proxy materialization and synthetic-edge removal;
dummy chain nodes receive the common prefix of their endpoint paths.  Every
element is therefore an ancestor index — a parent box, which `framedParents`
makes a group — or a group box index itself.  True for executed layouts,
strictly simpler than the endpoint exclusion (a per-node path-membership fact,
not a route statement), and pinned by the `componentRun` success equation and
the `components` membership of `comp`. -/
def RunClusterPathGroupMembers (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ (i : Nat) (nd : ProperNode),
      run.proper.nodes[i]? = some nd →
      ∀ k ∈ nd.node.clusterPath, ∀ b,
        inp.boxes[k]? = some b → b.role = .group

/-- The measured-graph cluster-path fact is exactly the plain-node case of
`SceneExecution.plain_graph_node`: an exclusive source is never a group under
`WellFormed`, so its measured-graph node keeps `Compound.path inp.boxes box`. -/
theorem measuredGraphClusterPathOfPlainNode {inp : Input} {o : Options} {res : FamilyResult}
    (_hwf : WellFormed (inputModel inp o)) (_hframed : framedParents inp = true) :
    MeasuredGraphClusterPathOfPlainNode inp o res := by
  intro execution key box hsource hrole node hnode
  obtain ⟨gnode, hgnode, _, hpath, _⟩ :=
    execution.plain_graph_node hsource (fun ⟨hg, _⟩ => hrole hg)
  have heq : gnode = node := Option.some.inj (hgnode.symm.trans hnode)
  rw [← heq]
  exact hpath

/-- Reduction: the measured-graph cluster-path provenance together with the
run-level declaration bridge imply the exclusive-declaration endpoint-path
exclusion.  `ExclusiveRunNodeDecl` identifies `RouteImpl.nodeDecl run.proper v`
with the box index `key`; `RunClusterPathGroupMembers` shows every member of an
endpoint's cluster path indexes a group box, while `WellFormed` makes an
exclusive box a non-group, so `key` cannot occur. -/
theorem exclusiveDeclOutsideEndpointPaths_of_clusterPath
    {inp : Input} {o : Options} {res : FamilyResult}
    (_hpath : MeasuredGraphClusterPathOfPlainNode inp o res)
    (hdecl : ExclusiveRunNodeDecl inp o res)
    (hgroup : RunClusterPathGroupMembers inp o res) :
    ExclusiveDeclOutsideEndpointPaths inp o res := by
  intro hwf _hframed execution comp candidate run hcomp hrun
    v key source hv hsource hexcl _rt _hrt _i₀ _i₁ _hfirst _hlast
  have hdeclEq : RouteImpl.nodeDecl run.proper v = key :=
    hdecl execution comp candidate run hcomp hrun v key source hv hsource
  have hrole : source.role ≠ .group := by
    intro hg
    obtain ⟨_, _, _, _, _, _, hgroups⟩ := (wellFormed_iff (inputModel inp o)).mp hwf
    have := hgroups source (List.mem_of_getElem? hsource) hg
    rw [this] at hexcl
    exact Bool.noConfusion hexcl
  rw [hdeclEq]
  constructor
  · intro hkey
    cases hnode? : run.proper.nodes[(RouteImpl.edgeAt run.proper _i₀).tail]? with
    | none => simp [hnode?] at hkey
    | some nd =>
      simp only [hnode?, Option.map_some, Option.getD_some] at hkey
      exact hrole (hgroup execution comp candidate run hcomp hrun _ nd hnode? key hkey source hsource)
  · intro hkey
    cases hnode? : run.proper.nodes[(RouteImpl.edgeAt run.proper _i₁).head]? with
    | none => simp [hnode?] at hkey
    | some nd =>
      simp only [hnode?, Option.map_some, Option.getD_some] at hkey
      exact hrole (hgroup execution comp candidate run hcomp hrun _ nd hnode? key hkey source hsource)

/-- Same-part witness: an exclusive scene box whose source key lies in the
selected part's component is the transported `frameRect` of the real run node
at the key's local position, and that node is a plain (non-group) node, so its
frame is its node rect.  This lemma does the emission-side work both remaining
seams share; it uses the executed fold, the part's own placement, and the packed
rect write, but no clearance or scope reasoning. -/
private theorem exclusive_box_run_witness
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {run : Run}
    {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (_hloops : componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops)
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area })
    {key : Nat} {source : ModelBox}
    (hsource : inp.boxes[key]? = some source)
    (hexcl : source.exclusive = true)
    (hmem : key ∈ q.1.1) :
    ∃ v : Nat,
      q.1.1[v]? = some key ∧
      v < (componentCandidate execution.graph q.1.1 candidate).nodes.length ∧
      RouteImpl.IsReal run.proper v ∧
      ((componentCandidate execution.graph q.1.1 candidate).nodes.getD v default).border ≠ -2 ∧
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD key default))) =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run
                execution.measured loops).minX)
              (0 - (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run
                execution.measured loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run v)))) := by
  obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
  have hvlen : v < (componentCandidate execution.graph q.1.1 candidate).nodes.length := by
    rw [candidate_nodes_length]
    exact (List.getElem?_eq_some_iff.mp hv).1
  have hkeylen : key < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsource).1
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact hkeylen
  have hentry := chosen_part_frame_entry hpart hv
  dsimp only at hentry
  have hval := actual_components_packed_rect_value (by rfl) execution.components_eq
    execution.packed_eq packed hpacked hselected hentry hkeysize default
  have hgraphlen : key < execution.graph.nodes.length :=
    sceneExecution_graph_len execution hkeylen
  have hgraphnode : execution.graph.nodes[key]? =
      some (execution.graph.nodes[key]'hgraphlen) := List.getElem?_eq_getElem hgraphlen
  have hreal := componentRun_source_isReal hrun (candidate_node_of_part_key hv hgraphnode)
  obtain ⟨_, _, _, _, _, _, hgroups⟩ := (wellFormed_iff (inputModel inp o)).mp hwf
  have hnode : source.role = BoxRole.node := by
    have hnotgroup : source.role ≠ BoxRole.group := by
      intro hg
      have := hgroups source (List.mem_of_getElem? hsource) hg
      rw [this] at hexcl
      exact Bool.noConfusion hexcl
    cases hr : source.role with
    | node => rfl
    | group => exact absurd hr hnotgroup
  have hborder :=
    execution.effective_candidate_node_not_top (component := q.1.1) (candidate := candidate)
      (v := v) (key := key) (source := source) hv hsource (Or.inl hnode)
  refine ⟨v, hv, hvlen, hreal, hborder, ?_⟩
  exact congrArg (fun r => shiftRect execution.params.canvasMargin
    execution.params.canvasMargin
    (orientRect o.direction execution.packedAcc.canvasH r)) hval

/-- The route-scope bridge seam of `FlatC6Assembly`: for a successful flat
execution, an exclusive scene box outside the dump route scope either is the
transported frame of a real node of the route's own component run (satisfying
the run-level endpoint and cluster-path exclusions through the id residual), or
lies inside the transported shelf of a different packed part. -/
theorem routeScopeBridge {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
    (hpaths : ExclusiveDeclOutsideEndpointPaths inp o res) :
    RouteScopeBridge inp o res := by
  have _hexec := execution
  intro exec packed hpacked comp candidate run loops area c q hcomp hrun hloops hpart
    hselected i edge hedge route box hroute hboxmem hex hscope
  have halign : comp = q.1.1 :=
    part_component_aligned exec packed hpacked hselected hcomp hrun hloops hpart hedge
  subst comp
  -- reverse scene-box lookup
  rw [exec.boxes_eq_map] at hboxmem
  obtain ⟨pair, hpair, hboxeq⟩ := List.mem_map.mp hboxmem
  have hsource : inp.boxes[pair.2]? = some pair.1 := List.mem_zipIdx_iff_getElem?.mp hpair
  have hkeylen : pair.2 < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsource).1
  have hkeysize : pair.2 < exec.componentsAcc.rects.size := by
    rw [exec.components_rects_size]
    exact hkeylen
  have hexcl : pair.1.exclusive = true := by
    rw [← hboxeq] at hex
    exact hex
  have hscope' : pair.1.id ∉ LayoutDump.routeScope res.scene.layoutDump route := by
    rw [← hboxeq] at hscope
    exact hscope
  have hq1mem : q.1 ∈ exec.componentsAcc.parts :=
    List.mem_of_getElem? (zip_getElem?_left hselected)
  have hparts := (actual_components_parts_geometry (by rfl) exec.components_eq).1
  have hq1comp : q.1.1 ∈ components exec.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hq1mem
  have hboxrect : box.rect =
      shiftRect exec.params.canvasMargin exec.params.canvasMargin
        (orientRect o.direction exec.packedAcc.canvasH
          (exec.packedAcc.rects.getD pair.2 default)) := by
    rw [← hboxeq]
  by_cases hmem : pair.2 ∈ q.1.1
  · obtain ⟨v, hv, hvlen, hreal, _, hbrect⟩ :=
      exclusive_box_run_witness exec hwf packed hpacked hselected hrun hloops hpart
      hsource hexcl hmem
    have hexclrt := hpaths hwf hframed exec q.1.1 candidate run hq1comp hrun v pair.2 pair.1 hv
      hsource hexcl
    refine ⟨v, Or.inl ⟨hvlen, hreal, ?_, ?_⟩⟩
    · intro rt hrt i₀ i₁ hfirst hlast
      exact fun _ _ => hexclrt rt hrt i₀ i₁ hfirst hlast
    · rw [hboxrect]
      exact hbrect
  · obtain ⟨part', hpart'mem, entry, hentrymem, hentrykey⟩ :=
      sceneExecution_parts_entry exec hkeylen
    obtain ⟨v', hv'key, hv'rect⟩ := mem_zip_getElem? hentrymem
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
    have hselected' : (exec.componentsAcc.parts.zip packed.boxes)[c']? =
        some (part', packed.boxes[c']'hc'len) :=
      List.getElem?_zip_eq_some.mpr ⟨hc'get, hshelf⟩
    have hframe : part'.2.rects[v']? = some entry.2 := hv'rect
    have hentry2 : (part'.1.zip part'.2.rects)[v']? = some (pair.2, entry.2) :=
      List.getElem?_zip_eq_some.mpr ⟨hv'key, hframe⟩
    have hval' := actual_components_packed_rect_value (by rfl) exec.components_eq
      exec.packed_eq packed hpacked hselected' hentry2 hkeysize default
    have hcont := part_rects_within_shelf hpacked hc'get hc'len entry.2
      (List.mem_of_getElem? hframe)
    have hc'ne : c' ≠ c := by
      intro heq
      have hqc : exec.componentsAcc.parts[c']? = some q.1 := by
        rw [heq]
        exact zip_getElem?_left hselected
      have hpe : part' = q.1 := Option.some.inj (hc'get.symm.trans hqc)
      exact hmem (hpe ▸ hkeymem')
    refine ⟨0, Or.inr ⟨c', packed.boxes[c']'hc'len, hc'ne, hshelf, ?_⟩⟩
    rw [hboxrect, hval']
    simpa only [shelfRectT, partRectT, hshelf, Option.getD_some] using hcont

/-- Point-transport composition along a shelf origin. -/
private theorem shiftPoint_compose (dx dy nx ny : Int) (p : Point) :
    shiftPoint dx dy (shiftPoint (0 - nx) (0 - ny) p) = shiftPoint (dx - nx) (dy - ny) p := by
  cases p
  simp only [shiftPoint, Point.mk.injEq]
  constructor <;> omega

/-- A segment between two points of a closed shelf rect misses the interior of
any rect the disjoint partner shelf contains: with both shelves of positive
extent, disjoint open interiors leave one of the four axis separations, and
each matches a separating-axis disjunct of `Polyline.segMisses`. -/
private theorem segMisses_of_shelf {S B R : Rect} {p q : Point}
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

/-- Whole-polyline version of `segMisses_of_shelf`. -/
private theorem allSegsMiss_of_shelves {S B R : Rect} : ∀ {points : List Point},
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
      exact ⟨segMisses_of_shelf hd hposS hposB (hpts p List.mem_cons_self)
        (hpts p' (List.mem_cons_of_mem _ List.mem_cons_self)) hsub,
        ih hd (fun x hx => hpts x (List.mem_cons_of_mem _ hx)) hposS hposB hsub⟩

/-- Packing-transport residual: the shelf that the executed packing assigns to
a part whose component owns an edge has positive extent in both axes.  This is
the positivity `componentLoops_route_misses_foreign_boxes` analogously takes
for the loop slot (`LoopReservation`): without it, a degenerate shelf could put
the part's closed boundary inside a neighbouring shelf's interior. -/
def RoutePartShelfPositive (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (_hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge),
    0 < (shelfRectT execution packed c).w ∧ 0 < (shelfRectT execution packed c).h

/-- The chain-case seam of `FlatC6Assembly`: a non-self-loop scene route misses
the interior of an exclusive box outside its route scope.  The same-part branch
is `componentRun_exclusive_clear` applied to the bridged run node (with the
id residuals supplying the endpoint and cluster-path exclusions); the
other-part branch is the shelf separation of `PartSeparation`, which needs the
route part's shelf to have positive extent. -/
theorem flatC6ChainCase {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hnodeDecl : ExclusiveRunNodeDecl inp o res)
    (hscoped : RunRouteEndpointIdsScoped inp o res)
    (hpaths : ExclusiveDeclOutsideEndpointPaths inp o res)
    (hpos : RoutePartShelfPositive inp o res) :
    FlatC6ChainCase inp o res := by
  intro execution hclear hbridge r b hr hb hex hscope key hkget hkeylen
    packed c q candidate run loops i edge area hpacked hselected hrun hloops hpart
    hedge hdecl hfound
  have _hbridge := hbridge
  -- the executed component of the selected part
  have hq1comp : q.1.1 ∈ components execution.graph := by
    obtain ⟨hparts, _⟩ := actual_components_parts_geometry (by rfl) execution.components_eq
    rw [← hparts]
    exact List.mem_map_of_mem
      (List.mem_of_getElem? (zip_getElem?_left hselected))
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have hedgemem : edge ∈ (componentCandidate execution.graph q.1.1 candidate).edges :=
    List.mem_of_getElem? hedge
  have hbounds := candidate_edge_endpoints_bounded execution.graph q.1.1 candidate hq1comp
    (sceneExecution_edges_bounded execution) hedgemem
  -- the chain edge is no self-loop, or the executed loops would contain it
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
  -- the scene route is the transported run route
  have hkeyedge : res.scene.routes[edge.decl]? = some r := by
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
  -- reverse scene-box lookup
  rw [execution.boxes_eq_map] at hb
  obtain ⟨pair, hpair, hboxeq⟩ := List.mem_map.mp hb
  have hsource : inp.boxes[pair.2]? = some pair.1 := List.mem_zipIdx_iff_getElem?.mp hpair
  have hkeylen : pair.2 < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsource).1
  have hkeysize : pair.2 < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact hkeylen
  have hexcl : pair.1.exclusive = true := by
    rw [← hboxeq] at hex
    exact hex
  have hscope' : pair.1.id ∉ LayoutDump.routeScope res.scene.layoutDump r := by
    rw [← hboxeq] at hscope
    exact hscope
  have hboxrect : b.rect =
      shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD pair.2 default)) := by
    rw [← hboxeq]
  by_cases hmem : pair.2 ∈ q.1.1
  · -- same part: the bridged run node and the run-level clearance
    obtain ⟨v, hv, hvlen, hreal, hborder, hbrect⟩ :=
      exclusive_box_run_witness execution hwf packed hpacked hselected hrun hloops hpart
      hsource hexcl hmem
    have hnd : RouteImpl.nodeDecl run.proper v = pair.2 :=
      hnodeDecl execution q.1.1 candidate run hq1comp hrun v pair.2 pair.1 hv hsource
    -- the run route's chain supplies a proper edge with original `i`
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
      exact absurd hjmem (by simp)
    | some i₀ =>
      cases h₁ : (RouteImpl.edgesOf run.proper i).getLast? with
      | none =>
        have hnil : RouteImpl.edgesOf run.proper i = [] := (List.getLast?_eq_none_iff).mp h₁
        rw [hnil] at hjmem
        exact absurd hjmem (by simp)
      | some i₁ =>
        have hfirst : (RouteImpl.edgesOf run.proper native.original).head? = some i₀ := by
          rw [hnativeOrig]; exact h₀
        have hlast : (RouteImpl.edgesOf run.proper native.original).getLast? = some i₁ := by
          rw [hnativeOrig]; exact h₁
        have hexclrt := hpaths hwf hframed execution q.1.1 candidate run hq1comp hrun v pair.2 pair.1 hv
          hsource hexcl
        have hclusters := hexclrt native (List.mem_iff_getElem?.mpr ⟨i, hnative⟩) i₀ i₁
          hfirst hlast
        have hscoping := hscoped execution q.1.1 candidate run hq1comp hrun i edge native r
          hedge hnative hnativeOrig hkeyedge i₀ i₁ hfirst hlast
        have hv0 : v ≠ (RouteImpl.edgeAt run.proper i₀).tail := by
          intro hev
          have hbx : inp.boxes[RouteImpl.nodeDecl run.proper
              (RouteImpl.edgeAt run.proper i₀).tail]? = some pair.1 := by
            have hshift : RouteImpl.nodeDecl run.proper
                (RouteImpl.edgeAt run.proper i₀).tail =
                RouteImpl.nodeDecl run.proper v := by rw [hev]
            rw [hshift, hnd]
            exact hsource
          exact hscope' (hscoping.1 pair.1 hbx)
        have hv1 : v ≠ (RouteImpl.edgeAt run.proper i₁).head := by
          intro hev
          have hbx : inp.boxes[RouteImpl.nodeDecl run.proper
              (RouteImpl.edgeAt run.proper i₁).head]? = some pair.1 := by
            have hshift : RouteImpl.nodeDecl run.proper
                (RouteImpl.edgeAt run.proper i₁).head =
                RouteImpl.nodeDecl run.proper v := by rw [hev]
            rw [hshift, hnd]
            exact hsource
          exact hscope' (hscoping.2 pair.1 hbx)
        have hclearRun : FrameClearance run.proper run.layers run.xs :=
          hclear execution q.1.1 candidate run (candidateOrder candidate) hq1comp hrun
        have hmiss := componentRun_exclusive_clear
          (checkedParams_valid execution.checked)
          (componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate)
          (componentCandidate_shape (components_nodup execution.graph q.1.1 hq1comp)
            (measuredGraph_shape execution.graph_eq) candidate)
          hclearRun hrun hi hnative hfirst hlast (componentRun_original_nodes_covered hrun v hvlen)
            hreal hv0 hv1
          hclusters.1 hclusters.2
          execution.params.canvasMargin o.direction execution.packedAcc.canvasH q.2.x q.2.y
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minX
          (placeBounds execution.params (componentCandidate execution.graph q.1.1 candidate)
            run execution.measured loops).minY
        rw [congrArg Route.points hreq, hboxrect, hbrect, shiftRect_pack_normalize,
          plain_frame_eq_boxRect execution.params
            (componentCandidate execution.graph q.1.1 candidate) run v
            (componentRun_original_nodes_covered hrun v hvlen) hborder]
        exact hmiss
  · -- other part: shelf separation
    obtain ⟨part', hpart'mem, entry, hentrymem, hentrykey⟩ :=
      sceneExecution_parts_entry execution hkeylen
    obtain ⟨v', hv'key, hv'rect⟩ := mem_zip_getElem? hentrymem
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
    have hframe : part'.2.rects[v']? = some entry.2 := hv'rect
    have hentry2 : (part'.1.zip part'.2.rects)[v']? = some (pair.2, entry.2) :=
      List.getElem?_zip_eq_some.mpr ⟨hv'key, hframe⟩
    have hval' := actual_components_packed_rect_value (by rfl) execution.components_eq
      execution.packed_eq packed hpacked hselected' hentry2 hkeysize default
    have hcont := part_rects_within_shelf hpacked hc'get hc'len entry.2
      (List.mem_of_getElem? hframe)
    have hc'ne : c' ≠ c := by
      intro heq
      have hqc : execution.componentsAcc.parts[c']? = some q.1 := by
        rw [heq]
        exact zip_getElem?_left hselected
      have hpe : part' = q.1 := Option.some.inj (hc'get.symm.trans hqc)
      exact hmem (hpe ▸ hkeymem')
    -- the box lies in the transported shelf of its own part
    have hbIn : (shelfRectT execution packed c').Contained b.rect := by
      rw [hboxrect, hval']
      simpa only [shelfRectT, partRectT, hshelf, Option.getD_some] using hcont
    -- the route points lie in the transported shelf of part c
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
          shiftPoint_compose]
      rw [← hpeq, ← hconv]
      exact hin'
    -- assemble
    intro hhit
    obtain ⟨hw, hh, hnm⟩ := hhit
    have hposS := hpos execution packed hpacked hselected hedge
    have hposB : 0 < (shelfRectT execution packed c').w ∧
        0 < (shelfRectT execution packed c').h := by
      unfold Rect.Contained at hbIn
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hbIn
      constructor <;> omega
    exact hnm (allSegsMiss_of_shelves
      (partsShelvesDisjoint_of_pack hpacked c c' hclt hc'len (Ne.symm hc'ne)) hptsIn hposS
        hposB hbIn)

end PipelineImpl
end Layered
end Elegant

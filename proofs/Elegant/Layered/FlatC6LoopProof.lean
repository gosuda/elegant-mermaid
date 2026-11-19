import Elegant.Layered.FlatC6Assembly
import Elegant.Layered.FlatC6ScopeBridgeProof
import Elegant.Layered.RouteTransport
import Elegant.Layered.PartSeparation
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.SceneBounds

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# The self-loop case of the flat clause C6 seam

This module discharges `FlatC6LoopCase` from `FlatC6Assembly`: a scene route
that is the `routePointTransport` image of a `LoopPlacement` for a self edge
of an executed component run never meets the interior of an exclusive scene
box outside its route scope.

The structure follows `FlatC6ScopeBridgeProof.flatC6ChainCase`: the executed
component of the selected part is identified, the route scope bridge
(`RouteScopeBridge`) is consumed to place the foreign scene box, and the two
branches are closed by the run-level loop miss
(`componentLoops_route_misses_foreign_boxes`) transported to the scene, or by
the shelf separation of `PartSeparation`.

Step 1 of the task (the `b = v` sanity check) is discharged by
`loopFootprint_self_disjoint`.  The footprint is the rectangle starting at the
right edge of the node's own `frameRect`, so its interior never meets the
node's own interior, unconditionally.
-/

/-- Step 1: the loop footprint of `v` is disjoint from the frame of `v`
itself.  The footprint's `x` interval starts at the frame's right edge
`f.x + f.w`, so the interior-meeting inequality in the `x` component is
`f.x + f.w < f.x + f.w`, impossible regardless of the (possibly degenerate)
extent or the frame position.  No execution fact is needed. -/
theorem loopFootprint_self_disjoint (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (v : Nat) :
    Disjoint (loopFootprint cg run labels v) (frameRect default cg run v) := by
  unfold Disjoint Rect.meetsInterior loopFootprint
  rintro ⟨hx, -⟩
  dsimp only at hx
  omega

/-- An executed component run has no exact ports: `componentRun` constructs
its `Run` by the thirteen-field constructor whose final field is always the
empty list.  Destructuring the binds like `componentRun_spec` and substituting
the final identity leaves the constructor value, whose `.exact` reduces to
`[]`. -/
theorem componentRun_exact_nil {P : Params} {cg : Graph} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {run : Run}
    (h : componentRun P cg labels orderOptions = .ok run) : run.exact = [] := by
  unfold componentRun at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p0, _, h⟩ := bind_ok h
  obtain ⟨p, _, h⟩ := bind_ok h
  obtain ⟨ord, _, h⟩ := bind_ok h
  obtain ⟨xs, _, h⟩ := bind_ok h
  obtain ⟨routed, _, h⟩ := bind_ok h
  obtain ⟨r, _, h⟩ := bind_ok h
  obtain ⟨yt, _, h⟩ := bind_ok h
  obtain ⟨routes, _, h⟩ := bind_ok h
  have h := Except.ok.inj h
  subst h
  rfl

/-- Local re-proof of the private `ComponentCoverage.componentCandidate_nodes_length`. -/
private theorem candidate_nodes_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- Endpoint projections of the pristine form of an edge.  Local copy of the
private lemma of the same name in `FlatC6ScopeBridgeProof`. -/
private theorem edge_original_tail (e : Edge) :
    e.original.tail = if e.reversed then e.head else e.tail := by
  unfold Edge.original
  cases h : e.reversed <;> simp

/-- Endpoint projections of the pristine form of an edge.  Local copy of the
private lemma of the same name in `FlatC6ScopeBridgeProof`. -/
private theorem edge_original_head (e : Edge) :
    e.original.head = if e.reversed then e.tail else e.head := by
  unfold Edge.original
  cases h : e.reversed <;> simp
/-- Every edge of a component candidate keeps both endpoints below the
candidate's node count.  Local copy of the private lemma of the same name in
`FlatC6ScopeBridgeProof`. -/
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

/-- The executed fold preserves the route array size.  Local copy of the
private lemma of the same name in `ExecutedPortsFacts`. -/
private theorem components_fold_routes_size (P : Params) (inp : Input) (o : Options)
    (graph : Graph) (labels : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponent P inp o graph acc comp labels) start =
        .ok out →
      out.routes.size = start.routes.size
  | [], start, out, h => by
    have he : start = out := Except.ok.inj h
    rw [he]
  | comp :: comps, start, out, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨next, hnext, hrest⟩ := bind_ok h
    rw [components_fold_routes_size P inp o graph labels comps next out hrest]
    exact (layoutComponent_sizes hnext).2.1.symm

/-- Point-transport composition along a shelf origin.  Local copy of the
private lemma of the same name in `FlatC6ScopeBridgeProof`. -/
private theorem shiftPoint_compose (dx dy nx ny : Int) (p : Point) :
    shiftPoint dx dy (shiftPoint nx ny p) = shiftPoint (dx + nx) (dy + ny) p := by
  cases p
  simp only [shiftPoint, Point.mk.injEq]
  constructor <;> omega

/-- A segment between two points of a closed shelf rect misses the interior of
any rect the disjoint partner shelf contains.  Local copy of the private
lemma of the same name in `FlatC6ScopeBridgeProof`. -/
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

/-- Whole-polyline version of `segMisses_of_shelf`.  Local copy of the
private lemma of the same name in `FlatC6ScopeBridgeProof`. -/
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

/-- The scene route of a self-loop edge is the `routePointTransport` image of
the emitted `LoopPlacement` points.  This is the loop analog of
`chosen_part_route_entry`: the placement is emitted by
`componentLoops_emitted_self_edge`, lifted through the packed accumulator
(`actual_components_packAcc_routes_getD`), and the scene route entry is
read off by `sceneOf_routes_getElem?`; `routePointTransport_eq` folds the three
nested shifts into the transport. -/
private theorem scene_loop_route_points {inp : Input} {o : Options} {res : FamilyResult}
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
    have h := components_fold_routes_size execution.params inp o execution.graph
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

/-- Segment between two points of a closed shelf rect misses the interior of
any rect the disjoint partner shelf contains.  With both shelves of positive
extent, disjoint open interiors leave one of the four axis separations, and
each matches a separating-axis disjunct of `Polyline.segMisses`. -/
private theorem segMisses_of_shelf_l (S B R : Rect) {p q : Point}
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
  unfold Polyline.segMisses
  unfold pointInRect at hp hq
  unfold Rect.Contained at hsub
  rcases hsep with hx | hx | hy | hy
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- Whole-polyline version of `segMisses_of_shelf_l`. -/
private theorem allSegsMiss_of_shelves_l (S B R : Rect) : ∀ {points : List Point},
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
      exact ⟨segMisses_of_shelf_l S B R hd hposS hposB (hpts p List.mem_cons_self)
        (hpts p' (List.mem_cons_of_mem _ List.mem_cons_self)) hsub,
        ih hd (fun x hx => hpts x (List.mem_cons_of_mem _ hx)) hposS hposB hsub⟩

/-- Residual (exclusive-box provenance): an exclusive scene box whose rect is the
transported `frameRect` of a real node of an executed component run comes from a
plain node, so the candidate node at that position has `border = 0`.  The rect
equation pins the run node to the scene box; `modelWellFormed` forbids exclusive
groups, so an exclusive source box has node role and its frame is a plain node
frame.  No existing lemma states the `border = 0` conclusion (`measuredGraph`
only records `≠ -2` for node-role boxes). -/
def LoopForeignBoxBorderZero (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ {q : (List Nat × Part) × Rect} {loops : List (Nat × LoopPlacement)}
      (v : Nat) (b : Box),
      RouteImpl.IsReal run.proper v →
      b ∈ res.scene.boxes → b.exclusive = true →
      b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBounds execution.params
                (componentCandidate execution.graph comp candidate) run execution.measured
                loops).minX)
              (0 - (placeBounds execution.params
                (componentCandidate execution.graph comp candidate) run execution.measured
                loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph comp candidate) run v)))) →
      ((componentCandidate execution.graph comp candidate).nodes.getD v default).border = 0
/-- Real-part exclusive-box provenance: the `LoopForeignBoxBorderZeroRealQ`
/conclusion shape, with `q` pinned to the selected packed part. The old
/`LoopForeignBoxBorderZero` quantifies `q` universally and is false as stated
/(a fixed group aligns with a same-size exclusive node); the consumer only
/ever applies it at the real packed part, so the loop case takes this form.
/Discharged in `FlatC6ClosedProof` via `loopForeignBoxBorderZeroRealQ` from
/the five `LoopRect*Real` residuals. -/
def LoopForeignBoxBorderZeroReal (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (_hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box),
      RouteImpl.IsReal run.proper v →
      b ∈ res.scene.boxes → b.exclusive = true →
      b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minX)
              (0 - (placeBounds execution.params
                (componentCandidate execution.graph q.1.1 candidate) run execution.measured
                loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph q.1.1 candidate) run v)))) →
      ((componentCandidate execution.graph q.1.1 candidate).nodes.getD v default).border = 0

/-- The loop case of the flat clause C6 seam.  The reservation
(`LoopReservation`) and footprint-separation (`LoopFootprintSeparation`)
premises are consumed exactly where `componentLoops_route_misses_foreign_boxes`
demands them; the route scope bridge supplies the scene box, and the
registration above transports the run-level loop miss to the scene. -/
theorem flatC6LoopCase {inp : Input} {o : Options} {res : FamilyResult}
    (hpos : RoutePartShelfPositive inp o res)
    (hbord : LoopForeignBoxBorderZeroReal inp o res) :
    FlatC6LoopCase inp o res := by
  intro execution hclear hbridge hloopRes hloopSep r b hr hb hex hscope key hkget hkeylen
    packed c q candidate run loops i edge area hpacked hselected hrun hloops hpart
    hedge hdecl loop hfound
  have _hclear := hclear
  -- the executed component of the selected part
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
  have hbounds := candidate_edge_endpoints_bounded execution.graph q.1.1 candidate hq1comp
    (sceneExecution_edges_bounded execution) hedgemem
  -- the loop edge is a self edge, or the executed loops would not contain it
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
  -- the scene route is the transported loop placement
  obtain ⟨sroute, hsget, hsroute⟩ := scene_loop_route_points execution packed hpacked
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
    have h1 : res.scene.routes[edge.decl]? = some r := by rw [hdecl]; exact hkget
    have h2 : res.scene.routes[edge.decl]? =
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
  -- the route scope bridge places the foreign scene box
  have hbridge' := hbridge execution packed hpacked hq1comp hrun hloops hpart hselected
    hedge (by rw [hdecl]; exact hkget) hb hex hscope
  obtain ⟨v, hv⟩ := hbridge'
  cases hv with
  | inl hleft =>
    obtain ⟨-, hreal, -, hbrect⟩ := hleft
    -- the bridged foreign node comes from a plain node, discharging the
    -- restricted separation premise
    have hborder0 : ((componentCandidate execution.graph q.1.1 candidate).nodes.getD v
        default).border = 0 :=
      hbord execution candidate run packed hpacked c q hselected hpart hq1comp hrun
        v b hreal hb hex hbrect
    -- same part: the run-level loop miss, transported to the scene
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
    obtain ⟨c', r', hne, hshelfget, hcont⟩ := hright
    have hc'len : c' < packed.boxes.length := (List.getElem?_eq_some_iff.mp hshelfget).1
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
          shiftPoint_compose]
        congr <;> omega
      rw [← hpeq, ← hconv]
      exact hin'
    have hbIn : (shelfRectT execution packed c').Contained b.rect := by
      simpa only [shelfRectT, partRectT, hshelfget, Option.getD_some] using hcont
    intro hhit
    obtain ⟨hw, hh, hnm⟩ := hhit
    have hposS := hpos execution packed hpacked hselected hedge
    have hposB : 0 < (shelfRectT execution packed c').w ∧
        0 < (shelfRectT execution packed c').h := by
      have hbIn2 := hbIn
      unfold Rect.Contained at hbIn2
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hbIn2
      constructor <;> omega
    exact hnm (allSegsMiss_of_shelves_l _ _ _
      (partsShelvesDisjoint_of_pack hpacked c c' hclt hc'len (Ne.symm hne)) hptsIn hposS
        hposB hbIn)

end PipelineImpl
end Layered
end Elegant

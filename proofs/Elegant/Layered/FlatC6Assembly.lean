import Elegant.Layered.PipelineFacts
import Elegant.Layered.RouteScopeClearance
import Elegant.Layered.FlatC6Loops
import Elegant.Layered.FrameClearanceSeam
import Elegant.Layered.SceneBounds
import Elegant.Layered.Pack
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Layered.RouteTransport
import ElegantGeometry.Validator
import ElegantGeometry.Route

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Flat clause 6: assembly from the executed seams

`Validator.C6` asks that a route never meet the interior of an exclusive box
outside its route scope (`[from, to] ++ ancestors`).  For a successful flat
`PipelineImpl.layout` the scene routes and boxes are transports of the
component-run data that `componentRun_exclusive_clear` (chain routes) and
`componentLoops_route_misses_foreign_boxes` (self-loops) already bound.  The
named hypothesis defs below isolate exactly the remaining executed facts that
are not yet discharged by a single lemma; the assembly itself is proved from
them.

* `RouteScopeBridge` is the id-to-run-node/scope translation: a scene box
  outside the dump route scope is the transported frame of a real node of the
  executing component run, and that node satisfies the run-level scope
  exclusions `componentRun_exclusive_clear` consumes.
* `LoopReservation` and `LoopFootprintSeparation` are the two named premises
  `componentLoops_route_misses_foreign_boxes` takes for a self-loop.
* `FlatC6ChainCase` and `FlatC6LoopCase` are the two OPEN transport cases: the
  run-level miss of a chain route or a self-loop, carried through packing and
  orientation to the scene route and the bridged scene box.
-/

/-- The loop reservation premise `componentLoops_route_misses_foreign_boxes`
takes: a positive slot and enough frame height for the loop band. -/
def LoopReservation (cg : Graph) (run : Run) (labels : List MeasuredLabel)
    (v : Nat) : Prop :=
  0 < cg.slot ∧
    (loopSizes cg.edges labels v cg.slot).length *
      Loops.band cg.slot (loopSizes cg.edges labels v cg.slot) ≤
      (frameRect default cg run v).h

/-- The footprint-separation premise `componentLoops_route_misses_foreign_boxes`
takes: the loop footprint of `v` is disjoint from every foreign node frame. -/
def LoopFootprintSeparation (cg : Graph) (run : Run) (labels : List MeasuredLabel)
    (v b : Nat) : Prop :=
  Disjoint (loopFootprint cg run labels v) (frameRect default cg run b)

/-- Bridge from a scene route and a foreign exclusive scene box to the executed
component run.  Given the executed `SceneExecution`, the packed selection that
produced the route, the component edge, and a foreign exclusive scene box, it
returns the real node `v` of the run whose transported frame rect is the scene
box, together with the run-level scope exclusions
`componentRun_exclusive_clear` consumes.  This is the same id/scope
translation `RouteLabelDumpBridges` performs for labels; it carries no geometry
beyond the rect equality the scene assembly already establishes. -/
def RouteScopeBridge (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res)
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
    (_hroute : res.scene.routes[edge.decl]? = some route)
    (_hboxmem : box ∈ res.scene.boxes)
    (_hex : box.exclusive = true)
    (_hscope : box.id ∉ LayoutDump.routeScope res.scene.layoutDump route),
    (∃ v : Nat, v < (componentCandidate execution.graph comp candidate).nodes.length ∧
      RouteImpl.IsReal run.proper v ∧
      (∀ rt ∈ run.routes, ∀ i₀ i₁,
        (RouteImpl.edgesOf run.proper rt.original).head? = some i₀ →
        (RouteImpl.edgesOf run.proper rt.original).getLast? = some i₁ →
        v ≠ (RouteImpl.edgeAt run.proper i₀).tail →
        v ≠ (RouteImpl.edgeAt run.proper i₁).head →
        RouteImpl.nodeDecl run.proper v ∉
          ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₀).tail]?).map
            (·.node.clusterPath)).getD [] ∧
        RouteImpl.nodeDecl run.proper v ∉
          ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₁).head]?).map
            (·.node.clusterPath)).getD []) ∧
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
                (componentCandidate execution.graph comp candidate) run v))))
    ∨
    -- The box belongs to a different packed part `c'`: its scene rect is
    -- contained in the transported shelf box of `c'`, disjoint from the shelf
    -- of the route's own part `c`.  `PartsSeparated` discharges this case.
    ∃ c' : Nat, ∃ r' : Rect, c' ≠ c ∧ packed.boxes[c']? = some r' ∧
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH r')).Contained box.rect)

/-- Open seam, chain-route case of the flat C6 core: the scene route is the
`routePointTransport` image of a `run.routes` entry of the executed component
run, and the foreign exclusive scene box is the transported `frameRect` of a
real run node outside the route's scope (`RouteScopeBridge`).  Intended proof:
`componentRun_exclusive_clear` supplies the run-level miss and the transport
lemmas carry it to the scene. -/
def FlatC6ChainCase (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res),
    FrameClearanceSeam inp o res → RouteScopeBridge inp o res →
    ∀ {r : Route} {b : Box}, r ∈ res.scene.routes → b ∈ res.scene.boxes →
    b.exclusive = true →
    b.id ∉ LayoutDump.routeScope res.scene.layoutDump r →
    ∀ {key : Nat}, res.scene.routes[key]? = some r → key < inp.routes.length →
    ∀ {packed : Pack.State} {c : Nat} {q : (List Nat × Part) × Rect}
      {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)}
      {i : Nat} {edge : Edge} (area : Int),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q →
    componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops →
    q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area } →
    (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge →
    edge.decl = key →
    loops.find? (fun l => l.1 == edge.decl) = none →
    ¬ Polyline.hitsRect r.points b.rect

/-- Open seam, self-loop case of the flat C6 core: the scene route is the
`routePointTransport` image of a `LoopPlacement` emitted for a self edge of
the executed component run, and the foreign exclusive scene box is again the
transported `frameRect` of a run node supplied by `RouteScopeBridge`.
Intended proof: `componentLoops_route_misses_foreign_boxes` bounds the loop
points against the foreign frame; the reservation and footprint-separation
premises discharge its side conditions. -/
def FlatC6LoopCase (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res),
    FrameClearanceSeam inp o res → RouteScopeBridge inp o res →
    (∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat),
      comp ∈ components execution.graph →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopReservation (componentCandidate execution.graph comp candidate) run
        execution.measured v) →
    (∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
        execution.measured v b) →
    ∀ {r : Route} {b : Box}, r ∈ res.scene.routes → b ∈ res.scene.boxes →
    b.exclusive = true →
    b.id ∉ LayoutDump.routeScope res.scene.layoutDump r →
    ∀ {key : Nat}, res.scene.routes[key]? = some r → key < inp.routes.length →
    ∀ {packed : Pack.State} {c : Nat} {q : (List Nat × Part) × Rect}
      {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)}
      {i : Nat} {edge : Edge} (area : Int),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q →
    componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured = .ok loops →
    q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area } →
    (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge →
    edge.decl = key →
    ∀ {loop : Nat × LoopPlacement},
    loops.find? (fun l => l.1 == edge.decl) = some loop →
    ¬ Polyline.hitsRect r.points b.rect

/-- The executed C6 core: a scene route misses an exclusive scene box outside its
route scope.  The route's component source splits on whether its edge is a
self-loop; the two open transport cases `FlatC6ChainCase` and `FlatC6LoopCase`
close the branches. -/
theorem flat_c6_core
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hchain : FlatC6ChainCase inp o res) (hloopCase : FlatC6LoopCase inp o res)
    (hclear : FrameClearanceSeam inp o res)
    (hbridge : RouteScopeBridge inp o res)
    (hloopRes : ∀ (e : SceneExecution inp o res) (comp : List Nat)
      (candidate : Nat) (run : Run) (v : Nat),
      comp ∈ components e.graph →
      componentRun e.params
        (componentCandidate e.graph comp candidate) e.measured
        (candidateOrder candidate) = .ok run →
      LoopReservation (componentCandidate e.graph comp candidate) run e.measured v)
    (hloopSep : ∀ (e : SceneExecution inp o res) (comp : List Nat)
      (candidate : Nat) (run : Run) (v b : Nat),
      comp ∈ components e.graph →
      ((componentCandidate e.graph comp candidate).nodes.getD b default).border = 0 →
      componentRun e.params
        (componentCandidate e.graph comp candidate) e.measured
        (candidateOrder candidate) = .ok run →
      LoopFootprintSeparation (componentCandidate e.graph comp candidate) run e.measured v b)
    {r : Route} {b : Box}
    (hr : r ∈ res.scene.routes) (hb : b ∈ res.scene.boxes)
    (hex : b.exclusive = true)
    (hscope : b.id ∉ LayoutDump.routeScope res.scene.layoutDump r) :
    ¬ Polyline.hitsRect r.points b.rect := by
  obtain ⟨key, hkget⟩ := List.mem_iff_getElem?.mp hr
  have hlen : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    exact sceneOf_routes_length execution.params inp o execution.lines
      execution.straightAcc execution.measured
  have hkey : key < inp.routes.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hkget).1
  obtain ⟨packed, c, q, candidate, run, loops, area, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ :=
    execution.route_component_source hkey
  cases hfound : loops.find? (fun l => l.1 == edge.decl) with
  | none =>
    exact hchain execution hclear hbridge hr hb hex hscope hkget hkey area
      hpacked hselected hrun hloops hpart hedge hdecl hfound
  | some loop =>
    exact hloopCase execution hclear hbridge (hloopRes execution) (hloopSep execution)
      hr hb hex hscope hkget hkey area hpacked hselected hrun hloops hpart hedge hdecl
      hfound

/-- Flat clause 6 assembled from the executed seams. -/
theorem layout_c6 {inp : Input} {o : Options} {res : FamilyResult}
    (hchain : FlatC6ChainCase inp o res) (hloopCase : FlatC6LoopCase inp o res)
    (hclear : FrameClearanceSeam inp o res)
    (hbridge : RouteScopeBridge inp o res)
    (hloopRes : ∀ (execution : SceneExecution inp o res) (comp : List Nat)
      (candidate : Nat) (run : Run) (v : Nat),
      comp ∈ components execution.graph →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopReservation (componentCandidate execution.graph comp candidate) run
        execution.measured v)
    (hloopSep : ∀ (execution : SceneExecution inp o res) (comp : List Nat)
      (candidate : Nat) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
        execution.measured v b)
    (h : PipelineImpl.layout inp o = .ok res) :
    Validator.C6 res.scene.layoutDump := by
  obtain ⟨execution⟩ := layout_sceneExecution h
  intro r hr b hb hex hscope
  exact flat_c6_core execution hchain hloopCase hclear hbridge hloopRes hloopSep
    hr hb hex hscope

end PipelineImpl
end Layered
end Elegant

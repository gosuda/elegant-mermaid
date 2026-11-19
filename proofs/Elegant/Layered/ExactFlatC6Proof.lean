import Elegant.Layered.FlatC6Assembly
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ExactFlatC5
import Elegant.Layered.ExactFlatC7
import Elegant.Layered.PartSeparation
import Elegant.Layered.RecursiveBLiftsB
import ElegantGeometry.Validator

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Exact flat clause 6 (`FlatC6B (layoutX exactIds)`).

Replay of `FlatC6ClosedProof.flatC6_closed` over `SceneExecutionX`: the
assembly (`x6_core`, `x6_c6`) replays `flat_c6_core`/`layout_c6` with
`SceneExecutionX.route_component_sourceX` in place of
`SceneExecution.route_component_source` (the scene assembly `sceneOf` is
shared; only the graph/run phases differ). The two transport cases, the
route-scope bridge, and the run/shelf/loop residuals stay narrow open
hypotheses of the main theorem, each a single fact quantified over executed
exact runs only. The loop case is stated without the plain `LoopReservation`
premise: on degenerate exact runs (e.g. a `2000x10` exact node) the band
inequality `n * band ≤ frame.h` is false (`1536 ≤ 10`), so no universal
reservation over executed exact runs is true, while the route miss still
holds (probe `c6=true`); the miss must go through part/shelf separation
rather than footprint confinement there.
* `X6_ChainCase` / `X6_LoopCase`: mirrors of `FlatC6ChainCase` /
  `FlatC6LoopCase` over `componentRunX`/`placeComponentExact`, the latter
  without a reservation hypothesis.
* `X6_LoopFootprintSeparation`: per-execution mirror of
  `LoopFootprintSeparation` over `componentRunX`.
* `X6_ChainEndpointKeys`: mirror of `ProperChainEndpointKeys` over
  `componentRunX`.
* `X6_DeclOutsidePaths`: mirror of `ExclusiveDeclOutsideEndpointPaths` over
  `componentRunX`.
* `X6_ShelfPositive`: mirror of `RoutePartShelfPositive` over
  `placeComponentExact` pack states.
* `X6_BorderZeroReal`: mirror of `LoopForeignBoxBorderZeroReal` over
  `placeComponentExact`/`placeBoundsX`.

The run-id premise reuses the existing exact residual
`X_ExclusiveRunNodeDecl` (`ExactFlatC7.lean`), proved closed by
`x_exclusiveRunNodeDecl_holds`. Probe:
`proofs/wip/Probe/ExactFlatC6TProbe.lean` (`c6=true` on flat, nested,
deep-nested, zero, wide, and tall fixed-size inputs, with and without exact
ids, all well-formed and framed).
-/

/-- X mirror of `RouteScopeBridge`: an exclusive scene box outside the dump
route scope is the transported `frameRect` of a real node of the executing
exact component run, or the content of a different packed part. -/
def X6_RouteScopeBridge (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {comp : List Nat} {candidate : Nat} {run : Run}
    {loops : List (Nat × LoopPlacement)} {area : Int}
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hcomp : comp ∈ components execution.graph)
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (_hloops : componentLoops execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured
      = .ok loops)
    (_hpart : q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph comp candidate) run 0 execution.measured
      loops with area := area })
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {i : Nat} {edge : Edge}
    (_hedge : (componentCandidate execution.graph comp candidate).edges[i]? =
      some edge)
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
            (shiftRect (0 - (placeBoundsX execution.params
                (componentCandidate execution.graph comp candidate) run
                execution.measured loops).minX)
              (0 - (placeBoundsX execution.params
                (componentCandidate execution.graph comp candidate) run
                execution.measured loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph comp candidate) run v))))
    ∨
    ∃ c' : Nat, ∃ r' : Rect, c' ≠ c ∧ packed.boxes[c']? = some r' ∧
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH r')).Contained box.rect)

/-- X mirror of `FlatC6ChainCase`: a non-self-loop exact scene route misses
the interior of a foreign exclusive scene box. -/
def X6_ChainCase (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res),
    FrameClearanceSeam inp o res → X6_RouteScopeBridge exactIds inp o res →
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
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      = .ok loops →
    q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area } →
    (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge →
    edge.decl = key →
    loops.find? (fun l => l.1 == edge.decl) = none →
    ¬ Polyline.hitsRect r.points b.rect

/-- X mirror of `FlatC6LoopCase`: a self-loop exact scene route misses the
interior of a foreign exclusive scene box. -/
def X6_LoopCase (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res),
    FrameClearanceSeam inp o res → X6_RouteScopeBridge exactIds inp o res →
    (∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRunX execution.params (exactDecls exactIds inp)
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
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
      = .ok loops →
    q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area } →
    (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge →
    edge.decl = key →
    ∀ {loop : Nat × LoopPlacement},
    loops.find? (fun l => l.1 == edge.decl) = some loop →
    ¬ Polyline.hitsRect r.points b.rect

/-- X mirror of `ProperChainEndpointKeys`: run route endpoints resolve to
model endpoint declarations, over `componentRunX`. -/
def X6_ChainEndpointKeys (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (comp : List Nat)
    (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ (i : Nat) (edge : Edge) (native : EdgeRoute),
      (run.routes[i]? = some native) →
      (native.original = i) →
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

/-- X mirror of `ExclusiveDeclOutsideEndpointPaths`: exclusive declarations
occur in no endpoint cluster path, over `componentRunX`. -/
def X6_DeclOutsidePaths (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (comp : List Nat)
    (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ (v : Nat) (key : Nat),
      RouteImpl.nodeDecl run.proper v = key →
      inp.boxes[key]?.map (·.exclusive) = some true →
      ∀ (i : Nat) (edge : Edge) (native : EdgeRoute),
        run.routes[i]? = some native →
        (componentCandidate execution.graph comp candidate).edges[i]? = some edge →
        ∀ (i₀ i₁ : Nat),
          (RouteImpl.edgesOf run.proper native.original).head? = some i₀ →
          (RouteImpl.edgesOf run.proper native.original).getLast? = some i₁ →
          key ∉ ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₀).tail]?).map
            (·.node.clusterPath)).getD [] ∧
          key ∉ ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₁).head]?).map
            (·.node.clusterPath)).getD []

/-- X mirror of `RoutePartShelfPositive`: the packed shelf of an exact part
with an edge is positive in both axes. -/
def X6_ShelfPositive (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (packed : Pack.State)
    (_hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {c : Nat} {q : (List Nat × Part) × Rect}
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {candidate : Nat} {i : Nat} {edge : Edge}
    (_hedge : (componentCandidate execution.graph q.1.1 candidate).edges[i]? =
      some edge),
    0 < (shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (packed.boxes[c]?.getD default))).w ∧
    0 < (shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (packed.boxes[c]?.getD default))).h

/-- X mirror of `LoopFootprintSeparation` per executed exact run: the loop
footprint of `v` is disjoint from the frame of `b`, over `componentRunX`. -/
def X6_LoopFootprintSeparation (exactIds : List String) (inp : Input)
    (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (comp : List Nat)
    (candidate : Nat) (run : Run) (v b : Nat),
    comp ∈ components execution.graph →
    ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
      execution.measured v b

/-- X mirror of `LoopForeignBoxBorderZeroReal`: a real exact run node behind
a positive foreign exclusive scene box has border zero. -/
def X6_BorderZeroReal (exactIds : List String) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionX exactIds inp o res) (candidate : Nat)
    (run : Run) (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed),
    ∀ {c : Nat} {q : (List Nat × Part) × Rect},
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q →
    ∀ {area : Int} {loops : List (Nat × LoopPlacement)},
    q.1.2 = { placeComponentExact execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area } →
    q.1.1 ∈ components execution.graph →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ {v : Nat} {b : Box},
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    0 < b.rect.w → 0 < b.rect.h →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBoundsX execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    ((componentCandidate execution.graph q.1.1 candidate).nodes.getD v default).border = 0

/-- The executed exact C6 core, replaying `flat_c6_core` over
`SceneExecutionX.route_component_sourceX`. -/
theorem x6_core {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hchain : X6_ChainCase exactIds inp o res)
    (hloop : X6_LoopCase exactIds inp o res)
    (hclear : FrameClearanceSeam inp o res)
    (hbridge : X6_RouteScopeBridge exactIds inp o res)
    (hloopSep : ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
        execution.measured v b)
    {r : Route} {b : Box}
    (hr : r ∈ res.scene.routes) (hb : b ∈ res.scene.boxes)
    (hex : b.exclusive = true)
    (hscope : b.id ∉ LayoutDump.routeScope res.scene.layoutDump r) :
    ¬ Polyline.hitsRect r.points b.rect := by
  obtain ⟨key, hkget⟩ := List.mem_iff_getElem?.mp hr
  have hlen : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    exact sceneOf_routes_length execution.params inp o execution.lines
      execution.packedAcc execution.measured
  have hkey : key < inp.routes.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hkget).1
  obtain ⟨packed, c, q, candidate, run, loops, area, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ :=
    execution.route_component_sourceX hkey
  cases hfound : loops.find? (fun l => l.1 == edge.decl) with
  | none =>
    exact hchain execution hclear hbridge hr hb hex hscope hkget hkey area
      hpacked hselected hrun hloops hpart hedge hdecl hfound
  | some loop =>
    exact hloop execution hclear hbridge hloopSep
      hr hb hex hscope hkget hkey area hpacked hselected hrun hloops hpart hedge hdecl
      hfound

/-- Flat clause 6 for the exact pipeline, assembled from the executed exact
seams, replaying `layout_c6`. -/
theorem x6_c6 {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult}
    (hchain : X6_ChainCase exactIds inp o res)
    (hloop : X6_LoopCase exactIds inp o res)
    (hclear : FrameClearanceSeam inp o res)
    (hbridge : X6_RouteScopeBridge exactIds inp o res)
    (hloopSep : X6_LoopFootprintSeparation exactIds inp o res)
    (h : layoutX exactIds inp o = .ok res) :
    Validator.C6 res.scene.layoutDump := by
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  intro r hr b hb hex hscope
  exact x6_core execution hchain hloop hclear hbridge
    (hloopSep execution) hr hb hex hscope

/-- Flat clause 6 for the exact pipeline: every successful `layoutX` keeps
every route clear of foreign exclusive boxes. The run-id premise reuses the
existing exact residual `X_ExclusiveRunNodeDecl`; the bridge, transport
cases, and loop/shelf/endpoint residuals stay narrow open hypotheses, each
a single fact over executed exact runs. -/
theorem flatC6B_layoutX (exactIds : List String)
    (hdecl : X_ExclusiveRunNodeDecl exactIds)
    (hkeys : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      X6_ChainEndpointKeys exactIds inp o res)
    (hpaths : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      X6_DeclOutsidePaths exactIds inp o res)
    (hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      X6_ShelfPositive exactIds inp o res)
    (hsep : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      X6_LoopFootprintSeparation exactIds inp o res)
    (hbord : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      X6_BorderZeroReal exactIds inp o res)
    (hbridge : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      X6_RouteScopeBridge exactIds inp o res)
    (hchain : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      X_ExclusiveRunNodeDecl exactIds →
      X6_ChainEndpointKeys exactIds inp o res →
      X6_DeclOutsidePaths exactIds inp o res →
      X6_ShelfPositive exactIds inp o res →
      X6_ChainCase exactIds inp o res)
    (hloop : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      X6_ShelfPositive exactIds inp o res →
      X6_BorderZeroReal exactIds inp o res →
      X6_LoopCase exactIds inp o res) :
    FlatC6B (layoutX exactIds) := by
  intro inp o res hwf hframed hclear hlay
  exact x6_c6
    (hchain inp o res hwf hframed hdecl (hkeys inp o res hwf hframed)
      (hpaths inp o res hwf hframed) (hpos inp o res hwf hframed))
    (hloop inp o res hwf hframed (hpos inp o res hwf hframed)
      (hbord inp o res hwf hframed))
    hclear
    (hbridge inp o res hwf hframed)
    (hsep inp o res hwf hframed)
    hlay

end PipelineImpl
end Layered
end Elegant

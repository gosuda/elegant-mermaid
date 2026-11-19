import Elegant.Layered.RegionC5Endpoints
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.RegionFlatC4

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region C5 boundary split: plain endpoints proved, group residual.

`RegionC5Endpoints.lean` closes `flatC5B_layoutRIds_closed` from the single
open def `R_GroupBoundaryR`. This file splits that residual in two along the
input-box role: routes with no group endpoint (`R_PlainBoundaryR`, proved
here for both region specs) and routes touching a group box
(`R_GroupEndpointBoundaryR`, the single remaining public residual, strictly
narrower than `R_GroupBoundaryR`). `flatC5B_layoutRIds_final` recombines them.

Proof route for the plain case (mirrors `ExactFlatC5.lean`,
`ExactFlatC5Rank.lean`, `ExactFlatC5Bottom.lean` over `componentRunR_specR`):
the route's first point is an anchor on the tail node rect, transported
through placement and packing; group endpoints would attach to the group
frame's border row instead. Region differences: edges may be reversed by
`rankEquivalentR`, so endpoint lookup goes through the returned graph `cg'`
by `decl` (`r_orientedDeclRangeR_holds`); for a `some` spec the anchors are
computed after `crossCoordsR` and `reservedPortsR`.
-/

/-- Plain-endpoint boundary: every scene route of an executed region run on a
well-formed framed-parents input whose `fromId`/`toId` name no group box
carries endpoint points on the boundary of its `from`/`to` dump boxes.
Strictly narrower than `R_GroupBoundaryR` (plain routes only). -/
def R_PlainBoundaryR (exactIds : List String) (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ∀ out ∈ res.scene.routes,
    (∀ gb ∈ inp.boxes, gb.role = .group → gb.id ≠ out.fromId ∧ gb.id ≠ out.toId) →
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧ Validator.onBoundary finish toBox.rect

/-- Group-endpoint boundary residual: the same boundary conclusion restricted
to scene routes touching a group box (`fromId` or `toId` names a group box).
Strictly narrower than `R_GroupBoundaryR` (group-touching routes only). -/
def R_GroupEndpointBoundaryR (exactIds : List String) (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ∀ out ∈ res.scene.routes,
    (∃ gb ∈ inp.boxes, gb.role = .group ∧ (gb.id = out.fromId ∨ gb.id = out.toId)) →
    ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧ Validator.onBoundary finish toBox.rect

/-- Flat C5 for the region pipeline from the split: plain endpoints are
proved (`R_PlainBoundaryR`), group endpoints stay as the one residual. -/
theorem flatC5B_layoutRIds_final (exactIds : List String) (idSets : List (String × List String))
    (hP : R_PlainBoundaryR exactIds idSets)
    (hG : R_GroupEndpointBoundaryR exactIds idSets) : FlatC5B (layoutRIds exactIds idSets) := by
  apply flatC5B_layoutRIds_closed exactIds idSets
  intro inp o res execution hwf hfp out hout
  by_cases hGrp : ∃ gb ∈ inp.boxes, gb.role = .group ∧ (gb.id = out.fromId ∨ gb.id = out.toId)
  · exact hG execution hwf hfp out hout hGrp
  · exact hP execution hwf hfp out hout (fun gb hgb hrole => by
      refine ⟨fun hcon => hGrp ⟨gb, hgb, hrole, Or.inl hcon⟩, fun hcon => hGrp ⟨gb, hgb, hrole, Or.inr hcon⟩⟩)

/-- Peel helper (prefixed copy: `bind_ok` is private in every module). -/
private theorem rcbBind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β} (h : x.bind f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Membership inversion for the reserved-lane planner: mirror of
`RouteImpl.plannedLanes_mem` with `makeLaneR` in place of `makeLane`. -/
theorem rcbPlannedLanesR_mem {slot : Int} {p : Proper} {base : Routing} {x : List Int}
    {reversed : List Bool} {widths : List Int} {reserved : List (Option Int)}
    {run : RouteImpl.ReversedLane}
    (h : run ∈ plannedLanesR slot p base x reversed widths reserved) :
    ∃ o index, (o, index) ∈ (RouteImpl.laneOriginals p reversed).zipIdx ∧
      run = makeLaneR slot p base x reversed widths reserved
        (RouteImpl.laneOriginals p reversed) o index := by
  unfold plannedLanesR at h
  dsimp only at h
  simp only [List.mem_map] at h
  obtain ⟨q, hq, rfl⟩ := h
  exact ⟨q.1, q.2, hq, rfl⟩

/-- Every reserved-lane run is reversed: mirror of
`RouteImpl.plannedLane_reversed`. -/
theorem rcbPlannedLaneR_reversed {slot : Int} {p : Proper} {base : Routing} {x : List Int}
    {reversed : List Bool} {widths : List Int} {reserved : List (Option Int)}
    {run : RouteImpl.ReversedLane}
    (h : run ∈ plannedLanesR slot p base x reversed widths reserved) :
    reversed.getD run.original false = true := by
  obtain ⟨o, index, hq, rfl⟩ := rcbPlannedLanesR_mem h
  have hm : o ∈ RouteImpl.laneOriginals p reversed := by
    rw [← List.zipIdx_map_fst 0 (RouteImpl.laneOriginals p reversed)]
    exact List.mem_map.mpr ⟨(o, index), hq, rfl⟩
  simp only [RouteImpl.laneOriginals, List.mem_filter, Bool.and_eq_true] at hm
  exact hm.2.1

/-- Every reversed nonempty chain has a reserved lane: mirror of
`RouteImpl.plannedLane_exists`. -/
theorem rcbPlannedLaneR_exists {slot : Int} {p : Proper} {base : Routing} {x : List Int}
    {reversed : List Bool} {widths : List Int} {reserved : List (Option Int)} {o : Nat}
    (ho : o < p.chains.length) (hr : reversed.getD o false = true)
    (hne : (RouteImpl.edgesOf p o).isEmpty = false) :
    ∃ run ∈ plannedLanesR slot p base x reversed widths reserved, run.original = o := by
  have hm : o ∈ RouteImpl.laneOriginals p reversed := by
    simp only [RouteImpl.laneOriginals, List.mem_filter, List.mem_range, Bool.and_eq_true,
      Bool.not_eq_true']
    exact ⟨ho, hr, hne⟩
  rw [← List.zipIdx_map_fst 0 (RouteImpl.laneOriginals p reversed)] at hm
  obtain ⟨q, hq, hqo⟩ := List.mem_map.mp hm
  refine ⟨makeLaneR slot p base x reversed widths reserved
    (RouteImpl.laneOriginals p reversed) q.1 q.2, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨q, hq, rfl⟩
  · exact hqo

/-- Endpoint fields of a reserved lane: mirror of
`RouteImpl.plannedLane_endpoints`. Only the parked `lane` value differs from
`makeLane`; all endpoint fields are identical. -/
theorem rcbPlannedLaneR_endpoints {slot : Int} {p : Proper} {base : Routing} {x : List Int}
    {reversed : List Bool} {widths : List Int} {reserved : List (Option Int)}
    {run : RouteImpl.ReversedLane} {i₀ i₁ : Nat}
    (hm : run ∈ plannedLanesR slot p base x reversed widths reserved)
    (h0 : (RouteImpl.edgesOf p run.original).head? = some i₀)
    (h1 : (RouteImpl.edgesOf p run.original).getLast? = some i₁) :
    run.sourceX = base.targetX.getD i₁ 0 ∧
      run.targetX = base.sourceX.getD i₀ 0 ∧
      run.sourceNode = (RouteImpl.edgeAt p i₁).head ∧
      run.targetNode = (RouteImpl.edgeAt p i₀).tail ∧
      run.sourceGap = RouteImpl.gapOf p i₁ ∧ run.targetGap = RouteImpl.gapOf p i₀ ∧
      run.targetRun = base.sourceRun.getD i₀ 0 := by
  obtain ⟨o, index, _, rfl⟩ := rcbPlannedLanesR_mem hm
  have hh : (RouteImpl.edgesOf p o).headD 0 = i₀ := by
    cases he : RouteImpl.edgesOf p o with
    | nil => simp [he, makeLaneR] at h0
    | cons a as =>
      simp only [makeLaneR, he, List.head?_cons, Option.some.injEq] at h0
      simpa [List.headD, he] using h0
  have hl : ((RouteImpl.edgesOf p o).getLast?).getD 0 = i₁ := by
    have h1' : (RouteImpl.edgesOf p o).getLast? = some i₁ := by simpa only [makeLaneR] using h1
    rw [h1']
    rfl
  simp only [makeLaneR, hh, hl]
  trivial

/-- Lane-semantic endpoints for the reserved router: replay of
`RouteImpl.laneSemantic_endpoints` over `routeWithLanesR_spec`. The parked
`lane` value never reaches `pieceStart`/`pieceEnd` or the reversed
`sourceX`/`targetX`, so the same case split goes through. -/
theorem rcbLaneSemanticR_endpoints {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x y top : List Int} {reversed : List Bool} {widths : List Int}
    {reserved : List (Option Int)} {lr : RouteImpl.LaneRouting} {routes : List EdgeRoute}
    (hr : routeWithLanesR slot p layers x reversed widths reserved = .ok lr)
    (h : RouteImpl.routePointsWithLanes slot p layers x y top lr = .ok routes) :
    ∀ rt ∈ routes, ∀ i₀ i₁, (RouteImpl.edgesOf p rt.original).head? = some i₀ →
      (RouteImpl.edgesOf p rt.original).getLast? = some i₁ →
      if reversed.getD rt.original false then
        rt.points.head? = some ⟨lr.routing.targetX.getD i₁ 0,
          RouteImpl.yAt y (RouteImpl.edgeAt p i₁).head⟩ ∧
        rt.points.getLast? = some ⟨lr.routing.sourceX.getD i₀ 0,
          RouteImpl.yAt y (RouteImpl.edgeAt p i₀).tail +
            RouteImpl.nodeH p (RouteImpl.edgeAt p i₀).tail⟩
      else
        rt.points.head? = some (RouteImpl.pieceStart p y lr.routing i₀) ∧
        rt.points.getLast? = some (RouteImpl.pieceEnd p y lr.routing i₁) := by
  intro rt hrt i₀ i₁ h0 h1
  obtain ⟨ho, he⟩ := RouteImpl.routePointsWithLanes_mem h hrt
  obtain ⟨base, hb, _, hlr⟩ := routeWithLanesR_spec hr
  have hruns : lr.runs = plannedLanesR slot p base x reversed widths reserved := by
    rw [hlr]; rfl
  cases hf : lr.runs.find? (fun run => run.original == rt.original) with
  | none =>
    have hn : reversed.getD rt.original false = false := by
      apply Classical.byContradiction
      intro hn
      have ht : reversed.getD rt.original false = true := by
        cases he : reversed.getD rt.original false <;> simp_all
      have hne : (RouteImpl.edgesOf p rt.original).isEmpty = false := by
        cases he : RouteImpl.edgesOf p rt.original <;> simp_all
      obtain ⟨run, hm, hor⟩ := rcbPlannedLaneR_exists (base := base) (x := x)
        (widths := widths) (reserved := reserved) ho ht hne
      have hn := List.find?_eq_none.mp hf run (by rw [hruns]; exact hm)
      exact hn (by simp only [hor, beq_self_eq_true])
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    exact RouteImpl.laneRouteOf_forward_endpoints hf he h0 h1
  | some run =>
    have hm : run ∈ plannedLanesR slot p base x reversed widths reserved := by
      rw [← hruns]; exact List.mem_of_find?_eq_some hf
    have hor : run.original = rt.original := by
      simpa only [beq_iff_eq] using List.find?_some hf
    have hrev := rcbPlannedLaneR_reversed hm
    rw [hor] at hrev
    simp only [hrev, ↓reduceIte]
    have hmends := rcbPlannedLaneR_endpoints hm (by rw [hor]; exact h0) (by rw [hor]; exact h1)
    have hends := RouteImpl.laneRouteOf_reverse_endpoints hf he
    rcases hmends with ⟨hsx, htx, hsn, htn, _, _, _⟩
    rw [hsx, htx, hsn, htn] at hends
    have hs : lr.routing.sourceX = base.sourceX := by rw [hlr]; rfl
    have ht : lr.routing.targetX = base.targetX := by rw [hlr]; rfl
    simpa only [hs, ht] using hends

/-- Port-level endpoints for the reserved router: replay of
`route_endpoints_on_ports` over `routeWithLanesR_spec`. Port ranges and the
base routing spec are lane-independent. -/
theorem rcbRouteWithLanesR_endpoints {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x y top : List Int} {reversed : List Bool} {widths : List Int}
    {reserved : List (Option Int)} {lr : RouteImpl.LaneRouting} {routes : List EdgeRoute}
    (hr : routeWithLanesR slot p layers x reversed widths reserved = .ok lr)
    (h : RouteImpl.routePointsWithLanes slot p layers x y top lr = .ok routes) :
    ∀ rt ∈ routes, ∀ i₀ i₁, (RouteImpl.edgesOf p rt.original).head? = some i₀ →
      (RouteImpl.edgesOf p rt.original).getLast? = some i₁ →
      ∃ px qx,
        RouteImpl.sourcePort p x i₀ = .ok px ∧ RouteImpl.targetPort p x i₁ = .ok qx ∧
        (RouteImpl.boxRect p x y (RouteImpl.edgeAt p i₀).tail).x ≤ px ∧
        px ≤ (RouteImpl.boxRect p x y (RouteImpl.edgeAt p i₀).tail).x +
          (RouteImpl.boxRect p x y (RouteImpl.edgeAt p i₀).tail).w ∧
        (RouteImpl.boxRect p x y (RouteImpl.edgeAt p i₁).head).x ≤ qx ∧
        qx ≤ (RouteImpl.boxRect p x y (RouteImpl.edgeAt p i₁).head).x +
          (RouteImpl.boxRect p x y (RouteImpl.edgeAt p i₁).head).w ∧
        (if reversed.getD rt.original false then
          rt.points.head? = some ⟨qx, (RouteImpl.boxRect p x y
            (RouteImpl.edgeAt p i₁).head).y⟩ ∧
          rt.points.getLast? = some ⟨px, (RouteImpl.boxRect p x y
            (RouteImpl.edgeAt p i₀).tail).y +
            (RouteImpl.boxRect p x y (RouteImpl.edgeAt p i₀).tail).h⟩
        else
          rt.points.head? = some ⟨px, if RouteImpl.frameKind p
            (RouteImpl.edgeAt p i₀).tail = -2 then
            (RouteImpl.boxRect p x y (RouteImpl.edgeAt p i₀).tail).y else
            (RouteImpl.boxRect p x y (RouteImpl.edgeAt p i₀).tail).y +
            (RouteImpl.boxRect p x y (RouteImpl.edgeAt p i₀).tail).h⟩ ∧
          rt.points.getLast? = some ⟨qx, (RouteImpl.boxRect p x y
            (RouteImpl.edgeAt p i₁).head).y⟩) := by
  intro rt hrt i₀ i₁ h0 h1
  obtain ⟨base, hb, _, hlr⟩ := routeWithLanesR_spec hr
  have hports := rcbLaneSemanticR_endpoints hr h rt hrt i₀ i₁ h0 h1
  have hi0 := RouteImpl.mem_edgesOf (RouteImpl.mem_of_head' h0)
  have hi1 := RouteImpl.mem_edgesOf (List.mem_of_getLast? h1)
  have pr0 := RouteImpl.port_ranges hb hi0
  have pr1 := RouteImpl.port_ranges hb hi1
  have hp := (RouteImpl.route_spec hb).2.2.2.2.1
  refine ⟨base.sourceX.getD i₀ 0, base.targetX.getD i₁ 0,
    (hp i₀ hi0).1, (hp i₁ hi1).2, pr0.1, pr0.2.1, pr1.2.2.1, pr1.2.2.2, ?_⟩
  have hs : lr.routing.sourceX = base.sourceX := by rw [hlr]; rfl
  have ht : lr.routing.targetX = base.targetX := by rw [hlr]; rfl
  simpa only [hs, ht, RouteImpl.pieceStart, RouteImpl.pieceEnd,
    RouteImpl.boxRect] using hports


/-- Geometry facts for the reserved router: replay of
`RouteImpl.routeWithLanes_geometry` over `routeWithLanesR_spec`. -/
theorem rcbRouteWithLanesR_geometry {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x : List Int} {reversed : List Bool} {widths : List Int}
    {reserved : List (Option Int)} {lr : RouteImpl.LaneRouting}
    (h : routeWithLanesR slot p layers x reversed widths reserved = .ok lr) :
    RouteImpl.layersOk p layers = true ∧ x.length = p.nodes.length ∧
      lr.routing.sourceX.length = p.edges.length ∧
      lr.routing.targetX.length = p.edges.length ∧
      lr.routing.gaps.length = layers.length - 1 ∧
      (∀ i, i < p.edges.length →
        RouteImpl.sourcePort p x i = .ok (lr.routing.sourceX.getD i 0) ∧
        RouteImpl.targetPort p x i = .ok (lr.routing.targetX.getD i 0)) ∧
      ∀ g ∈ lr.routing.gaps, ∃ segs, g = RouteImpl.numberLaneGap segs := by
  obtain ⟨base, hb, _, rfl⟩ := routeWithLanesR_spec h
  obtain ⟨hl, hx, hs, ht, hp, hg, _⟩ := RouteImpl.route_spec hb
  refine ⟨hl, hx, hs, ht, ?_, hp, ?_⟩
  · simp only [RouteImpl.assembleLaneRouting, List.length_map, List.length_range]
    rw [hg]
    simp
  · intro g hm
    simp only [RouteImpl.assembleLaneRouting, List.mem_map, List.mem_range] at hm
    obtain ⟨k, _, rfl⟩ := hm
    exact ⟨_, rfl⟩


/-- `reservedPortsR` only rewrites node heights: chains are unchanged. -/
theorem rcbReservedPortsR_chains {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {x : List Int} {out : List Int × Proper}
    (h : reservedPortsR pl cg labels x = .ok out) : out.2.chains = pl.p.chains := by
  unfold reservedPortsR at h
  obtain ⟨fo, _, hcont⟩ := rcbBind_ok h
  dsimp only at hcont
  have he := Except.ok.inj hcont
  have hfin := congrArg (fun q : List Int × Proper => q.2.chains) he
  dsimp only at hfin
  exact hfin.symm

/-- `reservedPortsR` only rewrites node heights: edges are unchanged. -/
theorem rcbReservedPortsR_edges {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {x : List Int} {out : List Int × Proper}
    (h : reservedPortsR pl cg labels x = .ok out) : out.2.edges = pl.p.edges := by
  unfold reservedPortsR at h
  obtain ⟨fo, _, hcont⟩ := rcbBind_ok h
  dsimp only at hcont
  have he := Except.ok.inj hcont
  have hfin := congrArg (fun q : List Int × Proper => q.2.edges) he
  dsimp only at hfin
  exact hfin.symm




/-- `crossCoordsR` keeps edges: placement only rewrites coordinates. -/
theorem rcbCrossCoordsR_edges {P : Params} {rm : ComponentRegions} {cg : Graph}
    {labels : List MeasuredLabel} {p : Proper} {minimum : RegionConstraints}
    {layers : List (List Nat)}
    {out : List Int × List (List Nat) × List (Option Int) × Proper}
    (h : crossCoordsR P rm cg labels p minimum layers = .ok out) :
    out.2.snd.snd.edges = p.edges := by
  unfold crossCoordsR at h
  obtain ⟨children, _, h⟩ := rcbBind_ok h
  dsimp only at h
  split at h
  · have hF : False := by
      simp only [bind, Except.bind] at h
      exact absurd h (by simp)
    exact hF.elim
  · obtain ⟨ngs, _, h⟩ := rcbBind_ok h
    obtain ⟨x, _, h⟩ := rcbBind_ok h
    obtain ⟨_, _, h⟩ := rcbBind_ok h
    obtain ⟨⟨alloc, x2⟩, halloc, h⟩ := rcbBind_ok h
    obtain ⟨⟨x3, p3⟩, hres, h⟩ := rcbBind_ok h
    dsimp only at h
    have he := Except.ok.inj h
    have hedges : p3.edges = p.edges := rcbReservedPortsR_edges hres
    have hfin := congrArg
      (fun q : List Int × List (List Nat) × List (Option Int) × Proper =>
        q.2.snd.snd.edges) he
    dsimp only at hfin
    rw [← hfin]
    exact hedges

/-- `crossCoordsR` only rewrites coordinates: the returned proper graph keeps
the input chains (via `rcbReservedPortsR_chains`). -/
theorem rcbCrossCoordsR_chains {P : Params} {rm : ComponentRegions} {cg : Graph}
    {labels : List MeasuredLabel} {p : Proper} {minimum : RegionConstraints}
    {layers : List (List Nat)}
    {out : List Int × List (List Nat) × List (Option Int) × Proper}
    (h : crossCoordsR P rm cg labels p minimum layers = .ok out) :


    out.2.snd.snd.chains = p.chains := by
  unfold crossCoordsR at h
  obtain ⟨children, _, h⟩ := rcbBind_ok h
  dsimp only at h
  split at h
  · have hF : False := by
      simp only [bind, Except.bind] at h
      exact absurd h (by simp)
    exact hF.elim
  · obtain ⟨ngs, _, h⟩ := rcbBind_ok h
    obtain ⟨x, _, h⟩ := rcbBind_ok h
    obtain ⟨_, _, h⟩ := rcbBind_ok h
    obtain ⟨⟨alloc, x2⟩, halloc, h⟩ := rcbBind_ok h
    obtain ⟨⟨x3, p3⟩, hres, h⟩ := rcbBind_ok h
    dsimp only at h
    have he := Except.ok.inj h
    have hchains : p3.chains = p.chains := rcbReservedPortsR_chains hres
    have hfin := congrArg
      (fun q : List Int × List (List Nat) × List (Option Int) × Proper =>
        q.2.snd.snd.chains) he
    dsimp only at hfin
    rw [← hfin]
    exact hchains

/-- Coordinate steps keep chains: record updates for sizes, titles, extents
and materialization, plus `addClusterBorders_metadata` for borders. -/
theorem rcbCoordinateR_chains {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {labeled : Proper} :
    (coordinateGraphR P exact spec labeled).chains = labeled.chains := by
  cases spec with
  | none => rw [coordinateGraphR_none]; exact coordinateGraphX_chains P exact labeled
  | some s =>
    have h1 : (sizeProperPortsX P exact labeled).chains = labeled.chains := rfl
    have h2 : (titleReservationsR s.titles P.clusterPad
        (sizeProperPortsX P exact labeled)).chains =
        (sizeProperPortsX P exact labeled).chains := rfl
    have h3 := (OrderImpl.addClusterBorders_metadata
      (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled))
      P.clusterBorderW).2.1
    have h4 : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).chains =
        (OrderImpl.addClusterBorders (titleReservationsR s.titles P.clusterPad
          (sizeProperPortsX P exact labeled)) P.clusterBorderW).chains := rfl
    have h5 : (materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled))
        P.clusterBorderW))).chains =
        (clearProxyExtents (OrderImpl.addClusterBorders (titleReservationsR s.titles
          P.clusterPad (sizeProperPortsX P exact labeled)) P.clusterBorderW)).chains := rfl
    unfold coordinateGraphR
    rw [h5, h4, h3, h2, h1]

/-- Region-run chains cover every rewritten edge: replay of
`componentRunX_proper_chains_length` over `componentRunR_specR`. Placement
and coordinate steps keep chains by the helpers above. -/
theorem rcbProperChainsR : componentRunR_proper_chains_length_factR := by
  unfold componentRunR_proper_chains_length_factR
  intro P exact spec inp cg cg' run labels orderOptions h
  obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
    reserved, placedProper, q0, yt, ysMid, hs⟩ := componentRunR_specR h
  obtain ⟨hRs, hRank, hNorm, hLabels, hCoord, hMin, hOrd, hLabelWidths, hPlaced,
    hProxy, hDrop, hLanes, hYt, hYsMid, hReserve, hRoutes, hRouting, hCoordProper,
    hCoordYs, hBudget, hExact⟩ := hs
  have hdropC : run.proper.chains = q0.chains := by
    rw [← hDrop, OrderImpl.dropSynthetic_chains]
  have hproxC : q0.chains = placedProper.chains :=
    proxyWidths_chains hProxy
  have hplace : placedProper.chains = pCoord.chains := by
    rcases hPlaced with ⟨_, _, _, _, rfl⟩ | ⟨rm, m, _, _, hcross⟩
    · rfl
    · exact rcbCrossCoordsR_chains hcross
  have hco : pCoord.chains = labeled.chains := by
    rw [← hCoord]
    exact rcbCoordinateR_chains
  obtain ⟨_, _, hlblC, _⟩ := Labels.addLabelNodes_metadata hLabels
  have hnorm : p0.chains.length = cg'.edges.length :=
    normalize_chains_length hNorm
  rw [hdropC, hproxC, hplace, hco, hlblC]
  exact hnorm
/-- Region normalized source: replay of `X_componentRun_normalized_source`
over `componentRunR_specR`. Edge behavior through coordinates and placement
is shared; only the title/size wrappers differ by spec. -/
theorem rcbNormalizedSourceR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    ∃ ranks normalized,
      normalize cg' ranks = .ok normalized ∧
      run.proper.edges = normalized.edges ∧
      run.proper.chains = normalized.chains := by
  obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
    reserved, placedProper, q0, yt, ysMid, hs⟩ := componentRunR_specR hrun
  obtain ⟨hRs, hRank, hNorm, hLabels, hCoord, hMin, hOrd, hLabelWidths, hPlaced,
    hProxy, hDrop, hLanes, hYt, hYsMid, hReserve, hRoutes, hRouting, hCoordProper,
    hCoordYs, hBudget, hExact⟩ := hs
  obtain ⟨hlabelEdges, _, hlabelChains, _⟩ := Labels.addLabelNodes_metadata hLabels
  have hplacedEdges : placedProper.edges = pCoord.edges := by
    rcases hPlaced with ⟨_, _, _, _, rfl⟩ | ⟨rm, m, _, _, hcross⟩
    · rfl
    · exact rcbCrossCoordsR_edges hcross
  have hplacedChains : placedProper.chains = pCoord.chains := by
    rcases hPlaced with ⟨_, _, _, _, rfl⟩ | ⟨rm, m, _, _, hcross⟩
    · rfl
    · exact rcbCrossCoordsR_chains hcross
  have hprojectedEdges := (proxyWidths_rel hProxy).1
  have hcoordChains : pCoord.chains = labeled.chains := by
    rw [← hCoord]
    exact rcbCoordinateR_chains
  have hdropChains : run.proper.chains = p0.chains := by
    rw [← hDrop, OrderImpl.dropSynthetic_chains, proxyWidths_chains hProxy,
      hplacedChains, hcoordChains, hlabelChains]
  cases spec with
  | none =>
    have hclean : ∀ e ∈ (titleReservations
        (sizeProperPortsX P exact labeled)).edges, e.synthetic = false := by
      intro e he
      have hedge : (titleReservations
          (sizeProperPortsX P exact labeled)).edges = p0.edges := hlabelEdges
      rw [hedge] at he
      exact normalize_clean hNorm e he
    have hdropEdges : (OrderImpl.dropSynthetic q0).edges =
        (OrderImpl.dropSynthetic
          (OrderImpl.addClusterBorders (titleReservations
            (sizeProperPortsX P exact labeled)) P.clusterBorderW)).edges := by
      show q0.edges.filter (fun e => !e.synthetic) = _
      rw [hprojectedEdges, hplacedEdges, ← hCoord]
      rfl
    refine ⟨ranks, p0, hNorm, ?_, hdropChains⟩
    rw [← hDrop, hdropEdges,
      OrderImpl.dropSynthetic_addClusterBorders_edges _ _ hclean]
    exact hlabelEdges
  | some s =>
    have hclean : ∀ e ∈ (titleReservationsR s.titles P.clusterPad
        (sizeProperPortsX P exact labeled)).edges, e.synthetic = false := by
      intro e he
      have hedge : (titleReservationsR s.titles P.clusterPad
          (sizeProperPortsX P exact labeled)).edges = p0.edges := hlabelEdges
      rw [hedge] at he
      exact normalize_clean hNorm e he
    have hdropEdges : (OrderImpl.dropSynthetic q0).edges =
        (OrderImpl.dropSynthetic
          (OrderImpl.addClusterBorders (titleReservationsR s.titles P.clusterPad
            (sizeProperPortsX P exact labeled)) P.clusterBorderW)).edges := by
      show q0.edges.filter (fun e => !e.synthetic) = _
      rw [hprojectedEdges, hplacedEdges, ← hCoord]
      rfl
    refine ⟨ranks, p0, hNorm, ?_, hdropChains⟩
    rw [← hDrop, hdropEdges,
      OrderImpl.dropSynthetic_addClusterBorders_edges _ _ hclean]
    exact hlabelEdges

/-- Region-run edge points read the resolved route: replay of
`componentRunX_edgePoints_of_index` over `componentRunR_route_of_indexR`
and `rcbProperChainsR`. -/
theorem rcbEdgePointsR {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {e : Edge}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {i : Nat} (hi : i < cg'.edges.length) :
    edgePoints run i e = (run.routes[i]'(
      by rw [componentRunR_routes_lengthR h, rcbProperChainsR h]; exact hi)).points := by
  have hic : i < run.proper.chains.length := by
    rw [rcbProperChainsR h]
    exact hi
  obtain ⟨rt, hget, _, _⟩ := componentRunR_route_of_indexR h hic
  have hir : i < run.routes.length := (List.getElem?_eq_some_iff.mp hget).1
  have hrt : run.routes[i]'hir = rt := (List.getElem?_eq_some_iff.mp hget).2
  simp only [edgePoints, List.getD_eq_getElem?_getD, hget, Option.getD_some, hrt]

/-- Region part route-entry projection: replay of
`X_placeComponentExact_route_entry_of_producer` over `componentRunR`. The
routes construction is identical; only the run equation changes. -/
theorem rcbPlaceEntryR {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    (cursor : Int) (loops : List (Nat × LoopPlacement)) (i : Nat)
    (hi : i < cg'.edges.length)
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg'.edges[i]).decl) :
    (placeComponentExact P cg' run cursor labels loops).routes[i]? =
      some ((cg'.edges[i]).decl,
        (run.routes[i]'(by
          rw [componentRunR_routes_lengthR hrun, rcbProperChainsR hrun]
          exact hi)).points.map
          (shiftPoint (cursor - (placeBoundsX P cg' run labels loops).minX)
            (-(placeBoundsX P cg' run labels loops).minY))) := by
  have hfind := loops_find?_none_of_ne hloop
  unfold placeComponentExact placeBoundsX
  dsimp only
  simp only [List.getElem?_map, zipIdx_getElem?, List.getElem?_eq_getElem hi,
    Option.map_some, hfind, Option.map_none, Option.getD_none, Nat.zero_add,
    rcbEdgePointsR hrun hi]

/-- Run-level ordinary route attachment over region runs: replay of
`componentRun_ordinary_route_attachment` over `componentRunR_specR`. The
empty-reserved case reuses `route_endpoints_on_ports`; the nonempty case uses
`rcbRouteWithLanesR_endpoints`. Endpoint lookup goes through the returned
graph `cg'` by `decl`; anchors are computed after `crossCoordsR` and
`reservedPortsR`, so only `run.proper`/`run.xs`/`run.ys` are observed. -/
theorem rcbOrdinaryAttachmentR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {i : Nat} (hi : i < cg'.edges.length) {first last : Nat}
    (hfirst : (RouteImpl.edgesOf run.proper i).head? = some first)
    (hlast : (RouteImpl.edgesOf run.proper i).getLast? = some last)
    (hsource : (cg'.nodes.getD (RouteImpl.edgeAt run.proper first).tail default).border ≠ -2)
    (htarget : (cg'.nodes.getD (RouteImpl.edgeAt run.proper last).head default).border ≠ -2)
    (cursor : Int) (loops : List (Nat × LoopPlacement))
    (hloop : ∀ l ∈ loops, l.1 ≠ (cg'.edges[i]).decl)
    (margin : Int) (direction : Direction) (canvasH boxX boxY : Int) :
    ∃ rt : EdgeRoute, ∃ start finish : Point,
      run.routes[i]? = some rt ∧ rt.original = i ∧
      (placeComponentExact P cg' run cursor labels loops).routes[i]? =
        some ((cg'.edges[i]).decl, rt.points.map
          (shiftPoint (cursor - (placeBoundsX P cg' run labels loops).minX)
            (-(placeBoundsX P cg' run labels loops).minY))) ∧
      rt.points.head? = some start ∧ rt.points.getLast? = some finish ∧
      let source := frameRect P cg' run (RouteImpl.edgeAt run.proper first).tail
      let target := frameRect P cg' run (RouteImpl.edgeAt run.proper last).head
      let reversed := (cg'.edges.map (·.reversed)).getD i false
      let bounds := placeBoundsX P cg' run labels loops
      let transport := routePointTransport margin direction canvasH boxX boxY
        bounds.minX bounds.minY
      let transportRect := fun rect => shiftRect margin margin
        (orientRect direction canvasH
          (shiftRect (boxX - bounds.minX) (boxY - bounds.minY) rect))
      Validator.onBoundary (transport start) (transportRect (if reversed then target else source)) ∧
      Validator.onBoundary (transport finish) (transportRect (if reversed then source else target)) := by
  have hic : i < run.proper.chains.length := by
    rw [rcbProperChainsR hrun]
    exact hi
  obtain ⟨rt, hrt, horiginal, _⟩ := componentRunR_route_of_indexR hrun hic
  obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
    reserved, placedProper, q0, yt, ysMid, hs⟩ := componentRunR_specR hrun
  obtain ⟨hRs, hRank, hNorm, hLabels, hCoord, hMin, hOrd, hLabelWidths, hPlaced,
    hProxy, hDrop, hLanes, hYt, hYsMid, hReserve, hRoutes, hRouting, hCoordProper,
    hCoordYs, hBudget, hExact⟩ := hs
  have hm : rt ∈ run.routes := List.mem_iff_getElem?.mpr ⟨i, hrt⟩
  have hfirst' : (RouteImpl.edgesOf run.proper rt.original).head? = some first := by
    simpa only [horiginal] using hfirst
  have hlast' : (RouteImpl.edgesOf run.proper rt.original).getLast? = some last := by
    simpa only [horiginal] using hlast
  have hEnds : ∃ px qx : Int,
      RouteImpl.sourcePort run.proper run.xs first = .ok px ∧
      RouteImpl.targetPort run.proper run.xs last = .ok qx ∧
      (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper first).tail).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper first).tail).x +
        (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper first).tail).w ∧
      (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper last).head).x ≤ qx ∧
      qx ≤ (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper last).head).x +
        (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper last).head).w ∧
      (if (cg'.edges.map (·.reversed)).getD i false then
        rt.points.head? = some ⟨qx, (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper last).head).y⟩ ∧
        rt.points.getLast? = some ⟨px, (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).y +
          (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).h⟩
      else
        rt.points.head? = some ⟨px, if RouteImpl.frameKind run.proper
          (RouteImpl.edgeAt run.proper first).tail = -2 then
          (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).y else
          (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).y +
          (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).h⟩ ∧
        rt.points.getLast? = some ⟨qx, (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper last).head).y⟩) := by
    cases hLanes with
    | inl hA =>
      obtain ⟨_, hrouting⟩ := hA
      have h := Elegant.Layered.route_endpoints_on_ports hrouting hRoutes rt hm
        first last hfirst' hlast'
      rwa [horiginal] at h
    | inr hB =>
      obtain ⟨_, hroutingR⟩ := hB
      have h := rcbRouteWithLanesR_endpoints hroutingR hRoutes rt hm
        first last hfirst' hlast'
      rwa [horiginal] at h
  obtain ⟨px, qx, _, _, hpx0, hpx1, hqx0, hqx1, hend⟩ := hEnds
  have hgeomOk : RouteImpl.layersOk run.proper run.layers = true := by
    cases hLanes with
    | inl hA => exact (RouteImpl.routeWithLanes_geometry hA.2).1
    | inr hB => exact (rcbRouteWithLanesR_geometry hB.2).1
  obtain ⟨_, hdims, _, _, hedge⟩ := RouteImpl.layersOk_spec hgeomOk
  have hf := hedge first (RouteImpl.mem_edgesOf (RouteImpl.mem_of_head' hfirst))
  have hl := hedge last (RouteImpl.mem_edgesOf (List.mem_of_getLast? hlast))
  have hsh := (hdims _ hf.1).2
  have hth := (hdims _ hl.2.1).2
  have hsboundary : Validator.onBoundary
      ⟨px, (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper first).tail).y +
        (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper first).tail).h⟩
      (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper first).tail) := by
    simp only [Validator.onBoundary, RouteImpl.boxRect]
    exact ⟨hpx0, hpx1, by omega, by omega, Or.inr (Or.inr (Or.inr True.intro))⟩
  have hsboundary_ite : Validator.onBoundary
      ⟨px, if RouteImpl.frameKind run.proper (RouteImpl.edgeAt run.proper first).tail = -2 then
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).y else
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).y +
        (RouteImpl.boxRect run.proper run.xs run.ys
          (RouteImpl.edgeAt run.proper first).tail).h⟩
      (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper first).tail) := by
    by_cases hfk : RouteImpl.frameKind run.proper
        (RouteImpl.edgeAt run.proper first).tail = -2
    · simp only [Validator.onBoundary, RouteImpl.boxRect, hfk, ↓reduceIte]
      exact ⟨hpx0, hpx1, by omega, by omega, Or.inr (Or.inr (Or.inl True.intro))⟩
    · simp only [Validator.onBoundary, RouteImpl.boxRect, hfk, ↓reduceIte]
      exact ⟨hpx0, hpx1, by omega, by omega, Or.inr (Or.inr (Or.inr True.intro))⟩
  have htboundary : Validator.onBoundary
      ⟨qx, (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper last).head).y⟩
      (RouteImpl.boxRect run.proper run.xs run.ys
        (RouteImpl.edgeAt run.proper last).head) := by
    simp only [Validator.onBoundary, RouteImpl.boxRect]
    exact ⟨hqx0, hqx1, by omega, by omega, Or.inr (Or.inr (Or.inl True.intro))⟩
  have hplaced := rcbPlaceEntryR hrun cursor loops i hi hloop
  have hget : run.routes[i]'(
      by rw [componentRunR_routes_lengthR hrun, rcbProperChainsR hrun]; exact hi) = rt :=
    (List.getElem?_eq_some_iff.mp hrt).2
  rw [hget] at hplaced
  rw [plain_frame_eq_boxRect P cg' run _ hf.1 hsource,
    plain_frame_eq_boxRect P cg' run _ hl.2.1 htarget]
  split at hend
  · rename_i hrev
    obtain ⟨hhead, htail⟩ := hend
    refine ⟨rt, _, _, hrt, horiginal, hplaced, hhead, htail, ?_⟩
    dsimp only
    simp only [hrev, ↓reduceIte]
    constructor
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr htboundary
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr hsboundary
  · rename_i hrev
    obtain ⟨hhead, htail⟩ := hend
    refine ⟨rt, _, _, hrt, horiginal, hplaced, hhead, htail, ?_⟩
    dsimp only
    simp only [hrev]
    constructor
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr hsboundary_ite
    · apply (onBoundary_shift _ _ _ _).mpr
      apply (onBoundary_orient _ _ _ _).mpr
      exact (onBoundary_shift _ _ _ _).mpr htboundary







end PipelineImpl
end Layered
end Elegant

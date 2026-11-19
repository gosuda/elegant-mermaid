import Elegant.Layered.RegionActualParts
import Elegant.Layered.RecursiveBLiftsA

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-!
# Region flat C4: every scene route of `layoutRIds` is orthogonal.

Packet P2 of `local://region-tower-plan.md` (field 4, `flatC4`).

Mirror of the exact twin in `ExactFlatFacts.lean:444-725`:
`componentRunX_routes_orthogonal` (`:444-458`) via `componentRunX_spec` +
`Layered.route_orthogonal`, then `placeComponentExact_routes_orthogonal`
(`:462-481`), `placePartX_routes_orthogonal` (`:504-520`),
`layoutComponentX_routes_orthogonal` (`:626-648`),
`componentsX_routes_orthogonal` (`:650-670`), `packAccX_routes_orthogonal`
(`:672-703`), `SceneExecutionX.routes_orthogonal` (`:705-724`), and the
`flatC4` term of `exactBaseSeams` (`Kinds/UsecaseValidExact.lean:210-212`).

Region replay: `componentRunR_routes_eqR` (`RegionActualParts.lean`) gives the
`routePointsWithLanes` equation. The lane equation has two leaves: an empty
`reserved` list reuses `RouteImpl.routeWithLanes` (so `Layered.route_orthogonal`
applies directly), while a nonempty one uses `routeWithLanesR`
(`RegionPlacement.lean:435-444`), which differs from `routeWithLanes` only in
the parked `lane` value (`makeLaneR` vs `makeLane`: all gap/segment/endpoint
fields are identical). Orthogonality is lane-value independent:
`laneSemanticR_orthogonal` below replays `RouteImpl.laneSemantic_orthogonal`
(`Route.lean:3330-3371`) over the `routeWithLanesR_spec` extraction.

Truth probes (`proofs/wip/Probe/RegionFlatC4Probe.lean`, `lake env lean`):
- two-region witness (copy of `rapProbeInp`/`rapProbeSets`): run succeeds with
  `(routes, orth, reversedLanes, nodes, chains, layers, xs)`
  `= (3, [true, true, true], 0, 90, 3, 8, 90)`.
- nested-region witness (`G` over `{A,B}`, `A` over `{A1,A2}`, edges
  `a1->b1, a2->b1, b1->a1` with `b1->a1` reversed): run succeeds with
  `(3, [true, true, true], 1, 64, 3, 7, 64)` — one reversed lane, still all
  orthogonal. This exercises the `routeWithLanesR` leaf.
- stage evidence for the residual: on both witnesses the reserved path is
  taken and `crossCoordsR` succeeds with dummy flags and edge declarations
  preserved, `(reservedTaken, ok, dummyEq, declEq) = (true, true, true, true)`.

Residual: the single open fact is `rfc4CrossCoordsR_metadata_factR`, the
node-dummy preservation of a successful `crossCoordsR` run. Everything else
is proved: the `none`-spec shape (`componentRunR_properShape_noneR` via
`componentRunR_none` + `componentRunX_properShape`), the lanes equation
(`componentRunR_lanes_eqR`, four-leaf repeel), placed edge points without a
chains bridge (`rfc4EdgePoints_orthogonalR`), the coordinate stage
(`rfc4CoordinateR_shape`: `normalize` + `addLabelNodes` + `sizeProperPortsX`
+ `titleReservationsR` + `addClusterBorders` shape transfer), the
`proxyWidths`/`dropSynthetic` transport (`rfc4ShapePack`), and the
`crossCoordsR` edge preservation (`rfc4CrossCoordsR_edges`, nodes-only
rewrite). The `some`-spec shape (`componentRunR_properShape_someR`) is proved
conditional on the residual; orthogonality and the `flatC4B` discharge follow.
The residual is strictly narrower than the target (one stage equation over
successful runs only), a single public fact, and true on both probes above.
-/

/-- Peel helper for the region C4 replay (prefixed copy: `bind_ok` is private
in every module that uses it). -/
private theorem rfc4bind_ok {α β : Type}
    {x : Except LayoutError α} {f : α → Except LayoutError β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Extraction for the reserved-lane router: mirror of `routeWithLanes_spec`
(`Route.lean:2812-2828`) with `plannedLanesR` in place of `plannedLanes`. -/
theorem routeWithLanesR_spec {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x : List Int} {reversed : List Bool} {widths : List Int}
    {reserved : List (Option Int)} {lr : RouteImpl.LaneRouting}
    (h : routeWithLanesR slot p layers x reversed widths reserved = .ok lr) :
    ∃ base, RouteImpl.route p layers x = .ok base ∧ 1 ≤ slot ∧
      lr = RouteImpl.assembleLaneRouting p base reversed
        (plannedLanesR slot p base x reversed widths reserved) := by
  unfold routeWithLanesR at h
  split at h
  · simp at h
  · next hs =>
    split at h
    · simp at h
    · next base hb =>
      dsimp only at h
      split at h
      · simp only [Except.ok.injEq] at h
        exact ⟨base, hb, by omega, h.symm⟩
      · simp at h


/-- Lane-value-independent orthogonality for the reserved-lane router: replay of
 `RouteImpl.laneSemantic_orthogonal` (`Route.lean:3330-3371`) over the
 `routeWithLanesR_spec` extraction. `makeLaneR` changes only the parked `lane`
 value, so the same case split (reversed seven-point path vs forward chain
 junctions over the shared base routing) goes through unchanged. -/
theorem laneSemanticR_orthogonal {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x y top : List Int} {reversed : List Bool} {widths : List Int}
    {reserved : List (Option Int)} {lr : RouteImpl.LaneRouting}
    {routes : List EdgeRoute} (hP : RouteImpl.ProperShape p)
    (hr : routeWithLanesR slot p layers x reversed widths reserved = .ok lr)
    (h : RouteImpl.routePointsWithLanes slot p layers x y top lr = .ok routes) :
    ∀ rt ∈ routes, Polyline.isOrthogonal rt.points = true := by
  intro rt hrt
  obtain ⟨_, he⟩ := RouteImpl.routePointsWithLanes_mem h hrt
  obtain ⟨base, hb, _, hlr⟩ := routeWithLanesR_spec hr
  cases hf : lr.runs.find? (fun run => run.original == rt.original) with
  | some run =>
    simp only [RouteImpl.laneRouteOf, hf] at he
    split at he
    · simp only [Except.ok.injEq] at he
      have hpts := congrArg EdgeRoute.points he
      rw [← hpts]
      dsimp only
      rw [RouteImpl.isOrthogonal_iff]
      apply RouteImpl.pairsAll_dedup
      rw [← RouteImpl.isOrthogonal_iff]
      exact RouteImpl.reversedPoints_orthogonal _ _ _ _ _ _ _
    · simp at he
  | none =>
    simp only [RouteImpl.laneRouteOf, hf] at he
    unfold RouteImpl.routeOf at he
    split at he
    · simp at he
    · next pcs hpcs =>
      simp only [Except.ok.injEq] at he
      have hpts := congrArg EdgeRoute.points he
      rw [← hpts]
      rw [RouteImpl.isOrthogonal_iff]
      apply RouteImpl.pairsAll_dedup
      refine RouteImpl.pairsAll_flatten_of _ (RouteImpl.pieceStart p y lr.routing)
        (RouteImpl.pieceEnd p y lr.routing) (RouteImpl.ChainLink p) ?_
        (RouteImpl.edgesOf p rt.original) pcs ?_ (hP rt.original)
      · intro i j hij
        have hc := RouteImpl.chain_junction_orthogonal (y := y) hb hij
        have hs : lr.routing.sourceX = base.sourceX := by rw [hlr]; rfl
        have ht : lr.routing.targetX = base.targetX := by rw [hlr]; rfl
        simpa only [RouteImpl.pieceStart, RouteImpl.pieceEnd, hs, ht] using hc
      · exact RouteImpl.Zipped.imp _ _ (fun i _ pc hpc => RouteImpl.pieceOf_basic hpc)
          (RouteImpl.mapOk_zipped _ _ _ hpcs)

/-- The region run lanes come from one of the two routers: an empty `reserved`
list reuses `RouteImpl.routeWithLanes`, otherwise `routeWithLanesR`. Proved by
re-peeling the four leaves of `componentRunR` exactly as
`componentRunR_routes_eqR` does (`RegionActualParts.lean:1073-1193`). -/
theorem componentRunR_lanes_eqR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    (∃ reversed widths, RouteImpl.routeWithLanes P.slot run.proper run.layers
      run.xs reversed widths = .ok run.lanes) ∨
    (∃ reversed widths reserved, routeWithLanesR P.slot run.proper run.layers
      run.xs reversed widths reserved = .ok run.lanes) := by
  unfold componentRunR at h
  obtain ⟨rs, _, h⟩ := rfc4bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨rr, _, h⟩ := rfc4bind_ok h
    obtain ⟨ranked, _, h⟩ := rfc4bind_ok h
    cases ranked with
    | mk ranks rest =>
      cases rest with
      | mk cg1 rankBudget =>
        dsimp only at h
        obtain ⟨p0, _, h⟩ := rfc4bind_ok h
        obtain ⟨p, _, h⟩ := rfc4bind_ok h
        obtain ⟨_, _, h⟩ := rfc4bind_ok h
        obtain ⟨ord, _, h⟩ := rfc4bind_ok h
        obtain ⟨xs, _, h⟩ := rfc4bind_ok h
        obtain ⟨placed, _, h⟩ := rfc4bind_ok h
        obtain ⟨routed, _, h⟩ := rfc4bind_ok h
        split at h
        · obtain ⟨lanes_1, hlanes, h⟩ := rfc4bind_ok h
          obtain ⟨yt, _, h⟩ := rfc4bind_ok h
          obtain ⟨resv, _, h⟩ := rfc4bind_ok h
          obtain ⟨routes, _, h⟩ := rfc4bind_ok h
          have he := Except.ok.inj h
          have hP : run.proper = OrderImpl.dropSynthetic routed.fst :=
            (congrArg (fun q : Graph × Run => q.2.proper) he).symm
          have hL : run.layers = placed.2.fst :=
            (congrArg (fun q : Graph × Run => q.2.layers) he).symm
          have hX : run.xs = routed.snd :=
            (congrArg (fun q : Graph × Run => q.2.xs) he).symm
          have hN : run.lanes = lanes_1 :=
            (congrArg (fun q : Graph × Run => q.2.lanes) he).symm
          rw [hP, hL, hX, hN]
          exact Or.inl ⟨_, _, hlanes⟩
        · obtain ⟨lanes_1, hlanes, h⟩ := rfc4bind_ok h
          obtain ⟨yt, _, h⟩ := rfc4bind_ok h
          obtain ⟨resv, _, h⟩ := rfc4bind_ok h
          obtain ⟨routes, _, h⟩ := rfc4bind_ok h
          have he := Except.ok.inj h
          have hP : run.proper = OrderImpl.dropSynthetic routed.fst :=
            (congrArg (fun q : Graph × Run => q.2.proper) he).symm
          have hL : run.layers = placed.2.fst :=
            (congrArg (fun q : Graph × Run => q.2.layers) he).symm
          have hX : run.xs = routed.snd :=
            (congrArg (fun q : Graph × Run => q.2.xs) he).symm
          have hN : run.lanes = lanes_1 :=
            (congrArg (fun q : Graph × Run => q.2.lanes) he).symm
          rw [hP, hL, hX, hN]
          exact Or.inr ⟨_, _, _, hlanes⟩
  · obtain ⟨ranked, _, h⟩ := rfc4bind_ok h
    cases ranked with
    | mk ranks rest =>
      cases rest with
      | mk cg1 rankBudget =>
        dsimp only at h
        obtain ⟨p0, _, h⟩ := rfc4bind_ok h
        obtain ⟨p, _, h⟩ := rfc4bind_ok h
        obtain ⟨_, _, h⟩ := rfc4bind_ok h
        obtain ⟨_, _, h⟩ := rfc4bind_ok h
        obtain ⟨ord, _, h⟩ := rfc4bind_ok h
        split at h
        · simp only [bind, Except.bind] at h
          exact absurd h (by simp)
        · obtain ⟨_, _, h⟩ := rfc4bind_ok h
          obtain ⟨placed, _, h⟩ := rfc4bind_ok h
          obtain ⟨routed, _, h⟩ := rfc4bind_ok h
          split at h
          · obtain ⟨lanes_1, hlanes, h⟩ := rfc4bind_ok h
            obtain ⟨yt, _, h⟩ := rfc4bind_ok h
            obtain ⟨resv, _, h⟩ := rfc4bind_ok h
            obtain ⟨routes, _, h⟩ := rfc4bind_ok h
            have he := Except.ok.inj h
            have hP : run.proper = OrderImpl.dropSynthetic routed.fst :=
              (congrArg (fun q : Graph × Run => q.2.proper) he).symm
            have hL : run.layers = placed.2.fst :=
              (congrArg (fun q : Graph × Run => q.2.layers) he).symm
            have hX : run.xs = routed.snd :=
              (congrArg (fun q : Graph × Run => q.2.xs) he).symm
            have hN : run.lanes = lanes_1 :=
              (congrArg (fun q : Graph × Run => q.2.lanes) he).symm
            rw [hP, hL, hX, hN]
            exact Or.inl ⟨_, _, hlanes⟩
          · obtain ⟨lanes_1, hlanes, h⟩ := rfc4bind_ok h
            obtain ⟨yt, _, h⟩ := rfc4bind_ok h
            obtain ⟨resv, _, h⟩ := rfc4bind_ok h
            obtain ⟨routes, _, h⟩ := rfc4bind_ok h
            have he := Except.ok.inj h
            have hP : run.proper = OrderImpl.dropSynthetic routed.fst :=
              (congrArg (fun q : Graph × Run => q.2.proper) he).symm
            have hL : run.layers = placed.2.fst :=
              (congrArg (fun q : Graph × Run => q.2.layers) he).symm
            have hX : run.xs = routed.snd :=
              (congrArg (fun q : Graph × Run => q.2.xs) he).symm
            have hN : run.lanes = lanes_1 :=
              (congrArg (fun q : Graph × Run => q.2.lanes) he).symm
            rw [hP, hL, hX, hN]
            exact Or.inr ⟨_, _, _, hlanes⟩

/-- Runs executed with no region spec keep a well-shaped proper graph: they
coincide with the exact run (`componentRunR_none`), whose shape is proved
(`componentRunX_properShape`). -/
theorem componentRunR_properShape_noneR {P : Params} {exact : List Nat}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunR P exact none inp cg labels orderOptions = .ok (cg', run)) :
    RouteImpl.ProperShape run.proper := by
  have hmap : (componentRunX P exact cg labels orderOptions).map
      (fun r => (cg, r)) = .ok (cg', run) := by
    rw [← componentRunR_none]
    exact h
  cases hX : componentRunX P exact cg labels orderOptions with
  | error e =>
    rw [hX] at hmap
    simp only [Except.map] at hmap
    cases hmap
  | ok run' =>
    have hok : (Except.ok (cg, run') : Except LayoutError (Graph × Run)) =
        Except.ok (cg', run) := by
      have h2 := hmap
      rw [hX] at h2
      simpa only [Except.map] using h2
    have hpair : (cg, run') = (cg', run) := Except.ok.inj hok
    have hrun : run' = run := by simpa using congrArg Prod.snd hpair
    rw [← hrun]
    exact componentRunX_properShape hX

private def rfc4TitleRF (node : ProperNode) : ProperNode :=
  if node.node.border == -2 || node.node.border == 2 then
    { node with node := { node.node with w := 0, h := 0 } } else node

private theorem rfc4TitleRF_dummy (n : ProperNode) :
    (rfc4TitleRF n).dummy = n.dummy := by
  unfold rfc4TitleRF
  split <;> rfl

private theorem rfc4TitleReservationsR_nodes (titles : List (Int × Int)) (pad : Int)
    (p : Proper) :
    (titleReservationsR titles pad p).nodes = p.nodes.map rfc4TitleRF ++
      (p.nodes.zipIdx.filter fun q => q.1.node.border == -2).map fun q => { q.1 with node := { q.1.node with border := 3, loopExtent := 0, h := (titles.getD q.1.node.decl (0, 0)).2 + pad } } := rfl

private theorem rfc4TitleReservationsR_edges (titles : List (Int × Int)) (pad : Int)
    (p : Proper) : (titleReservationsR titles pad p).edges = p.edges := rfl

private theorem rfc4CoordinateR_shape {P : Params} {exact : List Nat} (s : RegionSpec)
    {labels : List MeasuredLabel} {cg : Graph} {ranks : List Int} {p0 labeled : Proper}
    (hn : normalize cg ranks = .ok p0)
    (hlabels : Labels.addLabelNodes cg p0 (componentLabels cg labels) = .ok labeled) :
    ProperShape (OrderImpl.dropSynthetic (OrderImpl.addClusterBorders
      (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled))
      P.clusterBorderW)) ∧
    (∀ e ∈ (titleReservationsR s.titles P.clusterPad
      (sizeProperPortsX P exact labeled)).edges, e.synthetic = false) ∧
    (titleReservationsR s.titles P.clusterPad
      (sizeProperPortsX P exact labeled)).edges = p0.edges := by
  obtain ⟨he, _, _, hdummy⟩ := Labels.addLabelNodes_metadata hlabels
  have hlabeled : RouteImpl.ProperShape labeled :=
    RouteImpl.properShape_of_metadata he hdummy (normalize_shape hn)
  have hsized : Metadata.NodeMetadata labeled (sizeProperPortsX P exact labeled) := by
    apply Metadata.nodeMetadata_of_lookup_maps
    intro v
    have hk := congrArg (Option.map (fun t : Bool × Int × List Nat => t.1))
      (sizeProperPortsX_key P exact labeled v)
    simpa [Option.map_map, Function.comp_def] using hk
  have hs1 : RouteImpl.ProperShape (sizeProperPortsX P exact labeled) :=
    Metadata.properShape_transfer (p := labeled) (q := sizeProperPortsX P exact labeled)
      rfl hsized hlabeled
  have hT : RouteImpl.ProperShape (titleReservationsR s.titles P.clusterPad
      (sizeProperPortsX P exact labeled)) :=
    Metadata.properShape_transfer (p := sizeProperPortsX P exact labeled) rfl
      (Metadata.nodeMetadata_map_append rfc4TitleRF rfc4TitleRF_dummy _
        (rfc4TitleReservationsR_nodes s.titles P.clusterPad _)) hs1
  have hedge : (titleReservationsR s.titles P.clusterPad
      (sizeProperPortsX P exact labeled)).edges = p0.edges := by
    have hse : (sizeProperPortsX P exact labeled).edges = labeled.edges := rfl
    rw [rfc4TitleReservationsR_edges, hse]
    exact he
  have hclean : ∀ e ∈ (titleReservationsR s.titles P.clusterPad
      (sizeProperPortsX P exact labeled)).edges, e.synthetic = false := by
    intro e he'
    rw [hedge] at he'
    exact normalize_clean hn e he'
  have hext := OrderImpl.addClusterBorders_metadata
    (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled))
    P.clusterBorderW
  have hAdd := Metadata.properShape_borderExtension hext hclean hT
  exact ⟨hAdd, hclean, hedge⟩

private theorem rfc4DropSynthetic_metadata {a b : Proper}
    (h : Metadata.NodeMetadata a b) :
    Metadata.NodeMetadata (OrderImpl.dropSynthetic a) (OrderImpl.dropSynthetic b) := by
  intro v nd hv
  have hv' : a.nodes[v]? = some nd := hv
  obtain ⟨nd', hn', hd'⟩ := h v nd hv'
  exact ⟨nd', hn', hd'⟩

private theorem rfc4ReservedPortsR_edges {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {x : List Int} {out : List Int × Proper}
    (h : reservedPortsR pl cg labels x = .ok out) : out.2.edges = pl.p.edges := by
  unfold reservedPortsR at h
  obtain ⟨fo, _, h⟩ := rfc4bind_ok h
  have he := Except.ok.inj h
  have hc := congrArg (fun q : List Int × Proper => q.2.edges) he
  exact hc.symm

private theorem rfc4CrossCoordsR_edges {P : Params} {rm : ComponentRegions} {cg : Graph}
    {labels : List MeasuredLabel} {p : Proper} {minimum : RegionConstraints}
    {layers : List (List Nat)} {out : List Int × List (List Nat) × List (Option Int) × Proper}
    (h : crossCoordsR P rm cg labels p minimum layers = .ok out) :
    out.2.snd.snd.edges = p.edges := by
  unfold crossCoordsR at h
  obtain ⟨children, _, h⟩ := rfc4bind_ok h
  dsimp only at h
  split at h
  · have hF : False := by
      simp only [bind, Except.bind] at h
      exact absurd h (by simp)
    exact hF.elim
  · obtain ⟨ngs, _, h⟩ := rfc4bind_ok h
    obtain ⟨x, _, h⟩ := rfc4bind_ok h
    obtain ⟨_, _, h⟩ := rfc4bind_ok h
    obtain ⟨⟨alloc, x2⟩, halloc, h⟩ := rfc4bind_ok h
    obtain ⟨⟨x3, p3⟩, hres, h⟩ := rfc4bind_ok h
    have he := Except.ok.inj h
    have hfin := (congrArg (fun q :
      List Int × List (List Nat) × List (Option Int) × Proper => q.2.snd.snd.edges) he).symm
    exact hfin.trans (rfc4ReservedPortsR_edges hres)

private theorem rfc4ShapePack {P : Params} {exact : List Nat} (s : RegionSpec)
    {labels : List MeasuredLabel} {cg : Graph} {ranks : List Int} {p0 labeled : Proper}
    {p' : Proper} {xs1 : List Int} {q0 : Proper} {xs2 : List Int} {run : Run}
    (hn : normalize cg ranks = .ok p0)
    (hlab : Labels.addLabelNodes cg p0 (componentLabels cg labels) = .ok labeled)
    (hprox : proxyWidths p' xs1 = .ok (q0, xs2))
    (hdrop : run.proper = OrderImpl.dropSynthetic q0)
    (hPE : p'.edges = (coordinateGraphR P exact (some s) labeled).edges)
    (hN3 : Metadata.NodeMetadata (coordinateGraphR P exact (some s) labeled) p') :
    RouteImpl.ProperShape run.proper := by
  obtain ⟨hAdd, hclean, _⟩ := rfc4CoordinateR_shape s hn hlab
  obtain ⟨hrE, _, _, _, hP1, _⟩ := proxyWidths_rel hprox
  have hN1 : Metadata.NodeMetadata
      (OrderImpl.addClusterBorders (titleReservationsR s.titles P.clusterPad
        (sizeProperPortsX P exact labeled)) P.clusterBorderW)
      (clearProxyExtents (OrderImpl.addClusterBorders (titleReservationsR s.titles
        P.clusterPad (sizeProperPortsX P exact labeled)) P.clusterBorderW)) :=
    Metadata.nodeMetadata_map clearF (fun n => (clearF_keys n).1) (clearProxyExtents_nodes _)
  have hN2 : Metadata.NodeMetadata
      (clearProxyExtents (OrderImpl.addClusterBorders (titleReservationsR s.titles
        P.clusterPad (sizeProperPortsX P exact labeled)) P.clusterBorderW))
      (coordinateGraphR P exact (some s) labeled) := by
    intro v nd h
    obtain ⟨n2, hn2, hd2⟩ := materialize_exists _ h
    have hmatch : (materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact labeled))
      P.clusterBorderW))).nodes[v]? =
        (coordinateGraphR P exact (some s) labeled).nodes[v]? := rfl
    rw [hmatch] at hn2
    exact ⟨n2, hn2, hd2⟩
  have hN4 : Metadata.NodeMetadata p' q0 := by
    intro v nd h
    obtain ⟨nd', hn', hd', _, _⟩ := hP1 v nd h
    exact ⟨nd', hn', hd'⟩
  have hdropE : (OrderImpl.dropSynthetic q0).edges =
      (OrderImpl.dropSynthetic (OrderImpl.addClusterBorders (titleReservationsR s.titles
        P.clusterPad (sizeProperPortsX P exact labeled)) P.clusterBorderW)).edges := by
    show q0.edges.filter (fun e => !e.synthetic) = _
    rw [hrE, hPE]
    rfl
  have hmeta : Metadata.NodeMetadata
      (OrderImpl.dropSynthetic (OrderImpl.addClusterBorders (titleReservationsR s.titles
        P.clusterPad (sizeProperPortsX P exact labeled)) P.clusterBorderW))
      (OrderImpl.dropSynthetic q0) :=
    Metadata.nodeMetadata_trans
      (rfc4DropSynthetic_metadata (Metadata.nodeMetadata_trans hN1 hN2))
      (rfc4DropSynthetic_metadata (Metadata.nodeMetadata_trans hN3 hN4))
  rw [hdrop]
  exact Metadata.properShape_transfer hdropE hmeta hAdd

/-- Open stage fact (the single residual of this file): the cross-coordinate
placement preserves node dummy flags. `reservedPortsR` only rewrites node
heights (edges proved preserved in `rfc4CrossCoordsR_edges`); the remaining
`foldlM` dummy-map preservation belongs with the placement packet (P5).
True on executed runs: both probes take the reserved path with dummy flags
and edge declarations preserved (see the `#eval` checks in
`proofs/wip/Probe/RegionFlatC4Probe.lean`). -/
def rfc4CrossCoordsR_metadata_factR : Prop :=
  ∀ {P : Params} {rm : ComponentRegions} {cg : Graph} {labels : List MeasuredLabel}
    {p : Proper} {minimum : RegionConstraints} {layers : List (List Nat)}
    {placed : List Int × List (List Nat) × List (Option Int) × Proper},
    crossCoordsR P rm cg labels p minimum layers = .ok placed →
    Metadata.NodeMetadata p placed.2.snd.snd

theorem componentRunR_properShape_someR
    (hcross : rfc4CrossCoordsR_metadata_factR)
    {P : Params} {exact : List Nat} {spec : Option RegionSpec} (s : RegionSpec)
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hspec : spec = some s)
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    RouteImpl.ProperShape run.proper := by
  subst hspec
  unfold componentRunR at h
  obtain ⟨_, _, h⟩ := rfc4bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := rfc4bind_ok h
    obtain ⟨⟨_, _, _⟩, _, h⟩ := rfc4bind_ok h
    dsimp only at h
    obtain ⟨p0, hn, h⟩ := rfc4bind_ok h
    obtain ⟨plab, hlab, h⟩ := rfc4bind_ok h
    obtain ⟨_, _, h⟩ := rfc4bind_ok h
    obtain ⟨_, _, h⟩ := rfc4bind_ok h
    obtain ⟨_, _, h⟩ := rfc4bind_ok h
    obtain ⟨placed, hplaced, h⟩ := rfc4bind_ok h
    obtain ⟨⟨q0, _⟩, hprox, h⟩ := rfc4bind_ok h
    dsimp only at h
    have hpl := Except.ok.inj hplaced
    have hPE : placed.2.snd.snd.edges =
        (coordinateGraphR P exact (some s) plab).edges := by
      rw [← hpl]
    have hN3 : Metadata.NodeMetadata (coordinateGraphR P exact (some s) plab)
        placed.2.snd.snd := by
      rw [← hpl]
      exact fun v nd hh => ⟨nd, hh, rfl⟩
    split at h
    · obtain ⟨_, _, h⟩ := rfc4bind_ok h
      obtain ⟨_, _, h⟩ := rfc4bind_ok h
      obtain ⟨_, _, h⟩ := rfc4bind_ok h
      obtain ⟨_, _, h⟩ := rfc4bind_ok h
      have he := Except.ok.inj h
      have hdrop := (congrArg (fun q : Graph × Run => q.2.proper) he).symm
      exact rfc4ShapePack s hn hlab hprox hdrop hPE hN3
    · obtain ⟨_, _, h⟩ := rfc4bind_ok h
      obtain ⟨_, _, h⟩ := rfc4bind_ok h
      obtain ⟨_, _, h⟩ := rfc4bind_ok h
      obtain ⟨_, _, h⟩ := rfc4bind_ok h
      have he := Except.ok.inj h
      have hdrop := (congrArg (fun q : Graph × Run => q.2.proper) he).symm
      exact rfc4ShapePack s hn hlab hprox hdrop hPE hN3
  · obtain ⟨⟨_, _, _⟩, _, h⟩ := rfc4bind_ok h
    dsimp only at h
    obtain ⟨p0, hn, h⟩ := rfc4bind_ok h
    obtain ⟨plab, hlab, h⟩ := rfc4bind_ok h
    obtain ⟨_, _, h⟩ := rfc4bind_ok h
    obtain ⟨_, _, h⟩ := rfc4bind_ok h
    obtain ⟨_, _, h⟩ := rfc4bind_ok h
    split at h
    · simp only [bind, Except.bind] at h
      exact absurd h (by simp)
    · obtain ⟨_, _, h⟩ := rfc4bind_ok h
      obtain ⟨placed, hplaced, h⟩ := rfc4bind_ok h
      obtain ⟨⟨q0, _⟩, hprox, h⟩ := rfc4bind_ok h
      dsimp only at h
      have hN3 : Metadata.NodeMetadata (coordinateGraphR P exact (some s) plab)
          placed.2.snd.snd := hcross hplaced
      have hPE : placed.2.snd.snd.edges =
          (coordinateGraphR P exact (some s) plab).edges :=
        rfc4CrossCoordsR_edges hplaced
      split at h
      · obtain ⟨_, _, h⟩ := rfc4bind_ok h
        obtain ⟨_, _, h⟩ := rfc4bind_ok h
        obtain ⟨_, _, h⟩ := rfc4bind_ok h
        obtain ⟨_, _, h⟩ := rfc4bind_ok h
        have he := Except.ok.inj h
        have hdrop := (congrArg (fun q : Graph × Run => q.2.proper) he).symm
        exact rfc4ShapePack s hn hlab hprox hdrop hPE hN3
      · obtain ⟨_, _, h⟩ := rfc4bind_ok h
        obtain ⟨_, _, h⟩ := rfc4bind_ok h
        obtain ⟨_, _, h⟩ := rfc4bind_ok h
        obtain ⟨_, _, h⟩ := rfc4bind_ok h
        have he := Except.ok.inj h
        have hdrop := (congrArg (fun q : Graph × Run => q.2.proper) he).symm
        exact rfc4ShapePack s hn hlab hprox hdrop hPE hN3

/-- Every route of a successful region run is orthogonal: the exact twin
`componentRunX_routes_orthogonal` (`ExactFlatFacts.lean:444-458`), replayed
over `componentRunR`. The `none`-spec shape is proved above; the `some`-spec
shape (`componentRunR_properShape_someR`) is proved conditional on the
cross-coordinate residual below. The lane equation splits on the two
routers: empty `reserved` reuses `RouteImpl.routeWithLanes` (so
`Layered.route_orthogonal` applies directly), otherwise the lane-independent
`laneSemanticR_orthogonal` handles `routeWithLanesR`. -/
theorem componentRunR_routes_orthogonalR
    (hsome : rfc4CrossCoordsR_metadata_factR) {P : Params}
    {exact : List Nat} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    ∀ rt ∈ run.routes, Polyline.isOrthogonal rt.points = true := by
  have hP : RouteImpl.ProperShape run.proper := by
    cases hspec : spec with
    | none =>
      subst hspec
      exact componentRunR_properShape_noneR h
    | some s => exact componentRunR_properShape_someR hsome s hspec h
  have hroutes := componentRunR_routes_eqR h
  have hlanes := componentRunR_lanes_eqR h
  rcases hlanes with ⟨reversed, widths, hr⟩ | ⟨reversed, widths, reserved, hr⟩
  · exact Layered.route_orthogonal hP hr hroutes
  · exact laneSemanticR_orthogonal hP hr hroutes

/-- Placed edge points are orthogonal without any chain-length bridge: in
bounds they read a member route (orthogonal by the run fact); out of bounds
`getD` returns `default` whose points are `[]`. -/
theorem rfc4EdgePoints_orthogonalR (hsome : rfc4CrossCoordsR_metadata_factR)
    {P : Params} {exact : List Nat} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    (i : Nat) (e : Edge) :
    Polyline.isOrthogonal (edgePoints run i e) = true := by
  have hortho := componentRunR_routes_orthogonalR hsome h
  unfold edgePoints
  by_cases hi : i < run.routes.length
  · have hget : run.routes.getD i default = run.routes[i]'hi := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        Option.getD_some]
    rw [hget]
    exact hortho _ (List.getElem_mem hi)
  · have hnone : run.routes[i]? = none := by
      cases hget : run.routes[i]? with
      | some rt =>
        obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hget
        omega
      | none => rfl
    have hget : run.routes.getD i default = default := by
      rw [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    rw [hget]
    show Polyline.isOrthogonal ([] : List Point) = true
    simp [Polyline.isOrthogonal]

/-- Region placement emits orthogonal routes: mirror of
`placeComponentExact_routes_orthogonal` (`ExactFlatFacts.lean:462-481`) with
the bridge-free `rfc4EdgePoints_orthogonalR` in place of the exact
index-chasing `componentRunX_edgePoints_orthogonal`. -/
theorem placeComponentExact_routes_orthogonalR
    (hsome : rfc4CrossCoordsR_metadata_factR) {P : Params}
    {exact : List Nat} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {loops : List (Nat × LoopPlacement)}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    (hloops : componentLoops P cg' run labels = .ok loops) (cursor : Int) :
    ∀ q ∈ (placeComponentExact P cg' run cursor labels loops).routes,
      Polyline.isOrthogonal q.2 = true := by
  intro q hq
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hq
  apply (Layered.isOrthogonal_shift _ _ _).mpr
  cases hf : loops.find? (fun l => l.1 == entry.1.decl) with
  | some loop =>
    simpa only [hf, Option.map_some, Option.getD_some] using
      componentLoops_orthogonal hloops loop (List.mem_of_find?_eq_some hf)
  | none =>
    simp only [Option.map_none, Option.getD_none]
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp
      (List.mem_zipIdx_iff_getElem?.mp hentry)
    rw [← he]
    exact rfc4EdgePoints_orthogonalR hsome hrun _ _

private def rfc4RoutesOrthogonal (a : Array (List Point)) : Prop :=
  ∀ k, Polyline.isOrthogonal (a.getD k []) = true

private theorem rfc4RoutesFold (entries : List (Nat × List Point))
    (f : List Point → List Point)
    (hf : ∀ points, Polyline.isOrthogonal points = true →
      Polyline.isOrthogonal (f points) = true)
    (he : ∀ q ∈ entries, Polyline.isOrthogonal q.2 = true)
    (a : Array (List Point)) (ha : rfc4RoutesOrthogonal a) :
    rfc4RoutesOrthogonal (entries.foldl (fun arr q => arr.set! q.1 (f q.2)) a) := by
  induction entries generalizing a with
  | nil => exact ha
  | cons q rest ih =>
    simp only [List.foldl_cons]
    apply ih (fun r hr => he r (List.mem_cons_of_mem _ hr))
    intro k
    rw [RankImpl.getD_set!]
    split
    · exact hf q.2 (he q List.mem_cons_self)
    · exact ha k

private theorem placePartR_routes_orthogonalR
    (hsome : rfc4CrossCoordsR_metadata_factR) {P : Params}
    {exact : List Nat} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions} {comp : List Nat} {acc out : Acc}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    (ha : rfc4RoutesOrthogonal acc.routes)
    (h : placePart comp cg' run P acc labels (@placeComponentExact) true = .ok out) :
    rfc4RoutesOrthogonal out.routes := by
  unfold placePart at h
  obtain ⟨loops, hloops, h⟩ := rfc4bind_ok h
  dsimp only at h
  split at h
  · simp at h
  · have he := Except.ok.inj h
    subst out
    exact rfc4RoutesFold _ id (fun _ h => h)
      (placeComponentExact_routes_orthogonalR hsome hrun hloops 0) _ ha

private theorem layoutComponentR_routes_orthogonalR
    (hsome : rfc4CrossCoordsR_metadata_factR) {P : Params}
    {exactIds : List String} {spec : Option RegionSpec} {inp : Input} {o : Options}
    {g : Graph} {comp : List Nat} {labels : List MeasuredLabel} {acc out : Acc}
    (ha : rfc4RoutesOrthogonal acc.routes)
    (h : layoutComponentR P exactIds spec inp o g acc comp labels = .ok out) :
    rfc4RoutesOrthogonal out.routes := by
  obtain ⟨_, _, hprod⟩ := layoutComponentR_parts h
  obtain ⟨_, chosen, cg, run, _, _, _, hc, hv, _, hrun, _, _⟩ := hprod
  unfold layoutComponentR at h
  obtain ⟨chosen', hc', h⟩ := rfc4bind_ok h
  obtain ⟨result, hplace, h⟩ := rfc4bind_ok h
  obtain ⟨metric, _, h⟩ := rfc4bind_ok h
  obtain ⟨titleAreas, _, h⟩ := rfc4bind_ok h
  have he := Except.ok.inj h
  have hch : chosen' = chosen := Except.ok.inj (hc'.symm.trans hc)
  subst hch
  rw [hv] at hplace
  have hrr : out.routes = result.routes :=
    (congrArg (fun a : Acc => a.routes) he).symm
  rw [hrr]
  exact placePartR_routes_orthogonalR hsome hrun ha hplace

private theorem componentsR_routes_orthogonalR
    (hsome : rfc4CrossCoordsR_metadata_factR) {P : Params}
    {exactIds : List String} {spec : Option RegionSpec} {inp : Input}
    {o : Options} {g : Graph} {labels : List MeasuredLabel} :
    ∀ (comps : List (List Nat)) (start out : Acc),
      rfc4RoutesOrthogonal start.routes →
      comps.foldlM (fun acc comp => layoutComponentR P exactIds spec inp o g acc comp labels)
        start = .ok out →
      rfc4RoutesOrthogonal out.routes := by
  intro comps
  induction comps with
  | nil =>
    intro start out ha h
    have he : start = out := Except.ok.inj h
    subst out
    exact ha
  | cons comp comps ih =>
    intro start out ha h
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hm, h⟩ := rfc4bind_ok h
    apply ih mid out
    · exact layoutComponentR_routes_orthogonalR hsome ha hm
    · exact h

private theorem packAccR_routes_orthogonalR {P : Params} {o : Options}
    {acc out : Acc} (ha : rfc4RoutesOrthogonal acc.routes)
    (hparts : ∀ q ∈ acc.parts, ∀ route ∈ q.2.routes,
      Polyline.isOrthogonal route.2 = true)
    (h : packAcc P o acc = .ok out) : rfc4RoutesOrthogonal out.routes := by
  unfold packAcc at h
  obtain ⟨packed, _, h⟩ := rfc4bind_ok h
  have he := Except.ok.inj h
  subst out
  rw [packAcc_routes_eq_foldl]
  have hpairs : ∀ q ∈ acc.parts.zip packed.boxes,
      ∀ route ∈ q.1.2.routes, Polyline.isOrthogonal route.2 = true := by
    intro q hq
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hq
    exact hparts q.1 (List.mem_of_getElem? (zip_getElem?_left hk))
  have preserve : ∀ (pairs : List ((List Nat × Part) × Rect)) (a : Array (List Point)),
      (∀ q ∈ pairs, ∀ route ∈ q.1.2.routes,
        Polyline.isOrthogonal route.2 = true) →
      rfc4RoutesOrthogonal a →
      rfc4RoutesOrthogonal (pairs.foldl (fun arr q => q.1.2.routes.foldl
        (fun a r => a.set! r.1 (r.2.map (shiftPoint q.2.x q.2.y))) arr) a) := by
    intro pairs
    induction pairs with
    | nil => intro a _ ha; exact ha
    | cons q pairs ih =>
      intro a hpairs ha
      simp only [List.foldl_cons]
      apply ih _ (fun r hr => hpairs r (List.mem_cons_of_mem _ hr))
      exact rfc4RoutesFold _ _
        (fun points h => (Layered.isOrthogonal_shift _ _ points).mpr h)
        (hpairs q List.mem_cons_self) _ ha
  exact preserve _ _ hpairs ha

theorem SceneExecutionR.routes_orthogonalR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (hsome : rfc4CrossCoordsR_metadata_factR) :
    ∀ route ∈ res.scene.routes, Polyline.isOrthogonal route.points = true := by
  have hinit : rfc4RoutesOrthogonal
      (Array.replicate inp.routes.length ([] : List Point)) := by
    intro k
    simp [Array.getD, Polyline.isOrthogonal]
  have hmid := componentsR_routes_orthogonalR hsome _ _ _ hinit execution.components_eq
  have hparts : ∀ q ∈ execution.componentsAcc.parts,
      ∀ route ∈ q.2.routes, Polyline.isOrthogonal route.2 = true := by
    obtain ⟨_, hall⟩ := actual_components_partsR rfl execution.components_eq
    intro q hq
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hrun, hloops, hroutes⟩ := hall q hq
    rw [hroutes]
    exact placeComponentExact_routes_orthogonalR hsome hrun hloops 0
  have hpacked := packAccR_routes_orthogonalR hmid hparts execution.packed_eq
  rw [execution.scene_eq]
  intro route hroute
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hroute
  exact (Layered.isOrthogonal_shift_orient _ _ _ _ _).mpr (hpacked q.2)

/-- Clause 4 of the layout validator for a successful region flat
`PipelineImpl.layoutRIds`: every scene route is orthogonal. Mirror of the
`flatC4` term of `exactBaseSeams` (`Kinds/UsecaseValidExact.lean:210-212`),
conditional on the single open route fact. -/
theorem flatC4B_layoutRIds (exactIds : List String)
    (idSets : List (String × List String))
    (hsome : rfc4CrossCoordsR_metadata_factR) :
    FlatC4B (layoutRIds exactIds idSets) := by
  intro inp o res h route hroute
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  exact SceneExecutionR.routes_orthogonalR execution hsome route hroute

end PipelineImpl

end Layered
end Elegant

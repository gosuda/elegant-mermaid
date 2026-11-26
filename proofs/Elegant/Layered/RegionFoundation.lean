import Elegant.Layered.RegionPipeline
import Elegant.Layered.RegionReduction
import Elegant.Layered.ExactPipeline
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ComponentRunGen

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-!
# Region base foundation: `layoutRIds` execution record and first transported facts.

This module lives in `PipelineImpl`, the home of `layoutRIds` (`RegionPipeline.lean`)
and of the no-region reductions (`RegionReduction.lean`), and opens `RegionImpl` for the
region run, candidate, and coordinate definitions.

## Item 1. `componentRunR` against `componentRunX` and `componentRunGen`.

Stage-by-stage diff (`componentRunX` on the left, `componentRunR` on the right;
`componentRunGen` matches `componentRunX` stage for stage by `componentRunX_eq_gen`):

* Signature: R takes two extra arguments, `spec : Option RegionSpec` and `inp : Input`,
  and returns the run paired with the final-orientation graph,
  `Except LayoutError (Graph × Run)`, instead of `Except LayoutError Run`.
* Stage 0 (new, no X/gen counterpart): `rs ← newComponentRegions spec P inp cg`
  resolves the spec sets against this component's clusters (`none` when `spec` is `none`).
* Ranking (changed): X/gen run `rankWithBudget (Compound.rankingGraph cg)` and keep `cg`.
  R runs `rankEquivalentR rm cg` when `rs = some rm`: collapse each set onto its first
  region, orient the semantic edges against the constraint order, rank the condensed
  graph, and expand the ranks. The returned graph carries the final edge orientations
  and replaces `cg` downstream; the budget comes from the region ranking.
* `normalize` and `Labels.addLabelNodes`: identical calls (on the possibly rewritten ranks).
* Coordinate/size (changed hook): X is `coordinateGraphX P exact p`, that is
  `titleReservations (sizeProperPortsX P exact p)` under borders, clearing, and
  materialization; gen is `coordinateGen sizeHook P p` with `sizeHook` fixed to
  `sizeProperPortsX P exact`. R is `coordinateGraphR P exact spec p`: `none` reuses
  `coordinateGraphX` (`coordinateGraphR_none`), while `some s` keeps the same size part
  `sizeProperPortsX P exact p` but replaces the title part with
  `titleReservationsR s.titles P.clusterPad`, which zeroes `±2`-border nodes and gives
  each title its own height instead of the loop height.
* Minimum (new): `minimum ← match rs with | none => pure none | some rm => constrainR rm P p`
  computes the frame minimum of every cluster and row. No X/gen counterpart.
* `orderWithBudget`: identical call.
* Placement (changed, extra arguments): X/gen run
  `crossCoordsClusterWith P.nodeGap P.clusterPad p ord.layers`, a single coordinate list.
  R runs `crossCoordsR P rm cg labels p m ord.layers` when `rs = some rm`: pin the layer
  order (`regionChildren`, `childPreorderGo`, `pinLayers`), cross on the pinned layers,
  check spans, allocate every frame, lane, and member (`allocatePl`, `regionFrames`,
  `reservedPortsR`). It returns `(coordinateXs, pinnedLayers, reserved, p')`: a new layer
  order, reserved lanes `List (Option Int)`, and a possibly rewritten proper graph.
* `proxyWidths` and `OrderImpl.dropSynthetic`: identical calls.
* Lanes/routing (changed hook, extra argument): X/gen always run
  `RouteImpl.routeWithLanes`. R runs the plain call only when `reserved` is empty and
  otherwise `routeWithLanesR ... reserved`, which parks a reversed edge at its reserved
  lane instead of the outer fallback.
* `rankCoordsWith`, `proxyYs`: identical calls.
* Reserve (same as the X hook instantiation): R always runs
  `reserveExactRanks cg exact labels p layers ys yt.2`, exactly gen's `reserveHook`
  instantiated as in `componentRunX_eq_gen`.
* `RouteImpl.routePointsWithLanes`: identical call.
* `exactOut`: the identical filterMap expression as X/gen.
* Budget: `rankBudget || ord.budgetExhausted`, the same shape (rank part from either ranking).

Verdict: `componentRunR` is NOT an instance of `componentRunGen` with the three existing
hooks (`sizeHook`, `reserveHook`, `exactOut`). The size and reserve stages already coincide
with the X instantiation, but ranking, titles, placement, and routing each need region
data (`spec` / `inp` / `rm` / `minimum` / `reserved`) that no existing hook receives.
The `none` case coincides with `componentRunX` (`componentRunR_none` in
`RegionReduction.lean`); `componentRunR_none_eq_gen` below restates that coincidence
through `componentRunGen`.

### Missing hooks that would capture the region stages

To express `componentRunR` with `spec ≠ none` through `componentRunGen`, the generalized
run would need, in addition to `sizeHook`, `reserveHook`, and `exactOut`:

* `rankHook : Graph → Except LayoutError (List Int × Graph × Bool)`, replacing
  `rankWithBudget (Compound.rankingGraph ·)` at the ranking stage; it must return the
  rewritten graph alongside the ranks and the budget flag (regions: `rankEquivalentR rm`
  once `rm` is resolved from `(spec, inp, cg)` by `newComponentRegions`).
* `titleHook : List (Int × Int) → Int → Proper → Proper`, replacing `titleReservations`
  inside `coordinateGen` at the coordinate stage (regions: `titleReservationsR`).
* `placeHook : Proper → List (List Nat) → Except LayoutError (List Int × List (List Nat) × List (Option Int) × Proper)`,
  replacing `crossCoordsClusterWith P.nodeGap P.clusterPad · ·` at the placement stage
  (regions: `crossCoordsR P rm cg labels · minimum`); it may reorder layers, reserve
  lanes, and rewrite the proper graph.
* `laneHook : Int → Proper → List (List Nat) → List Int → List Bool → List Int → List (Option Int) → Except LayoutError RouteImpl.LaneRouting`,
  replacing `RouteImpl.routeWithLanes` at the routing stage (regions: `routeWithLanesR`,
  falling back to `routeWithLanes` when every reservation is `none`).

None of these is added here: `ComponentRunGen` is untouched. The strongest true relations
over the existing hooks are `componentRunR_none` (exact run, proved in
`RegionReduction.lean`), `componentRunR_none_eq_gen` below, and `componentRunR_spec`
for the `none` case.
-/

/-- The region run with no spec is the generalized run with the exact hooks
(up to pairing with the unchanged graph). -/
theorem componentRunR_none_eq_gen (P : Params) (exact : List Nat) (inp : Input)
    (cg : Graph) (labels : List MeasuredLabel) (orderOptions : OrderOptions) :
    componentRunR P exact none inp cg labels orderOptions =
      (componentRunGen P (sizeProperPortsX P exact) (reserveExactRanks cg exact labels)
        (cg.nodes.zipIdx.filterMap fun q => if exact.contains q.1.decl then some q.2 else none)
        cg labels orderOptions).map fun run => (cg, run) := by
  rw [componentRunR_none, componentRunX_eq_gen]

/-!
## Item 2. Execution record for `layoutRIds`.
-/

/-- One executed region base layout: the same phase equations as `SceneExecutionX`,
with the components fold running `layoutComponentR` under the spec resolved from
`idSets` and the measured title dimensions. No field asserts a geometric bound. -/
structure SceneExecutionR (exactIds : List String) (idSets : List (String × List String))
    (inp : Input) (o : Options) (res : FamilyResult) where
  params : Params
  metric : Measure.Metric
  lines : List (List Measure.Line)
  measured : List MeasuredLabel
  graph0 : Graph
  graph : Graph
  componentsAcc : Acc
  packedAcc : Acc
  checked : checkedParams o.profile inp.kind = .ok params
  metric_eq : metricOf o.profile o.fontFamily = .ok metric
  lines_eq : boxLines metric
    (Measure.wrapTarget metric.profile params.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
    inp = .ok lines
  measured_eq : measureLabels params metric
    (Measure.wrapTarget metric.profile params.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
    inp o.direction = .ok measured
  graph0_eq : measuredGraph params inp o lines = .ok graph0
  graph_eq : exactGraph params exactIds inp o measured graph0 = .ok graph
  components_eq : (components graph).foldlM
    (fun acc comp => layoutComponentR params exactIds
      (if idSets.isEmpty then none
        else some (RegionSpec.mk idSets (lines.map fun ls =>
          let width := ls.foldl (fun w line => max w line.width) 0
          let height := (max 1 ls.length : Int) * params.lineH
          match o.direction with
          | .LR | .RL => (height, width)
          | .TB | .BT => (width, height))))
      inp o graph acc comp measured)
    ⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ = .ok componentsAcc
  packed_eq : packAcc params o componentsAcc = .ok packedAcc
  scene_eq : res.scene = sceneOf params inp o lines packedAcc measured

/-- Recover the region phases `layoutRIds` used: measured graph, exact graph,
selected-component fold with `layoutComponentR`, and packed accumulator. -/
theorem layoutRIds_success_phases {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {result : FamilyResult} (h : layoutRIds exactIds idSets inp o = .ok result) :
    ∃ P metric lines measured graph0 graph mid packed,
      checkedParams o.profile inp.kind = .ok P ∧
      metricOf o.profile o.fontFamily = .ok metric ∧
      boxLines metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0)) inp = .ok lines ∧
      measureLabels P metric
        (Measure.wrapTarget metric.profile P.wrapWidth
          (if o.profile == .cell then o.maxWidth else 0)) inp o.direction = .ok measured ∧
      measuredGraph P inp o lines = .ok graph0 ∧
      exactGraph P exactIds inp o measured graph0 = .ok graph ∧
      (components graph).foldlM
        (fun acc comp => layoutComponentR P exactIds
          (if idSets.isEmpty then none
            else some (RegionSpec.mk idSets (lines.map fun ls =>
              let width := ls.foldl (fun w line => max w line.width) 0
              let height := (max 1 ls.length : Int) * P.lineH
              match o.direction with
              | .LR | .RL => (height, width)
              | .TB | .BT => (width, height))))
          inp o graph acc comp measured)
        ⟨0, 0, 0, Array.replicate inp.boxes.length default,
          Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
          false, [], []⟩ = .ok mid ∧
      packAcc P o mid = .ok packed ∧
      result.scene = sceneOf P inp o lines packed measured ∧
      result.budgetExhausted = packed.budget ∧
      result.itemArea = packed.parts.foldl (fun area part => area + part.2.area) 0 := by
  unfold layoutRIds at h
  obtain ⟨P, hP, h⟩ := bind_ok h
  obtain ⟨metric, hm, h⟩ := bind_ok h
  obtain ⟨lines, hl, h⟩ := bind_ok h
  obtain ⟨measured, hmeasured, h⟩ := bind_ok h
  obtain ⟨graph0, hg0, h⟩ := bind_ok h
  obtain ⟨graph, hg, h⟩ := bind_ok h
  obtain ⟨mid, hmid, h⟩ := bind_ok h
  obtain ⟨packed, hpacked, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · have he := Except.ok.inj h
    subst result
    exact ⟨P, metric, lines, measured, graph0, graph, mid, packed,
      hP, hm, hl, hmeasured, hg0, hg, hmid, hpacked, rfl, rfl, rfl⟩

/-- Extract the measured graph, exact graph, region-component fold, and packed
accumulator that `layoutRIds` used. -/
theorem layoutRIds_sceneExecution {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutRIds exactIds idSets inp o = .ok res) :
    Nonempty (SceneExecutionR exactIds idSets inp o res) := by
  obtain ⟨P, metric, lines, measured, graph0, graph, componentsAcc, packedAcc,
    hP, hm, hl, hmeasured, hg0, hg, hc, hp, hs, _, _⟩ := layoutRIds_success_phases h
  exact ⟨⟨P, metric, lines, measured, graph0, graph, componentsAcc, packedAcc,
    hP, hm, hl, hmeasured, hg0, hg, hc, hp, hs⟩⟩

/-!
## Item 3. First transported facts over `SceneExecutionR`.
-/

/-- Region scene boxes read the input boxes in order (shared `sceneOf` equation). -/
theorem SceneExecutionR.boxes_eq_mapR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) :
    res.scene.boxes = (inp.boxes.zipIdx.map fun q =>
      Box.mk q.1.id q.1.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD q.2 default)))
        q.1.parent q.1.exclusive) :=
  congrArg (fun s : Scene => s.boxes) execution.scene_eq

/-- Region components preserve the array sizes. -/
theorem layoutComponentR_sizes {P : Params} {exactIds : List String}
    {spec : Option RegionSpec} {inp : Input} {o : Options} {g : Graph}
    {acc acc' : Acc} {comp : List Nat} {labels : List MeasuredLabel}
    (h : layoutComponentR P exactIds spec inp o g acc comp labels = .ok acc') :
    acc.rects.size = acc'.rects.size ∧ acc.routes.size = acc'.routes.size ∧
      acc.labels.size = acc'.labels.size := by
  unfold layoutComponentR at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  have hr := congrArg Acc.rects he
  have ho := congrArg Acc.routes he
  have hl := congrArg Acc.labels he
  unfold placePart at hresult
  obtain ⟨_, _, hres⟩ := bind_ok hresult
  dsimp only at hres
  split at hres
  · simp at hres
  · have heq := Except.ok.inj hres
    subst heq
    dsimp only at hr ho hl
    refine ⟨?_, ?_, ?_⟩
    · rw [← hr]; exact (size_zipFold_eq id _ _ _).symm
    · rw [← ho]; exact (size_keyFold_pts_eq id _ _).symm
    · rw [← hl]; exact (size_keyFold_rects_eq id _ _).symm

/-- Region fold preserves the route array size. -/
private theorem rf_components_fold_routes_sizeR (P : Params) (exactIds : List String)
    (spec : Option RegionSpec) (inp : Input) (o : Options) (g : Graph)
    (measured : List MeasuredLabel) :
    ∀ (comps : List (List Nat)) (start out : Acc),
      comps.foldlM (fun acc comp => layoutComponentR P exactIds spec inp o g acc comp measured)
        start = .ok out → out.routes.size = start.routes.size
  | [], start, out, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
  | comp :: rest, start, out, h => by
    simp only [List.foldlM_cons] at h
    cases hc : layoutComponentR P exactIds spec inp o g start comp measured with
    | error e => simp [hc, bind, Except.bind] at h
    | ok next =>
      simp only [hc, bind, Except.bind] at h
      exact (rf_components_fold_routes_sizeR P exactIds spec inp o g measured rest next out h).trans
        (layoutComponentR_sizes hc).2.1.symm

/-- Region execution keeps the route array length. -/
private theorem SceneExecutionR.components_routes_sizeR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res) :
    execution.componentsAcc.routes.size = inp.routes.length := by
  have h := rf_components_fold_routes_sizeR execution.params exactIds _ inp o execution.graph
    execution.measured (components execution.graph) _ _ execution.components_eq
  simpa only [Array.size_replicate] using h

/-- The region run with no spec satisfies the exact run equations. -/
theorem componentRunR_spec {P : Params} {exact : List Nat} {inp : Input} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact none inp cg labels orderOptions = .ok (cg, run)) :
    ∃ ranks p0 labeled q0, normalize cg ranks = .ok p0 ∧
      Labels.addLabelNodes cg p0 (componentLabels cg labels) = .ok labeled ∧
      coordinateGraphX P exact labeled = run.coordinateProper ∧
      (∃ ord, orderWithBudget run.coordinateProper orderOptions = .ok ord ∧
        ord.layers = run.layers) ∧
      crossCoordsClusterWith P.nodeGap P.clusterPad run.coordinateProper run.layers =
        .ok run.coordinateXs ∧
      proxyWidths run.coordinateProper run.coordinateXs = .ok (q0, run.xs) ∧
      OrderImpl.dropSynthetic q0 = run.proper ∧
      RouteImpl.routeWithLanes P.slot run.proper run.layers run.xs
        (cg.edges.map (·.reversed))
        (cg.edges.map fun edge => (stackSize cg.slot (routeLabels labels edge.decl)).width) =
          .ok run.lanes ∧ run.lanes.routing = run.routing ∧
      RouteImpl.routePointsWithLanes P.slot run.proper run.layers run.xs run.ys run.top
        run.lanes = .ok run.routes := by
  have hX : componentRunX P exact cg labels orderOptions = .ok run := by
    have hmap := componentRunR_none P exact inp cg labels orderOptions ▸ h
    cases hX0 : componentRunX P exact cg labels orderOptions with
    | error e =>
      have hR : componentRunR P exact none inp cg labels orderOptions = .error e := by
        simp only [componentRunR_none, hX0, Except.map]
      rw [hR] at h
      cases h
    | ok r =>
      have hR : componentRunR P exact none inp cg labels orderOptions = .ok (cg, r) := by
        simp only [componentRunR_none, hX0, Except.map]
      rw [hR] at h
      have heq : r = run := congrArg Prod.snd (Except.ok.inj h)
      exact congrArg Except.ok heq
  exact componentRunX_spec hX

end PipelineImpl
end Layered
end Elegant

import Elegant.Layered.RegionPipeline
import Elegant.Layered.PipelineFacts

set_option autoImplicit false

/-!
# Region run stage equations (`componentRunR_specR`).

Packet P3 of `local://region-tower-plan.md`: from
`componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)`
derive one equation per stage, for both the `none` and the `some` region
cases. This mirrors `componentRunX_spec` (`ExactFlatFacts.lean:284`) and
extends the none-only `componentRunR_spec` (`RegionFoundation.lean:291`).

## Truth probes (see `proofs/wip/Probe/RegionRunSpecTProbe.lean`)

The naive X-shaped equation
`coordinateGraphR P exact spec labeled = run.coordinateProper` is FALSE in
general for the `some` case: on the two-region witness (two region sets over
`G1 | {A, B}` and `G2 | {C, D}` with three cross edges; the run succeeds with
8 layers, 90 coordinate xs, 90 proper nodes, 3 routes) `crossCoordsR`
rewrites the proper graph (`placedProper ≠ pCoord`, witnessed by
`rrsCoordRewrite = true`). A nested-region witness (sets over `G1 | {A, B}`
and `A | {A1, A2}`) run through the greedy candidate (index 2, with two
reversed edges) succeeds with 7 layers, 64 xs, 64 nodes, 2 routes.

The true narrower form proved here keeps the coordinate output `pCoord` and
the placement output `placedProper` (which always equals
`run.coordinateProper`) separate; they coincide exactly when `rs = none`.
Likewise `orderWithBudget` is stated over `pCoord`, and the
minimum/placement/lane equations split on `rs` and on `reserved.isEmpty`.
-/

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-- One equation per `componentRunR` stage, for both region cases. `pCoord`
is the `coordinateGraphR` output; `placedProper` is the placement output and
always equals `run.coordinateProper` (they coincide iff `rs = none`). -/
structure ComponentRunRStages (P : Params) (exact : List Nat)
    (spec : Option RegionSpec) (inp : Input) (cg : Graph)
    (labels : List MeasuredLabel) (orderOptions : OrderOptions) (cg' : Graph)
    (run : Run) (rs : Option ComponentRegions) (ranks : List Int)
    (rankBudget : Bool) (p0 labeled pCoord : Proper)
    (minimum : Option RegionConstraints) (ord : OrderResult)
    (labelWidths : List Int) (reserved : List (Option Int))
    (placedProper q0 : Proper) (yt : List Int × List Int) (ysMid : List Int) :
    Prop where
  hRs : newComponentRegions spec P inp cg = .ok rs
  hRank : (∃ rr : RankImpl.RankResult, rs = none ∧ rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧ ranks = rr.ranks ∧ cg' = cg ∧ rankBudget = rr.budgetExhausted) ∨ (∃ rm : ComponentRegions, rs = some rm ∧ rankEquivalentR rm cg = .ok (ranks, cg', rankBudget))
  hNorm : normalize cg' ranks = .ok p0
  hLabels : Labels.addLabelNodes cg' p0 (componentLabels cg' labels) = .ok labeled
  hCoord : coordinateGraphR P exact spec labeled = pCoord
  hMin : (rs = none ∧ minimum = none) ∨ (∃ rm : ComponentRegions, ∃ m : RegionConstraints, rs = some rm ∧ minimum = some m ∧ constrainR rm P pCoord = .ok m)
  hOrd : orderWithBudget pCoord orderOptions = .ok ord
  hLabelWidths : labelWidths = cg'.edges.map fun edge => (stackSize cg'.slot (routeLabels labels edge.decl)).width
  hPlaced : (rs = none ∧ crossCoordsClusterWith P.nodeGap P.clusterPad pCoord ord.layers = .ok run.coordinateXs ∧ run.layers = ord.layers ∧ reserved = [] ∧ placedProper = pCoord) ∨ (∃ rm : ComponentRegions, ∃ m : RegionConstraints, rs = some rm ∧ minimum = some m ∧ crossCoordsR P rm cg' labels pCoord m ord.layers = .ok (run.coordinateXs, run.layers, reserved, placedProper))
  hProxy : proxyWidths placedProper run.coordinateXs = .ok (q0, run.xs)
  hDrop : OrderImpl.dropSynthetic q0 = run.proper
  hLanes : (reserved.isEmpty = true ∧ RouteImpl.routeWithLanes P.slot run.proper run.layers run.xs (cg'.edges.map (·.reversed)) labelWidths = .ok run.lanes) ∨ (reserved.isEmpty = false ∧ routeWithLanesR P.slot run.proper run.layers run.xs (cg'.edges.map (·.reversed)) labelWidths reserved = .ok run.lanes)
  hYt : rankCoordsWith P.rankGap P.slot placedProper run.layers (run.lanes.routing.gaps.map (·.slots)) = .ok yt
  hYsMid : proxyYs placedProper run.layers yt.2 yt.1 = ysMid
  hReserve : reserveExactRanks cg' exact labels placedProper run.layers ysMid yt.2 = .ok (run.ys, run.top)
  hRoutes : RouteImpl.routePointsWithLanes P.slot run.proper run.layers run.xs run.ys run.top run.lanes = .ok run.routes
  hRouting : run.lanes.routing = run.routing
  hCoordProper : run.coordinateProper = placedProper
  hCoordYs : run.coordinateYs = yt.1
  hBudget : run.budget = (rankBudget || ord.budgetExhausted)
  hExact : run.exact = (cg'.nodes.zipIdx.filterMap fun q => if exact.contains q.1.decl then some q.2 else none)

/-- Stages for runs with no component regions: ranking keeps `cg`, the
minimum is `none`, placement is `crossCoordsClusterWith`, and the coordinate
graph output coincides with `run.coordinateProper`. -/
private theorem rrspec_stages_none {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    (hN : newComponentRegions spec P inp cg = .ok none) :
    ∃ (ranks : List Int) (rankBudget : Bool) (p0 labeled : Proper)
      (ord : OrderResult) (placed : List Int × List (List Nat) × List (Option Int)
      × Proper) (routed : Proper × List Int) (yt : List Int × List Int),
      ComponentRunRStages P exact spec inp cg labels orderOptions cg' run none
        ranks rankBudget p0 labeled (coordinateGraphR P exact spec labeled) none
        ord
        (cg'.edges.map fun edge =>
          (stackSize cg'.slot (routeLabels labels edge.decl)).width)
        placed.2.2.1 (coordinateGraphR P exact spec labeled) routed.1 yt
        (proxyYs (coordinateGraphR P exact spec labeled) run.layers yt.2 yt.1) := by
  unfold componentRunR at h
  obtain ⟨rs, hrs, h⟩ := bind_ok h
  have hrsN : rs = none := Except.ok.inj (hrs.symm.trans hN)
  subst hrsN
  dsimp only at h
  obtain ⟨rr, hrr, h⟩ := bind_ok h
  obtain ⟨ranked, hranked, h⟩ := bind_ok h
  cases ranked with
  | mk ranks rest =>
    cases rest with
    | mk cg1 rankBudget =>
      dsimp only at h
      obtain ⟨p0, hp0, h⟩ := bind_ok h
      obtain ⟨labeled, hlab, h⟩ := bind_ok h
      obtain ⟨minv, hmin, h⟩ := bind_ok h
      obtain ⟨ord, hord, h⟩ := bind_ok h
      obtain ⟨xs, hxs, h⟩ := bind_ok h
      obtain ⟨placed, hplaced, h⟩ := bind_ok h
      obtain ⟨routed, hrouted, h⟩ := bind_ok h
      cases hres : placed.2.2.1.isEmpty with
      | true =>
        rw [hres, ite_eq_left rfl] at h
        obtain ⟨lanes_1, hlanes, h⟩ := bind_ok h
        obtain ⟨yt, hyt, h⟩ := bind_ok h
        obtain ⟨resv, hresv, h⟩ := bind_ok h
        obtain ⟨routes, hroutes, h⟩ := bind_ok h
        have he := Except.ok.inj h
        have hcg : cg' = cg1 := (congrArg Prod.fst he).symm
        subst hcg
        have hrankedt := Except.ok.inj hranked
        have hr1 : ranks = rr.ranks := (congrArg Prod.fst hrankedt).symm
        have hcb : cg' = cg := (congrArg (fun t => t.2.1) hrankedt).symm
        have hrb : rankBudget = rr.budgetExhausted :=
          (congrArg (fun t => t.2.2) hrankedt).symm
        have hplacedt := Except.ok.inj hplaced
        have hxs_eq : xs = placed.1 := congrArg Prod.fst hplacedt
        have hly : ord.layers = placed.2.1 := congrArg (fun t => t.2.1) hplacedt
        have hnil : ([] : List (Option Int)) = placed.2.2.1 :=
          congrArg (fun t => t.2.2.1) hplacedt
        have hpp : coordinateGraphR P exact spec labeled = placed.2.2.2 :=
          congrArg (fun t => t.2.2.2) hplacedt
        have hP : run.proper = OrderImpl.dropSynthetic routed.1 :=
          (congrArg (fun q : Graph × Run => q.2.proper) he).symm
        have hL : run.layers = placed.2.1 :=
          (congrArg (fun q : Graph × Run => q.2.layers) he).symm
        have hX : run.xs = routed.2 :=
          (congrArg (fun q : Graph × Run => q.2.xs) he).symm
        have hY : run.ys = resv.1 :=
          (congrArg (fun q : Graph × Run => q.2.ys) he).symm
        have hT : run.top = resv.2 :=
          (congrArg (fun q : Graph × Run => q.2.top) he).symm
        have hRt : run.routing = lanes_1.routing :=
          (congrArg (fun q : Graph × Run => q.2.routing) he).symm
        have hR : run.routes = routes :=
          (congrArg (fun q : Graph × Run => q.2.routes) he).symm
        have hB : run.budget = (rankBudget || ord.budgetExhausted) :=
          (congrArg (fun q : Graph × Run => q.2.budget) he).symm
        have hN : run.lanes = lanes_1 :=
          (congrArg (fun q : Graph × Run => q.2.lanes) he).symm
        have hCP : run.coordinateProper = placed.2.2.2 :=
          (congrArg (fun q : Graph × Run => q.2.coordinateProper) he).symm
        have hCX : run.coordinateXs = placed.1 :=
          (congrArg (fun q : Graph × Run => q.2.coordinateXs) he).symm
        have hCY : run.coordinateYs = yt.1 :=
          (congrArg (fun q : Graph × Run => q.2.coordinateYs) he).symm
        have hE : run.exact =
            (cg'.nodes.zipIdx.filterMap fun q =>
              if exact.contains q.1.decl then some q.2 else none) :=
          (congrArg (fun q : Graph × Run => q.2.exact) he).symm
        have hrouted2 : routed = (routed.1, run.xs) := by rw [hX]
        have hresv2 : resv = (run.ys, run.top) := by rw [hY, hT]
        rw [←hP, ←hL, ←hX, ←hN] at hlanes
        have hxx : xs = run.coordinateXs := hxs_eq.trans hCX.symm
        have hPlaced1 : crossCoordsClusterWith P.nodeGap P.clusterPad
            (coordinateGraphR P exact spec labeled) ord.layers =
            .ok run.coordinateXs := by rw [hxx] at hxs; exact hxs
        have hPlaced2 : run.layers = ord.layers := hL.trans hly.symm
        rw [←hpp, ←hCX, hrouted2] at hrouted
        rw [←hpp, ←hL, ←hN] at hyt
        rw [←hpp, ←hL] at hresv
        rw [hresv2] at hresv
        rw [←hP, ←hL, ←hX, ←hY, ←hT, ←hN, ←hR] at hroutes
        exact ⟨ranks, rankBudget, p0, labeled, ord, placed, routed, yt,
          { hRs := hrs, hRank := Or.inl ⟨rr, rfl, hrr, hr1, hcb, hrb⟩,
            hNorm := hp0, hLabels := hlab, hCoord := rfl,
            hMin := Or.inl ⟨rfl, rfl⟩, hOrd := hord, hLabelWidths := rfl,
            hPlaced := Or.inl ⟨rfl, hPlaced1, hPlaced2, hnil.symm, rfl⟩,
            hProxy := hrouted, hDrop := hP.symm,
            hLanes := Or.inl ⟨hres, hlanes⟩, hYt := hyt,
            hYsMid := rfl, hReserve := hresv, hRoutes := hroutes,
            hRouting := by rw [hN]; exact hRt.symm,
            hCoordProper := by rw [←hpp] at hCP; exact hCP,
            hCoordYs := hCY, hBudget := hB, hExact := hE }⟩
      | false =>
        have hnil : ([] : List (Option Int)) = placed.2.2.1 := by
          have hplacedt := Except.ok.inj hplaced
          exact congrArg (fun t => t.2.2.1) hplacedt
        rw [←hnil] at hres
        simp at hres

/-- Stages for runs with component regions: ranking rewrites the graph via
`rankEquivalentR`, the minimum comes from `constrainR`, placement is
`crossCoordsR` (which may rewrite the proper graph), and reversed edges park
at reserved lanes when `reserved` is nonempty. -/
private theorem rrspec_stages_some {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (rm : ComponentRegions)
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    (hS : newComponentRegions spec P inp cg = .ok (some rm)) :
    ∃ (ranks : List Int) (rankBudget : Bool) (p0 labeled : Proper)
      (ord : OrderResult) (m : RegionConstraints)
      (placed : List Int × List (List Nat) × List (Option Int) × Proper)
      (routed : Proper × List Int) (yt : List Int × List Int),
      ComponentRunRStages P exact spec inp cg labels orderOptions cg' run
        (some rm) ranks rankBudget p0 labeled
        (coordinateGraphR P exact spec labeled) (some m) ord
        (cg'.edges.map fun edge =>
          (stackSize cg'.slot (routeLabels labels edge.decl)).width)
        placed.2.2.1 placed.2.2.2 routed.1 yt
        (proxyYs placed.2.2.2 run.layers yt.2 yt.1) := by
  unfold componentRunR at h
  obtain ⟨rs, hrs, h⟩ := bind_ok h
  have hrsS : rs = some rm := Except.ok.inj (hrs.symm.trans hS)
  subst hrsS
  dsimp only at h
  obtain ⟨ranked, hranked, h⟩ := bind_ok h
  cases ranked with
  | mk ranks rest =>
    cases rest with
    | mk cg1 rankBudget =>
      dsimp only at h
      obtain ⟨p0, hp0, h⟩ := bind_ok h
      obtain ⟨labeled, hlab, h⟩ := bind_ok h
      obtain ⟨m, hmc, h⟩ := bind_ok h
      obtain ⟨minv, hmin, h⟩ := bind_ok h
      obtain ⟨ord, hord, h⟩ := bind_ok h
      have hminv : minv = some m := (Except.ok.inj hmin).symm
      subst hminv
      dsimp only at h
      obtain ⟨m0, hm0, h⟩ := bind_ok h
      have hm0v : m = m0 := Except.ok.inj hm0
      subst hm0v
      obtain ⟨placed, hcross, h⟩ := bind_ok h
      obtain ⟨routed, hrouted, h⟩ := bind_ok h
      cases hres : placed.2.2.1.isEmpty with
      | true =>
        rw [hres, ite_eq_left rfl] at h
        obtain ⟨lanes_1, hlanes, h⟩ := bind_ok h
        obtain ⟨yt, hyt, h⟩ := bind_ok h
        obtain ⟨resv, hresv, h⟩ := bind_ok h
        obtain ⟨routes, hroutes, h⟩ := bind_ok h
        have he := Except.ok.inj h
        have hcg : cg' = cg1 := (congrArg Prod.fst he).symm
        subst hcg
        have hP : run.proper = OrderImpl.dropSynthetic routed.1 :=
          (congrArg (fun q : Graph × Run => q.2.proper) he).symm
        have hL : run.layers = placed.2.1 :=
          (congrArg (fun q : Graph × Run => q.2.layers) he).symm
        have hX : run.xs = routed.2 :=
          (congrArg (fun q : Graph × Run => q.2.xs) he).symm
        have hY : run.ys = resv.1 :=
          (congrArg (fun q : Graph × Run => q.2.ys) he).symm
        have hT : run.top = resv.2 :=
          (congrArg (fun q : Graph × Run => q.2.top) he).symm
        have hRt : run.routing = lanes_1.routing :=
          (congrArg (fun q : Graph × Run => q.2.routing) he).symm
        have hR : run.routes = routes :=
          (congrArg (fun q : Graph × Run => q.2.routes) he).symm
        have hB : run.budget = (rankBudget || ord.budgetExhausted) :=
          (congrArg (fun q : Graph × Run => q.2.budget) he).symm
        have hN : run.lanes = lanes_1 :=
          (congrArg (fun q : Graph × Run => q.2.lanes) he).symm
        have hCP : run.coordinateProper = placed.2.2.2 :=
          (congrArg (fun q : Graph × Run => q.2.coordinateProper) he).symm
        have hCX : run.coordinateXs = placed.1 :=
          (congrArg (fun q : Graph × Run => q.2.coordinateXs) he).symm
        have hCY : run.coordinateYs = yt.1 :=
          (congrArg (fun q : Graph × Run => q.2.coordinateYs) he).symm
        have hE : run.exact =
            (cg'.nodes.zipIdx.filterMap fun q =>
              if exact.contains q.1.decl then some q.2 else none) :=
          (congrArg (fun q : Graph × Run => q.2.exact) he).symm
        have hrouted2 : routed = (routed.1, run.xs) := by rw [hX]
        have hresv2 : resv = (run.ys, run.top) := by rw [hY, hT]
        have hpt : placed =
            (run.coordinateXs, run.layers, placed.2.2.1, placed.2.2.2) :=
          Prod.ext hCX.symm (Prod.ext hL.symm (Prod.ext rfl rfl))
        rw [hpt] at hcross
        rw [←hP, ←hL, ←hX, ←hN] at hlanes
        rw [←hCX, hrouted2] at hrouted
        rw [←hL, ←hN] at hyt
        rw [←hL] at hresv
        rw [hresv2] at hresv
        rw [←hP, ←hL, ←hX, ←hY, ←hT, ←hN, ←hR] at hroutes
        exact ⟨ranks, rankBudget, p0, labeled, ord, m, placed, routed, yt,
          { hRs := hrs, hRank := Or.inr ⟨rm, rfl, hranked⟩,
            hNorm := hp0, hLabels := hlab, hCoord := rfl,
            hMin := Or.inr ⟨rm, m, rfl, rfl, hmc⟩,
            hOrd := hord, hLabelWidths := rfl,
            hPlaced := Or.inr ⟨rm, m, rfl, rfl, hcross⟩,
            hProxy := hrouted, hDrop := hP.symm,
            hLanes := Or.inl ⟨hres, hlanes⟩, hYt := hyt,
            hYsMid := rfl, hReserve := hresv, hRoutes := hroutes,
            hRouting := by rw [hN]; exact hRt.symm,
            hCoordProper := hCP, hCoordYs := hCY,
            hBudget := hB, hExact := hE }⟩
      | false =>
        have hne : ¬((false : Bool) = true) := by decide
        rw [hres, ite_eq_right hne] at h
        obtain ⟨lanes_1, hlanes, h⟩ := bind_ok h
        obtain ⟨yt, hyt, h⟩ := bind_ok h
        obtain ⟨resv, hresv, h⟩ := bind_ok h
        obtain ⟨routes, hroutes, h⟩ := bind_ok h
        have he := Except.ok.inj h
        have hcg : cg' = cg1 := (congrArg Prod.fst he).symm
        subst hcg
        have hP : run.proper = OrderImpl.dropSynthetic routed.1 :=
          (congrArg (fun q : Graph × Run => q.2.proper) he).symm
        have hL : run.layers = placed.2.1 :=
          (congrArg (fun q : Graph × Run => q.2.layers) he).symm
        have hX : run.xs = routed.2 :=
          (congrArg (fun q : Graph × Run => q.2.xs) he).symm
        have hY : run.ys = resv.1 :=
          (congrArg (fun q : Graph × Run => q.2.ys) he).symm
        have hT : run.top = resv.2 :=
          (congrArg (fun q : Graph × Run => q.2.top) he).symm
        have hRt : run.routing = lanes_1.routing :=
          (congrArg (fun q : Graph × Run => q.2.routing) he).symm
        have hR : run.routes = routes :=
          (congrArg (fun q : Graph × Run => q.2.routes) he).symm
        have hB : run.budget = (rankBudget || ord.budgetExhausted) :=
          (congrArg (fun q : Graph × Run => q.2.budget) he).symm
        have hN : run.lanes = lanes_1 :=
          (congrArg (fun q : Graph × Run => q.2.lanes) he).symm
        have hCP : run.coordinateProper = placed.2.2.2 :=
          (congrArg (fun q : Graph × Run => q.2.coordinateProper) he).symm
        have hCX : run.coordinateXs = placed.1 :=
          (congrArg (fun q : Graph × Run => q.2.coordinateXs) he).symm
        have hCY : run.coordinateYs = yt.1 :=
          (congrArg (fun q : Graph × Run => q.2.coordinateYs) he).symm
        have hE : run.exact =
            (cg'.nodes.zipIdx.filterMap fun q =>
              if exact.contains q.1.decl then some q.2 else none) :=
          (congrArg (fun q : Graph × Run => q.2.exact) he).symm
        have hrouted2 : routed = (routed.1, run.xs) := by rw [hX]
        have hresv2 : resv = (run.ys, run.top) := by rw [hY, hT]
        have hpt : placed =
            (run.coordinateXs, run.layers, placed.2.2.1, placed.2.2.2) :=
          Prod.ext hCX.symm (Prod.ext hL.symm (Prod.ext rfl rfl))
        rw [hpt] at hcross
        rw [←hP, ←hL, ←hX, ←hN] at hlanes
        rw [←hCX, hrouted2] at hrouted
        rw [←hL, ←hN] at hyt
        rw [←hL] at hresv
        rw [hresv2] at hresv
        rw [←hP, ←hL, ←hX, ←hY, ←hT, ←hN, ←hR] at hroutes
        exact ⟨ranks, rankBudget, p0, labeled, ord, m, placed, routed, yt,
          { hRs := hrs, hRank := Or.inr ⟨rm, rfl, hranked⟩,
            hNorm := hp0, hLabels := hlab, hCoord := rfl,
            hMin := Or.inr ⟨rm, m, rfl, rfl, hmc⟩,
            hOrd := hord, hLabelWidths := rfl,
            hPlaced := Or.inr ⟨rm, m, rfl, rfl, hcross⟩,
            hProxy := hrouted, hDrop := hP.symm,
            hLanes := Or.inr ⟨hres, hlanes⟩, hYt := hyt,
            hYsMid := rfl, hReserve := hresv, hRoutes := hroutes,
            hRouting := by rw [hN]; exact hRt.symm,
            hCoordProper := hCP, hCoordYs := hCY,
            hBudget := hB, hExact := hE }⟩

/-- Every `componentRunR` run exhibits its stage witnesses: dispatch on the
resolved component regions. -/
theorem componentRunR_stages {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    ∃ (rs : Option ComponentRegions) (ranks : List Int) (rankBudget : Bool)
      (p0 labeled pCoord : Proper) (minimum : Option RegionConstraints)
      (ord : OrderResult) (labelWidths : List Int)
      (reserved : List (Option Int)) (placedProper q0 : Proper)
      (yt : List Int × List Int) (ysMid : List Int),
      ComponentRunRStages P exact spec inp cg labels orderOptions cg' run rs
        ranks rankBudget p0 labeled pCoord minimum ord labelWidths reserved
        placedProper q0 yt ysMid := by
  have hfull := h
  unfold componentRunR at h
  obtain ⟨rs, hrs, _hcont⟩ := bind_ok h
  cases rs with
  | none =>
    obtain ⟨ranks, rankBudget, p0, labeled, ord, placed, routed, yt, hs⟩ :=
      rrspec_stages_none hfull hrs
    exact ⟨none, ranks, rankBudget, p0, labeled,
      coordinateGraphR P exact spec labeled, none, ord,
      cg'.edges.map fun edge =>
        (stackSize cg'.slot (routeLabels labels edge.decl)).width,
      placed.2.2.1, coordinateGraphR P exact spec labeled, routed.1, yt,
      proxyYs (coordinateGraphR P exact spec labeled) run.layers yt.2 yt.1,
      hs⟩
  | some rm =>
    obtain ⟨ranks, rankBudget, p0, labeled, ord, m, placed, routed, yt, hs⟩ :=
      rrspec_stages_some rm hfull hrs
    exact ⟨some rm, ranks, rankBudget, p0, labeled,
      coordinateGraphR P exact spec labeled, some m, ord,
      cg'.edges.map fun edge =>
        (stackSize cg'.slot (routeLabels labels edge.decl)).width,
      placed.2.2.1, placed.2.2.2, routed.1, yt,
      proxyYs placed.2.2.2 run.layers yt.2 yt.1, hs⟩

/-- The region run equations, one per stage, for both region cases. This is
the `componentRunR` analogue of `componentRunX_spec`, with the ranking,
minimum, placement, and lane stages split on `rs` and `reserved.isEmpty`;
the `some`-case coordinate output `pCoord` and placement output
`placedProper = run.coordinateProper` are kept separate (they coincide iff
`rs = none`). -/
theorem componentRunR_specR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    ∃ (rs : Option ComponentRegions) (ranks : List Int) (rankBudget : Bool)
      (p0 labeled pCoord : Proper) (minimum : Option RegionConstraints)
      (ord : OrderResult) (labelWidths : List Int)
      (reserved : List (Option Int)) (placedProper q0 : Proper)
      (yt : List Int × List Int) (ysMid : List Int),
      newComponentRegions spec P inp cg = .ok rs ∧
      ((∃ rr : RankImpl.RankResult, rs = none ∧
        rankWithBudget (Compound.rankingGraph cg) = .ok rr ∧ ranks = rr.ranks ∧
        cg' = cg ∧ rankBudget = rr.budgetExhausted) ∨
        (∃ rm : ComponentRegions,
          rs = some rm ∧ rankEquivalentR rm cg = .ok (ranks, cg', rankBudget))) ∧
      normalize cg' ranks = .ok p0 ∧
      Labels.addLabelNodes cg' p0 (componentLabels cg' labels) = .ok labeled ∧
      coordinateGraphR P exact spec labeled = pCoord ∧
      ((rs = none ∧ minimum = none) ∨ (∃ rm : ComponentRegions,
        ∃ m : RegionConstraints, rs = some rm ∧ minimum = some m ∧
        constrainR rm P pCoord = .ok m)) ∧
      orderWithBudget pCoord orderOptions = .ok ord ∧
      labelWidths = (cg'.edges.map fun edge =>
        (stackSize cg'.slot (routeLabels labels edge.decl)).width) ∧
      ((rs = none ∧ crossCoordsClusterWith P.nodeGap P.clusterPad pCoord ord.layers =
        .ok run.coordinateXs ∧ run.layers = ord.layers ∧ reserved = [] ∧
        placedProper = pCoord) ∨ (∃ rm : ComponentRegions,
        ∃ m : RegionConstraints, rs = some rm ∧ minimum = some m ∧
        crossCoordsR P rm cg' labels pCoord m ord.layers =
          .ok (run.coordinateXs, run.layers, reserved, placedProper))) ∧
      proxyWidths placedProper run.coordinateXs = .ok (q0, run.xs) ∧
      OrderImpl.dropSynthetic q0 = run.proper ∧
      ((reserved.isEmpty = true ∧ RouteImpl.routeWithLanes P.slot run.proper
        run.layers run.xs (cg'.edges.map (·.reversed)) labelWidths =
        .ok run.lanes) ∨ (reserved.isEmpty = false ∧ routeWithLanesR P.slot
        run.proper run.layers run.xs (cg'.edges.map (·.reversed)) labelWidths
        reserved = .ok run.lanes)) ∧
      rankCoordsWith P.rankGap P.slot placedProper run.layers
        (run.lanes.routing.gaps.map (·.slots)) = .ok yt ∧
      proxyYs placedProper run.layers yt.2 yt.1 = ysMid ∧
      reserveExactRanks cg' exact labels placedProper run.layers ysMid yt.2 =
        .ok (run.ys, run.top) ∧
      RouteImpl.routePointsWithLanes P.slot run.proper run.layers run.xs run.ys
        run.top run.lanes = .ok run.routes ∧
      run.lanes.routing = run.routing ∧
      run.coordinateProper = placedProper ∧
      run.coordinateYs = yt.1 ∧
      run.budget = (rankBudget || ord.budgetExhausted) ∧
      run.exact = (cg'.nodes.zipIdx.filterMap fun q =>
        if exact.contains q.1.decl then some q.2 else none) := by
  obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
    reserved, placedProper, q0, yt, ysMid, hs⟩ := componentRunR_stages h
  exact ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
    reserved, placedProper, q0, yt, ysMid, hs.hRs, hs.hRank, hs.hNorm,
    hs.hLabels, hs.hCoord, hs.hMin, hs.hOrd, hs.hLabelWidths, hs.hPlaced,
    hs.hProxy, hs.hDrop, hs.hLanes, hs.hYt, hs.hYsMid, hs.hReserve, hs.hRoutes,
    hs.hRouting, hs.hCoordProper, hs.hCoordYs, hs.hBudget, hs.hExact⟩

end PipelineImpl
end Layered
end Elegant

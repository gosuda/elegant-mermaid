import Elegant.Layered.Pipeline

set_option autoImplicit false

/-! Layered family with exact boxes. Exact boxes retain the adapter's size, route self-loops
through distinct boundary ports, and reserve the loop footprint below their rank. Declaration
indices identify exact boxes before component extraction; `Run.exact` holds component-local
indices for scene assembly. -/

namespace Elegant
namespace Layered
namespace PipelineImpl


def exactGraph (P : Params) (exactIds : List String) (inp : Input) (o : Options)
    (labels : List MeasuredLabel) (g : Graph) : Except LayoutError Graph := do
  let nodes ← g.nodes.mapM fun node => do
    match inp.boxes[node.decl]? with
    | none => pure node
    | some box =>
      if !exactIds.contains box.id && !(box.role == .group && inp.fixedSizes.any (·.1 == box.id))
      then pure node
      else
        match inp.fixedSizes.find? (·.1 == box.id) with
        | none => throw .domain
        | some fixed =>
          let size := orientNode o.direction { node with w := fixed.2.w, h := fixed.2.h }
          let extent := Loops.exactExtent P.slot (loopSizes g.edges labels node.decl P.slot)
          if extent < 0 then throw .domain
          if I32_MAX < extent ∨ I32_MAX < size.w + 2 * extent then throw .overflow
          pure { size with loopExtent := extent.toNat }
  pure { g with nodes := nodes }

def reserveExactRanks (cg : Graph) (exact : List Nat) (labels : List MeasuredLabel)
    (p : Proper) (layers : List (List Nat)) (ys top : List Int) :
    Except LayoutError (List Int × List Int) := do
  let heights := layers.map fun layer =>
    layer.foldl (fun h v => max h (RouteImpl.nodeH p v)) 0
  let extra := cg.nodes.zipIdx.foldl (fun acc q =>
    if !exact.contains q.1.decl then acc
    else
      let sizes := loopSizes cg.edges labels q.2 cg.slot
      if sizes.isEmpty then acc
      else
        let rank := (p.rank.getD q.2 0).toNat
        let reserved := max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes)
        let needed := ys.getD q.2 0 + reserved - top.getD rank 0 - heights.getD rank 0
        acc.set rank (max (acc.getD rank 0) needed)) (List.replicate top.length 0)
  let shifts := (extra.foldl (fun acc e => (acc.1 + e, acc.2 ++ [acc.1]))
    (0, ([] : List Int))).2
  let top ← top.zipIdx.mapM fun q => Measure.checkedI32 (q.1 + shifts.getD q.2 0)
  let ys ← ys.zipIdx.mapM fun q =>
    Measure.checkedI32 (q.1 + shifts.getD ((p.rank.getD q.2 0).toNat) 0)
  pure (ys, top)
def sizeProperPortsX (P : Params) (exact : List Nat) (p : Proper) : Proper :=
  { p with nodes := p.nodes.zipIdx.map fun q =>
    if q.1.dummy || q.1.node.border != 0 || exact.contains q.1.node.decl then q.1
    else
      let incoming := ((p.edges.filter fun edge => edge.head == q.2).map (·.tail)).eraseDups.length
      let outgoing := ((p.edges.filter fun edge => edge.tail == q.2).map (·.head)).eraseDups.length
      { q.1 with node := { q.1.node with
        w := max q.1.node.w ((((max incoming outgoing : Nat) + 1 : Nat) : Int) * P.portGap) } } }

def coordinateGraphX (P : Params) (exact : List Nat) (p : Proper) : Proper :=
  materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW))

def componentRunX (P : Params) (exact : List Nat) (cg : Graph) (labels : List MeasuredLabel := [])
    (orderOptions : OrderOptions := {}) : Except LayoutError Run := do
  let rr ← rankWithBudget (Compound.rankingGraph cg)
  let p0 ← normalize cg rr.ranks
  let p ← Labels.addLabelNodes cg p0 (componentLabels cg labels)
  let p := coordinateGraphX P exact p
  let ord ← orderWithBudget p orderOptions
  let coordinateXs ← crossCoordsClusterWith P.nodeGap P.clusterPad p ord.layers
  let routed ← proxyWidths p coordinateXs
  let routeProper := OrderImpl.dropSynthetic routed.1
  let xs := routed.2
  let lanes ← RouteImpl.routeWithLanes P.slot routeProper ord.layers xs
    (cg.edges.map (·.reversed))
    (cg.edges.map fun edge => (stackSize cg.slot (routeLabels labels edge.decl)).width)
  let r := lanes.routing
  let yt ← rankCoordsWith P.rankGap P.slot p ord.layers (r.gaps.map (·.slots))
  let ys := proxyYs p ord.layers yt.2 yt.1
  let (ys, top) ← reserveExactRanks cg exact labels p ord.layers ys yt.2
  let routes ← RouteImpl.routePointsWithLanes P.slot routeProper ord.layers xs ys top lanes
  pure ⟨routeProper, ord.layers, xs, ys, top, r, routes,
    rr.budgetExhausted || ord.budgetExhausted, lanes, p, coordinateXs, yt.1,
    (cg.nodes.zipIdx.filterMap fun q => if exact.contains q.1.decl then some q.2 else none)⟩

/-- The decl indices of the boxes that keep their size: the listed ids and every collapsed
child frame. -/
def exactDecls (exactIds : List String) (inp : Input) : List Nat :=
  inp.boxes.zipIdx.filterMap fun q =>
    if exactIds.contains q.1.id || (q.1.role == .group && inp.fixedSizes.any (·.1 == q.1.id))
    then some q.2 else none

def componentTrialX (P : Params) (exactIds : List String) (inp : Input) (o : Options) (g : Graph)
    (comp : List Nat) (labels : List MeasuredLabel) (index : Nat) :
    Except LayoutError (Portfolio.Candidate (Graph × Run)) := do
  let cg := componentCandidate g comp index
  let run ← componentRunX P (exactDecls exactIds inp) cg labels (candidateOrder index)
  let scene ← componentScene P inp o cg run labels (@placeComponentExact)
  pure { value := (cg, run), scene := scene, budgetExhausted := run.budget }

def layoutComponentX (P : Params) (exactIds : List String) (inp : Input) (o : Options)
    (g : Graph) (acc : Acc) (comp : List Nat) (labels : List MeasuredLabel := []) :
    Except LayoutError Acc := do
  let chosen ← Portfolio.portfolio o.thoroughness (componentTrialX P exactIds inp o g comp labels)
  let result ← placePart comp chosen.value.1 chosen.value.2 P acc labels (@placeComponentExact) true
  let childArea := inp.fixedAreas.foldl (fun total child =>
    if chosen.scene.boxes.any (fun box => box.id == child.1) then total + child.2 else total) 0
  let metric ← metricOf o.profile
  let titleAreas ← (inp.boxes.zipIdx.filter fun q =>
    q.1.role == .group && chosen.scene.boxes.any (fun box => box.id == q.1.id)).mapM fun q => do
      let lines ← StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD q.2 q.1.id).toList
      pure ((lines.foldl (fun width line => max width line.width) 0) *
        ((max 1 lines.length : Int) * P.lineH))
  pure { result with
    budget := acc.budget || chosen.budgetExhausted
    parts := acc.parts ++ ((result.parts.drop acc.parts.length).map fun placed =>
      (placed.1, { placed.2 with area := placed.2.area + childArea + titleAreas.sum })) }

def layoutX (exactIds : List String) (inp : Input) (o : Options) : Except LayoutError FamilyResult := do
  let P ← checkedParams o.profile inp.kind
  let m ← metricOf o.profile
  let lines ← boxLines m
    (Measure.wrapTarget m.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0)) inp
  let measured ← measureLabels P m
    (Measure.wrapTarget m.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0)) inp o.direction
  let g ← measuredGraph P inp o lines
  let g ← exactGraph P exactIds inp o measured g
  let start : Acc :=
    ⟨0, 0, 0, Array.replicate inp.boxes.length default, Array.replicate inp.routes.length [],
      Array.replicate inp.labels.length default, false, [], []⟩
  let acc ← (components g).foldlM
    (fun acc comp => layoutComponentX P exactIds inp o g acc comp measured) start
  let acc ← packAcc P o acc
  let scene := sceneOf P inp o lines acc measured
  if I32_MAX < scene.canvas.w ∨ I32_MAX < scene.canvas.h then throw .overflow
  else pure ⟨scene, acc.budget, acc.parts.foldl (fun area part => area + part.2.area) 0⟩

def layoutRecursiveB (base : Input → Options → Except LayoutError FamilyResult) : Nat → Input → Options →
    Except LayoutError FamilyResult
  | 0, inp, o => base inp o
  | fuel + 1, inp, o => do
    match inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) with
    | none => base inp o
    | some group =>
      let P ← checkedParams o.profile inp.kind
      let metric ← metricOf o.profile
      let childInput := selectInput inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id
      let child ← layoutRecursiveB base fuel childInput
        { o with direction := directionOf group.direction }
      let index := inp.boxes.findIdx? (fun box => box.id == group.id)
      let title := inp.texts.getD (index.getD 0) group.id
      let titleLines ← StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0)) title.toList
      let titleWidth := titleLines.foldl (fun width line => max width line.width) 0
      let titleHeight := (max 1 titleLines.length : Int) * P.lineH
      let margin := P.canvasMargin
      let size := childFrameSize group.direction P.clusterPad titleWidth titleHeight
        ⟨child.scene.canvas.w - 2 * margin, child.scene.canvas.h - 2 * margin⟩
      let parentInput := selectInput inp
        (fun box => !Compound.inside inp.boxes group.id box.id)
      let parentInput := { parentInput with
        fixedSizes := parentInput.fixedSizes ++ [(group.id, size)]
        fixedChildren := parentInput.fixedChildren ++ [(group.id, child.scene)]
        fixedAreas := parentInput.fixedAreas ++ [(group.id, child.itemArea)] }
      let parent ← layoutRecursiveB base fuel parentInput o
      expandChild P inp o group titleHeight parent child

def layoutRecursiveX (exactIds : List String) : Nat → Input → Options →
    Except LayoutError FamilyResult :=
  layoutRecursiveB (layoutX exactIds)

end PipelineImpl

/-- The family entry for a base layout of one recursion level. -/
def layoutFamilyB (base : Input → Options → Except LayoutError FamilyResult) (inp : Input)
    (o : Options) : Except LayoutFailure FamilyResult :=
  if o.limits.maxNodes < inp.boxes.length then
    .error (.tooLarge o.limits.maxNodes inp.boxes.length)
  else if o.limits.maxEdges < inp.routes.length then
    .error (.tooLarge o.limits.maxEdges inp.routes.length)
  else if o.limits.maxTextBytes < inputTextBytes inp then
    .error (.tooLarge o.limits.maxTextBytes (inputTextBytes inp))
  else if !modelWellFormed (inputModel inp o) then .error (.geometry .domain)
  else
    match PipelineImpl.layoutRecursiveB base (inp.boxes.length + 1) inp o with
    | .error error => .error (.geometry error)
    | .ok result => .ok result

/-- The family entry with the ids of the boxes that keep their size. -/
def layoutFamilyX (exactIds : List String) (inp : Input) (o : Options) :
    Except LayoutFailure FamilyResult :=
  layoutFamilyB (PipelineImpl.layoutX exactIds) inp o

end Layered
end Elegant

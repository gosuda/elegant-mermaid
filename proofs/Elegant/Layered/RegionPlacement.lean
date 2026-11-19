import Elegant.Layered.RegionModel

set_option autoImplicit false

/-! Concurrent-region placement. The region tree pins the layer order (regions of one set sit
adjacent under their parent), the buckets gather the nodes and reversed lanes each frame must
hold, and the allocation walks the tree once to place every frame, its members and its lanes
inside the reserved widths (Go's `regions_placement.go`). `componentRunR` threads the region
model through the phases of `PipelineImpl.componentRunX`, and `routeWithLanesR` places a
reversed edge at its reserved lane instead of the outer fallback. -/

namespace Elegant
namespace Layered
namespace RegionImpl

open PipelineImpl

/-! ### The region tree and the pinned order -/

/-- Go's `regionChildren`: the cluster forest with each set's regions grouped in place. -/
def regionChildren (rm : ComponentRegions) : Except LayoutError (List (List Nat)) := do
  let n := rm.clusters.length
  let base := (List.range n).foldl (fun ch g =>
    let par := parentGroup rm g
    setAt ch par (ch.getD par [] ++ [g])) (List.replicate (n + 1) [])
  rm.sets.zipIdx.foldlM (fun acc q =>
    let s := q.1
    let owner := s.regions.foldl (fun ow r => setAt ow r q.2) (List.replicate n n)
    let owned (g : Nat) : Bool := owner.getD g n == q.2
    let cs := acc.getD s.parent []
    match cs.findIdx? owned with
    | none => throw .domain
    | some first =>
      let kept := cs.filter fun g => !owned g
      pure (setAt acc s.parent (kept.take first ++ s.regions ++ kept.drop first))) base

/-- Go's `childPreorder`: root first, children in list order. -/
def childPreorderGo (children : List (List Nat)) : Nat → List Nat → List Nat → List Nat
  | 0, _, order => order
  | fuel + 1, stack, order =>
    match stack.getLast? with
    | none => order
    | some g =>
      childPreorderGo children fuel
        (stack.dropLast ++ (children.getD g []).reverse) (order ++ [g])

/-- The cluster of every proper node, or the root for the unparented ones. -/
def nodeGroupsOf (rm : ComponentRegions) (p : Proper) : Except LayoutError (List Nat) :=
  p.nodes.zipIdx.mapM fun q =>
    match q.1.node.clusterPath.getLast? with
    | none => pure rm.clusters.length
    | some decl =>
      match clusterOfDecl rm decl with
      | some k => pure k
      | none => throw .domain

def pinPrefixes (children : List (List Nat)) (order : List Nat) : List (List Int) :=
  order.foldl (fun pre g =>
    (children.getD g []).zipIdx.foldl (fun pre q =>
      setAt pre q.1 (pre.getD g [] ++ [((q.2 : Int) + 2)])) pre)
    (List.replicate children.length [])

def kindOf (border : Int) : Int :=
  if border == -1 then 0 else if border == 1 then 9223372036854775807 else 1

def lexLe : List Int → List Int → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a != b then a < b else lexLe as bs

/-- Go's `regionTree.pin`: stable-sort every layer by the region-tree prefixes and the border
kind. -/
def pinLayers (p : Proper) (nodeGroups : List Nat) (children : List (List Nat))
    (order : List Nat) (layers : List (List Nat)) : List (List Nat) :=
  let pre := pinPrefixes children order
  let keys := p.nodes.zipIdx.map fun q =>
    pre.getD (nodeGroups.getD q.2 0) [] ++ [kindOf q.1.node.border]
  layers.map fun layer =>
    layer.mergeSort fun a b => lexLe (keys.getD a []) (keys.getD b [])

def chainUp (rm : ComponentRegions) (root : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, _ => []
  | fuel + 1, g, acc =>
    if g == root then acc else chainUp rm root fuel (parentGroup rm g) (g :: acc)

/-- Go's `regionTree.edgeOwner`: the deepest cluster holding both endpoints; `chainUp` lists the
path outermost first, so the deepest shared cluster is the last shared entry. -/
def edgeOwnerOf (rm : ComponentRegions) (nodeGroups : List Nat) (root : Nat) (a b : Nat) : Nat :=
  let seen := chainUp rm root (root + 1) (nodeGroups.getD a root) []
  let chain := chainUp rm root (root + 1) (nodeGroups.getD b root) []
  (chain.reverse.find? fun g => seen.contains g).getD root

/-! ### Buckets -/

structure RegionBuckets where
  members : List (List Nat)
  widths : List Int
  low : List Int
  high : List Int
  lanes : List (List Nat)
  laneWidth : List Int
  loopWidth : List Int
deriving Repr

def newRegionBuckets (rm : ComponentRegions) (cg : Graph) (p : Proper)
    (nodeGroups : List Nat) (labelWidths : List Int) (x : List Int) : RegionBuckets :=
  let root := rm.clusters.length
  let n := root + 1
  let empty : RegionBuckets :=
    { members := List.replicate n [], widths := List.replicate n 0,
      low := List.replicate n 2147483647, high := List.replicate n (-2147483648),
      lanes := List.replicate n [], laneWidth := List.replicate n 0,
      loopWidth := List.replicate n 0 }
  let gathered := p.nodes.zipIdx.foldl (fun acc q =>
    if q.1.node.border != 0 then acc
    else
      let owner := nodeGroups.getD q.2 0
      let width := q.1.node.w + 2 * (q.1.node.loopExtent : Int)
      let left := RouteImpl.xAt x q.2 - Int.tdiv width 2
      let right := left + width
      { acc with
        low := setAt acc.low owner (min (acc.low.getD owner 2147483647) left)
        high := setAt acc.high owner (max (acc.high.getD owner (-2147483648)) right)
        members := setAt acc.members owner (acc.members.getD owner [] ++ [q.2]) }) empty
  let widths := (List.range n).map fun g =>
    if (gathered.members.getD g []).isEmpty then 0
    else gathered.high.getD g 0 - gathered.low.getD g 0
  let loopWidth := rm.clusters.zipIdx.foldl (fun lw q =>
    setAt lw q.2 (q.1.extent : Int)) (List.replicate n 0)
  let withLanes := cg.edges.zipIdx.foldl (fun acc q =>
    if !q.1.reversed || q.1.tail == q.1.head then acc
    else
      let owner := edgeOwnerOf rm nodeGroups root q.1.tail q.1.head
      if owner == root then acc
      else
        { acc with
          lanes := setAt acc.lanes owner (acc.lanes.getD owner [] ++ [q.2])
          laneWidth := setAt acc.laneWidth owner
            (max (acc.laneWidth.getD owner 0) (labelWidths.getD q.2 0)) }) gathered
  { withLanes with widths := widths, loopWidth := loopWidth }

def laneExtentOf (b : RegionBuckets) (slot : Int) (group : Nat) : Int :=
  (2 * slot + b.laneWidth.getD group 0) * ((b.lanes.getD group []).length : Int)

def regionInsetOf (P : Params) : Int := P.clusterPad + P.clusterBorderW

/-! ### Width reservation and allocation -/

structure RegionPlacement where
  rm : ComponentRegions
  p : Proper
  children : List (List Nat)
  order : List Nat
  buckets : RegionBuckets
  minimum : RegionConstraints
deriving Repr

def reserveWidths (pl : RegionPlacement) (P : Params) : List Int :=
  let root := pl.rm.clusters.length
  let footprints := pl.rm.clusters.map fun c => c.titleW
  let inset := regionInsetOf P
  pl.order.reverse.foldl (fun widths g =>
    let own := pl.buckets.widths.getD g 0
    let childSum := (pl.children.getD g []).foldl (fun w c => w + widths.getD c 0) own
    let width := childSum + laneExtentOf pl.buckets P.slot g
    let width :=
      if g != root then
        max (max (width + 2 * inset) (pl.minimum.widths.getD g 0))
          ((footprints.getD g 0) + 2 * inset)
      else width
    setAt widths g (width + pl.buckets.loopWidth.getD g 0))
    (List.replicate (root + 1) 0)

structure RegionAllocation where
  widths : List Int
  lefts : List Int
  lanes : List (Option Int)
deriving Repr

def allocateGroup (pl : RegionPlacement) (P : Params) (widths : List Int) (group : Nat)
    (state : List Int × List Int × List (Option Int)) :
    Except LayoutError (List Int × List Int × List (Option Int)) := do
  let root := pl.rm.clusters.length
  let (x, lefts, lanes) := state
  let start := (lefts.getD group 0) +
    (if group != root then pl.minimum.origins.getD group 0 else 0)
  let cursor0 := start + pl.buckets.widths.getD group 0
  let x :=
    if (pl.buckets.members.getD group []).isEmpty then x
    else
      let shift := start - pl.buckets.low.getD group 0
      (pl.buckets.members.getD group []).foldl (fun x v => setAt x v (x.getD v 0 + shift)) x
  let placed ← (pl.children.getD group []).foldlM (fun acc child =>
      pure (acc.1 + widths.getD child 0, setAt acc.2 child acc.1)) (cursor0, lefts)
  let inset := regionInsetOf P
  let cursor :=
    if group != root && !(pl.buckets.lanes.getD group []).isEmpty then
      (placed.2.getD group 0) + widths.getD group 0 - pl.buckets.loopWidth.getD group 0 -
        inset - laneExtentOf pl.buckets P.slot group
    else placed.1
  let lanes ← (pl.buckets.lanes.getD group []).foldlM (fun acc edge => do
      let cursor := acc.2 + P.slot
      if I32_MAX < cursor then throw .overflow
      else
        pure (setAt acc.1 edge (some cursor),
          cursor + P.slot + pl.buckets.laneWidth.getD group 0))
    (lanes, cursor)
  pure (x, placed.2, lanes.1)

def allocatePl (pl : RegionPlacement) (P : Params) (x : List Int) :
    Except LayoutError (RegionAllocation × List Int) := do
  let widths := reserveWidths pl P
  let root := pl.rm.clusters.length
  let out ← pl.order.foldlM (fun state g => allocateGroup pl P widths g state)
    (x, List.replicate (root + 1) 0, List.replicate (pl.p.chains.length) none)
  pure (⟨widths, out.2.1, out.2.2⟩, out.1)

/-! ### Frames and ports -/

def regionFrames (pl : RegionPlacement) (P : Params) (alloc : RegionAllocation)
    (x : List Int) : List Int :=
  pl.rm.clusters.zipIdx.foldl (fun x q =>
    let c := q.1
    let left := alloc.lefts.getD q.2 0
    let frameRight := left + alloc.widths.getD q.2 0 - pl.buckets.loopWidth.getD q.2 0
    let center := left + Int.tdiv (frameRight - left) 2
    let x := pl.p.nodes.zipIdx.foldl (fun x nq =>
      if nq.1.node.clusterPath.getLast? != some c.decl then x
      else
        match nq.1.node.border with
        | -1 => setAt x nq.2 (left + Int.tdiv P.clusterBorderW 2)
        | 1 => setAt x nq.2 (frameRight - P.clusterBorderW + Int.tdiv P.clusterBorderW 2)
        | 3 => setAt x nq.2 center
        | _ => x) x
    setAt (setAt x c.top center) c.bottom center) x

def clusterPortR (pl : RegionPlacement) (clusterIdx : Nat) (node : Nat) (x : List Int) :
    Except LayoutError (List Int) := do
  let c := pl.rm.clusters.getD clusterIdx default
  let rank := rk pl.p.rank node
  let found : Option Nat × Option Nat :=
    pl.p.nodes.zipIdx.foldl (fun acc q =>
      if q.1.node.clusterPath.getLast? != some c.decl || rk pl.p.rank q.2 != rank then acc
      else
        match q.1.node.border with
        | -1 => (some q.2, acc.2)
        | 1 => (acc.1, some q.2)
        | _ => acc) (none, none)
  match found with
  | (some l, some r) =>
    let lo := RouteImpl.xAt x l - Int.tdiv (RouteImpl.nodeW pl.p l) 2
    let hi := RouteImpl.xAt x r - Int.tdiv (RouteImpl.nodeW pl.p r) 2 + RouteImpl.nodeW pl.p r
    if hi < lo then throw .domain
    else pure (setAt x node (lo + Int.tdiv (hi - lo) 2))
  | _ => throw .domain

/-- Go's `reservedPorts`: recentre the frame anchors on their border nodes and raise the top
node to the title or loop footprint. -/
def reservedPortsR (pl : RegionPlacement) (cg : Graph) (labels : List MeasuredLabel)
    (x : List Int) : Except LayoutError (List Int × Proper) := do
  let out ← pl.rm.clusters.zipIdx.foldlM (fun acc q => do
    let c := q.1
    let footprint := max c.titleH
      (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
    if c.titleW < 0 ∨ footprint < 0 then throw .domain
    else
      let x ← clusterPortR pl q.2 c.top acc.1
      let x ← clusterPortR pl q.2 c.bottom x
      let top := acc.2.getD c.top default
      let nodes := acc.2.set! c.top
        { top with node := { top.node with
            h := max (RouteImpl.nodeH pl.p c.top) footprint } }
      pure (x, nodes)) (x, pl.p.nodes.toArray)
  pure (out.1, { pl.p with nodes := out.2.toList })

def commonSpansR (rm : ComponentRegions) (minimum : RegionConstraints) (p : Proper) :
    Except LayoutError Unit := do
  let n := rm.clusters.length
  let required ← minimum.bands.foldlM (fun req band =>
    if band.right ≤ band.left || band.group ≥ n then throw .domain
    else
      let span := minimum.spans.getD band.group ⟨⟨0, 0⟩, false⟩
      if !span.ok || span.span != band.span then throw .domain
      else pure (setAt req band.group ⟨band.span, true⟩))
    (List.replicate n (⟨⟨0, 0⟩, false⟩ : OptionalSpan))
  rm.clusters.zipIdx.forM fun q =>
    let span := required.getD q.2 (⟨⟨0, 0⟩, false⟩ : OptionalSpan)
    if span.ok &&
        (rk p.rank q.1.top != span.span.first || rk p.rank q.1.bottom != span.span.last) then
      throw .domain
    else pure ()

/-- Go's `componentRegions.crossCoords`: pin, cross, check the spans, then place. -/
def crossCoordsR (P : Params) (rm : ComponentRegions) (cg : Graph)
    (labels : List MeasuredLabel) (p : Proper) (minimum : RegionConstraints)
    (layers : List (List Nat)) :
    Except LayoutError (List Int × List (List Nat) × List (Option Int) × Proper) := do
  let children ← regionChildren rm
  let order := childPreorderGo children (children.length + 1) [rm.clusters.length] []
  if order.length != children.length then throw .domain
  let ngs ← nodeGroupsOf rm p
  let pinned := pinLayers p ngs children order layers
  let x ← crossCoordsClusterWith P.nodeGap P.clusterPad p pinned
  commonSpansR rm minimum p
  let labelWidths := cg.edges.map fun edge =>
    (stackSize cg.slot (routeLabels labels edge.decl)).width
  let buckets := newRegionBuckets rm cg p ngs labelWidths x
  let pl : RegionPlacement := ⟨rm, p, children, order, buckets, minimum⟩
  let (alloc, x) ← allocatePl pl P x
  let x := regionFrames pl P alloc x
  let (x, p) ← reservedPortsR pl cg labels x
  pure (x, pinned, alloc.lanes, p)

/-! ### Region cycle flags (Go's `groupGreedyFlags`) -/

def ggDegrees (edges : List (Nat × Nat)) (n : Nat) (alive : List Nat) :
    List Nat × List Nat :=
  edges.foldl (fun acc e =>
    if alive.contains e.1 && alive.contains e.2 then
      (setAt acc.1 e.1 (acc.1.getD e.1 0 + 1), setAt acc.2 e.2 (acc.2.getD e.2 0 + 1))
    else acc) (List.replicate n 0, List.replicate n 0)

def ggEarliest (decls : List Nat) (alive : List Nat) (deg : List Nat) : Option Nat :=
  alive.foldl (fun best v =>
    if deg.getD v 0 == 0 then
      match best with
      | none => some v
      | some b => if decls.getD v v < decls.getD b b then some v else best
    else best) none

def ggPick (decls : List Nat) (edges : List (Nat × Nat)) (n : Nat) (alive : List Nat) :
    Nat × Bool :=
  let (outD, inD) := ggDegrees edges n alive
  match ggEarliest decls alive outD with
  | some v => (v, true)
  | none =>
    match ggEarliest decls alive inD with
    | some v => (v, false)
    | none =>
      let best := alive.foldl (fun best v =>
        match best with
        | none => some v
        | some b =>
          let dv := (inD.getD v 0 : Int) - (outD.getD v 0 : Int)
          let db := (inD.getD b 0 : Int) - (outD.getD b 0 : Int)
          if dv < db || (dv == db && decls.getD v v < decls.getD b b) then some v else best)
        none
      ((best).getD 0, false)

def ggLoop (decls : List Nat) (edges : List (Nat × Nat)) (n : Nat) : Nat → List Nat →
    List Nat → List Nat → List Nat
  | 0, _, left, right => left ++ right.reverse
  | fuel + 1, alive, left, right =>
    if alive.isEmpty then left ++ right.reverse
    else
      let (v, sink) := ggPick decls edges n alive
      if sink then ggLoop decls edges n fuel (alive.erase v) left (v :: right)
      else ggLoop decls edges n fuel (alive.erase v) (left ++ [v]) right

/-- The greedy feedback order over the shape whose vertices are the plain nodes and the
clusters, Go's `groupGreedy.positions`. -/
def groupGreedyFlags (cg : Graph) : List Bool :=
  let plain := cg.nodes.zipIdx.filter fun q => q.1.border == 0
  let clusters := cg.nodes.zipIdx.filter fun q => q.1.border == -2
  let decls := (plain.map fun q => q.1.decl) ++ clusters.map fun q => q.1.decl
  let slotOf (v : Nat) : Nat :=
    match cg.nodes[v]? with
    | none => 0
    | some node =>
      if node.border == 0 then (plain.findIdx? fun q => q.2 == v).getD 0
      else if node.border == -2 then
        plain.length + (clusters.findIdx? fun q => q.2 == v).getD 0
      else plain.length + (clusters.findIdx? fun q => q.1.decl == node.decl).getD 0
  let edges := cg.edges.map fun e => (slotOf e.tail, slotOf e.head)
  let ordering := ggLoop decls edges decls.length (decls.length + 1)
    (List.range decls.length) [] []
  cg.edges.map fun e =>
    ordering.idxOf (slotOf e.tail) > ordering.idxOf (slotOf e.head)

/-- With regions there is no cycle breaking: the ranking orients the edges itself, and only the
greedy candidate carries preferred flags. -/
def componentCandidateR (spec : Option RegionSpec) (g : Graph) (comp : List Nat) (index : Nat) :
    Graph :=
  match spec with
  | none => componentCandidate g comp index
  | some _ =>
    let raw := componentGraph g comp
    let source := { raw with edges := raw.edges.map Edge.original }
    let flags :=
      if index == 2 then groupGreedyFlags source
      else List.replicate source.edges.length false
    { source with edges := source.edges.zipIdx.map fun q =>
      if flags.getD q.2 false then
        { q.1 with tail := q.1.head, head := q.1.tail, reversed := true }
      else q.1 }

/-! ### Reserved reversed lanes -/

def makeLaneR (slot : Int) (p : Proper) (base : Routing) (x : List Int)
    (reversed : List Bool) (widths : List Int) (reserved : List (Option Int))
    (originals : List Nat) (o index : Nat) : RouteImpl.ReversedLane :=
  let maxLabel := (List.range reversed.length).foldl (fun m i =>
    if reversed.getD i false then max m (widths.getD i 0) else m) 0
  let fallback := (originals.take index).foldl (fun n oo =>
    if (reserved.getD oo none).isNone then n + 1 else n) 0
  let lane := match reserved.getD o none with
    | some lx => lx
    | none => RouteImpl.laneRight p x + slot + (fallback : Int) * (2 * slot + maxLabel)
  let es := RouteImpl.edgesOf p o
  let first := es.headD 0
  let last := es.getLast?.getD 0
  let sg := RouteImpl.gapOf p last
  let tg := RouteImpl.gapOf p first
  { original := o
    lane := lane
    sourceGap := sg
    targetGap := tg
    sourceSegment := (RouteImpl.forwardGapSegments p base reversed sg).length +
      RouteImpl.runGapCount p (originals.take index) sg
    targetSegment := (RouteImpl.forwardGapSegments p base reversed tg).length +
      RouteImpl.runGapCount p (originals.take index) tg + if sg = tg then 1 else 0
    sourceX := base.targetX.getD last 0
    targetX := base.sourceX.getD first 0
    targetRun := base.sourceRun.getD first 0
    sourceNode := (RouteImpl.edgeAt p last).head
    targetNode := (RouteImpl.edgeAt p first).tail }

def plannedLanesR (slot : Int) (p : Proper) (base : Routing) (x : List Int)
    (reversed : List Bool) (widths : List Int) (reserved : List (Option Int)) :
    List RouteImpl.ReversedLane :=
  let originals := RouteImpl.laneOriginals p reversed
  originals.zipIdx.map fun q =>
    makeLaneR slot p base x reversed widths reserved originals q.1 q.2

def routeWithLanesR (slot : Int) (p : Proper) (layers : List (List Nat)) (x : List Int)
    (reversed : List Bool) (labelWidths : List Int) (reserved : List (Option Int)) :
    Except LayoutError RouteImpl.LaneRouting :=
  if slot < 1 then .error .domain
  else match RouteImpl.route p layers x with
  | .error e => .error e
  | .ok base =>
    let runs := plannedLanesR slot p base x reversed labelWidths reserved
    if runs.all fun run => decide (I32_MIN ≤ run.lane ∧ run.lane ≤ I32_MAX) then
      .ok (RouteImpl.assembleLaneRouting p base reversed runs)
    else .error .overflow

/-! ### The region-aware component run -/

/-- Go's `addTitleReservation` under `regionTitles`: the title keeps its own height, never the
loop height. -/
def titleReservationsR (titles : List (Int × Int)) (pad : Int) (p : Proper) : Proper :=
  let tops := p.nodes.zipIdx.filter fun q => q.1.node.border == -2
  { p with
    nodes := (p.nodes.map fun node =>
      if node.node.border == -2 || node.node.border == 2 then
        { node with node := { node.node with w := 0, h := 0 } } else node) ++
      tops.map fun q =>
        { q.1 with node := { q.1.node with border := 3, loopExtent := 0,
                                            h := (titles.getD q.1.node.decl (0, 0)).2 + pad } }
    rank := p.rank ++ tops.map fun q => rk p.rank q.2 }

def coordinateGraphR (P : Params) (exact : List Nat) (spec : Option RegionSpec) (p : Proper) :
    Proper :=
  match spec with
  | none => coordinateGraphX P exact p
  | some s =>
    materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact p)) P.clusterBorderW))

/-- The run and the graph with the final edge orientations: the ranking rewrites the reversed
flags, and the scene assembly reads them. -/
def componentRunR (P : Params) (exact : List Nat) (spec : Option RegionSpec) (inp : Input)
    (cg : Graph) (labels : List MeasuredLabel := [])
    (orderOptions : OrderOptions := {}) : Except LayoutError (Graph × Run) := do
  let rs ← newComponentRegions spec P inp cg
  let ranked ← match rs with
    | none =>
      let rr ← rankWithBudget (Compound.rankingGraph cg)
      pure (rr.ranks, cg, rr.budgetExhausted)
    | some rm => rankEquivalentR rm cg
  let (ranks, cg, rankBudget) := ranked
  let p0 ← normalize cg ranks
  let p ← Labels.addLabelNodes cg p0 (componentLabels cg labels)
  let p := coordinateGraphR P exact spec p
  let minimum ← match rs with
    | none => pure none
    | some rm => do
      let m ← constrainR rm P p
      pure (some m)
  let ord ← orderWithBudget p orderOptions
  let labelWidths := cg.edges.map fun edge =>
    (stackSize cg.slot (routeLabels labels edge.decl)).width
  let placed ← match rs with
    | none =>
      let xs ← crossCoordsClusterWith P.nodeGap P.clusterPad p ord.layers
      pure (xs, ord.layers, [], p)
    | some rm =>
      let m ← match minimum with
        | none => throw .domain
        | some m => pure m
      crossCoordsR P rm cg labels p m ord.layers
  let (coordinateXs, layers, reserved, p) := placed
  let routed ← proxyWidths p coordinateXs
  let routeProper := OrderImpl.dropSynthetic routed.1
  let xs := routed.2
  let lanes ←
    if reserved.isEmpty then
      RouteImpl.routeWithLanes P.slot routeProper layers xs
        (cg.edges.map (·.reversed)) labelWidths
    else
      routeWithLanesR P.slot routeProper layers xs (cg.edges.map (·.reversed)) labelWidths
        reserved
  let r := lanes.routing
  let yt ← rankCoordsWith P.rankGap P.slot p layers (r.gaps.map (·.slots))
  let ys := proxyYs p layers yt.2 yt.1
  let (ys, top) ← reserveExactRanks cg exact labels p layers ys yt.2
  let routes ← RouteImpl.routePointsWithLanes P.slot routeProper layers xs ys top lanes
  pure (cg, ⟨routeProper, layers, xs, ys, top, r, routes,
    rankBudget || ord.budgetExhausted, lanes, p, coordinateXs, yt.1,
    (cg.nodes.zipIdx.filterMap fun q => if exact.contains q.1.decl then some q.2 else none)⟩)

end RegionImpl
end Layered
end Elegant

import Elegant.Model
import Elegant.Scene
import Elegant.Measure
import Elegant.StyledMeasure
import Elegant.Gen.Layoutconst
import Elegant.Layered.Cycles
import Elegant.Layered.Rank
import Elegant.Layered.Normalize
import Elegant.Layered.Order
import Elegant.Layered.Coords
import Elegant.Layered.Route
import Elegant.Layered.Labels
import Elegant.Layered.Loops
import Elegant.Layered.Pack
import Elegant.Layered.Compound
import Elegant.Layered.Portfolio
import Elegant.Layered.FramePorts
import Elegant.Layered.NoteIds
import Elegant.Layered.Straighten

set_option autoImplicit false

/-! Executable layered family. Compound constraints participate only in ranking; semantic
chains, private title reservations, and ordering borders retain separate responsibilities.
Independent child layouts are expanded for candidate scoring and item-area accounting before
component packing. Direction and margin transforms precede the adapter's one cell projection.
Compositional execution witnesses and geometry theorems live in PipelineFacts. -/

namespace Elegant
namespace Layered

structure EdgeOptions where
  markerStart : String
  markerEnd : String
  stroke : String
  minLength : Int
deriving Repr

def EdgeOptions.plain : EdgeOptions := ⟨"", "", "normal", 1⟩

structure Input where
  kind : String
  boxes : List ModelBox
  routes : List ModelRoute
  texts : List String
  edges : List EdgeOptions
  fixedChildren : List (String × Scene) := []
  fixedSizes : List (String × Size) := []
  fixedAreas : List (String × Int) := []
  labels : List ModelLabel := []
deriving Repr

structure FamilyResult where
  scene : Scene
  budgetExhausted : Bool
  itemArea : Int := 0
def candidateOrder (index : Nat) : OrderOptions :=
  match index with
  | 1 => { start := .breadthFirst }
  | 3 => { key := .median }
  | 4 => { start := .reversed }
  | _ => {}

namespace PipelineImpl

structure Params where
  nodePadX : Int
  nodePadY : Int
  nodeBorder : Int
  lineH : Int
  nodeMinW : Int
  nodeMinH : Int
  portGap : Int
  nodeGap : Int
  rankGap : Int
  slot : Int
  cornerRadius : Int
  clusterPad : Int
  clusterBorderW : Int
  wrapWidth : Int
  canvasMargin : Int
deriving Repr, Inhabited

def Params.Valid (P : Params) : Prop :=
  1 ≤ P.nodeGap ∧ 1 ≤ P.rankGap ∧ 1 ≤ P.slot ∧
    Int.fdiv P.slot 2 < Int.fdiv (P.rankGap + 1) 2

instance (P : Params) : Decidable P.Valid := by
  unfold Params.Valid
  infer_instance

/-- Name-keyed lookup in the generated table, for names assembled at run time (`kindConstant`,
the kind adapters). The table is opaque to proofs; a proof that needs a value reads the
`LayoutConst` definitions. -/
def constantOf (profile : Profile) (name : String) : Option Int :=
  (layoutconst.find? fun c => c.name == profile.id ++ "." ++ name).map (·.value)

/-- A per-kind constant `<kind>.<name>`; zero when the kind has none. -/
def kindConstant (profile : Profile) (kind name : String) : Int :=
  (constantOf profile (kind ++ "." ++ name)).getD 0

/-- A positive kind constant overrides a family default; the corpus table holds no other kind. -/
def kindOverride (profile : Profile) (kind name : String) (dflt : Int) : Int :=
  if 0 < kindConstant profile kind name then kindConstant profile kind name else dflt

def canvasMarginOf (profile : Profile) (kind : String) : Int :=
  kindOverride profile kind "diagram_padding" (LayoutConst.canvas_margin.get profile)

def baseParams (profile : Profile) : Option Params :=
  some ⟨LayoutConst.node_pad_x.get profile, LayoutConst.node_pad_y.get profile,
    LayoutConst.node_border.get profile, LayoutConst.line_h.get profile,
    LayoutConst.node_min_w.get profile, LayoutConst.node_min_h.get profile,
    LayoutConst.port_gap.get profile, LayoutConst.node_gap.get profile,
    LayoutConst.rank_gap.get profile, LayoutConst.slot.get profile,
    LayoutConst.corner_radius.get profile, LayoutConst.cluster_pad.get profile,
    LayoutConst.cluster_border_w.get profile, 0, 0⟩

def Params.forKind (profile : Profile) (kind : String) (P : Params) : Params :=
  { P with
    nodeGap := kindOverride profile kind "node_spacing" P.nodeGap
    rankGap := kindOverride profile kind "rank_spacing" P.rankGap
    wrapWidth := kindConstant profile kind "wrapping_width"
    canvasMargin := canvasMarginOf profile kind }

def paramsOf (profile : Profile) (kind : String := "") : Option Params :=
  (baseParams profile).map (Params.forKind profile kind)

def checkedParams (profile : Profile) (kind : String := "") : Except LayoutError Params :=
  match paramsOf profile kind with
  | none => .error .domain
  | some P => if P.Valid then .ok P else .error .domain

def metricOf : Profile → Except LayoutError Measure.Metric
  | .vector => Measure.Role.label.metric
  | .cell => .ok Measure.Metric.cell

def nodeSize (P : Params) (lines : List Measure.Line) : Except LayoutError (Int × Int) :=
  let w := lines.foldl (fun acc l => max acc l.width) 0 + 2 * P.nodePadX + 2 * P.nodeBorder
  let h := (lines.length : Int) * P.lineH + 2 * P.nodePadY + 2 * P.nodeBorder
  if I32_MAX < w ∨ I32_MAX < h then .error .overflow
  else .ok (max w P.nodeMinW, max h P.nodeMinH)

def boxLines (m : Measure.Metric) (target : Int) (inp : Input) :
    Except LayoutError (List (List Measure.Line)) :=
  inp.boxes.zipIdx.mapM fun q =>
    let text := inp.texts.getD q.2 q.1.id
    StyledMeasure.wrap m target text.toList

def sizedNode (P : Params) (decl : Nat) (lines : List Measure.Line) : Except LayoutError Node := do
  let size ← nodeSize P lines
  pure { decl := decl, w := size.1, h := size.2, loopExtent := 0 }

def sizedNodes (P : Params) (lines : List (List Measure.Line)) : Except LayoutError (List Node) :=
  lines.zipIdx.mapM fun q => sizedNode P q.2 q.1

structure MeasuredLabel where
  index : Nat
  edge : Nat
  model : ModelLabel
  lines : List Measure.Line
  width : Int
  height : Int
  gutter : Int

def measureLabels (P : Params) (m : Measure.Metric) (target : Int) (inp : Input) (direction : Direction) :
    Except LayoutError (List MeasuredLabel) := do
  let labels : List (Option MeasuredLabel) ← inp.labels.zipIdx.mapM fun q => do
    match inp.routes.findIdx? (fun r => r.id == q.1.owner) with
    | none => pure none
    | some edge =>
      let lines ← StyledMeasure.wrap m target q.1.text.toList
      let width := lines.foldl (fun w l => max w l.width) 0
      let height := (lines.length : Int) * P.lineH
      let gutter := if m.profile == .cell then P.slot else 0
      if I32_MAX < width ∨ I32_MAX < height ∨ I32_MAX < width + gutter ∨
          I32_MAX < height + gutter then throw .overflow
      let (width, height) := match direction with
        | .LR | .RL => (height, width)
        | .TB | .BT => (width, height)
      pure (some (MeasuredLabel.mk q.2 edge q.1 lines width height gutter))
  pure (labels.filterMap id)

def routeLabels (labels : List MeasuredLabel) (edge : Nat) : List MeasuredLabel :=
  labels.filter fun l => l.edge == edge

def stackSize (slot : Int) (labels : List MeasuredLabel) : LoopLabel :=
  ⟨labels.foldl (fun w l => max w l.width) 0,
    labels.foldl (fun h l => h + l.height) 0 + slot * ((labels.length - 1 : Nat) : Int)⟩

def componentLabels (cg : Graph) (labels : List MeasuredLabel) : List EdgeLabelSize :=
  cg.edges.zipIdx.filterMap fun q =>
    match routeLabels labels q.1.decl with
    | [] => none
    | first :: rest =>
      let size := stackSize cg.slot (first :: rest)
      some ⟨q.2, size.width + first.gutter, size.height⟩

def edgeOf (inp : Input) (r : ModelRoute) (i : Nat) : Except LayoutError Edge :=
  match inp.boxes.findIdx? (fun b => b.id == r.fromId),
      inp.boxes.findIdx? (fun b => b.id == r.toId) with
  | some a, some b => .ok ⟨a, b, max (if inp.labels.any (fun l => l.owner == r.id) then 2 else 1)
      (inp.edges.getD i EdgeOptions.plain).minLength, i, false⟩
  | _, _ => .error .domain

def graphEdgesFrom (inp : Input) : Nat → List ModelRoute → Except LayoutError (List Edge)
  | _, [] => .ok []
  | i, r :: rs => do
    let edge ← edgeOf inp r i
    let edges ← graphEdgesFrom inp (i + 1) rs
    pure (edge :: edges)

def graphEdges (inp : Input) : Except LayoutError (List Edge) :=
  graphEdgesFrom inp 0 inp.routes


def orientNode (d : Direction) (n : Node) : Node :=
  match d with
  | .LR | .RL => { n with w := n.h, h := n.w }
  | .TB | .BT => n

def loopEdges (edges : List Edge) (v : Nat) : List Edge :=
  edges.filter fun e => e.tail == v && e.head == v

def loopSizes (edges : List Edge) (labels : List MeasuredLabel) (v : Nat)
    (slot : Int) : List LoopLabel :=
  (loopEdges edges v).map fun e => stackSize slot (routeLabels labels e.decl)

def measuredGraph (P : Params) (inp : Input) (o : Options) (lines : List (List Measure.Line)) :
    Except LayoutError Graph := do
  let nodes ← sizedNodes P lines
  let edges ← graphEdges inp
  let m ← metricOf o.profile
  let labels ← measureLabels P m
    (Measure.wrapTarget m.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0)) inp o.direction
  let nodes ← (nodes.map (orientNode o.direction)).zipIdx.mapM fun q => do
      let sizes := loopSizes edges labels q.2 P.slot
      let extent := Loops.extent P.slot sizes
      if extent < 0 then throw .domain
      let base := match inp.boxes[q.2]? with
        | none => q.1
        | some box => match inp.fixedSizes.find? (fun (fixed : String × Size) => fixed.1 == box.id) with
          | none => q.1
          | some fixed => orientNode o.direction
              { q.1 with w := fixed.2.w, h := fixed.2.h }
      let loopHeight := Loops.requiredHeight P.slot sizes
      let frame := (inp.boxes[q.2]?).any (fun box =>
        box.role == .group && !inp.fixedSizes.any (fun fixed => fixed.1 == box.id))
      let height := if frame then loopHeight else max base.h loopHeight
      if I32_MAX < extent ∨ I32_MAX < base.w + 2 * extent ∨ I32_MAX < height then
        throw .overflow
      pure { base with
        h := height
        loopExtent := extent.toNat
        clusterPath := match inp.boxes[q.2]? with
          | none => []
          | some box => Compound.path inp.boxes box }
  pure (Compound.prepare (inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node }
    else box)
    P.clusterPad (lines.map fun ls =>
      let width := ls.foldl (fun w line => max w line.width) 0
      let height := (max 1 ls.length : Int) * P.lineH
      match o.direction with
      | .LR | .RL => (height, width)
      | .TB | .BT => (width, height))
    { nodes := nodes, edges := edges, slot := P.slot })

def labelPass (edges : List Edge) (lab : Array Nat) : Array Nat :=
  edges.foldl
    (fun l e =>
      let m := min l[e.tail]! l[e.head]!
      (l.set! e.tail m).set! e.head m)
    lab

def labelsFix (edges : List Edge) : Nat → Array Nat → Array Nat
  | 0, lab => lab
  | f + 1, lab => labelsFix edges f (labelPass edges lab)

def components (g : Graph) : List (List Nat) :=
  let n := g.nodes.length
  let lab := labelsFix (g.edges ++ Compound.constraints g) (n + 1) (Array.range n)
  ((List.range n).filter fun v => lab[v]! == v).map fun r =>
    (List.range n).filter fun v => lab[v]! == r

def componentGraph (g : Graph) (comp : List Nat) : Graph :=
  { nodes := comp.map fun v => g.nodes.getD v default
    edges := (g.edges.filter fun e => comp.contains e.tail).map fun e =>
      { e with tail := comp.idxOf e.tail, head := comp.idxOf e.head }
    slot := g.slot }

structure Run where
  proper : Proper
  layers : List (List Nat)
  xs : List Int
  ys : List Int
  top : List Int
  routing : Routing
  routes : List EdgeRoute
  budget : Bool
  lanes : RouteImpl.LaneRouting := default

  coordinateProper : Proper := default
  coordinateXs : List Int := []
  coordinateYs : List Int := []
  exact : List Nat := []
def sizeProperPorts (P : Params) (p : Proper) : Proper :=
  { p with nodes := p.nodes.zipIdx.map fun q =>
    if q.1.dummy || q.1.node.border != 0 then q.1
    else
      let incoming := ((p.edges.filter fun edge => edge.head == q.2).map (·.tail)).eraseDups.length
      let outgoing := ((p.edges.filter fun edge => edge.tail == q.2).map (·.head)).eraseDups.length
      { q.1 with node := { q.1.node with
        w := max q.1.node.w ((((max incoming outgoing : Nat) + 1 : Nat) : Int) * P.portGap) } } }

def titleReservations (p : Proper) : Proper :=
  let titles := p.nodes.zipIdx.filter fun q =>
    q.1.node.border == -2
  { p with
    nodes := (p.nodes.map fun node =>
      if node.node.border == -2 || node.node.border == 2 then
        { node with node := { node.node with w := 0, h := 0 } } else node) ++
      titles.map (fun q =>
        { q.1 with node := { q.1.node with border := 3, loopExtent := 0 } })
    rank := p.rank ++ titles.map (fun q => rk p.rank q.2) }

def clearProxyExtents (p : Proper) : Proper :=
  { p with nodes := p.nodes.map fun node =>
    if node.node.border == -2 || node.node.border == 2 then
      { node with node := { node.node with loopExtent := 0 } } else node }

def proxySpan (p : Proper) (xs : List Int) (owner index : Nat) :
    Except LayoutError FramePorts.Span := do
  if xs.length != p.nodes.length then throw .domain
  let selected := p.nodes.zipIdx.filter fun q =>
    (q.1.node.border == -1 || q.1.node.border == 1) &&
      q.1.node.clusterPath.getLast? == some owner &&
      rk p.rank q.2 == rk p.rank index
  let spans ← selected.mapM fun q =>
    FramePorts.borderSpan (xs.getD q.2 0) q.1.node.w
  match spans with
  | [] => throw .domain
  | first :: rest =>
    pure (rest.foldl (fun a b => ⟨min a.lo b.lo, max a.hi b.hi⟩) first)

def proxyWidths (p : Proper) (xs : List Int) : Except LayoutError (Proper × List Int) := do
  let updated ← p.nodes.zipIdx.mapM fun q => do
    if q.1.node.border == -2 || q.1.node.border == 2 then
      match q.1.node.clusterPath.getLast? with
      | none => throw .domain
      | some owner =>
        let span ← proxySpan p xs owner q.2
        let width ← FramePorts.checked (span.hi - span.lo)
        if width < 0 then throw .domain
        let center ← FramePorts.checked (span.lo + Int.fdiv width 2)
        pure ({ q.1 with node := { q.1.node with w := width } }, center)
    else pure (q.1, xs.getD q.2 0)
  pure ({ p with nodes := updated.map (·.1) }, updated.map (·.2))

def materializeDummyPaths (p : Proper) : Proper :=
  { p with nodes := p.nodes.zipIdx.map fun q =>
    if q.1.dummy then
      { q.1 with node := { q.1.node with clusterPath := OrderImpl.nodePath p q.2 } }
    else q.1 }

def coordinateGraph (P : Params) (p : Proper) : Proper :=
  materializeDummyPaths (clearProxyExtents (OrderImpl.addClusterBorders
    (titleReservations (sizeProperPorts P p)) P.clusterBorderW))

def proxyYs (p : Proper) (layers : List (List Nat)) (top ys : List Int) : List Int :=
  ys.zipIdx.map fun q =>
    let node := (p.nodes.getD q.2 default).node
    if node.border == -2 then top.getD (rk p.rank q.2).toNat 0
    else if node.border == 2 then top.getD (rk p.rank q.2).toNat 0 +
      CoordsImpl.layerHeight p (layers.getD (rk p.rank q.2).toNat [])
    else q.1

def componentRun (P : Params) (cg : Graph) (labels : List MeasuredLabel := [])
    (orderOptions : OrderOptions := {}) : Except LayoutError Run := do
  let rr ← rankWithBudget (Compound.rankingGraph cg)
  let p0 ← normalize cg rr.ranks
  let p ← Labels.addLabelNodes cg p0 (componentLabels cg labels)
  let p := coordinateGraph P p
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
  let routes ← RouteImpl.routePointsWithLanes P.slot routeProper ord.layers xs ys yt.2 lanes
  pure ⟨routeProper, ord.layers, xs, ys, yt.2, r, routes,
    rr.budgetExhausted || ord.budgetExhausted, lanes, p, coordinateXs, yt.1, []⟩

def nodeRect (_cg : Graph) (run : Run) (i : Nat) : Rect :=
  let n := (run.proper.nodes.getD i default).node
  ⟨run.xs.getD i 0 - Int.fdiv n.w 2, run.ys.getD i 0, n.w, n.h⟩

def edgePoints (run : Run) (i : Nat) (_e : Edge) : List Point :=
  (run.routes.getD i default).points

structure Bounds where
  minX : Int
  minY : Int
  right : Int
  bottom : Int

def boundsOf (rects : List Rect) (pts : List Point) : Bounds :=
  let start : Bounds :=
    match rects with
    | [] => match pts with
      | [] => ⟨0, 0, 0, 0⟩
      | p :: _ => ⟨p.x, p.y, p.x, p.y⟩
    | r :: _ => ⟨r.x, r.y, 0, 0⟩
  let b := rects.foldl
    (fun b r => ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
    start
  pts.foldl
    (fun b p => ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩) b

def frameRect (_P : Params) (cg : Graph) (run : Run) (i : Nat) : Rect :=
  let node := cg.nodes.getD i default
  if node.border != -2 then nodeRect cg run i
  else
    let rectangles := run.proper.nodes.zipIdx.filterMap fun q =>
      if q.1.node.clusterPath.contains node.decl then
        some (Labels.rectAt run.proper run.xs run.ys q.2)
      else none
    let borders := run.proper.nodes.zipIdx.filterMap fun q =>
      if (q.1.node.border == -1 || q.1.node.border == 1) &&
          q.1.node.clusterPath.getLast? == some node.decl then
        some (Labels.rectAt run.proper run.xs run.ys q.2)
      else none
    let vertical := boundsOf rectangles []
    let horizontal := boundsOf borders []
    ⟨horizontal.minX, vertical.minY, horizontal.right - horizontal.minX,
      vertical.bottom - vertical.minY⟩
def labelEnvelope (P : Params) (cg : Graph) (run : Run) (labels : List MeasuredLabel)
    (edge : Nat) (e : Edge) : Option Rect := do

  let first ← (routeLabels labels e.decl).head?
  let size := stackSize cg.slot (routeLabels labels e.decl)
  if e.tail == e.head then
    let loops := loopEdges cg.edges e.tail
    let sizes := loopSizes cg.edges labels e.tail cg.slot
    let index := (loops.map (·.decl)).idxOf e.decl
    let placement := (if run.exact.contains e.tail then Loops.exactPlacement else Loops.placement)
      (frameRect P cg run e.tail) cg.slot (Loops.band cg.slot sizes) loops.length index size
    pure placement.label
  else if e.reversed then do
    let lane ← run.lanes.runs.find? (fun lane => lane.original == edge)
    pure (RouteImpl.reversedLabelRect cg.slot run.top
      (run.layers.map (RouteImpl.layerHeight run.proper)) run.routing lane size.width size.height)
  else do
    let rank := rk run.proper.rank e.tail +
      Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2
    let q ← run.proper.nodes.zipIdx.find? (fun q =>
      q.1.edge == some edge && rk run.proper.rank q.2 == rank)
    pure (Labels.textRectAt run.proper run.xs run.ys q.2 first.gutter)

def placedLabels (P : Params) (cg : Graph) (run : Run) (labels : List MeasuredLabel) :
    List (Nat × Rect) :=
  labels.filterMap fun l => do
    let edge ← cg.edges.findIdx? (fun e => e.decl == l.edge)
    let e ← cg.edges[edge]?
    let envelope ← labelEnvelope P cg run labels edge e
    let siblings := routeLabels labels e.decl
    let rectangles := Labels.stackRects envelope.x envelope.y cg.slot
      (siblings.map fun l => (l.width, l.height))
    let placed ← (siblings.zip rectangles).find? (fun q => q.1.index == l.index)
    pure (l.index, placed.2)


def labelBounds (P : Params) (cg : Graph) (run : Run) (labels : List MeasuredLabel) : List Rect :=
  cg.edges.zipIdx.filterMap fun q => do
    let envelope ← labelEnvelope P cg run labels q.2 q.1
    if q.1.tail == q.1.head then pure envelope
    else
      let first ← (routeLabels labels q.1.decl).head?
      pure { envelope with
        x := envelope.x - first.gutter
        w := envelope.w + first.gutter }

structure Part where
  labels : List (Nat × Rect)
  rects : List Rect
  routes : List (Nat × List Point)
  width : Int
  height : Int
  area : Int := 0
  titles : List (Nat × Rect) := []
  straighten : Option StraightenCtx := none

def shiftPoint (dx dy : Int) (p : Point) : Point := ⟨p.x + dx, p.y + dy⟩

def shiftRect (dx dy : Int) (r : Rect) : Rect := ⟨r.x + dx, r.y + dy, r.w, r.h⟩
def nodeLoops (cg : Graph) (run : Run) (labels : List MeasuredLabel) (v : Nat) :
    Except LayoutError (List LoopPlacement) :=
  (if run.exact.contains v then Loops.exactLoops else Loops.loops)
    (nodeRect cg run v) cg.slot (loopSizes cg.edges labels v cg.slot)



def componentLoops (P : Params) (cg : Graph) (run : Run) (labels : List MeasuredLabel) :
    Except LayoutError (List (Nat × LoopPlacement)) := do
  let groups ← (List.range cg.nodes.length).mapM fun v => do
    let out ← (if run.exact.contains v then Loops.exactLoops else Loops.loops)
      (frameRect P cg run v) cg.slot (loopSizes cg.edges labels v cg.slot)
    pure (((loopEdges cg.edges v).zip out).map fun q => (q.1.decl, q.2))
  pure groups.flatten

def componentTitles (P : Params) (cg : Graph) (run : Run) : List (Nat × Rect) :=
  cg.nodes.zipIdx.filterMap fun top => do
    if top.1.border != -2 then none else do
      let title ← run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath)
      let frame := frameRect P cg run top.2
      pure (top.2, Rect.mk
        (run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2)
        (frame.y + P.clusterPad) top.1.w (top.1.h - P.clusterPad))

def placeComponent (P : Params) (cg : Graph) (run : Run) (cursor : Int)
    (labels : List MeasuredLabel := []) (loops : List (Nat × LoopPlacement) := []) : Part :=
  let rects := (List.range cg.nodes.length).map (frameRect P cg run)
  let labelRects := placedLabels P cg run labels
  let extents : List Rect := rects.zipIdx.map fun q =>
    ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot), q.1.h⟩
  let b := boundsOf (rects ++ extents ++ labelBounds P cg run labels ++
    (componentTitles P cg run).map (·.2))
    (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))
  let dx := cursor - b.minX
  let dy := 0 - b.minY
  let sctx : StraightenCtx :=
    { proper := run.proper, layers := run.layers,
      xs := run.xs, ys := run.ys, tops := run.top, routing := run.routing,
      lanes := run.lanes, slot := P.slot,
      reversed := cg.edges.map (·.reversed), decls := cg.edges.map (·.decl),
      dx := dx, dy := dy }
  { labels := labelRects.map (fun q => (q.1, shiftRect dx dy q.2))
    rects := rects.map (shiftRect dx dy)
    routes := cg.edges.zipIdx.map fun q =>
      (q.1.decl, (((loops.find? (fun l => l.1 == q.1.decl)).map
        (fun l => l.2.points)).getD (edgePoints run q.2 q.1)).map (shiftPoint dx dy))
    width := b.right - b.minX
    height := b.bottom - b.minY
    titles := (componentTitles P cg run).map (fun q => (q.1, shiftRect dx dy q.2))
    straighten := some sctx }

def placeComponentExact (P : Params) (cg : Graph) (run : Run) (cursor : Int)
    (labels : List MeasuredLabel := []) (loops : List (Nat × LoopPlacement) := []) : Part :=
  let rects := (List.range cg.nodes.length).map (frameRect P cg run)
  let labelRects := placedLabels P cg run labels
  let extents : List Rect := rects.zipIdx.map fun q =>
    let sizes := loopSizes cg.edges labels q.2 cg.slot
    let width := if run.exact.contains q.2 then Loops.exactExtent cg.slot sizes
      else Loops.extent cg.slot sizes
    let height := if run.exact.contains q.2 then
      max q.1.h ((sizes.length : Int) * Loops.band cg.slot sizes) else q.1.h
    ⟨q.1.x + q.1.w, q.1.y, width, height⟩
  let b := boundsOf (rects ++ extents ++ labelBounds P cg run labels ++
    (componentTitles P cg run).map (·.2))
    (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))
  let dx := cursor - b.minX
  let dy := -b.minY
  let sctx : StraightenCtx :=
    { proper := run.proper, layers := run.layers,
      xs := run.xs, ys := run.ys, tops := run.top, routing := run.routing,
      lanes := run.lanes, slot := P.slot,
      reversed := cg.edges.map (·.reversed), decls := cg.edges.map (·.decl),
      dx := dx, dy := dy }
  { labels := labelRects.map (fun q => (q.1, shiftRect dx dy q.2))
    rects := rects.map (shiftRect dx dy)
    routes := cg.edges.zipIdx.map fun q =>
      (q.1.decl, (((loops.find? (fun l => l.1 == q.1.decl)).map
        (fun l => l.2.points)).getD (edgePoints run q.2 q.1)).map (shiftPoint dx dy))
    width := b.right - b.minX
    height := b.bottom - b.minY
    titles := (componentTitles P cg run).map (fun q => (q.1, shiftRect dx dy q.2))
    straighten := some sctx }

def partArea (rects : List Rect) (routes : List (Nat × List Point)) : Int :=
  rects.foldl (fun total r => total + r.w * r.h) 0 +
    routes.foldl (fun total route =>
      let b := boundsOf [] route.2
      total + (b.right - b.minX) * (b.bottom - b.minY)) 0

structure Acc where
  cursor : Int
  canvasW : Int
  canvasH : Int
  rects : Array Rect
  routes : Array (List Point)
  labels : Array Rect
  budget : Bool
  parts : List (List Nat × Part) := []
  titles : List (Nat × Rect) := []

def placePart (comp : List Nat) (cg : Graph) (run : Run) (P : Params) (acc : Acc) (labels : List MeasuredLabel := [])
    (place : Params → Graph → Run → Int → List MeasuredLabel → List (Nat × LoopPlacement) → Part :=
      @placeComponent) (exactFootprints : Bool := false) : Except LayoutError Acc := do
  let loops ← componentLoops P cg run labels
  let part₀ := place P cg run 0 labels loops
  let part := { part₀ with
    area := partArea (part₀.rects ++ part₀.titles.map (·.2) ++ labelBounds P cg run labels ++
      ((List.range cg.nodes.length).map fun v =>
        let rect := nodeRect cg run v
        ⟨rect.x + rect.w, rect.y,
          (if exactFootprints && run.exact.contains v then Loops.exactExtent else Loops.extent)
            cg.slot (loopSizes cg.edges labels v cg.slot),
          (if exactFootprints && run.exact.contains v then max rect.h else id)
            (((loopEdges cg.edges v).length : Int) *
              Loops.band cg.slot (loopSizes cg.edges labels v cg.slot))⟩)) part₀.routes }
  if I32_MAX < acc.cursor + part.width + P.nodeGap then .error .overflow
  else
    .ok { cursor := acc.cursor + part.width + P.nodeGap
          canvasW := acc.cursor + part.width
          canvasH := max acc.canvasH part.height
          rects := (comp.zip part.rects).foldl
            (fun a q => if q.1 < a.size then a.set! q.1 q.2 else a) acc.rects
          routes := part.routes.foldl (fun a q => a.set! q.1 q.2) acc.routes
          labels := part.labels.foldl (fun a q => a.set! q.1 q.2) acc.labels
          budget := acc.budget || run.budget
          parts := acc.parts ++ [(comp, part)]
          titles := acc.titles ++ part.titles.map (fun q => (comp.getD q.1 0, q.2)) }



def packAcc (P : Params) (o : Options) (acc : Acc) : Except LayoutError Acc := do
  let packed ← Pack.pack (if o.profile == .cell then o.maxWidth else 0)
    P.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
    (LayoutConst.component_aspect_den.get o.profile)
    (acc.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩)
  pure ((acc.parts.zip packed.boxes).foldl (fun out q =>
    let comp := q.1.1
    let part := q.1.2
    let dx := q.2.x
    let dy := q.2.y
    { out with
      rects := (comp.zip part.rects).foldl
        (fun a r => if r.1 < a.size then a.set! r.1 (shiftRect dx dy r.2) else a) out.rects
      routes := part.routes.foldl
        (fun a r => a.set! r.1 (r.2.map (shiftPoint dx dy))) out.routes
      labels := part.labels.foldl
        (fun a r => a.set! r.1 (shiftRect dx dy r.2)) out.labels
      titles := out.titles ++ part.titles.map
        (fun r => (comp.getD r.1 0, shiftRect dx dy r.2)) })
    { acc with canvasW := packed.width, canvasH := packed.height, titles := [] })

/-- The straightening context of a packed part and its pack offset: the shift
from the part's first rectangle to that rectangle's packed position. -/
def straightenOffset (comp : List Nat) (part : Part) (rects : Array Rect) :
    Option (StraightenCtx × Int × Int) :=
  match part.straighten, comp.zip part.rects with
  | some ctx0, (v, r) :: _ =>
    match rects[v]? with
    | some base => some (ctx0, base.x - r.x, base.y - r.y)
    | none => none
  | _, _ => none

/-- The global box list straightening checks: packed rectangles with node flags. -/
def installed_global_boxes (acc : Acc) (inp : Input) : List (Bool × Rect) :=
  (List.range acc.rects.size).filterMap fun v =>
    match acc.rects[v]?, inp.boxes[v]? with
    | some r, some m => some (decide (m.role == BoxRole.node), r)
    | _, _ => none

/-- The obstacles of one part's straightening: every node box, and the other
real nodes of the part. -/
def straightenPartBoxes (inp : Input) (acc : Acc) (ctx0 : StraightenCtx)
    (comp : List Nat) : List (Bool × Rect) :=
  installed_global_boxes acc inp ++
    comp.zipIdx.filterMap fun q =>
      if straightRealNode ctx0.proper q.2 then
        match acc.rects[q.1]?, inp.boxes[q.1]? with
        | some r, some m => if m.role == BoxRole.node then none else some (true, r)
        | _, _ => none
      else none

def straightenParts (boxesOf : StraightenCtx → List Nat → List (Bool × Rect))
    (rects : Array Rect) :
    List ((List Nat) × Part) → Array (List Point) →
    Except LayoutError (Array (List Point))
  | [], routes => .ok routes
  | q :: rest, routes =>
    match straightenOffset q.1 q.2 rects with
    | none => straightenParts boxesOf rects rest routes
    | some (ctx0, ox, oy) =>
      match straightenComponent { ctx0 with dx := ctx0.dx + ox, dy := ctx0.dy + oy } (boxesOf ctx0 q.1) routes with
      | .ok updated => straightenParts boxesOf rects rest updated
      | .error e => .error e

def straightenRoutes (inp : Input) (acc : Acc) : Except LayoutError (Array (List Point)) :=
  straightenParts (fun ctx0 comp => straightenPartBoxes inp acc ctx0 comp) acc.rects acc.parts acc.routes

def straightenAcc (inp : Input) (acc : Acc) : Except LayoutError Acc := do
  let routes ← straightenRoutes inp acc
  pure { acc with routes }

def orientPoint (d : Direction) (h : Int) (p : Point) : Point :=
  match d with
  | .TB => p
  | .BT => ⟨p.x, h - p.y⟩
  | .LR => ⟨p.y, p.x⟩
  | .RL => ⟨h - p.y, p.x⟩

def orientRect (d : Direction) (h : Int) (r : Rect) : Rect :=
  match d with
  | .TB => r
  | .BT => ⟨r.x, h - r.y - r.h, r.w, r.h⟩
  | .LR => ⟨r.y, r.x, r.h, r.w⟩
  | .RL => ⟨h - r.y - r.h, r.x, r.h, r.w⟩

def orientCanvas (d : Direction) (w h : Int) : Size :=
  match d with
  | .TB | .BT => ⟨w, h⟩
  | .LR | .RL => ⟨h, w⟩

def markerAxis (a b : Point) : MarkerAxis :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  if dy.natAbs ≤ dx.natAbs then
    if dx < 0 then .negativeX else .positiveX
  else
    if dy < 0 then .negativeY else .positiveY

def markerRefAt (name : String) (pos prev : Point) : List Primitive :=
  if name = "" then [] else [.markerRef name pos (markerAxis prev pos)]

def edgePaint (stroke : String) : Paint :=
  match stroke with
  | "thick" => { style := "edge", width := .emphasis }
  | "dotted" => { style := "edge", line := .dotted }
  | "dashed" => { style := "edge", line := .dashed }
  | _ => { style := "edge" }

def edgeItems (P : Params) (pts : List Point) (e : EdgeOptions) : List Primitive :=
  if e.stroke == "invisible" then []
  else if pts.length < 2 then [.polyline pts P.cornerRadius (edgePaint e.stroke)]
  else
    .polyline pts P.cornerRadius (edgePaint e.stroke) ::
      (markerRefAt e.markerStart (pts.getD 0 default) (pts.getD 1 default) ++
        markerRefAt e.markerEnd (pts.getD (pts.length - 1) default)
          (pts.getD (pts.length - 2) default))

def nodeItems (P : Params) (r : Rect) (lines : List Measure.Line) : List Primitive :=
  let h := (lines.length : Int) * P.lineH
  [.rect r { style := "node" },
    .text { rect := ⟨r.x, r.y + Int.tdiv (r.h - h) 2, r.w, h⟩
            role := .label
            size := 14
            align := .middle
            style := "text"
            lines := lines.map fun l => [⟨String.ofList l.text, false, false⟩] }]


def titleRect (P : Params) (rect : Rect) (lines : List Measure.Line) : Rect :=
  ⟨rect.x + P.clusterPad, rect.y + P.clusterPad,
    max 0 (rect.w - 2 * P.clusterPad), (max 1 lines.length : Int) * P.lineH⟩
def ownedTextRect (P : Params) (box : Box) (lines : List Measure.Line) : Rect :=
  if box.role == "group" then titleRect P box.rect lines
  else
    let height := (lines.length : Int) * P.lineH
    ⟨box.rect.x, box.rect.y + Int.fdiv (box.rect.h - height) 2, box.rect.w, height⟩

def groupItems (P : Params) (rect : Rect) (lines : List Measure.Line) : List Primitive :=
  [.rect rect { style := "group" },
   .text {
     rect := titleRect P rect lines
     role := .label
     size := 14
     align := .middle
     style := "text"
     lines := lines.map fun line => [⟨String.ofList line.text, false, false⟩] }]

def sceneItems (P : Params) (inp : Input) (boxes : List Box) (routes : List Route)
    (lines : List (List Measure.Line)) (labels : List SceneLabel := []) : List Group :=
  ((boxes.zipIdx.filter fun q => q.1.role == "group").map fun q =>
    ⟨.group, q.1.id, groupItems P q.1.rect (lines.getD q.2 [])⟩) ++
  routes.zipIdx.map (fun q =>
    ⟨.edge, q.1.id, edgeItems P q.1.points (inp.edges.getD q.2 EdgeOptions.plain) ++
      ((labels.filter fun l => l.owner == q.1.id).map fun l =>
        .text {
          rect := l.rect
          role := .label
          size := 14
          align := .middle
          style := "text"
          lines := l.lines.map fun text => [⟨text, false, false⟩] })⟩) ++
  ((boxes.zipIdx.filter fun q => q.1.role == "node").map fun q =>
    ⟨.node, q.1.id, nodeItems P q.1.rect (lines.getD q.2 [])⟩)

def applyTitles (titles : List (String × Rect)) (groups : List Group) : List Group :=
  groups.map fun group =>
    match titles.find? (fun title => title.1 == group.owner) with
    | none => group
    | some title => { group with items := group.items.map fun item =>
        match item with
        | .text text => .text { text with rect := title.2 }
        | _ => item }

def groupTitles (groups : List Group) : List (String × Rect) :=
  groups.filterMap fun group => do
    if group.role != .group then none else do
      let rect ← group.items.findSome? fun item =>
        match item with
        | .text text => some text.rect
        | _ => none
      pure (group.owner, rect)

def sceneOf (P : Params) (inp : Input) (o : Options) (lines : List (List Measure.Line))
    (acc : Acc) (measured : List MeasuredLabel := []) : Scene :=
  let h := acc.canvasH
  let margin := P.canvasMargin
  let boxes := inp.boxes.zipIdx.map fun q =>
    ⟨q.1.id, q.1.role.id, shiftRect margin margin (orientRect o.direction h (acc.rects.getD q.2 default)), q.1.parent,
      q.1.exclusive⟩
  let routes := inp.routes.zipIdx.map fun q =>
    ⟨q.1.id, q.1.fromId, q.1.toId, q.1.orthogonal,
      (acc.routes.getD q.2 []).map (fun p => shiftPoint margin margin (orientPoint o.direction h p))⟩
  let titles := acc.titles.filterMap fun title => do
    let box ← inp.boxes[title.1]?
    let textLines := lines.getD title.1 []
    let width := textLines.foldl (fun value line => max value line.width) 0
    let height := (max 1 textLines.length : Int) * P.lineH
    let size := match o.direction with
      | .LR | .RL => Size.mk height width
      | .TB | .BT => Size.mk width height
    let rect := { title.2 with w := size.w, h := size.h }
    pure (box.id, shiftRect margin margin (orientRect o.direction h rect))
  let labels : List SceneLabel := inp.labels.zipIdx.filterMap fun q =>
    if inp.boxes.any (fun box => box.id == q.1.owner && box.exclusive) then none
    else match measured.find? (fun label => label.index == q.2) with
    | some label => some
      { id := q.1.id, owner := q.1.owner, text := q.1.text
        rect := shiftRect margin margin
          (orientRect o.direction h (acc.labels.getD label.index default))
        lines := label.lines.map fun line => String.ofList line.text }
    | none =>
      match inp.boxes.findIdx? (fun box => box.id == q.1.owner && !box.exclusive) with
      | none => none
      | some index =>
        let titleLines := lines.getD index []
        some {
          id := q.1.id, owner := q.1.owner, text := q.1.text
          rect := ((titles.find? (fun title => title.1 == q.1.owner)).map (·.2)).getD
            (ownedTextRect P (boxes.getD index ⟨"", "", default, "", false⟩) titleLines)
          lines := titleLines.map fun line => String.ofList line.text }
  { kind := inp.kind
    profile := o.profile
    options := o
    canvas := orientCanvas o.direction (acc.canvasW + 2 * margin) (h + 2 * margin)
    boxes := boxes
    routes := routes
    labels := labels
    items := applyTitles titles (sceneItems P inp boxes routes lines labels) }

def cycleGraph (g : Graph) : Graph :=
  if g.nodes.any (fun node => node.border == -2) then Compound.protect g
  else breakCycles g

def childInset (direction : String) (pad titleWidth titleHeight : Int) : Point :=
  match direction with
  | "LR" => ⟨pad + titleWidth, pad⟩
  | "RL" => ⟨pad, pad⟩
  | "BT" => ⟨pad, pad⟩
  | _ => ⟨pad, pad + titleHeight⟩

def childFrameSize (direction : String) (pad titleWidth titleHeight : Int)
    (content : Size) : Size :=
  match direction with
  | "LR" | "RL" =>
    ⟨content.w + titleWidth + 2 * pad, max content.h titleHeight + 2 * pad⟩
  | _ =>
    ⟨max content.w titleWidth + 2 * pad, content.h + titleHeight + 2 * pad⟩

def childTitleRect (direction : String) (pad width height : Int) (frame : Rect) : Rect :=
  let centeredX := frame.x + Int.fdiv (frame.w - width) 2
  let centeredY := frame.y + Int.fdiv (frame.h - height) 2
  match direction with
  | "BT" => ⟨centeredX, frame.y + frame.h - pad - height, width, height⟩
  | "LR" => ⟨frame.x + pad, centeredY, width, height⟩
  | "RL" => ⟨frame.x + frame.w - pad - width, centeredY, width, height⟩
  | _ => ⟨centeredX, frame.y + pad, width, height⟩

def expandedComponentCost (P : Params) (inp : Input) (o : Options) (scene : Scene) :
    Except LayoutError Scene :=
  inp.fixedChildren.foldlM (fun expanded child => do
    match expanded.boxes.find? (fun box => box.id == child.1) with
    | none => pure expanded
    | some frame =>
      let metric ← metricOf o.profile
      let index := (inp.boxes.findIdx? (fun box => box.id == child.1)).getD 0
      let lines ← StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD index child.1).toList
      let margin := P.canvasMargin
      let direction := ((inp.boxes[index]?).map (·.direction)).getD ""
      let titleWidth := lines.foldl (fun width line => max width line.width) 0
      let inset := childInset direction P.clusterPad titleWidth
        ((max 1 lines.length : Int) * P.lineH)
      let dx := frame.rect.x + inset.x - margin
      let dy := frame.rect.y + inset.y - margin
      pure { expanded with
        boxes := expanded.boxes ++ child.2.boxes.map (fun box =>
          { box with rect := shiftRect dx dy box.rect })
        routes := expanded.routes ++ child.2.routes.map (fun route =>
          { route with points := route.points.map (shiftPoint dx dy) })
        labels := expanded.labels ++ child.2.labels.map (fun label =>
          { label with rect := shiftRect dx dy label.rect }) }) scene

def componentScene (P : Params) (inp : Input) (o : Options) (cg : Graph)
    (run : Run) (labels : List MeasuredLabel)
    (place : Params → Graph → Run → Int → List MeasuredLabel → List (Nat × LoopPlacement) → Part :=
      @placeComponent) : Except LayoutError Scene := do
  let loops ← componentLoops P cg run labels
  let part := place P cg run 0 labels loops
  let boxes := cg.nodes.zipIdx.filterMap fun q =>
    match inp.boxes[q.1.decl]? with
    | none => none
    | some model =>
      if q.1.border == 2 then none else
      some (Box.mk model.id model.role.id
        (orientRect o.direction part.height (part.rects.getD q.2 default))
        model.parent model.exclusive)
  let routes := cg.edges.filterMap fun edge =>
    match inp.routes[edge.decl]?, part.routes.find? (fun route => route.1 == edge.decl) with
    | some model, some placed =>
      some (Route.mk model.id model.fromId model.toId model.orthogonal
        (placed.2.map (orientPoint o.direction part.height)))
    | _, _ => none
  let sceneLabels : List SceneLabel := part.labels.filterMap fun placed =>
    match labels.find? (fun label => label.index == placed.1) with
    | none => none
    | some label =>
      if inp.boxes.any (fun box => box.id == label.model.owner && box.exclusive) then none
      else some {
        id := label.model.id, owner := label.model.owner, text := label.model.text
        rect := orientRect o.direction part.height placed.2
        lines := label.lines.map fun line => String.ofList line.text }
  let metric ← metricOf o.profile
  let titleLabels ← inp.labels.filterMapM fun model => do
    match boxes.find? (fun box => box.id == model.owner && !box.exclusive) with
    | none => pure none
    | some frame =>
      let lines ← StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0)) model.text.toList
      pure (some ({
        id := model.id, owner := model.owner, text := model.text
        rect := ownedTextRect P frame lines
        lines := lines.map fun line => String.ofList line.text } : SceneLabel))
  let scene : Scene := {
    kind := inp.kind, profile := o.profile, options := o
    canvas := orientCanvas o.direction part.width part.height
    boxes := boxes, routes := routes, labels := titleLabels ++ sceneLabels }

  expandedComponentCost P inp o scene
def componentCandidate (g : Graph) (comp : List Nat) (index : Nat) : Graph :=
  let raw := componentGraph g comp
  let source := { raw with edges := raw.edges.map Edge.original }
  if index == 2 then
    let greedy := breakCyclesGreedy source
    if source.nodes.any (fun node => node.border == -2) then Compound.protect greedy else greedy
  else cycleGraph source

def componentTrial (P : Params) (inp : Input) (o : Options) (g : Graph)
    (comp : List Nat) (labels : List MeasuredLabel) (index : Nat) :
    Except LayoutError (Portfolio.Candidate (Graph × Run)) := do
  let cg := componentCandidate g comp index
  let run ← componentRun P cg labels (candidateOrder index)
  let scene ← componentScene P inp o cg run labels
  pure { value := (cg, run), scene := scene, budgetExhausted := run.budget }

def layoutComponent (P : Params) (inp : Input) (o : Options) (g : Graph) (acc : Acc)
    (comp : List Nat) (labels : List MeasuredLabel := []) : Except LayoutError Acc := do
  let chosen ← Portfolio.portfolio o.thoroughness (componentTrial P inp o g comp labels)
  let result ← placePart comp chosen.value.1 chosen.value.2 P acc labels
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
def layout (inp : Input) (o : Options) : Except LayoutError FamilyResult := do
  let P ← checkedParams o.profile inp.kind
  let m ← metricOf o.profile
  let lines ← boxLines m
    (Measure.wrapTarget m.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0)) inp
  let measured ← measureLabels P m
    (Measure.wrapTarget m.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0)) inp o.direction
  let g0 ← measuredGraph P inp o lines
  let g := g0
  let start : Acc :=
    ⟨0, 0, 0, Array.replicate inp.boxes.length default, Array.replicate inp.routes.length [],
      Array.replicate inp.labels.length default, false, [], []⟩
  let acc ← (components g).foldlM
    (fun acc comp => layoutComponent P inp o g acc comp measured) start
  let acc ← packAcc P o acc
  let acc ← straightenAcc inp acc
  let scene := sceneOf P inp o lines acc measured
  if I32_MAX < scene.canvas.w ∨ I32_MAX < scene.canvas.h then throw .overflow
  else pure ⟨scene, acc.budget, acc.parts.foldl (fun area part => area + part.2.area) 0⟩

def selectInput (inp : Input) (keep : ModelBox → Bool) (root : String := "") : Input :=
  let selected := inp.boxes.zipIdx.filter fun q => keep q.1
  let boxes := selected.map fun q =>
    if q.1.parent == root then { q.1 with parent := "" } else q.1
  let routes := inp.routes.zipIdx.filter fun q =>
    boxes.any (fun box => box.id == q.1.fromId) &&
      boxes.any (fun box => box.id == q.1.toId)
  { inp with
    boxes := boxes
    texts := selected.map fun q => inp.texts.getD q.2 q.1.id
    routes := routes.map (·.1)
    edges := routes.map fun q => inp.edges.getD q.2 EdgeOptions.plain
    labels := inp.labels.filter fun label =>
      boxes.any (fun box => box.id == label.owner) ||
        routes.any (fun route => route.1.id == label.owner) }

def directionOf (text : String) : Direction :=
  if text == "BT" then .BT else if text == "LR" then .LR
  else if text == "RL" then .RL else .TB

def expandChild (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleHeight : Int) (parent child : FamilyResult) : Except LayoutError FamilyResult := do
  let frame ← match parent.scene.boxes.find? (fun box => box.id == group.id) with
    | none => .error .domain
    | some frame => .ok frame
  let margin := P.canvasMargin
  let metric ← metricOf o.profile
  let index := (inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0
  let titleLines ← StyledMeasure.wrap metric
    (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
    (inp.texts.getD index group.id).toList
  let titleWidth := titleLines.foldl (fun width line => max width line.width) 0
  let inset := childInset group.direction P.clusterPad titleWidth titleHeight
  let dx := frame.rect.x + inset.x - margin
  let dy := frame.rect.y + inset.y - margin
  let childBoxes := child.scene.boxes.map fun box =>
    { box with
      rect := shiftRect dx dy box.rect
      parent := if box.parent == "" then group.id else box.parent }
  let childRoutes := child.scene.routes.map fun route =>
    { route with points := route.points.map (shiftPoint dx dy) }
  let childLabels := child.scene.labels.map fun label =>
    { label with rect := shiftRect dx dy label.rect }
  let boxes := inp.boxes.filterMap fun model =>
    (childBoxes ++ parent.scene.boxes).find? (fun box => box.id == model.id)
  let routes := inp.routes.filterMap fun model =>
    (childRoutes ++ parent.scene.routes).find? (fun route => route.id == model.id)
  let labels := inp.labels.filterMap fun model => do
    let label ← (childLabels ++ parent.scene.labels).find? (fun label => label.id == model.id)
    let titleRect := childTitleRect group.direction P.clusterPad titleWidth titleHeight frame.rect
    pure (if model.owner == group.id then { label with rect := titleRect } else label)
  let metric ← metricOf o.profile
  let lines ← boxLines metric
    (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0)) inp
  let titles := (group.id, childTitleRect group.direction P.clusterPad
    titleWidth titleHeight frame.rect) ::
    ((groupTitles child.scene.items).map (fun title => (title.1, shiftRect dx dy title.2)) ++
      groupTitles parent.scene.items)
  let scene := { parent.scene with
    boxes := boxes, routes := routes, labels := labels
    items := applyTitles titles (sceneItems P inp boxes routes lines labels) }
  pure {
    scene := scene, budgetExhausted := parent.budgetExhausted || child.budgetExhausted
    itemArea := parent.itemArea }

def layoutRecursive : Nat → Input → Options → Except LayoutError FamilyResult
  | 0, inp, o => layout inp o
  | fuel + 1, inp, o => do
    match inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) with
    | none => layout inp o
    | some group =>
      let P ← checkedParams o.profile inp.kind
      let metric ← metricOf o.profile
      let childInput := selectInput inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id
      let child ← layoutRecursive fuel childInput { o with direction := directionOf group.direction }
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
      let parent ← layoutRecursive fuel parentInput o
      expandChild P inp o group titleHeight parent child

end PipelineImpl


def inputTextBytes (inp : Input) : Nat :=
  let boxBytes := inp.boxes.zipIdx.foldl
    (fun n q => n + (inp.texts.getD q.2 q.1.id).utf8ByteSize) 0
  inp.labels.foldl (fun n l =>
    if inp.boxes.any (fun b => l.owner == b.id && l.id == b.id ++ ".label") then n
    else n + l.text.utf8ByteSize) boxBytes

def inputModel (inp : Input) (o : Options) : Model :=
  { kind := inp.kind, profile := o.profile, options := o
    boxes := inp.boxes, routes := inp.routes, labels := inp.labels }

/-- One attached note keeps its target's parent: a note parked under a foreign group would
be placed inside the target bundle and overlap that foreign frame (validator C8a). Native
rejects the same pairs (`validAttachmentPair`). -/
def noteParentOK (boxes : List ModelBox) (a : Nat × Nat × Bool) : Bool :=
  match boxes[a.1]?, boxes[a.2.1]? with
  | some target, some note => note.parent == target.parent
  | _, _ => false

/-- Every attached note box shares its target's parent. -/
def attachedNoteParents (inp : Input) : Bool :=
  (attachedNotes inp.boxes).all fun a => noteParentOK inp.boxes a

def framedParents (inp : Input) : Bool :=
  inp.boxes.all fun box =>
    box.parent == "" ||
      inp.boxes.any fun parent =>
        parent.id == box.parent && parent.role == .group &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == parent.id)

def layoutFamily (inp : Input) (o : Options) : Except LayoutFailure FamilyResult :=
  if o.limits.maxNodes < inp.boxes.length then
    .error (.tooLarge o.limits.maxNodes inp.boxes.length)
  else if o.limits.maxEdges < inp.routes.length then
    .error (.tooLarge o.limits.maxEdges inp.routes.length)
  else if o.limits.maxTextBytes < inputTextBytes inp then
    .error (.tooLarge o.limits.maxTextBytes (inputTextBytes inp))
  else if !modelWellFormed (inputModel inp o) then .error (.geometry .domain)
  else if !framedParents inp then .error (.geometry .domain)
  else if !attachedNoteParents inp then .error (.geometry .domain)
  else
    match PipelineImpl.layoutRecursive (inp.boxes.length + 1) inp o with
    | .error error => .error (.geometry error)
    | .ok result => .ok result
end Layered
end Elegant

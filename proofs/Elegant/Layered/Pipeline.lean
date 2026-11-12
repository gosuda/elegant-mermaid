import Elegant.Model
import Elegant.Scene
import Elegant.Measure
import Elegant.Gen.Layoutconst
import Elegant.Layered.Cycles
import Elegant.Layered.Rank
import Elegant.Layered.Normalize
import Elegant.Layered.Order
import Elegant.Layered.Coords
import Elegant.Layered.Route

set_option autoImplicit false

/-! Pipeline of the layered family for flat graphs (spec/layout/layered.md, steps 1 to 12 without
clusters, label nodes, self-loop bands, reversed-edge lanes, packing rows and the portfolio).
`layoutFamily` measures and wraps every box text, sizes the nodes, breaks cycles, splits the
graph into weak components, lays each component out (rank, normalise, order, cross coordinates,
routing, rank coordinates, route points), places the components left to right with `node_gap`
between them, translates the canvas to the origin, and maps the internal `TB` orientation to the
requested direction. It computes the same integers as `internal/layout/layered/pipeline.go`. The
scene groups follow `assembleScene`: one `edge` group per route (a polyline with the markers of
its `EdgeOptions`), then one `node` group per box (a rectangle and the wrapped text lines).

`normalize_gapDeclsDistinct` and `coordPhases_coordFacts` discharge the hypotheses of the routing
module (`GapDeclsDistinct` and `CoordFacts`) from the results of the normalise and coordinate
phases, and `layoutFamily_component_facts` states that every component of a successful layout
satisfies them. -/

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
deriving Repr

structure FamilyResult where
  scene : Scene
  budgetExhausted : Bool

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
deriving Repr, Inhabited

def Params.Valid (P : Params) : Prop :=
  1 ≤ P.nodeGap ∧ 1 ≤ P.rankGap ∧ 1 ≤ P.slot ∧ Int.fdiv P.slot 2 ≤ P.rankGap

instance (P : Params) : Decidable P.Valid := by
  unfold Params.Valid
  infer_instance

def constantOf (profile : Profile) (name : String) : Option Int :=
  (layoutconst.find? fun c => c.name == profile.id ++ "." ++ name).map (·.value)

opaque paramsOf (profile : Profile) : Option Params :=
  match constantOf profile "node_pad_x", constantOf profile "node_pad_y",
      constantOf profile "node_border", constantOf profile "line_h",
      constantOf profile "node_min_w", constantOf profile "node_min_h",
      constantOf profile "port_gap", constantOf profile "node_gap",
      constantOf profile "rank_gap", constantOf profile "slot",
      constantOf profile "corner_radius" with
  | some a, some b, some c, some d, some e, some f, some g, some h, some i, some j, some k =>
    some ⟨a, b, c, d, e, f, g, h, i, j, k⟩
  | _, _, _, _, _, _, _, _, _, _, _ => none

def checkedParams (profile : Profile) : Except LayoutError Params :=
  match paramsOf profile with
  | none => .error .domain
  | some P => if P.Valid then .ok P else .error .domain

def metricOf : Profile → Except LayoutError Measure.Metric
  | .vector => Measure.Role.label.metric
  | .cell => .ok Measure.Metric.cell

def breakTokens : List (List Char) := ["<br>".toList, "<br/>".toList, "<br />".toList]

def tokenAt (s t : List Char) : Bool :=
  decide (t.length ≤ s.length) && (t.zip s).all fun q => q.1.toLower == q.2.toLower

def forcedAt (s : List Char) : Option (List Char) := breakTokens.find? (tokenAt s)

def splitForced : Nat → List Char → List Char → List (List Char × List Char)
  | 0, acc, rest => [(acc.reverse ++ rest, [])]
  | _ + 1, acc, [] => [(acc.reverse, [])]
  | f + 1, acc, c :: cs =>
    match forcedAt (c :: cs) with
    | some t => (acc.reverse, t) :: splitForced f [] ((c :: cs).drop t.length)
    | none => splitForced f (c :: acc) cs

def appendForced (lines partLines : List Measure.Line) (forced : List Char) :
    List Measure.Line :=
  match forced with
  | [] => lines ++ partLines
  | _ =>
    match partLines.getLast? with
    | none => lines ++ [⟨[], forced, 0⟩]
    | some l => lines ++ (partLines.dropLast ++ [{ l with sep := l.sep ++ forced }])

def wrapForced (m : Measure.Metric) (target : Int) (s : List Char) :
    Except LayoutError (List Measure.Line) :=
  (splitForced (s.length + 1) [] s).foldlM
    (fun lines part => do
      let partLines ← Measure.wrap m target part.1
      pure (appendForced lines partLines part.2))
    []

def nodeSize (P : Params) (lines : List Measure.Line) : Except LayoutError (Int × Int) :=
  let w := lines.foldl (fun acc l => max acc l.width) 0 + 2 * P.nodePadX + 2 * P.nodeBorder
  let h := (lines.length : Int) * P.lineH + 2 * P.nodePadY + 2 * P.nodeBorder
  if I32_MAX < w ∨ I32_MAX < h then .error .overflow
  else .ok (max w P.nodeMinW, max h P.nodeMinH)

def boxLines (m : Measure.Metric) (target : Int) (inp : Input) :
    Except LayoutError (List (List Measure.Line)) :=
  inp.boxes.zipIdx.mapM fun q => wrapForced m target (inp.texts.getD q.2 q.1.id).toList

def sizedNode (P : Params) (decl : Nat) (lines : List Measure.Line) : Except LayoutError Node := do
  let size ← nodeSize P lines
  pure ⟨decl, size.1, size.2⟩

def sizedNodes (P : Params) (lines : List (List Measure.Line)) : Except LayoutError (List Node) :=
  lines.zipIdx.mapM fun q => sizedNode P q.2 q.1

def edgeOf (inp : Input) (r : ModelRoute) (i : Nat) : Except LayoutError Edge :=
  match inp.boxes.findIdx? (fun b => b.id == r.fromId),
      inp.boxes.findIdx? (fun b => b.id == r.toId) with
  | some a, some b => .ok ⟨a, b, max 1 (inp.edges.getD i EdgeOptions.plain).minLength, i, false⟩
  | _, _ => .error .domain

def graphEdgesFrom (inp : Input) : Nat → List ModelRoute → Except LayoutError (List Edge)
  | _, [] => .ok []
  | i, r :: rs => do
    let edge ← edgeOf inp r i
    let edges ← graphEdgesFrom inp (i + 1) rs
    pure (edge :: edges)

def graphEdges (inp : Input) : Except LayoutError (List Edge) :=
  graphEdgesFrom inp 0 inp.routes

def portCount (edges : List Edge) (v : Nat) : Nat :=
  max ((edges.filter (fun e => e.head == v)).map (·.tail)).eraseDups.length
    ((edges.filter (fun e => e.tail == v)).map (·.head)).eraseDups.length

def sizePort (P : Params) (edges : List Edge) (i : Nat) (n : Node) : Node :=
  { n with w := max n.w ((((portCount edges i : Nat) : Int) + 1) * P.portGap) }

def sizePorts (P : Params) (edges : List Edge) (nodes : List Node) : List Node :=
  nodes.zipIdx.map fun q => sizePort P edges q.2 q.1

def orientNode (d : Direction) (n : Node) : Node :=
  match d with
  | .LR | .RL => { n with w := n.h, h := n.w }
  | .TB | .BT => n

def measuredGraph (P : Params) (inp : Input) (o : Options) (lines : List (List Measure.Line)) :
    Except LayoutError Graph := do
  let nodes ← sizedNodes P lines
  let edges ← graphEdges inp
  pure { nodes := (sizePorts P edges nodes).map (orientNode o.direction)
         edges := edges
         slot := P.slot }

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
  let lab := labelsFix g.edges (n + 1) (Array.range n)
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

def componentRun (P : Params) (cg : Graph) : Except LayoutError Run := do
  let rr ← rankWithBudget cg.withoutSelfLoops
  let p ← normalize cg rr.ranks
  let ord ← orderWithBudget p {}
  let xs ← crossCoordsWith P.nodeGap p ord.layers
  let r ← route p ord.layers xs
  let yt ← rankCoordsWith P.rankGap P.slot p ord.layers (r.gaps.map (·.slots))
  let routes ← routePointsWith P.slot p ord.layers xs yt.1 yt.2 r
  pure ⟨p, ord.layers, xs, yt.1, yt.2, r, routes, rr.budgetExhausted || ord.budgetExhausted⟩

def nodeRect (cg : Graph) (run : Run) (i : Nat) : Rect :=
  let n := cg.nodes.getD i default
  ⟨run.xs.getD i 0 - Int.fdiv n.w 2, run.ys.getD i 0, n.w, n.h⟩

def edgePoints (run : Run) (i : Nat) (e : Edge) : List Point :=
  let pts := (run.routes.getD i default).points
  if e.reversed then pts.reverse else pts

structure Bounds where
  minX : Int
  minY : Int
  right : Int
  bottom : Int

def boundsOf (rects : List Rect) (pts : List Point) : Bounds :=
  let start : Bounds :=
    match rects with
    | [] => ⟨0, 0, 0, 0⟩
    | r :: _ => ⟨r.x, r.y, 0, 0⟩
  let b := rects.foldl
    (fun b r => ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
    start
  pts.foldl
    (fun b p => ⟨min b.minX p.x, min b.minY p.y, max b.right p.x, max b.bottom p.y⟩) b

structure Part where
  rects : List Rect
  routes : List (Nat × List Point)
  width : Int
  height : Int

def shiftPoint (dx dy : Int) (p : Point) : Point := ⟨p.x + dx, p.y + dy⟩

def shiftRect (dx dy : Int) (r : Rect) : Rect := ⟨r.x + dx, r.y + dy, r.w, r.h⟩

def placeComponent (cg : Graph) (run : Run) (cursor : Int) : Part :=
  let rects := (List.range cg.nodes.length).map (nodeRect cg run)
  let b := boundsOf rects (run.routes.flatMap (·.points))
  let dx := cursor - b.minX
  let dy := 0 - b.minY
  { rects := rects.map (shiftRect dx dy)
    routes := cg.edges.zipIdx.map fun q =>
      (q.1.decl, (edgePoints run q.2 q.1).map (shiftPoint dx dy))
    width := b.right - b.minX
    height := b.bottom - b.minY }

structure Acc where
  cursor : Int
  canvasW : Int
  canvasH : Int
  rects : Array Rect
  routes : Array (List Point)
  budget : Bool

def placePart (comp : List Nat) (cg : Graph) (run : Run) (P : Params) (acc : Acc) :
    Except LayoutError Acc :=
  let part := placeComponent cg run acc.cursor
  if I32_MAX < acc.cursor + part.width + P.nodeGap then .error .overflow
  else
    .ok { cursor := acc.cursor + part.width + P.nodeGap
          canvasW := acc.cursor + part.width
          canvasH := max acc.canvasH part.height
          rects := (comp.zip part.rects).foldl (fun a q => a.set! q.1 q.2) acc.rects
          routes := part.routes.foldl (fun a q => a.set! q.1 q.2) acc.routes
          budget := acc.budget || run.budget }

def layoutComponent (P : Params) (g : Graph) (acc : Acc) (comp : List Nat) :
    Except LayoutError Acc := do
  let cg := componentGraph g comp
  let run ← componentRun P cg
  placePart comp cg run P acc

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

def sceneItems (P : Params) (inp : Input) (boxes : List Box) (routes : List Route)
    (lines : List (List Measure.Line)) : List Group :=
  routes.zipIdx.map (fun q =>
    ⟨.edge, q.1.id, edgeItems P q.1.points (inp.edges.getD q.2 EdgeOptions.plain)⟩) ++
  boxes.zipIdx.map fun q => ⟨.node, q.1.id, nodeItems P q.1.rect (lines.getD q.2 [])⟩

def sceneOf (P : Params) (inp : Input) (o : Options) (lines : List (List Measure.Line))
    (acc : Acc) : Scene :=
  let h := acc.canvasH
  let boxes := inp.boxes.zipIdx.map fun q =>
    ⟨q.1.id, q.1.role.id, orientRect o.direction h (acc.rects.getD q.2 default), q.1.parent,
      q.1.exclusive⟩
  let routes := inp.routes.zipIdx.map fun q =>
    ⟨q.1.id, q.1.fromId, q.1.toId, q.1.orthogonal,
      (acc.routes.getD q.2 []).map (orientPoint o.direction h)⟩
  { kind := inp.kind
    profile := o.profile
    options := o
    canvas := orientCanvas o.direction acc.canvasW h
    boxes := boxes
    routes := routes
    items := sceneItems P inp boxes routes lines }

def layout (inp : Input) (o : Options) : Except LayoutError FamilyResult := do
  let P ← checkedParams o.profile
  let m ← metricOf o.profile
  let lines ← boxLines m (Measure.wrapTarget m.profile 0 o.maxWidth) inp
  let g0 ← measuredGraph P inp o lines
  let g := breakCycles g0
  let start : Acc :=
    ⟨0, 0, 0, Array.replicate inp.boxes.length default, Array.replicate inp.routes.length [],
      false⟩
  let acc ← (components g).foldlM (layoutComponent P g) start
  pure ⟨sceneOf P inp o lines acc, acc.budget⟩

theorem bind_ok {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

theorem edgeOf_decl {inp : Input} {r : ModelRoute} {i : Nat} {e : Edge}
    (h : edgeOf inp r i = .ok e) : e.decl = i := by
  unfold edgeOf at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    rfl
  · simp at h

theorem graphEdgesFrom_decls (inp : Input) :
    ∀ (rs : List ModelRoute) (k : Nat) (es : List Edge),
      graphEdgesFrom inp k rs = .ok es → es.map (·.decl) = List.range' k rs.length := by
  intro rs
  induction rs with
  | nil =>
    intro k es h
    simp only [graphEdgesFrom, Except.ok.injEq] at h
    subst h
    simp
  | cons r rs ih =>
    intro k es h
    unfold graphEdgesFrom at h
    obtain ⟨edge, he, h⟩ := bind_ok h
    obtain ⟨edges, hes, h⟩ := bind_ok h
    have h := Except.ok.inj h
    subst h
    rw [List.map_cons, edgeOf_decl he, ih (k + 1) edges hes, List.length_cons, List.range'_succ]

theorem graphEdges_decls_nodup {inp : Input} {es : List Edge} (h : graphEdges inp = .ok es) :
    (es.map (·.decl)).Nodup := by
  unfold graphEdges at h
  rw [graphEdgesFrom_decls inp _ _ _ h]
  exact List.nodup_range'

theorem orient_decl (g : Graph) (e : Edge) : (g.orient e).decl = e.decl := by
  unfold Graph.orient
  split <;> rfl

theorem breakCycles_decls (g : Graph) :
    (breakCycles g).edges.map (·.decl) = g.edges.map (·.decl) := by
  rw [breakCycles_edges_eq, List.map_map]
  have hf : ((·.decl) ∘ g.orient : Edge → Nat) = (·.decl) := funext (orient_decl g)
  rw [hf]

theorem componentGraph_decls_nodup (g : Graph) (comp : List Nat)
    (h : (g.edges.map (·.decl)).Nodup) :
    ((componentGraph g comp).edges.map (·.decl)).Nodup := by
  unfold componentGraph
  simp only [List.map_map]
  exact List.Nodup.sublist ((List.filter_sublist).map _) h

theorem measuredGraph_decls_nodup {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {g0 : Graph}
    (h : measuredGraph P inp o lines = .ok g0) : (g0.edges.map (·.decl)).Nodup := by
  unfold measuredGraph at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨edges, he, h⟩ := bind_ok h
  have h := Except.ok.inj h
  subst h
  exact graphEdges_decls_nodup he

theorem foldlM_ok_mem {α β : Type} (f : β → α → Except LayoutError β) :
    ∀ (l : List α) (a b : β), l.foldlM f a = .ok b → ∀ x ∈ l, ∃ a' b', f a' x = .ok b' := by
  intro l
  induction l with
  | nil =>
    intro a b _ x hx
    simp at hx
  | cons y ys ih =>
    intro a b h x hx
    rw [List.foldlM_cons] at h
    cases hy : f a y with
    | error e =>
      rw [hy] at h
      simp [bind, Except.bind] at h
    | ok a1 =>
      rw [hy] at h
      simp only [bind, Except.bind] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨a, a1, hy⟩
      · exact ih a1 b h x hx'

theorem layoutComponent_run {P : Params} {g : Graph} {acc acc' : Acc} {comp : List Nat}
    (h : layoutComponent P g acc comp = .ok acc') :
    ∃ run, componentRun P (componentGraph g comp) = .ok run := by
  unfold layoutComponent at h
  dsimp only at h
  obtain ⟨run, hrun, _⟩ := bind_ok h
  exact ⟨run, hrun⟩

theorem componentRun_spec {P : Params} {cg : Graph} {run : Run}
    (h : componentRun P cg = .ok run) :
    ∃ ranks, normalize cg ranks = .ok run.proper ∧
      (∃ ord, orderWithBudget run.proper {} = .ok ord ∧ ord.layers = run.layers) ∧
      crossCoordsWith P.nodeGap run.proper run.layers = .ok run.xs ∧
      route run.proper run.layers run.xs = .ok run.routing ∧
      rankCoordsWith P.rankGap P.slot run.proper run.layers
        (run.routing.gaps.map (·.slots)) = .ok (run.ys, run.top) ∧
      routePointsWith P.slot run.proper run.layers run.xs run.ys run.top run.routing =
        .ok run.routes := by
  unfold componentRun at h
  obtain ⟨rr, _, h⟩ := bind_ok h
  obtain ⟨p, hp, h⟩ := bind_ok h
  obtain ⟨ord, hord, h⟩ := bind_ok h
  obtain ⟨xs, hxs, h⟩ := bind_ok h
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨yt, hy, h⟩ := bind_ok h
  obtain ⟨routes, hroutes, h⟩ := bind_ok h
  have h := Except.ok.inj h
  subst h
  exact ⟨rr.ranks, hp, ⟨ord, hord, rfl⟩, hxs, hr, hy, hroutes⟩

def DeclInv (gedges : List Edge) (q : Proper) : Prop :=
  ∀ e ∈ q.edges, ∃ ge, gedges[e.original]? = some ge ∧ e.decl = ge.decl

theorem normalizeEdge_declInv {gedges : List Edge} {slot : Int} {q q' : Proper} {e : Edge}
    {idx : Nat} (hge : gedges[idx]? = some e) (hI : DeclInv gedges q)
    (h : NormalizeImpl.normalizeEdge slot q e idx = .ok q') : DeclInv gedges q' := by
  unfold NormalizeImpl.normalizeEdge at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact hI
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        intro e' he'
        simp only [NormalizeImpl.appendChain] at he'
        rcases List.mem_append.mp he' with he' | he'
        · exact hI e' he'
        · simp only [NormalizeImpl.chainEdges, List.mem_map, List.mem_range] at he'
          obtain ⟨k, _, rfl⟩ := he'
          exact ⟨e, hge, rfl⟩

theorem normalizeLoop_declInv {gedges : List Edge} {slot : Int} :
    ∀ (l : List (Edge × Nat)) (q q' : Proper), (∀ x ∈ l, gedges[x.2]? = some x.1) →
      DeclInv gedges q → NormalizeImpl.normalizeLoop slot l q = .ok q' → DeclInv gedges q'
  | [], q, q', _, hI, h => by
    simp only [NormalizeImpl.normalizeLoop, Except.ok.injEq] at h
    subst h
    exact hI
  | x :: xs, q, q', hl, hI, h => by
    obtain ⟨e, i⟩ := x
    unfold NormalizeImpl.normalizeLoop at h
    split at h
    · simp at h
    · next q1 h1 =>
      exact normalizeLoop_declInv xs q1 q' (fun y hy => hl y (List.mem_cons_of_mem _ hy))
        (normalizeEdge_declInv (hl (e, i) (List.mem_cons_self ..)) hI h1) h

theorem normalize_declInv {g : Graph} {rank : List Int} {p : Proper}
    (h : normalize g rank = .ok p) : DeclInv g.edges p := by
  unfold NormalizeImpl.normalize at h
  split at h
  · simp at h
  · next slot hs =>
    split at h
    · refine normalizeLoop_declInv _ _ _ (fun x hx => List.mem_zipIdx_iff_getElem?.mp hx)
        (fun e he => ?_) h
      simp at he
    · simp at h

theorem nodup_map_inj {α : Type} (f : α → Nat) {l : List α} (hn : (l.map f).Nodup) {a b : Nat}
    {x y : α} (ha : l[a]? = some x) (hb : l[b]? = some y) (h : f x = f y) : a = b := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨hai, hax⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hbi, hbx⟩ := List.getElem?_eq_some_iff.mp hb
  have hpa := List.pairwise_iff_getElem.mp hn
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hpa a b (by simpa using hai) (by simpa using hbi) hlt
    simp [hax, hbx, h] at this
  · have := hpa b a (by simpa using hbi) (by simpa using hai) hlt
    simp [hax, hbx, h] at this

theorem pairwise_inj {α : Type} (g : α → Nat) :
    ∀ l : List α, l.Pairwise (fun a b => g a < g b) →
      ∀ a ∈ l, ∀ b ∈ l, g a = g b → a = b
  | [], _, a, ha, _, _, _ => by simp at ha
  | c :: l, hp, a, ha, b, hb, hab => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · have := h1 b hb'
        omega
    · rcases List.mem_cons.mp hb with rfl | hb'
      · have := h1 a ha'
        omega
      · exact pairwise_inj g l h2 a ha' b hb' hab

theorem chain_pairwise {R : Nat → Nat → Prop} (g : Nat → Nat) (hR : ∀ a b, R a b → g a < g b) :
    ∀ es : List Nat, RouteImpl.chainRel R es → es.Pairwise (fun a b => g a < g b)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [RouteImpl.chainRel] at h
    have ih := chain_pairwise g hR (b :: rest) h.2
    refine List.pairwise_cons.mpr ⟨fun c hc => ?_, ih⟩
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hR a c h.1
    · have h1 := (List.pairwise_cons.mp ih).1 c hc'
      have h2 := hR a b h.1
      omega

theorem edgeAt_mem {p : Proper} {i : Nat} (hi : i < p.edges.length) :
    RouteImpl.edgeAt p i ∈ p.edges := by
  have : RouteImpl.edgeAt p i = p.edges[i] := by
    simp [RouteImpl.edgeAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [this]
  exact List.getElem_mem hi

theorem mem_edgesOf {p : Proper} {o i : Nat} :
    i ∈ RouteImpl.edgesOf p o ↔ i < p.edges.length ∧ (RouteImpl.edgeAt p i).original = o := by
  simp [RouteImpl.edgesOf, List.mem_filter, List.mem_range]

theorem chain_gap_lt {p : Proper} {layers : List (List Nat)}
    (hl : RouteImpl.layersOk p layers = true) {i j : Nat} (h : RouteImpl.ChainLink p i j) :
    RouteImpl.gapOf p i < RouteImpl.gapOf p j := by
  obtain ⟨hi, _, hhead, _⟩ := h
  obtain ⟨_, _, _, hcov, hedge⟩ := RouteImpl.layersOk_spec hl
  obtain ⟨ht, _, hsp⟩ := hedge i hi
  obtain ⟨l, _, _, hnn⟩ := hcov _ ht
  unfold RouteImpl.gapOf
  rw [← hhead]
  omega

theorem gapDeclsDistinct_of_normalize {g : Graph} {rank : List Int} {p : Proper}
    {layers : List (List Nat)} (hd : (g.edges.map (·.decl)).Nodup)
    (hn : normalize g rank = .ok p) (hl : RouteImpl.layersOk p layers = true) :
    RouteImpl.GapDeclsDistinct p := by
  intro i j hi hj hgap hdecl
  obtain ⟨gi, hgi, hdi⟩ := normalize_declInv hn _ (edgeAt_mem hi)
  obtain ⟨gj, hgj, hdj⟩ := normalize_declInv hn _ (edgeAt_mem hj)
  have ho : (RouteImpl.edgeAt p i).original = (RouteImpl.edgeAt p j).original :=
    nodup_map_inj (·.decl) hd hgi hgj (by rw [← hdi, ← hdj, hdecl])
  have hch := normalize_shape hn (RouteImpl.edgeAt p i).original
  have hpw := chain_pairwise (RouteImpl.gapOf p) (fun a b hab => chain_gap_lt hl hab) _ hch
  exact pairwise_inj (RouteImpl.gapOf p) _ hpw i (mem_edgesOf.mpr ⟨hi, rfl⟩) j
    (mem_edgesOf.mpr ⟨hj, ho.symm⟩) hgap

theorem topsFrom_head (rg sl : Int) :
    ∀ (ss hs : List Int) (t : Int), ss.length + 1 = hs.length →
      (CoordsImpl.topsFrom rg sl t hs ss).getD 0 0 = t
  | [], [_], t, _ => by simp [CoordsImpl.topsFrom]
  | [], [], t, h => by simp at h
  | [], _ :: _ :: _, t, h => by simp at h
  | _ :: _, [], t, h => by simp at h
  | _ :: _, _ :: _, t, _ => by simp [CoordsImpl.topsFrom]

theorem topsFrom_step (rg sl : Int) :
    ∀ (ss hs : List Int) (t : Int) (k : Nat), ss.length + 1 = hs.length → k + 1 < hs.length →
      (CoordsImpl.topsFrom rg sl t hs ss).getD (k + 1) 0 =
        (CoordsImpl.topsFrom rg sl t hs ss).getD k 0 + hs.getD k 0 + rg + sl * ss.getD k 0 := by
  intro ss
  induction ss with
  | nil =>
    intro hs t k h1 h2
    simp at h1
    omega
  | cons s ss ih =>
    intro hs t k h1 h2
    cases hs with
    | nil => simp at h1
    | cons h hs =>
      cases hs with
      | nil => simp at h1
      | cons h2' hs' =>
        have hlen : ss.length + 1 = (h2' :: hs').length := by simpa using h1
        have e : CoordsImpl.topsFrom rg sl t (h :: h2' :: hs') (s :: ss) =
            t :: CoordsImpl.topsFrom rg sl (t + h + rg + sl * s) (h2' :: hs') ss := rfl
        rw [e]
        cases k with
        | zero =>
          simp only [List.getD_cons_succ, List.getD_cons_zero]
          rw [topsFrom_head rg sl ss (h2' :: hs') _ hlen]
        | succ k' =>
          simp only [List.getD_cons_succ]
          exact ih (h2' :: hs') _ k' hlen (by simpa using h2)

theorem coordFacts_of_pipeline {P : Params} (hP : P.Valid) {p : Proper}
    {layers : List (List Nat)} {xs ys top : List Int} {r : Routing}
    (hx : crossCoordsWith P.nodeGap p layers = .ok xs) (hr : route p layers xs = .ok r)
    (hy : rankCoordsWith P.rankGap P.slot p layers (r.gaps.map (·.slots)) = .ok (ys, top)) :
    CoordFacts p layers xs ys top r P.nodeGap P.rankGap P.slot := by
  obtain ⟨hg, hrg, hs, hh⟩ := hP
  refine ⟨hg, by omega, hs, hh, ?_, ?_, ?_⟩
  · intro layer hl i a b ha hb
    exact balance_separated hx layer hl i a b ha hb
  · intro k l v hkl hv hvn hrk
    exact rankAxis_node_in_band hy hkl hv hvn hrk
  · intro k l hkl hk
    obtain ⟨_, _, hlen, _, _, htop, _⟩ := CoordsImpl.rankCoordsWith_spec hy
    obtain ⟨_, _, _, _, _, hgaps, _⟩ := RouteImpl.route_spec hr
    subst htop
    have hgl : r.gaps.length = layers.length - 1 := by
      rw [hgaps]
      simp
    have hk' : k < r.gaps.length := by omega
    have hh : (layers.map (CoordsImpl.layerHeight p)).getD k 0 = CoordsImpl.layerHeight p l := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, hkl]
    have hs' : (r.gaps.map (·.slots)).getD k 0 = (r.gaps.getD k default).slots := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk']
    rw [topsFrom_step P.rankGap P.slot (r.gaps.map (·.slots))
      (layers.map (CoordsImpl.layerHeight p)) 0 k (by simp; omega) (by simpa using hk), hh, hs']
    rfl

theorem componentRun_facts {P : Params} (hP : P.Valid) {cg : Graph} {run : Run}
    (hd : (cg.edges.map (·.decl)).Nodup) (h : componentRun P cg = .ok run) :
    RouteImpl.ProperShape run.proper ∧ RouteImpl.GapDeclsDistinct run.proper ∧
      CoordFacts run.proper run.layers run.xs run.ys run.top run.routing P.nodeGap P.rankGap
        P.slot := by
  obtain ⟨ranks, hn, _, hx, hr, hy, _⟩ := componentRun_spec h
  obtain ⟨hl, _⟩ := RouteImpl.route_spec hr
  exact ⟨normalize_shape hn, gapDeclsDistinct_of_normalize hd hn hl,
    coordFacts_of_pipeline hP hx hr hy⟩

theorem checkedParams_valid {profile : Profile} {P : Params}
    (h : checkedParams profile = .ok P) : P.Valid := by
  unfold checkedParams at h
  split at h
  · simp at h
  · next Q hQ =>
    split at h
    · next hv =>
      simp only [Except.ok.injEq] at h
      subst h
      exact hv
    · simp at h

theorem layout_component_facts {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res) :
    ∃ P lines g0, checkedParams o.profile = .ok P ∧ measuredGraph P inp o lines = .ok g0 ∧
      ∀ comp ∈ components (breakCycles g0), ∃ run,
        componentRun P (componentGraph (breakCycles g0) comp) = .ok run ∧
        RouteImpl.ProperShape run.proper ∧ RouteImpl.GapDeclsDistinct run.proper ∧
        CoordFacts run.proper run.layers run.xs run.ys run.top run.routing P.nodeGap P.rankGap
          P.slot := by
  unfold layout at h
  dsimp only at h
  obtain ⟨P, hP, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨lines, _, h⟩ := bind_ok h
  obtain ⟨g0, hg0, h⟩ := bind_ok h
  obtain ⟨acc, hacc, _⟩ := bind_ok h
  refine ⟨P, lines, g0, hP, hg0, fun comp hcomp => ?_⟩
  obtain ⟨a', b', hab⟩ := foldlM_ok_mem _ _ _ _ hacc comp hcomp
  obtain ⟨run, hrun⟩ := layoutComponent_run hab
  refine ⟨run, hrun, ?_⟩
  refine componentRun_facts (checkedParams_valid hP) ?_ hrun
  refine componentGraph_decls_nodup _ _ ?_
  rw [breakCycles_decls]
  exact measuredGraph_decls_nodup hg0

theorem zipIdx_map_comp {α β : Type} (f : α → β) :
    ∀ (l : List α) (k : Nat), (l.zipIdx k).map (fun q => f q.1) = l.map f
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, zipIdx_map_comp f l (k + 1)]

theorem layout_ids {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res) :
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  unfold layout at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  have h := Except.ok.inj h
  subst h
  simp only [sceneOf, List.map_map]
  exact ⟨zipIdx_map_comp (·.id) inp.boxes 0, zipIdx_map_comp (·.id) inp.routes 0⟩

end PipelineImpl

def layoutFamily (inp : Input) (o : Options) : Except LayoutError FamilyResult :=
  PipelineImpl.layout inp o

theorem normalize_gapDeclsDistinct {g : Graph} {rank : List Int} {p : Proper}
    {layers : List (List Nat)} (hd : (g.edges.map (·.decl)).Nodup)
    (hn : normalize g rank = .ok p) (hl : RouteImpl.layersOk p layers = true) :
    GapDeclsDistinct p :=
  PipelineImpl.gapDeclsDistinct_of_normalize hd hn hl

theorem coordPhases_coordFacts {P : PipelineImpl.Params} (hP : P.Valid) {p : Proper}
    {layers : List (List Nat)} {xs ys top : List Int} {r : Routing}
    (hx : crossCoordsWith P.nodeGap p layers = .ok xs) (hr : route p layers xs = .ok r)
    (hy : rankCoordsWith P.rankGap P.slot p layers (r.gaps.map (·.slots)) = .ok (ys, top)) :
    CoordFacts p layers xs ys top r P.nodeGap P.rankGap P.slot :=
  PipelineImpl.coordFacts_of_pipeline hP hx hr hy

theorem layoutFamily_component_facts {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamily inp o = .ok res) :
    ∃ P lines g0, PipelineImpl.checkedParams o.profile = .ok P ∧
      PipelineImpl.measuredGraph P inp o lines = .ok g0 ∧
      ∀ comp ∈ PipelineImpl.components (breakCycles g0), ∃ run,
        PipelineImpl.componentRun P (PipelineImpl.componentGraph (breakCycles g0) comp) = .ok run ∧
        RouteImpl.ProperShape run.proper ∧ GapDeclsDistinct run.proper ∧
        CoordFacts run.proper run.layers run.xs run.ys run.top run.routing P.nodeGap P.rankGap
          P.slot :=
  PipelineImpl.layout_component_facts h

theorem layoutFamily_ids {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamily inp o = .ok res) :
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) :=
  PipelineImpl.layout_ids h

end Layered
end Elegant

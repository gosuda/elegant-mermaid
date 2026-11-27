import Elegant.Layered.Route
import ElegantGeometry.Route

namespace Elegant
namespace Layered

/-- Straightening context for one placed component: the untranslated
    layout inputs. The caller supplies the Pack offset separately. -/
structure StraightenCtx where
  proper : Proper
  layers : List (List Nat)
  xs : List Int
  ys : List Int
  tops : List Int
  routing : Routing
  lanes : RouteImpl.LaneRouting
  slot : Int
  reversed : List Bool
  decls : List Nat
  dx : Int
  dy : Int
deriving Inhabited

def straightPort (source target lo hi : Int) : Int :=
  if lo ≤ source ∧ source ≤ hi then source
  else if lo ≤ target ∧ target ≤ hi then target
  else lo + (hi - lo) / 2

def narrowI32 (n : Int) : Except LayoutError Int :=
  if -2147483648 ≤ n ∧ n ≤ 2147483647 then .ok n else .error .overflow

def straightAdjacent : List Point → List (Point × Point)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: straightAdjacent (b :: rest)
def straightStepClear (boxes : List (Bool × Rect)) (tailBox headBox : Rect)
    (top bottom cx : Int) : Bool :=
  boxes.all fun b =>
    b.2 == tailBox || b.2 == headBox || !b.1 ||
      !Polyline.hitsRectB [⟨cx, top⟩, ⟨cx, bottom⟩] b.2

def straightStepBusy (routes : Array (List Point)) (decl : Nat)
    (top bottom cx : Int) : Bool :=
  (List.range routes.size).any fun i =>
    decide (i ≠ decl) &&
      (straightAdjacent (routes.getD i [])).any fun s =>
        let a := s.1
        let b := s.2
        decide (a.x = b.x ∧ a.x = cx ∧ top ≤ max a.y b.y ∧ min a.y b.y ≤ bottom)

def straightOrientation (ax ay bx qy px py : Int) : Int :=
  let cross := (bx - ax) * (py - ay) - (qy - ay) * (px - ax)
  if cross < 0 then -1 else if cross > 0 then 1 else 0

def straightSegmentsCross (a b c d : Point) : Bool :=
  (straightOrientation a.x a.y b.x b.y c.x c.y *
      straightOrientation a.x a.y b.x b.y d.x d.y == -1) &&
    (straightOrientation c.x c.y d.x d.y a.x a.y *
      straightOrientation c.x c.y d.x d.y b.x b.y == -1)

def straightCrossings (a b : List Point) : Nat :=
  ((straightAdjacent a).map fun s =>
    ((straightAdjacent b).filter fun t => straightSegmentsCross s.1 s.2 t.1 t.2).length).sum

def straightCrossingsGrew (routes : Array (List Point)) (decl : Nat)
    (oldPoints newPoints : List Point) : Bool :=
  let total := fun pts =>
    ((List.range routes.size).filter fun i => decide (i != decl)).foldl
      (fun acc i => acc + straightCrossings pts (routes.getD i [])) 0
  decide (total newPoints > total oldPoints)

def straightRealNode (p : Proper) (v : Nat) : Bool :=
  match p.nodes[v]? with
  | some n => (!n.dummy) && (!n.label) && (n.node.border == 0)
  | none => false

def straightSetNth (xs : List Int) (i : Nat) (v : Int) : List Int :=
  xs.zipIdx.map fun q => if q.2 == i then v else q.1

structure StraightenWork where
  routing : Routing
  routes : Array (List Point)

def straightEdgeEligible (ctx : StraightenCtx) (routing : Routing) (i : Nat)
    (e : ProperEdge) : Bool :=
  let sx := routing.sourceX.getD i 0
  !e.synthetic && !(ctx.reversed.getD e.original false) &&
    straightRealNode ctx.proper e.tail && straightRealNode ctx.proper e.head &&
    e.tail != e.head && (routing.sourceRun.isEmpty || routing.sourceRun.getD i 0 == sx) &&
      !(sx == routing.targetX.getD i 0)

/-- The original route index, port column, and box span of one straightenable
    edge, already moved by the context offset. -/
structure StraightSpan where
  orig : Nat
  decl : Nat
  cx : Int
  pin : Int
  top : Int
  bottom : Int
  column : Int
  tailRect : Rect
  headRect : Rect

/-- Pure geometry of a straightening candidate: node sizes, box edges,
    overlap window, and port column. -/
structure StraightGeom where
  tw : Int
  hw : Int
  th : Int
  hh : Int
  tailLeft : Int
  headLeft : Int
  lo : Int
  hi : Int
  cx : Int

/-- The window and port column of edge `i`. -/
def straightGeom (ctx : StraightenCtx) (routing : Routing) (i : Nat)
    (e : ProperEdge) : StraightGeom :=
  let tw := match ctx.proper.nodes[e.tail]? with | some n => n.node.w | none => 0
  let hw := match ctx.proper.nodes[e.head]? with | some n => n.node.w | none => 0
  let th := match ctx.proper.nodes[e.tail]? with | some n => n.node.h | none => 0
  let hh := match ctx.proper.nodes[e.head]? with | some n => n.node.h | none => 0
  let tailLeft := ctx.xs.getD e.tail 0 - tw / 2
  let headLeft := ctx.xs.getD e.head 0 - hw / 2
  let lo := max tailLeft headLeft
  let hi := min (tailLeft + tw) (headLeft + hw)
  let cx := straightPort (routing.sourceX.getD i 0) (routing.targetX.getD i 0) lo hi
  ⟨tw, hw, th, hh, tailLeft, headLeft, lo, hi, cx⟩

def straightSpanOf (ctx : StraightenCtx) (routing : Routing) (i : Nat) :
    Except LayoutError (Option StraightSpan) := do
  match ctx.proper.edges[i]? with
  | none => pure none
  | some e =>
    if !straightEdgeEligible ctx routing i e then return none
    match straightGeom ctx routing i e with
    | ⟨tw, hw, th, hh, tailLeft, headLeft, lo, hi, cx⟩ =>
      if lo > hi then return none
      let pin ← narrowI32 cx
      let top ← narrowI32 (ctx.ys.getD e.tail 0 + th + ctx.dy)
      let bottom ← narrowI32 (ctx.ys.getD e.head 0 + ctx.dy)
      if top ≥ bottom then return none
      let column ← narrowI32 (cx + ctx.dx)
      pure (some ⟨e.original, ctx.decls.getD e.original 0, cx, pin, top, bottom, column,
        ⟨tailLeft + ctx.dx, top - th, tw, th⟩, ⟨headLeft + ctx.dx, bottom, hw, hh⟩⟩)

/-- The installed route of a span: two points on one column. -/
def StraightSpan.points (span : StraightSpan) : List Point :=
  [⟨span.column, span.top⟩, ⟨span.column, span.bottom⟩]

/-- The routing of edge `i` with its port, target, and run column set to `cx`. -/
def straightSnap (routing : Routing) (i : Nat) (cx : Int) : Routing :=
  { routing with sourceX := straightSetNth routing.sourceX i cx,
                 targetX := straightSetNth routing.targetX i cx,
                 sourceRun := straightSetNth routing.sourceRun i cx }

/-- The least and greatest x and y over a route. -/
def straightExtent : List Point → Option (Int × Int × Int × Int)
  | [] => none
  | q :: rest =>
    match straightExtent rest with
    | none => some (q.x, q.y, q.x, q.y)
    | some (x0, y0, x1, y1) => some (min x0 q.x, min y0 q.y, max x1 q.x, max y1 q.y)

/-- Whether every point of `new` lies inside the bounding box of `old`. -/
def straightInside (old new : List Point) : Bool :=
  match straightExtent old with
  | none => new.isEmpty
  | some (x0, y0, x1, y1) =>
    new.all fun q => decide (x0 ≤ q.x ∧ q.x ≤ x1 ∧ y0 ≤ q.y ∧ q.y ≤ y1)

/-- The rewrite one edge admits, or none when an acceptance check declines. -/
def straightenPlan (ctx : StraightenCtx) (boxes : List (Bool × Rect))
    (st : StraightenWork) (i : Nat) :
    Except LayoutError (Option (Routing × Nat × List Point)) := do
  match ← straightSpanOf ctx st.routing i with
  | none => pure none
  | some span =>
    if !straightStepClear boxes span.tailRect span.headRect span.top span.bottom span.column then
      return none
    if straightStepBusy st.routes span.decl span.top span.bottom span.column then return none
    if straightCrossingsGrew st.routes span.decl (st.routes.getD span.decl []) span.points ||
        !straightInside (st.routes.getD span.decl []) span.points then return none
    pure (some (straightSnap st.routing i span.pin, span.decl, span.points))

def straightenStep (ctx : StraightenCtx) (boxes : List (Bool × Rect))
    (st : StraightenWork) (i : Nat) : Except LayoutError StraightenWork := do
  match ← straightenPlan ctx boxes st i with
  | none => pure st
  | some (routing, decl, newPoints) =>
    pure { routing, routes := if h : decl < st.routes.size then st.routes.set decl newPoints h else st.routes }

/-- Straighten edges `start` to `start + n - 1` in ascending order. -/
def straightenFrom (ctx : StraightenCtx) (boxes : List (Bool × Rect)) :
    Nat → Nat → StraightenWork → Except LayoutError StraightenWork
  | 0, _, st => .ok st
  | n + 1, start, st => do
    let st ← straightenStep ctx boxes st start
    straightenFrom ctx boxes n (start + 1) st

def straightenComponent (ctx : StraightenCtx) (boxes : List (Bool × Rect))
    (routes : Array (List Point)) : Except LayoutError (Array (List Point)) := do
  let st ← straightenFrom ctx boxes ctx.proper.edges.length 0 { routing := ctx.routing, routes }
  pure st.routes


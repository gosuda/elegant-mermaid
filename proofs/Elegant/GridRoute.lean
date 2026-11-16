import ElegantGeometry.Basic

set_option autoImplicit false

/-! The routing and label placement of the grid family's block kind (`spec/layout/grid.md`,
grid-61 to grid-65): the lattice of gap midlines and end-box centre lines, the minimum-cost
search with the bend and crowding costs, the self-loop, and the label candidates.

The search is Dijkstra over the states `vertex * 4 + direction` with the total order
`(cost, state)` on queue items, so the pop order does not depend on the heap that holds them.
The lattice segment test is the direct overlap test: a segment is free exactly when no leaf
interior is crossed by it. -/

namespace Elegant
namespace Grid

/-! ### The priority queue -/

inductive Heap where
  | nil
  | node (cost : Int) (state : Nat) (left right : Heap)

def Heap.size : Heap → Nat
  | .nil => 0
  | .node _ _ l r => l.size + r.size + 1

/-- The total order `(cost, state)`. -/
def itemLE (c1 : Int) (s1 : Nat) (c2 : Int) (s2 : Nat) : Bool :=
  decide (c1 < c2) || (decide (c1 = c2) && decide (s1 ≤ s2))

def Heap.merge (a b : Heap) : Heap :=
  match a, b with
  | .nil, h => h
  | h, .nil => h
  | .node c1 s1 l1 r1, .node c2 s2 l2 r2 =>
    if itemLE c1 s1 c2 s2 then .node c1 s1 (Heap.merge (.node c2 s2 l2 r2) r1) l1
    else .node c2 s2 (Heap.merge (.node c1 s1 l1 r1) r2) l2
termination_by a.size + b.size
decreasing_by
  all_goals simp_wf
  all_goals simp only [Heap.size]
  all_goals omega

def Heap.push (h : Heap) (cost : Int) (state : Nat) : Heap :=
  Heap.merge (.node cost state .nil .nil) h

def Heap.pop : Heap → Option (Int × Nat × Heap)
  | .nil => none
  | .node c s l r => some (c, s, Heap.merge l r)

/-! ### Geometry helpers -/

def manhattan (a b : Point) : Int := ((a.x - b.x).natAbs : Int) + ((a.y - b.y).natAbs : Int)

def collinear (a b c : Point) : Bool :=
  (a.x == b.x && b.x == c.x) || (a.y == b.y && b.y == c.y)

def popCollinear : List Point → Point → List Point
  | b :: a :: rest, p => if collinear a b p then popCollinear (a :: rest) p else b :: a :: rest
  | acc, _ => acc

/-- Drop repeated points and the middle point of three collinear points. -/
def simplify (ps : List Point) : List Point :=
  (ps.foldl (fun acc p => if acc.head? = some p then acc else p :: popCollinear acc p) []).reverse

def overlaps (a b : Rect) : Bool :=
  decide (a.x < b.x + b.w) && decide (b.x < a.x + a.w) &&
    decide (a.y < b.y + b.h) && decide (b.y < a.y + a.h)

def strictlyInside (outer inner : Rect) : Bool :=
  decide (outer.x < inner.x) && decide (inner.x + inner.w < outer.x + outer.w) &&
    decide (outer.y < inner.y) && decide (inner.y + inner.h < outer.y + outer.h)

/-! ### Sorted unique coordinates -/

def dedup : List Int → List Int
  | a :: b :: rest => if a = b then dedup (b :: rest) else a :: dedup (b :: rest)
  | l => l

def sortedUnique (xs : List Int) : List Int := dedup (xs.mergeSort fun a b => decide (a ≤ b))

/-! ### The lattice -/

structure Lat where
  xs : Array Int
  ys : Array Int
  leaves : List Rect

def Lat.ny (l : Lat) : Nat := l.ys.size

def Lat.cells (l : Lat) : Nat := l.xs.size * l.ys.size

def Lat.point (l : Lat) (v : Nat) : Point := ⟨l.xs.getD (v / l.ny) 0, l.ys.getD (v % l.ny) 0⟩

/-- The lattice vertex at a point, when both coordinates are lattice lines. -/
def Lat.vertex (l : Lat) (p : Point) : Option Nat :=
  match l.xs.findIdx? (· == p.x), l.ys.findIdx? (· == p.y) with
  | some i, some j => some (i * l.ny + j)
  | _, _ => none

/-- The horizontal segment from vertex `(i, j)` to `(i + 1, j)` crosses no leaf interior. -/
def Lat.freeH (l : Lat) (i j : Nat) : Bool :=
  !l.leaves.any fun r =>
    decide (r.y < l.ys.getD j 0) && decide (l.ys.getD j 0 < r.y + r.h) &&
      decide (r.x < l.xs.getD (i + 1) 0) && decide (l.xs.getD i 0 < r.x + r.w)

/-- The vertical segment from vertex `(i, j)` to `(i, j + 1)` crosses no leaf interior. -/
def Lat.freeV (l : Lat) (i j : Nat) : Bool :=
  !l.leaves.any fun r =>
    decide (r.x < l.xs.getD i 0) && decide (l.xs.getD i 0 < r.x + r.w) &&
      decide (r.y < l.ys.getD (j + 1) 0) && decide (l.ys.getD j 0 < r.y + r.h)

/-- Directions: east 0, west 1, south 2, north 3. -/
def dirDelta : Nat → Int × Int
  | 0 => (1, 0)
  | 1 => (-1, 0)
  | 2 => (0, 1)
  | _ => (0, -1)

/-- The vertex one step from `v` in direction `d`, inside the lattice. -/
def Lat.neighbour (l : Lat) (v d : Nat) : Option Nat :=
  let i : Int := ((v / l.ny : Nat) : Int) + (dirDelta d).1
  let j : Int := ((v % l.ny : Nat) : Int) + (dirDelta d).2
  if v < l.cells ∧ 0 ≤ i ∧ i < (l.xs.size : Int) ∧ 0 ≤ j ∧ j < (l.ys.size : Int) then
    some (i.toNat * l.ny + j.toNat)
  else none

/-- The segment between adjacent vertices `v` and `u` moving in direction `d` is free. -/
def Lat.free (l : Lat) (v u d : Nat) : Bool :=
  let m := min v u
  if d < 2 then l.freeH (m / l.ny) (m % l.ny) else l.freeV (m / l.ny) (m % l.ny)

/-- One lattice step: the next vertex and the length of the segment. -/
def Lat.step (l : Lat) (v d : Nat) : Option (Nat × Int) :=
  match l.neighbour v d with
  | some u => if l.free v u d then some (u, manhattan (l.point v) (l.point u)) else none
  | none => none

/-! ### The search -/

structure End where
  port : Point
  vertex : Nat
  stub : Int
  deriving Repr, Inhabited

structure Entry where
  dist : Int
  prev : Int
  deriving Repr, Inhabited

/-- The segments used by earlier edges, keyed by the smaller vertex of the segment. -/
structure Used where
  h : Array (List Nat)
  v : Array (List Nat)

def Used.empty (cells : Nat) : Used := ⟨Array.replicate cells [], Array.replicate cells []⟩

def Used.get (u : Used) (d key : Nat) : List Nat :=
  if d < 2 then u.h.getD key [] else u.v.getD key []

def Used.add (u : Used) (d key edge : Nat) : Used :=
  if d < 2 then { u with h := u.h.set! key (edge :: u.h.getD key []) }
  else { u with v := u.v.set! key (edge :: u.v.getD key []) }

/-- Two edges share no end box. -/
def disjointEdges (a b : Nat × Nat) : Bool :=
  a.1 != b.1 && a.1 != b.2 && a.2 != b.1 && a.2 != b.2

structure Arrival where
  cost : Int
  state : Nat
  side : Nat
  deriving Repr, Inhabited

def outward : Nat → Nat
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | _ => 0

def inward : Nat → Nat
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | _ => 1

/-- The data one search reads: the lattice, the costs, and the edges. -/
structure Router where
  lat : Lat
  bend : Int
  edges : List (Nat × Nat)

def Router.turn (r : Router) (a b : Nat) : Int := if a = b then 0 else r.bend

def Router.crowd (r : Router) (used : Used) (cur v u d : Nat) : Int :=
  if (used.get d (min v u)).any (fun o => disjointEdges (r.edges.getD o (0, 0)) (r.edges.getD cur (0, 0)))
  then 4 * r.bend else 0

abbrev Tab := Array (Option Entry)

def relax (tab : Tab) (heap : Heap) (state : Nat) (cost : Int) (src : Int) : Tab × Heap :=
  match tab.getD state none with
  | some e =>
    if e.dist ≤ cost then (tab, heap)
    else (tab.set! state (some ⟨cost, src⟩), heap.push cost state)
  | none => (tab.set! state (some ⟨cost, src⟩), heap.push cost state)

def arrive (r : Router) (targets : List End) (cost : Int) (state : Nat)
    (best : Option Arrival) : Option Arrival :=
  (List.range 4).foldl (fun best s =>
    if (targets.getD s default).vertex = state / 4 then
      let total := cost + (targets.getD s default).stub + r.turn (state % 4) (inward s)
      match best with
      | some b => if total < b.cost then some ⟨total, state, s⟩ else best
      | none => some ⟨total, state, s⟩
    else best) best

def expand (r : Router) (used : Used) (cur : Nat) (tab : Tab) (heap : Heap) (cost : Int)
    (state : Nat) : Tab × Heap :=
  (List.range 4).foldl (fun (th : Tab × Heap) next =>
    match r.lat.step (state / 4) next with
    | some (u, len) =>
      relax th.1 th.2 (u * 4 + next)
        (cost + len + r.turn (state % 4) next + r.crowd used cur (state / 4) u next) (state : Int)
    | none => th) (tab, heap)

def stopQ (best : Option Arrival) (cost : Int) : Bool :=
  match best with
  | some b => decide (b.cost ≤ cost)
  | none => false

def staleQ (tab : Tab) (state : Nat) (cost : Int) : Bool :=
  match tab.getD state none with
  | some e => decide (e.dist < cost)
  | none => true

/-- The Dijkstra loop. `fuel` bounds the number of pops. -/
def dijkstra (r : Router) (used : Used) (cur : Nat) (targets : List End) :
    Nat → Tab → Heap → Option Arrival → Tab × Option Arrival
  | 0, tab, _, best => (tab, best)
  | fuel + 1, tab, heap, best =>
    match heap.pop with
    | none => (tab, best)
    | some (cost, state, heap') =>
      if stopQ best cost then (tab, best)
      else if staleQ tab state cost then dijkstra r used cur targets fuel tab heap' best
      else
        let best' := arrive r targets cost state best
        let (tab', heap'') := expand r used cur tab heap' cost state
        dijkstra r used cur targets fuel tab' heap'' best'

/-- Walk the predecessor chain back to the source seed. -/
def chain (lat : Lat) (tab : Tab) (sources : List End) :
    Nat → Nat → List Point → Option (List Point)
  | 0, _, _ => none
  | fuel + 1, state, acc =>
    match tab.getD state none with
    | some e =>
      let acc := lat.point (state / 4) :: acc
      if e.prev < 0 then some ((sources.getD (-1 - e.prev).toNat default).port :: acc)
      else chain lat tab sources fuel e.prev.toNat acc
    | none => none

/-- Record the segments of the found path as used by edge `cur`. -/
def claim (tab : Tab) (cur : Nat) : Nat → Nat → Used → Used
  | 0, _, used => used
  | fuel + 1, state, used =>
    match tab.getD state none with
    | some e =>
      if e.prev < 0 then used
      else
        let p := e.prev.toNat
        claim tab cur fuel p (used.add (state % 4) (min (p / 4) (state / 4)) cur)
    | none => used

/-- One source-to-target search. The result is the simplified route and the updated usage. -/
def search (r : Router) (used : Used) (cur : Nat) (sources targets : List End) :
    Option (List Point × Used) :=
  let states := r.lat.cells * 4
  let seeded := (List.range 4).foldl (fun (th : Tab × Heap) s =>
    relax th.1 th.2 ((sources.getD s default).vertex * 4 + outward s)
      (sources.getD s default).stub (-1 - (s : Int))) (Array.replicate states none, Heap.nil)
  match dijkstra r used cur targets (4 * states + 8) seeded.1 seeded.2 none with
  | (tab, some best) =>
    match chain r.lat tab sources (states + 1) best.state [(targets.getD best.side default).port] with
    | some pts => some (simplify pts, claim tab cur (states + 1) best.state used)
    | none => none
  | (_, none) => none

/-- The port on a side of a box and the junction on its gap midline. -/
def portOf (pad gapX gapY : Int) (r : Rect) : Nat → Point × Point
  | 0 => (⟨r.x + Int.fdiv r.w 2, r.y⟩, ⟨r.x + Int.fdiv r.w 2, r.y - gapY + pad⟩)
  | 1 => (⟨r.x + Int.fdiv r.w 2, r.y + r.h⟩, ⟨r.x + Int.fdiv r.w 2, r.y + r.h + pad⟩)
  | 2 => (⟨r.x, r.y + Int.fdiv r.h 2⟩, ⟨r.x - gapX + pad, r.y + Int.fdiv r.h 2⟩)
  | _ => (⟨r.x + r.w, r.y + Int.fdiv r.h 2⟩, ⟨r.x + r.w + pad, r.y + Int.fdiv r.h 2⟩)

/-- The four ends of a box, in the side order top, bottom, left, right. -/
def endsOf (lat : Lat) (pad gapX gapY : Int) (r : Rect) : Option (List End) :=
  (List.range 4).mapM fun s =>
    let pj := portOf pad gapX gapY r s
    (lat.vertex pj.2).map fun v => ⟨pj.1, v, manhattan pj.1 pj.2⟩

/-- The route of a self-loop: out of the right side and back in. -/
def loopOf (pad : Int) (r : Rect) : List Point :=
  let edge := r.x + r.w
  let out := r.x + r.w + pad
  let upper := r.y + Int.fdiv r.h 3
  let lower := r.y + Int.fdiv (2 * r.h) 3
  simplify [⟨edge, upper⟩, ⟨out, upper⟩, ⟨out, lower⟩, ⟨edge, lower⟩]

structure Edge where
  fromBox : Nat
  toBox : Nat
  label : Size
  deriving DecidableEq, Repr, Inhabited

/-- The geometry the routing and the label placement read. -/
structure RouteIn where
  pad : Int
  bend : Int
  thick : Int
  gapX : Int
  gapY : Int
  vlines : List Int
  hlines : List Int
  rects : List Rect
  leaves : List Rect
  frames : List Rect
  edges : List Edge

def maxLattice : Nat := 1048576

def buildLat (inp : RouteIn) : Except LayoutError Lat :=
  let centres := inp.edges.flatMap fun e =>
    [e.fromBox, e.toBox].map fun b =>
      let r := inp.rects.getD b default
      (r.x + Int.fdiv r.w 2, r.y + Int.fdiv r.h 2)
  let xs := sortedUnique (inp.vlines ++ centres.map (·.1))
  let ys := sortedUnique (inp.hlines ++ centres.map (·.2))
  if maxLattice < xs.length * ys.length then .error .overflow
  else .ok ⟨xs.toArray, ys.toArray, inp.leaves⟩

def routeEdges (inp : RouteIn) (r : Router) :
    Nat → List Edge → Used → List (List Point) → Option (List (List Point))
  | _, [], _, acc => some acc.reverse
  | k, e :: es, used, acc =>
    if e.fromBox = e.toBox then
      routeEdges inp r (k + 1) es used (loopOf inp.pad (inp.rects.getD e.fromBox default) :: acc)
    else
      match endsOf r.lat inp.pad inp.gapX inp.gapY (inp.rects.getD e.fromBox default),
          endsOf r.lat inp.pad inp.gapX inp.gapY (inp.rects.getD e.toBox default) with
      | some src, some tgt =>
        match search r used k src tgt with
        | some (pts, used') => routeEdges inp r (k + 1) es used' (pts :: acc)
        | none => none
      | _, _ => none

/-- Every edge route, in declaration order. -/
def routes (inp : RouteIn) : Except LayoutError (List (List Point)) :=
  match inp.edges with
  | [] => .ok []
  | edges =>
    match buildLat inp with
    | .error e => .error e
    | .ok lat =>
      let r : Router := ⟨lat, inp.bend, edges.map fun e => (e.fromBox, e.toBox)⟩
      match routeEdges inp r 0 edges (Used.empty lat.cells) [] with
      | some rs => .ok rs
      | none => .error .domain

/-! ### Labels -/

def segmentTouches (a b : Point) (thick : Int) (r : Rect) : Bool :=
  decide (min a.x b.x < r.x + r.w) && decide (r.x < max a.x b.x + thick) &&
    decide (min a.y b.y < r.y + r.h) && decide (r.y < max a.y b.y + thick)

def routeTouches (thick : Int) (r : Rect) : List Point → Bool
  | a :: b :: rest => segmentTouches a b thick r || routeTouches thick r (b :: rest)
  | _ => false

/-- The two candidate boxes beside one segment. -/
def beside (pad thick : Int) (a b : Point) (size : Size) : List Rect :=
  let mx := Int.fdiv (a.x + b.x) 2
  let my := Int.fdiv (a.y + b.y) 2
  let off := Int.fdiv pad 2
  if a.y = b.y then
    [⟨mx - Int.fdiv size.w 2, my - off - size.h, size.w, size.h⟩,
     ⟨mx - Int.fdiv size.w 2, my + thick + off, size.w, size.h⟩]
  else
    [⟨mx + thick + off, my - Int.fdiv size.h 2, size.w, size.h⟩,
     ⟨mx - off - size.w, my - Int.fdiv size.h 2, size.w, size.h⟩]

def segLen (route : List Point) (i : Nat) : Int :=
  manhattan (route.getD i default) (route.getD (i + 1) default)

/-- The candidates, over the segments from the longest to the shortest, ties by order. -/
def candidates (pad thick : Int) (route : List Point) (size : Size) : List Rect :=
  let idx := (List.range (route.length - 1)).filter fun i => decide (0 < segLen route i)
  let order := idx.mergeSort fun i j => decide (segLen route j ≤ segLen route i)
  order.flatMap fun i => beside pad thick (route.getD i default) (route.getD (i + 1) default) size

structure Site where
  routes : List (List Point)
  leaves : List Rect
  frames : List Rect
  placed : List Rect
  canvas : Rect

def Site.vacant (s : Site) (thick : Int) (r : Rect) : Bool :=
  strictlyInside s.canvas r &&
    s.frames.all (fun f => !overlaps f r || strictlyInside f r) &&
    !(s.leaves.any fun o => overlaps r o) && !(s.placed.any fun o => overlaps r o) &&
    !(s.routes.any fun rt => routeTouches thick r rt)

def fitLabel (s : Site) (pad thick : Int) (route : List Point) (size : Size) : Option Rect :=
  (candidates pad thick route size).find? fun c => s.vacant thick c

structure Spill where
  labels : List Rect
  placed : List Rect
  spillY : Int
  canvas : Rect

def placeAll (inp : RouteIn) (rts : List (List Point)) (canvas : Rect) :
    Except LayoutError (List Rect × Rect) :=
  let margin := max inp.pad 1
  let spillX := canvas.w + margin
  let step (st : Spill) (ke : Edge × Nat) : Except LayoutError Spill :=
    let e := ke.1
    if e.label.w = 0 ∧ e.label.h = 0 then .ok { st with labels := default :: st.labels }
    else
      let site : Site := ⟨rts, inp.leaves, inp.frames, st.placed, st.canvas⟩
      match fitLabel site inp.pad inp.thick (rts.getD ke.2 []) e.label with
      | some rect => .ok { st with labels := rect :: st.labels, placed := rect :: st.placed }
      | none =>
        if (COORD_LIMIT < spillX + e.label.w + margin) ∨
            (COORD_LIMIT < st.spillY + e.label.h + margin) then .error .overflow
        else
          let rect : Rect := ⟨spillX, st.spillY, e.label.w, e.label.h⟩
          let spillY := st.spillY + e.label.h + margin
          .ok ⟨rect :: st.labels, rect :: st.placed, spillY,
            ⟨st.canvas.x, st.canvas.y, max st.canvas.w (rect.x + rect.w + margin),
              max st.canvas.h spillY⟩⟩
  match inp.edges.zipIdx.foldlM step ⟨[], [], margin, canvas⟩ with
  | .error e => .error e
  | .ok st => .ok (st.labels.reverse, st.canvas)

end Grid
end Elegant

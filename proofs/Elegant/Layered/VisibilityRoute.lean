import Std.Data.HashMap
import Elegant.Model
import ElegantGeometry.Basic

set_option autoImplicit false

/-! Shortest orthogonal route on a visibility grid. The grid lines are the clearance lines one
unit outside every obstacle, the route end points, and, for a bounded grid, the bound. A state
is a grid vertex with the axis of the step that reached it; the cost is the length, then the
number of turns, and equal costs pop in vertex order, so the result is unique. Both the search
and the path rebuild run on a fuel that bounds their iterations. -/

namespace Elegant
namespace Layered
namespace Visibility

structure Vertex where
  x : Nat
  y : Nat
  dir : Nat
deriving BEq, Hashable, Repr, Inhabited

structure Cost where
  dist : Int
  turns : Nat
deriving BEq, Repr, Inhabited

def Cost.lt (a b : Cost) : Bool := a.dist < b.dist || (a.dist == b.dist && a.turns < b.turns)

structure Entry where
  cost : Cost
  vertex : Vertex
deriving Inhabited

def Entry.lt (a b : Entry) : Bool :=
  if a.cost.dist != b.cost.dist then a.cost.dist < b.cost.dist
  else if a.cost.turns != b.cost.turns then a.cost.turns < b.cost.turns
  else if a.vertex.x != b.vertex.x then a.vertex.x < b.vertex.x
  else if a.vertex.y != b.vertex.y then a.vertex.y < b.vertex.y
  else a.vertex.dir < b.vertex.dir

structure Grid where
  xs : Array Int
  ys : Array Int
  obstacles : List Rect
  bound : Option Rect

def ports (r : Rect) : List Point :=
  let x := r.x + Int.fdiv r.w 2
  let y := r.y + Int.fdiv r.h 2
  [⟨r.x, y⟩, ⟨r.x + r.w, y⟩, ⟨x, r.y⟩, ⟨x, r.y + r.h⟩]

def sortedLines (values : List Int) : Array Int :=
  ((values.mergeSort fun a b => decide (a ≤ b)).eraseDups).toArray

def newGrid (obstacles : List Rect) (points : List Point) (bound : Option Rect) : Grid :=
  let clearanceX := obstacles.flatMap fun r => [r.x - 1, r.x + r.w + 1]
  let clearanceY := obstacles.flatMap fun r => [r.y - 1, r.y + r.h + 1]
  let xs := clearanceX ++ points.map (·.x)
  let ys := clearanceY ++ points.map (·.y)
  match bound with
  | none => ⟨sortedLines xs, sortedLines ys, obstacles, none⟩
  | some b =>
    let xs := (xs ++ [b.x, b.x + b.w]).filter fun v => b.x ≤ v && v ≤ b.x + b.w
    let ys := (ys ++ [b.y, b.y + b.h]).filter fun v => b.y ≤ v && v ≤ b.y + b.h
    ⟨sortedLines xs, sortedLines ys, obstacles, some b⟩

def Grid.point (g : Grid) (v : Vertex) : Point := ⟨g.xs[v.x]!, g.ys[v.y]!⟩

def Grid.inside (g : Grid) (p : Point) : Bool :=
  match g.bound with
  | none => true
  | some b => b.x ≤ p.x && p.x ≤ b.x + b.w && b.y ≤ p.y && p.y ≤ b.y + b.h

def sideHits (a b : Point) (r : Rect) : Bool :=
  if r.w == 0 || r.h == 0 then false
  else if a.y == b.y then
    r.y < a.y && a.y < r.y + r.h && min a.x b.x < r.x + r.w && r.x < max a.x b.x
  else
    r.x < a.x && a.x < r.x + r.w && min a.y b.y < r.y + r.h && r.y < max a.y b.y

def Grid.clear (g : Grid) (a b : Point) : Bool :=
  g.inside a && g.inside b && !g.obstacles.any (sideHits a b)

def Grid.neighbours (g : Grid) (v : Vertex) : List Vertex :=
  (if 0 < v.x then [⟨v.x - 1, v.y, 0⟩] else []) ++
  (if v.x + 1 < g.xs.size then [⟨v.x + 1, v.y, 0⟩] else []) ++
  (if 0 < v.y then [⟨v.x, v.y - 1, 1⟩] else []) ++
  (if v.y + 1 < g.ys.size then [⟨v.x, v.y + 1, 1⟩] else [])

def Grid.step (g : Grid) (from_ to_ : Vertex) (cost : Cost) : Cost :=
  let a := g.point from_
  let b := g.point to_
  ⟨cost.dist + ((a.x - b.x).natAbs : Int) + ((a.y - b.y).natAbs : Int),
    if from_.dir != 2 && from_.dir != to_.dir then cost.turns + 1 else cost.turns⟩

structure Search where
  frontier : Array Entry
  dist : Std.HashMap Vertex Cost
  prev : Std.HashMap Vertex Vertex

def popMin (frontier : Array Entry) : Option (Entry × Array Entry) :=
  if frontier.isEmpty then none
  else
    let best := Id.run do
      let mut index := 0
      for i in [1:frontier.size] do
        if (frontier[i]!).lt (frontier[index]!) then index := i
      pure index
    some (frontier[best]!, (frontier.set! best frontier.back!).pop)

def Grid.relax (g : Grid) (entry : Entry) (s : Search) : Search :=
  (g.neighbours entry.vertex).foldl
    (fun s next =>
      if !g.clear (g.point entry.vertex) (g.point next) then s
      else
        let candidate := g.step entry.vertex next entry.cost
        let better := match s.dist[next]? with
          | some old => candidate.lt old
          | none => true
        if better then
          { frontier := s.frontier.push ⟨candidate, next⟩
            dist := s.dist.insert next candidate
            prev := s.prev.insert next entry.vertex }
        else s)
    s

def Grid.run (g : Grid) (ends : List Point) : Nat → Search → Option (Vertex × Search)
  | 0, _ => none
  | fuel + 1, s =>
    match popMin s.frontier with
    | none => none
    | some (entry, rest) =>
      let s := { s with frontier := rest }
      match s.dist[entry.vertex]? with
      | none => g.run ends fuel s
      | some current =>
        if current != entry.cost then g.run ends fuel s
        else if ends.contains (g.point entry.vertex) then some (entry.vertex, s)
        else g.run ends fuel (g.relax entry s)

def Grid.vertexAt (g : Grid) (p : Point) : Option Vertex :=
  match g.xs.findIdx? (· == p.x), g.ys.findIdx? (· == p.y) with
  | some x, some y => some ⟨x, y, 2⟩
  | _, _ => none

def Grid.seed (g : Grid) (starts : List Point) : Option Search :=
  starts.foldlM
    (fun s p =>
      if !g.inside p then some s
      else
        (g.vertexAt p).map fun v =>
          { s with frontier := s.frontier.push ⟨⟨0, 0⟩, v⟩, dist := s.dist.insert v ⟨0, 0⟩ })
    ⟨#[], {}, {}⟩

def Grid.chain (g : Grid) (prev : Std.HashMap Vertex Vertex) : Nat → Vertex → List Point → List Point
  | 0, v, acc => g.point v :: acc
  | fuel + 1, v, acc =>
    match prev[v]? with
    | none => g.point v :: acc
    | some parent => g.chain prev fuel parent (g.point v :: acc)

def collinear (a b c : Point) : Bool := (a.x == b.x && b.x == c.x) || (a.y == b.y && b.y == c.y)

def compress (points : List Point) : List Point :=
  (points.foldl
    (fun (acc : List Point) p =>
      match acc with
      | c :: b :: rest => if collinear b c p then p :: b :: rest else p :: acc
      | _ => p :: acc)
    []).reverse

def Grid.shortest (g : Grid) (starts ends : List Point) : Option (List Point) := do
  let seeded ← g.seed starts
  let fuel := 16 * g.xs.size * g.ys.size + 16 * starts.length + 16
  let (last, s) ← g.run ends fuel seeded
  pure (compress (g.chain s.prev (s.prev.size + 1) last []))

end Visibility
end Layered
end Elegant

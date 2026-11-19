import Elegant.GridRoute

set_option autoImplicit false

namespace Elegant.Grid.Architecture

structure Cell where
  x : Int := 0
  y : Int := 0
  deriving DecidableEq, Repr, Inhabited

inductive Side where
  | left | right | top | bottom
  deriving DecidableEq, Repr, Inhabited

def sideOrder : List Side := [.left, .right, .top, .bottom]

def step : Side → Cell
  | .left => ⟨-1, 0⟩
  | .right => ⟨1, 0⟩
  | .top => ⟨0, -1⟩
  | .bottom => ⟨0, 1⟩

structure Span where
  x0 : Int
  y0 : Int
  x1 : Int
  y1 : Int
  deriving DecidableEq, Repr, Inhabited

def Span.shift (r : Span) (dx dy : Int) : Span :=
  ⟨r.x0 + dx, r.y0 + dy, r.x1 + dx, r.y1 + dy⟩

def Span.union (a b : Span) : Span :=
  ⟨min a.x0 b.x0, min a.y0 b.y0, max a.x1 b.x1, max a.y1 b.y1⟩

def Span.overlaps (a b : Span) : Bool :=
  decide (a.x0 < b.x1 ∧ b.x0 < a.x1 ∧ a.y0 < b.y1 ∧ b.y0 < a.y1)

def emptySpan : Span := ⟨2^60, 2^60, -(2^60), -(2^60)⟩

structure Unit where
  node : Int := -1
  group : Int := -1
  deriving DecidableEq, Repr, Inhabited

structure Edge where
  a : Nat
  b : Nat
  sideA : Side
  sideB : Side
  deriving Repr, Inhabited

structure Alignment where
  column : Bool
  members : List Nat
  deriving Repr

structure Level where
  units : List Unit
  rects : List Span
  absolute : List Span
  cells : List Cell
  placed : List Bool
  edges : List Edge
  bounds : Span := emptySpan
  budgetExhausted : Bool := false
  deriving Repr

structure Params where
  pitchX : Int
  pitchY : Int
  ringCap : Nat
  aligns : List Alignment := []
  deriving Repr

def ceilDiv (a b : Int) : Int := Int.fdiv (a + b - 1) b

def seedCell (p : Params) (l : Level) (v : Nat) : Cell :=
  if l.bounds = emptySpan then ⟨0, 0⟩
  else ⟨ceilDiv (l.bounds.x1 - (l.rects.getD v default).x0) p.pitchX + 1, 0⟩

def put (p : Params) (l : Level) (v : Nat) (c : Cell) : Level :=
  let r := (l.rects.getD v default).shift (c.x * p.pitchX) (c.y * p.pitchY)
  { l with placed := l.placed.set v true, cells := l.cells.set v c, absolute := l.absolute.set v r, bounds := l.bounds.union r }

def reach (p : Params) (l : Level) (v u : Nat) (side : Side) : Cell :=
  let a := l.absolute.getD u default
  let r := l.rects.getD v default
  let origin := l.cells.getD u default
  match side with
  | .left => ⟨min (Int.fdiv (a.x0 - r.x1) p.pitchX) (origin.x - 1), origin.y⟩
  | .right => ⟨max (ceilDiv (a.x1 - r.x0) p.pitchX) (origin.x + 1), origin.y⟩
  | .top => ⟨origin.x, min (Int.fdiv (a.y0 - r.y1) p.pitchY) (origin.y - 1)⟩
  | .bottom => ⟨origin.x, max (ceilDiv (a.y1 - r.y0) p.pitchY) (origin.y + 1)⟩

def clear (p : Params) (l : Level) (v : Nat) (c : Cell) : Bool :=
  let r := (l.rects.getD v default).shift (c.x * p.pitchX) (c.y * p.pitchY)
  !(l.placed.zip l.absolute).any fun q => q.1 && r.overlaps q.2

def aligned (p : Params) (l : Level) (v : Nat) (c : Cell) : Bool :=
  let u := l.units.getD v default
  if u.node < 0 then true else
  p.aligns.all fun a =>
    if !a.members.contains u.node.toNat then true else
    match a.members.findSome? (fun (m : Nat) =>
      if (Int.ofNat m) = u.node then none else
      match l.units.findIdx? (fun w => w == (⟨Int.ofNat m, -1⟩ : Unit)) with
      | some j => if l.placed.getD j false then some (l.cells.getD j default) else none
      | none => none) with
    | none => true
    | some position => if a.column then position.x == c.x else position.y == c.y

def ringRows (origin : Cell) (distance : Int) (accept : Cell → Bool) :
    Nat → Int → Option Cell
  | 0, _ => none
  | fuel + 1, dy =>
    let dx := distance - max dy (-dy)
    let left : Cell := ⟨origin.x - dx, origin.y + dy⟩
    let right : Cell := ⟨origin.x + dx, origin.y + dy⟩
    if accept left then some left else if accept right then some right
    else ringRows origin distance accept fuel (dy + 1)

def ringSearch (origin : Cell) (accept : Cell → Bool) : Nat → Nat → Option Cell
  | 0, _ => none
  | fuel + 1, distance =>
    match ringRows origin (Int.ofNat distance) accept (2 * distance + 1) (-Int.ofNat distance) with
    | some c => some c
    | none => ringSearch origin accept fuel (distance + 1)

def sweep (p : Params) (l : Level) (v : Nat) : Nat :=
  let r := l.rects.getD v default
  (ceilDiv (l.bounds.x1 - l.bounds.x0 + r.x1 - r.x0) p.pitchX +
    ceilDiv (l.bounds.y1 - l.bounds.y0 + r.y1 - r.y0) p.pitchY + 2).toNat

def choose (p : Params) (l : Level) (v u : Nat) (side : Side) : Cell :=
  let sides := side :: sideOrder.filter (· != side)
  let candidates := ([0, 1] : List Int).flatMap fun extra => sides.map fun s =>
    let c := reach p l v u s
    ⟨c.x + extra * (step s).x, c.y + extra * (step s).y⟩
  let origin := l.cells.getD u default
  let search := fun (accept : Cell → Bool) (radius : Nat) =>
    match candidates.find? accept with
    | some c => some c
    | none => ringSearch origin accept radius 1
  match search (fun c => clear p l v c && aligned p l v c) p.ringCap with
  | some c => c
  | none => (search (clear p l v) (sweep p l v)).getD (seedCell p l v)

def expand (p : Params) (u : Nat) (l : Level) (queue : List Nat) : Level × List Nat :=
  l.edges.foldl (fun state e =>
    if e.a != u && e.b != u then state else
    let v := if e.b = u then e.a else e.b
    let side := if e.b = u then e.sideB else e.sideA
    if state.1.placed.getD v false then state
    else (put p state.1 v (choose p state.1 v u side), state.2 ++ [v])) (l, queue)

-- Fuel counts queue pops globally, including group units, exactly as the native builder.
def drain (p : Params) : Nat → Level → List Nat → Level × Nat
  | fuel, l, [] => (l, fuel)
  | 0, l, _ :: _ => ({ l with budgetExhausted := true }, 0)
  | fuel + 1, l, u :: rest =>
    let next := expand p u l rest
    drain p fuel next.1 next.2

def arrange (p : Params) (fuel : Nat) (l : Level) : Level × Nat :=
  (List.range l.units.length).foldl (fun state first =>
    if state.1.placed.getD first false then state
    else drain p state.2 (put p state.1 first (seedCell p state.1 first)) [first]) (l, fuel)

theorem drain_fuel_le (p : Params) (fuel : Nat) (l : Level) (queue : List Nat) :
    (drain p fuel l queue).2 ≤ fuel := by
  induction fuel generalizing l queue with
  | zero => cases queue <;> simp [drain]
  | succ fuel ih =>
    cases queue with
    | nil => simp [drain]
    | cons u rest =>
      simp only [drain]
      exact Nat.le_trans (ih _ _) (Nat.le_succ _)

end Elegant.Grid.Architecture

namespace Elegant.Grid.Architecture

theorem arrange_fuel_le (p : Params) (fuel : Nat) (l : Level) :
    (arrange p fuel l).2 ≤ fuel := by
  unfold arrange
  have h : ∀ (xs : List Nat) (state : Level × Nat),
      (xs.foldl (fun state first =>
        if state.1.placed.getD first false then state
        else drain p state.2
          (put p state.1 first (seedCell p state.1 first)) [first]) state).2 ≤ state.2 := by
    intro xs
    induction xs with
    | nil => intro state; exact Nat.le_refl _
    | cons first rest ih =>
      intro state
      simp only [List.foldl_cons]
      split
      · exact ih state
      · exact Nat.le_trans (ih _) (drain_fuel_le _ _ _ _)
  exact h _ _

def Span.contains (outer inner : Span) : Prop :=
  outer.x0 ≤ inner.x0 ∧ inner.x1 ≤ outer.x1 ∧
  outer.y0 ≤ inner.y0 ∧ inner.y1 ≤ outer.y1

theorem union_contains_left (a b : Span) : (a.union b).contains a := by
  unfold Span.union Span.contains
  exact ⟨Int.min_le_left _ _, Int.le_max_left _ _, Int.min_le_left _ _, Int.le_max_left _ _⟩

theorem union_contains_right (a b : Span) : (a.union b).contains b := by
  unfold Span.union Span.contains
  exact ⟨Int.min_le_right _ _, Int.le_max_right _ _, Int.min_le_right _ _, Int.le_max_right _ _⟩


structure Group where
  parent : Int
  titleW : Int
  titleH : Int
  icon : Bool
  deriving Repr, Inhabited

structure FrameParams where
  padding : Int
  inset : Int
  lineHeight : Int
  badge : Int
  deriving Repr

def frameOf (p : FrameParams) (g : Group) (inner : Span) : Span :=
  let head := if g.icon then max g.titleH p.badge else g.titleH
  let need := (if g.titleW > 0 || g.icon then 2 * p.inset + g.titleW else 0) +
    (if g.icon then p.badge + p.inset else 0)
  let x0 := inner.x0 - p.padding
  ⟨x0, inner.y0 - max (p.padding + p.lineHeight) (2 * p.inset + head),
    max (inner.x1 + p.padding) (x0 + need), inner.y1 + p.padding⟩

theorem frameOf_contains_inner (p : FrameParams) (g : Group) (inner : Span)
    (hpad : 0 ≤ p.padding) (hline : 0 ≤ p.lineHeight) :
    (frameOf p g inner).contains inner := by
  simp only [frameOf, Span.contains]
  have hx := Int.le_max_left (inner.x1 + p.padding)
    (inner.x0 - p.padding +
      ((if g.titleW > 0 || g.icon then 2 * p.inset + g.titleW else 0) +
        (if g.icon then p.badge + p.inset else 0)))
  have hy := Int.le_max_left (p.padding + p.lineHeight)
    (2 * p.inset + if g.icon then max g.titleH p.badge else g.titleH)
  exact ⟨by omega, by omega, by omega, by omega⟩

end Elegant.Grid.Architecture

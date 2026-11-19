import Elegant.GridArchitectureHierarchy

set_option autoImplicit false

namespace Elegant.Grid.Architecture

structure Node where
  parent : Int
  junction : Bool
  icon : Size
  label : Size
  deriving Repr, Inhabited

structure GeometryParams where
  pitchX : Int
  pitchY : Int
  labelWrap : Int
  iconW : Int
  iconH : Int
  inset : Int
  lineHeight : Int
  labelGap : Int
  thickness : Int
  gutter : Int
  badge : Int
  deriving Repr

structure Pitch where
  x : Int
  y : Int
  top : Int
  deriving Repr

def pitch (p : GeometryParams) (nodes : List Node) (edgeLabels : List Size) : Pitch :=
  let lw := nodes.foldl (fun a n => max a n.label.w) 0
  let lh := nodes.foldl (fun a n => max a n.label.h) 0
  let ew := edgeLabels.foldl (fun a s => max a s.w) 0
  let eh := edgeLabels.foldl (fun a s => max a s.h) 0
  let px := max p.pitchX (max (p.iconW + p.gutter) (lw + p.pitchX - p.labelWrap))
  let px := if ew > 0 then max px (max p.iconW lw + p.gutter +
    2 * (p.thickness + p.labelGap + ew)) else px
  let top0 := max 0 (Int.fdiv (p.pitchY - p.iconH) 2)
  let top := if eh > 0 then max top0 (p.thickness + p.labelGap + eh) else top0
  let tail := if lh > 0 then lh + p.thickness +
    max p.gutter (max 0 (p.pitchY - top0 - p.iconH - p.lineHeight))
    else max 0 (p.pitchY - top0 - p.iconH)
  ⟨px, max p.pitchY (top + p.iconH + tail), top⟩

def sized (x y : Int) (s : Size) : Span := ⟨x, y, x + s.w, y + s.h⟩

structure Geometry where
  boxes : List Span
  icons : List Span
  labels : List Span
  frames : List Span
  titles : List Span
  badges : List Span
  deriving Repr

def geometry (p : GeometryParams) (pitch : Pitch) (nodes : List Node)
    (groups : List Group) (resolved : Resolved) : Geometry :=
  let icons := nodes.zipIdx.map fun q =>
    let c := resolved.nodes.getD q.2 default
    let x := c.x * pitch.x + Int.fdiv (pitch.x - q.1.icon.w) 2
    let y := c.y * pitch.y + if q.1.junction then Int.fdiv (pitch.y - q.1.icon.h) 2 else pitch.top
    sized x y q.1.icon
  let labels := nodes.zipIdx.map fun q =>
    let r := icons.getD q.2 default
    sized (r.x0 + Int.fdiv (q.1.icon.w - q.1.label.w) 2) r.y1 q.1.label
  let boxes := nodes.zipIdx.map fun q =>
    let r := icons.getD q.2 default
    ⟨r.x0, r.y0, r.x1, r.y1 + q.1.label.h +
      (if q.1.label.h > 0 then p.thickness else 0)⟩
  let badges := groups.zipIdx.map fun q =>
    let f := resolved.frames.getD q.2 default
    let size := if q.1.icon then p.badge else 0
    sized (f.x0 + p.inset) (f.y0 + p.inset) ⟨size, size⟩
  let titles := groups.zipIdx.map fun q =>
    let f := resolved.frames.getD q.2 default
    sized (f.x0 + p.inset + (if q.1.icon then p.badge + p.inset else 0))
      (f.y0 + p.inset) ⟨q.1.titleW, q.1.titleH⟩
  ⟨boxes, icons, labels, resolved.frames, titles, badges⟩

structure PortEnd where
  point : Point
  gutter : Point
  line : Int
  vertical : Bool := false
  cell : Cell
  deriving Repr

def port (p : GeometryParams) (pitch : Pitch) (node : Node) (box icon : Span)
    (position : Cell) (side : Side) (index count : Nat) : PortEnd :=
  let i := if node.junction then 0 else index
  let k := if node.junction then 1 else count
  let along := fun len => Int.fdiv (((i : Int) + 1) * len) ((k : Int) + 1)
  let vx := fun k => k * pitch.x - p.gutter
  let hy := fun k => k * pitch.y - p.gutter
  match side with
  | .top =>
    let x := icon.x0 + along (icon.x1 - icon.x0)
    ⟨⟨x, box.y0⟩, ⟨x, hy position.y⟩, hy position.y, false, position⟩
  | .bottom =>
    let x := icon.x0 + along (icon.x1 - icon.x0)
    ⟨⟨x, box.y1⟩, ⟨x, hy (position.y + 1)⟩, hy (position.y + 1), false, position⟩
  | .left =>
    let y := icon.y0 + along (icon.y1 - icon.y0)
    ⟨⟨box.x0, y⟩, ⟨vx position.x, y⟩, vx position.x, true, position⟩
  | .right =>
    let y := icon.y0 + along (icon.y1 - icon.y0)
    ⟨⟨box.x1, y⟩, ⟨vx (position.x + 1), y⟩, vx (position.x + 1), true, position⟩

def compactPoints : List Point → List Point
  | a :: b :: rest => if a = b then compactPoints (b :: rest) else a :: compactPoints (b :: rest)
  | xs => xs

def path (p : GeometryParams) (pitch : Pitch) (a b : PortEnd) : List Point :=
  compactPoints <|
    if a.vertical = b.vertical && a.line == b.line then [a.point, a.gutter, b.gutter, b.point]
    else if a.vertical && b.vertical then
      let y := a.cell.y * pitch.y - p.gutter
      [a.point, a.gutter, ⟨a.line, y⟩, ⟨b.line, y⟩, b.gutter, b.point]
    else if !a.vertical && !b.vertical then
      let x := a.cell.x * pitch.x - p.gutter
      [a.point, a.gutter, ⟨x, a.line⟩, ⟨x, b.line⟩, b.gutter, b.point]
    else if a.vertical then
      [a.point, a.gutter, ⟨a.line, b.line⟩, b.gutter, b.point]
    else [a.point, a.gutter, ⟨b.line, a.line⟩, b.gutter, b.point]

structure EndRef where
  edge : Nat
  target : Bool
  deriving DecidableEq, Repr

def assignPorts (p : GeometryParams) (pitch : Pitch) (nodes : List Node)
    (edges : List Edge) (resolved : Resolved) (g : Geometry) : List (PortEnd × PortEnd) :=
  let refs : List EndRef := edges.zipIdx.flatMap fun q => [⟨q.2, false⟩, ⟨q.2, true⟩]
  let endpoint := fun (ref : EndRef) =>
    let e := edges.getD ref.edge default
    if ref.target then (e.b, e.sideB) else (e.a, e.sideA)
  let otherKey := fun (side : Side) (ref : EndRef) =>
    let e := edges.getD ref.edge default
    let c := resolved.nodes.getD (if ref.target then e.a else e.b) default
    if side = .left ∨ side = .right then c.y else c.x
  let endOf := fun (ref : EndRef) =>
    let (n, side) := endpoint ref
    let slots := (refs.filter (fun r => endpoint r == (n, side))).mergeSort fun a b =>
      decide (otherKey side a < otherKey side b) ||
        (otherKey side a == otherKey side b &&
          (decide (a.edge < b.edge) || (a.edge == b.edge && (!a.target || b.target))))
    port p pitch (nodes.getD n default) (g.boxes.getD n default) (g.icons.getD n default)
      (resolved.nodes.getD n default) side ((slots.findIdx? (· == ref)).getD 0) slots.length
  edges.zipIdx.map fun q => (endOf ⟨q.2, false⟩, endOf ⟨q.2, true⟩)

def routes (p : GeometryParams) (pitch : Pitch) (nodes : List Node)
    (edges : List Edge) (resolved : Resolved) (g : Geometry) : List (List Point) :=
  (assignPorts p pitch nodes edges resolved g).map fun ends => path p pitch ends.1 ends.2

end Elegant.Grid.Architecture

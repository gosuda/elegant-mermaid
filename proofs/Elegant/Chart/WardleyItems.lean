import Elegant.Chart.WardleyLabels

set_option autoImplicit false

namespace Elegant.Chart.Wardley

structure PaintConstants where
  labels : LabelConstants
  inertiaGap : Int
  inertiaWidth : Int
  marketRing : Int
  marketDot : Int
  arrowTip : Int
  arrowShaft : Int
  arrowHead : Int
  edge : Int
  deriving DecidableEq, Repr

def pathThrough (points : List Point) (closed : Bool) (paint : Paint) : Primitive :=
  let commands := match points with
    | [] => []
    | first :: rest => PathCommand.M first :: rest.map PathCommand.L
  .path (commands ++ if closed then [.Z] else []) paint

private def circle (p : Point) (radius : Int) (paint : Paint) : Primitive :=
  .ellipse p.x p.y radius radius paint

def cellSymbol (n : Node) : String × String :=
  if n.flags &&& 4 != 0 then ("box-hollow", "mark-hollow") else
    match n.strategy with
    | 1 => ("diamond-hollow", "mark-hollow")
    | 2 => ("diamond", "mark")
    | 3 => ("disc", "mark")
    | 4 => ("bullseye", "mark")
    | _ => ("ring", "mark-hollow")

def marketItems (c : PaintConstants) (pos : Point) : List Primitive :=
  let side := Int.fdiv (7 * c.marketRing) 8
  let corners : List Point := [⟨pos.x, pos.y - c.marketRing⟩,
    ⟨pos.x - side, pos.y + Int.fdiv c.marketRing 2⟩,
    ⟨pos.x + side, pos.y + Int.fdiv c.marketRing 2⟩]
  [circle pos (2 * c.labels.nodeRadius) { style := "mark-hollow" },
    .polygon corners { style := "rule" }] ++
    corners.map (fun p => circle p c.marketDot { style := "mark-hollow" })

def strategyItems (c : PaintConstants) (n : Node) (pos : Point) : List Primitive :=
  let outer := 2 * c.labels.nodeRadius
  match n.strategy with
  | 1 => [circle pos outer { style := "mark-hollow", line := .dashed }]
  | 2 => [circle pos outer { style := "mark" }]
  | 3 => [circle pos outer { style := "ink" }]
  | 4 => marketItems c pos
  | _ => []

def nodeItems (c : PaintConstants) (cell : Bool) (n : Node) (pos : Point) : List Primitive :=
  if n.flags &&& 1 != 0 then [] else
  if cell then
    let symbol := cellSymbol n
    [.symbolRef symbol.1 pos symbol.2] ++
      if n.flags &&& 2 != 0 then
        [.rect ⟨pos.x + c.inertiaGap, pos.y, 1, 1⟩ { style := "ink" }] else []
  else
    let shape := if n.flags &&& 4 != 0 then
        let half := Int.fdiv c.labels.squareSize 2
        [.rect ⟨pos.x - half, pos.y - half, c.labels.squareSize, c.labels.squareSize⟩
          { style := "node" }]
      else strategyItems c n pos ++ [circle pos c.labels.nodeRadius { style := "mark-hollow" }]
    shape ++ if n.flags &&& 2 != 0 then
      let reach := nodeReach c.labels false n
      let x := pos.x + reach + c.inertiaGap
      [.polyline [⟨x, pos.y - reach⟩, ⟨x, pos.y + reach⟩] 0
        { style := "ink-line", width := .units c.inertiaWidth }] else []

def ghostItems (c : PaintConstants) (cell : Bool) (pos : Point) : List Primitive :=
  if cell then [.symbolRef "ring" pos "mark-hollow"]
  else [circle pos c.labels.nodeRadius { style := "mark-hollow", line := .dotted }]

def forcePoints (c : PaintConstants) (r : Rect) : List Point :=
  let half := c.arrowShaft + c.arrowHead
  let cy := r.y + half
  let x1 := r.x + r.w - c.edge
  let tip := x1 - c.arrowTip
  [⟨r.x, cy - c.arrowShaft⟩, ⟨tip, cy - c.arrowShaft⟩, ⟨tip, cy - half⟩,
    ⟨x1, cy⟩, ⟨tip, cy + half⟩, ⟨tip, cy + c.arrowShaft⟩, ⟨r.x, cy + c.arrowShaft⟩]

def forceItems (c : PaintConstants) (reverse : Bool) (r : Rect) : List Primitive :=
  let points := forcePoints c r
  let points := if reverse then points.map (fun p => { p with x := 2 * r.x + r.w - c.edge - p.x })
    else points
  [.polygon points { style := "mark-hollow" }]

def annotationItems (c : PaintConstants) (cell : Bool) (p : Point) : List Primitive :=
  if cell then [] else [circle p c.labels.annotationRadius { style := "mark-hollow" }]

def frameItems (c : PaintConstants) (r : Rect) : List Primitive :=
  let x1 := r.x + r.w - c.edge
  let y1 := r.y + r.h - c.edge
  [pathThrough [⟨r.x, r.y⟩, ⟨x1, r.y⟩, ⟨x1, y1⟩, ⟨r.x, y1⟩] true { style := "group" }]

def decorItems (plot : Rect) (input : Input) : List Primitive :=
  let bottom := plot.y + plot.h
  [pathThrough [⟨plot.x, plot.y⟩, ⟨plot.x, bottom⟩, ⟨plot.x + plot.w, bottom⟩]
    false { style := "rule" }] ++
    (List.range (input.stageCount - 1)).map (fun i =>
      let x := (stageSpan plot input i).2
      pathThrough [⟨x, plot.y⟩, ⟨x, bottom⟩] false { style := "rule", line := .dotted })

end Elegant.Chart.Wardley

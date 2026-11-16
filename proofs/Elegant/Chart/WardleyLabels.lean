import Elegant.Chart.Wardley

set_option autoImplicit false

namespace Elegant.Chart.Wardley

structure LabelConstants where
  nodeRadius : Int
  labelGap : Int
  squareSize : Int
  annotationRadius : Int
  boxPad : Int
  linkLabelGap : Int
  axisGap : Int
  stageGap : Int
  stageHeight : Int
  deriving DecidableEq, Repr

structure TextExtent where
  w : Int := 0
  h : Int := 0
  deriving DecidableEq, Repr, Inhabited

def centredAt (p : Point) (t : TextExtent) : Rect :=
  ⟨p.x - Int.fdiv t.w 2, p.y - Int.fdiv t.h 2, t.w, t.h⟩

def fitCanvas (canvas : Size) (r : Rect) : Rect :=
  { r with x := clamp r.x 0 (max (canvas.w - r.w) 0)
           y := clamp r.y 0 (max (canvas.h - r.h) 0) }

def nodeReach (c : LabelConstants) (cell : Bool) (n : Node) : Int :=
  if n.flags &&& 4 != 0 then Int.fdiv c.squareSize 2
  else if !cell && n.strategy != 0 then 2 * c.nodeRadius else c.nodeRadius

def nodeLabel (c : LabelConstants) (cell : Bool) (n : Node) (pos : Point)
    (t : TextExtent) : Rect × Align :=
  if n.flags &&& 8 != 0 then
    let ox := if cell then Int.fdiv n.offsetX 8 else n.offsetX * 64
    let oy := if cell then Int.fdiv n.offsetY 16 else n.offsetY * 64
    (centredAt ⟨pos.x + ox, pos.y + oy⟩ t, .middle)
  else if n.flags &&& 1 != 0 then (centredAt pos t, .middle)
  else (⟨pos.x + nodeReach c cell n + c.labelGap, pos.y - t.h, t.w, t.h⟩, .start)

def linkLabel (c : LabelConstants) (a b : Point) (t : TextExtent) : Rect × Align :=
  let mx := Int.fdiv (a.x + b.x) 2
  let my := Int.fdiv (a.y + b.y) 2
  let dx := b.x - a.x
  let dy := b.y - a.y
  let gap := c.linkLabelGap
  if dy = 0 then (⟨mx - Int.fdiv t.w 2, my - gap - t.h, t.w, t.h⟩, .middle)
  else if dx = 0 then (⟨mx + gap, my - Int.fdiv t.h 2, t.w, t.h⟩, .start)
  else if (dx < 0) = (dy < 0) then (⟨mx + gap, my - gap - t.h, t.w, t.h⟩, .start)
  else (⟨mx - gap - t.w, my - gap - t.h, t.w, t.h⟩, .start)

def stageSpan (plot : Rect) (input : Input) (index : Nat) : Int × Int :=
  if input.boundaries.length = input.stageCount then
    let lo := if index = 0 then plot.x else
      plot.x + Int.fdiv (clamp ((input.boundaries[index - 1]?).getD 0) 0 1000 * plot.w) 1000
    let hi := plot.x + Int.fdiv (clamp ((input.boundaries[index]?).getD 0) 0 1000 * plot.w) 1000
    (lo, hi)
  else
    (plot.x + Int.fdiv ((index : Int) * plot.w) input.stageCount,
     plot.x + Int.fdiv (((index : Int) + 1) * plot.w) input.stageCount)

def stageLabel (c : LabelConstants) (plot : Rect) (input : Input) (index : Nat)
    (t : TextExtent) : Rect :=
  let span := stageSpan plot input index
  ⟨Int.fdiv (span.1 + span.2 - t.w) 2, plot.y + plot.h + c.stageGap, t.w, t.h⟩

def titleLabel (plot : Rect) (t : TextExtent) : Rect :=
  ⟨plot.x + Int.fdiv (plot.w - t.w) 2, Int.fdiv (plot.y - t.h) 2, t.w, t.h⟩

def xAxisLabel (c : LabelConstants) (plot : Rect) (t : TextExtent) : Rect :=
  ⟨plot.x + Int.fdiv (plot.w - t.w) 2,
    plot.y + plot.h + 2 * c.stageGap + c.stageHeight, t.w, t.h⟩

def yAxisLabel (c : LabelConstants) (plot : Rect) (t : TextExtent) : Rect :=
  ⟨plot.x, plot.y - t.h - c.axisGap, t.w, t.h⟩

def forceLabel (c : LabelConstants) (force : Rect) (t : TextExtent) : Rect :=
  ⟨force.x + Int.fdiv (force.w - t.w) 2, force.y + force.h + c.linkLabelGap, t.w, t.h⟩

def annotationLabel (c : LabelConstants) (pos : Point) (t : TextExtent) : Rect :=
  ⟨pos.x + c.annotationRadius + c.labelGap, pos.y - Int.fdiv t.h 2, t.w, t.h⟩

def annotationBox (c : LabelConstants) (plot : Rect) (pos : Point)
    (texts : List TextExtent) : Rect :=
  let w := texts.foldl (fun width t => max width t.w) 0
  let h := texts.foldl (fun height t => height + t.h) 0
  let p := project plot pos.x pos.y
  fitPlot plot ⟨p.x, p.y, w + 2 * c.boxPad, h + 2 * c.boxPad⟩

def annotationBoxLabel (c : LabelConstants) (box : Rect) (earlier : List TextExtent)
    (t : TextExtent) : Rect :=
  ⟨box.x + c.boxPad, box.y + c.boxPad + earlier.foldl (fun h t => h + t.h) 0, t.w, t.h⟩

end Elegant.Chart.Wardley

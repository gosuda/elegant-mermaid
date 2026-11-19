import Elegant.Chart.Scale
import Elegant.Chart.XYConsts
import Elegant.Scene
import Elegant.StyledMeasure

set_option autoImplicit false

/-! The xychart layout family (`spec/layout/charts.md`, charts-39 to charts-43), a port of Go's
`internal/layout/chart` (`xy*.go`). The family reads a decoded chart (axes, plots, titles and the
honoured config keys), measures every label, arranges the axes around the plot, places the labels
and the plot boxes, and paints the scene items. All values are integers: 1/64 px under the vector
profile and cells under the cell profile. -/

namespace Elegant
namespace Chart
namespace XY

/-! ### The decoded chart -/

structure XPoint where
  present : Bool
  slot : Int
  hasX : Bool
  x : Int
  value : Int
  label : String
  deriving DecidableEq, Repr

structure XPlot where
  kind : Nat
  title : String
  points : List XPoint
  deriving DecidableEq, Repr

def XPlot.isBar (p : XPlot) : Bool := p.kind == 0
def XPlot.isLine (p : XPlot) : Bool := p.kind == 1

structure Input where
  horizontal : Bool
  title : String
  xTitle : String
  yTitle : String
  band : Bool
  categories : List String
  xMin : Int
  xMax : Int
  yMin : Int
  yMax : Int
  plots : List XPlot
  width : Option Int
  height : Option Int
  reserved : Option Int
  showLabel : Option Bool
  fontSize : Option Int
  deriving DecidableEq, Repr

/-! ### Axes -/

inductive Pos where
  | bottom | left | top
  deriving DecidableEq, Repr

structure Space where
  w : Int := 0
  h : Int := 0
  line : Int := 0
  tick : Int := 0
  title : Int := 0
  showLabel : Bool := false
  deriving DecidableEq, Repr

def zeroRect : Rect := ⟨0, 0, 0, 0⟩

structure Axis where
  isX : Bool
  pos : Pos
  band : Bool
  distinct : List Nat
  n : Nat
  lo : Int
  hi : Int
  ticks : List Int
  labels : List String
  showLabels : Bool
  fontSize : Int
  outer : Int := 0
  r0 : Int := 0
  r1 : Int := 0
  space : Space := {}
  area : Rect := zeroRect
  deriving DecidableEq, Repr

def Axis.count (a : Axis) : Nat := a.labels.length

def Axis.innerLo (a : Axis) : Int := a.r0 + a.outer

def Axis.innerHi (a : Axis) : Int := a.r1 - a.outer

def Axis.tickDistance (a : Axis) : Int :=
  if a.count = 0 then 0
  else Int.fdiv (max (a.innerHi - a.innerLo) (a.innerLo - a.innerHi)) (a.count : Int)

/-- A bar axis whose ticks are too close widens its outer padding to hold the bars. -/
def Axis.raiseOuter (a : Axis) (ratio : Int) : Axis :=
  let dist := a.tickDistance
  if ratio * dist > 2000 * a.outer then { a with outer := Int.fdiv (ratio * dist) 2000 } else a

def Axis.bandIndex (a : Axis) (slot : Int) : Option Nat :=
  if slot < 0 then none else a.distinct[slot.toNat]?

def Axis.linear (a : Axis) : Linear :=
  if a.pos == .left then ⟨a.hi, a.lo, a.innerLo, a.innerHi⟩ else ⟨a.lo, a.hi, a.innerLo, a.innerHi⟩

def Axis.clampPosition (a : Axis) (v edge : Int) : Int := clamp v a.r0 (a.r1 - edge)

def Axis.bandPos (a : Axis) (slot edge : Int) : Int :=
  match a.bandIndex slot with
  | some index => a.clampPosition (bandPosition index a.n a.innerLo a.innerHi) edge
  | none => a.clampPosition a.innerLo edge

def Axis.valuePos (a : Axis) (v edge : Int) : Int :=
  a.clampPosition (a.linear.map (clamp v a.lo a.hi)) edge

def Axis.pointPos (a : Axis) (p : XPoint) (edge : Int) : Int :=
  if a.band then a.bandPos p.slot edge
  else if !p.hasX then a.clampPosition (a.r0 + a.outer) edge
  else a.valuePos p.x edge

def Axis.tickPos (a : Axis) (k : Nat) (edge : Int) : Int :=
  if a.band then a.bandPos (k : Int) edge else a.valuePos (a.ticks.getD k 0) edge

def distinctStep (acc : List String × List Nat) (name : String) : List String × List Nat :=
  match acc.1.findIdx? (· == name) with
  | some at_ => (acc.1, acc.2 ++ [at_])
  | none => (acc.1 ++ [name], acc.2 ++ [acc.1.length])

def distinctIndex (categories : List String) : List Nat × Nat :=
  let r := categories.foldl distinctStep ([], [])
  (r.2, r.1.length)

def checkMagnitude (vs : List Int) : Except LayoutError Unit :=
  if vs.all (fun v => decide (-I32_MAX ≤ v ∧ v ≤ I32_MAX)) then .ok () else .error .overflow

def formatNumber (t : Int) : String :=
  let n := t.natAbs
  let text := (if t < 0 then "-" else "") ++ toString (n / 1000)
  let fraction := n % 1000
  if fraction = 0 then text
  else
    let digits := (toString (1000 + fraction)).toList.drop 1
    text ++ "." ++ String.ofList (digits.reverse.dropWhile (· == '0')).reverse

def linearAxis (isX : Bool) (lo hi : Int) : Except LayoutError (Axis × Bool) := do
  checkMagnitude [lo, hi]
  let (ticks, capped) ← ticksOf lo hi
  return ({ isX, pos := .bottom, band := false, distinct := [], n := 0, lo, hi, ticks,
            labels := ticks.map formatNumber, showLabels := true, fontSize := 14 }, capped)

def newAxes (inp : Input) : Except LayoutError (Axis × Axis × Bool) := do
  let (y, capped) ← linearAxis false inp.yMin inp.yMax
  if inp.band then
    let (distinct, n) := distinctIndex inp.categories
    let x : Axis := { isX := true, pos := .bottom, band := true, distinct, n, lo := 0, hi := 0,
                      ticks := [], labels := inp.categories, showLabels := true, fontSize := 14 }
    return (x, y, capped)
  else
    let (x, xCapped) ← linearAxis true inp.xMin inp.xMax
    return (x, y, capped || xCapped)

/-! ### Label specs -/

inductive Kind where
  | title | xTitle | yTitle | xTick | yTick | legend | point
  deriving DecidableEq, Repr

structure Spec where
  id : String
  owner : String
  text : String
  kind : Kind
  index : Nat
  plot : Nat
  deriving DecidableEq, Repr

def plotId : String := "plot"

def seriesTitle (index : Nat) (title : String) : String :=
  if title != "" then title else "Series " ++ toString (index + 1)

def seriesBoxId (plot : Nat) : String := "p" ++ toString plot

def barBoxId (plot point : Nat) : String := seriesBoxId plot ++ ".b" ++ toString point

def pointLabelId (plot point : Nat) : String := seriesBoxId plot ++ ".l" ++ toString point

structure BoxSpec where
  id : String
  plot : Nat
  point : Nat
  isLine : Bool
  isPlot : Bool
  deriving DecidableEq, Repr

def plotBox : BoxSpec := ⟨plotId, 0, 0, false, true⟩

def seriesBoxes (inp : Input) : List BoxSpec :=
  inp.plots.zipIdx.flatMap fun (pl, i) =>
    if pl.isLine then [⟨seriesBoxId i, i, 0, true, false⟩]
    else pl.points.zipIdx.filterMap fun (pt, j) =>
      if pt.present then some ⟨barBoxId i j, i, j, false, false⟩ else none

def boxSpecs (inp : Input) : List BoxSpec := plotBox :: seriesBoxes inp

def tickSpecs (a : Axis) (kind : Kind) (pre : String) : List Spec :=
  a.labels.zipIdx.map fun (text, k) => ⟨pre ++ ".t" ++ toString k, plotId, text, kind, k, 0⟩

def labelSpecs (inp : Input) (x y : Axis) : List Spec :=
  let add (id text : String) (kind : Kind) : List Spec :=
    if text == "" then [] else [⟨id, plotId, text, kind, 0, 0⟩]
  add "title" inp.title .title ++ add "x.title" inp.xTitle .xTitle ++
    add "y.title" inp.yTitle .yTitle ++ tickSpecs x .xTick "x" ++ tickSpecs y .yTick "y" ++
    inp.plots.zipIdx.map (fun (pl, i) =>
      (⟨"legend." ++ toString i, plotId, seriesTitle i pl.title, .legend, 0, i⟩ : Spec)) ++
    inp.plots.zipIdx.flatMap fun (pl, i) =>
      pl.points.zipIdx.filterMap fun (pt, j) =>
        if pt.present && pt.label != "" then
          some ⟨pointLabelId i j, seriesBoxId i, pt.label, .point, j, i⟩
        else none

/-! ### Measurement -/

structure TextBox where
  lines : List Measure.Line
  w : Int
  h : Int

structure Item where
  spec : Spec
  role : Measure.Role
  size : Int
  box : TextBox

def roundHalfUp (a b : Int) : Int := Int.fdiv (2 * a + b) (2 * b)

def lineHeight (cell : Bool) (role : Measure.Role) (size : Int) : Int :=
  if cell then 1 else roundHalfUp (size * 64 * role.lineHeightPx) role.sizePx

def metricOf (cell : Bool) (role : Measure.Role) (size : Int) : Except LayoutError Measure.Metric :=
  if cell then pure Measure.Metric.cell
  else do
    let u ← Measure.upemOf role.weight
    pure { profile := .vector, sizePx := size, weight := role.weight, upem := u, fontFamily := false }

def measureText (cell : Bool) (text : String) (role : Measure.Role) (size : Int) :
    Except LayoutError TextBox := do
  let m ← metricOf cell role size
  match StyledMeasure.wrap m I32_MAX text.toList with
  | .error _ => throw .overflow
  | .ok lines =>
    return ⟨lines, lines.foldl (fun w l => max w l.width) 0,
      (lines.length : Int) * lineHeight cell role size⟩

def styleOf (c : XYConsts) (x : Axis) (s : Spec) : Measure.Role × Int :=
  match s.kind with
  | .title => (.title, Measure.Role.title.sizePx)
  | .xTick => (.label, x.fontSize)
  | .point => (.body, Int.fdiv c.pointSize 64)
  | _ => (.label, 14)

def measureAll (c : XYConsts) (cell : Bool) (x : Axis) (specs : List Spec) :
    Except LayoutError (List Item) :=
  specs.mapM fun s => do
    let (role, size) := styleOf c x s
    let box ← measureText cell s.text role size
    return ⟨s, role, size, box⟩

def findKind (items : List Item) (k : Kind) : Option (Nat × Item) :=
  (items.zipIdx.find? fun (it, _) => it.spec.kind == k).map fun (it, i) => (i, it)

def tickExtent (items : List Item) (k : Kind) : Int × Int :=
  items.foldl (fun (e : Int × Int) it =>
    if it.spec.kind == k then (max e.1 it.box.w, max e.2 it.box.h) else e) (0, 0)

/-! ### The arrangement -/

def tickKind (a : Axis) : Kind := if a.isX then .xTick else .yTick

def titleKind (a : Axis) : Kind := if a.isX then .xTitle else .yTitle

def titleNeed (c : XYConsts) (items : List Item) (k : Kind) (room : Int) : Int :=
  match findKind items k with
  | some (_, it) =>
    if it.box.h + 2 * c.axisTitlePad ≤ room then it.box.h + 2 * c.axisTitlePad else 0
  | none => 0

structure Core where
  line : Int
  tick : Int
  rest : Int
  showLabel : Bool
  outer : Int

/-- The side that an axis takes from `room`: the axis line, the tick marks and the label band, in
that order, and the outer padding that the labels need. -/
def spaceCore (c : XYConsts) (a : Axis) (room extHalf extNeed pad availOuter : Int) : Core :=
  let line : Int := if room > c.axisLine then c.axisLine else 0
  let r1 := room - line
  let outer := if a.showLabels then min (Int.fdiv extHalf 2) (Int.fdiv (c.outerMax * availOuter) 1000)
    else a.outer
  let need := extNeed + 2 * pad
  let showLabel := a.showLabels && decide (need ≤ r1)
  let r2 := if showLabel then r1 - need else r1
  let tick : Int := if r2 ≥ c.tickLen then c.tickLen else 0
  ⟨line, tick, r2 - tick, showLabel, outer⟩

def horizontalSpace (c : XYConsts) (items : List Item) (a : Axis) (availW availH : Int) : Axis :=
  let ext := tickExtent items (tickKind a)
  let k := spaceCore c a availH ext.1 ext.2 c.padY availW
  let title : Int := titleNeed c items (titleKind a) k.rest
  { a with outer := k.outer,
           space := ⟨availW, availH - (k.rest - title), k.line, k.tick, title, k.showLabel⟩ }

def verticalSpace (c : XYConsts) (items : List Item) (a : Axis) (availW availH : Int) : Axis :=
  let ext := tickExtent items (tickKind a)
  let k := spaceCore c a availW ext.2 ext.1 c.padX availH
  { a with outer := k.outer, space := ⟨availW - k.rest, availH, k.line, k.tick, 0, k.showLabel⟩ }

def titleSpace (c : XYConsts) (items : List Item) (availH : Int) : Int × Bool :=
  match findKind items .title with
  | none => (0, false)
  | some (_, it) =>
    let need := it.box.h + 2 * c.titlePad
    if need ≤ availH then (need, true) else (0, false)

def sideTitleSpace (c : XYConsts) (items : List Item) (horizontal : Bool) (availH : Int) :
    Int × Option Nat × Bool :=
  match findKind items (if horizontal then .xTitle else .yTitle) with
  | none => (0, none, false)
  | some (i, it) =>
    let need := it.box.h + 2 * c.axisTitlePad
    if need ≤ availH then (need, some i, true) else (0, some i, false)

structure LegendInfo where
  w : Int
  h : Int
  rows : Nat
  lh : Int
  beside : Bool

def legendInfo (c : XYConsts) (items : List Item) (availW availH : Int) : LegendInfo :=
  let legends := items.filter fun it => it.spec.kind == .legend
  let widest := legends.foldl (fun m it => max m it.box.w) 0
  let lh := legends.foldl (fun m it => max m it.box.h) 0
  let rows := legends.length
  if rows = 0 then ⟨0, 0, 0, lh, false⟩
  else
    let w := 2 * c.legendPad + c.legendMarker + c.markerGap + widest
    let h := 2 * c.legendPad + (rows : Int) * lh + ((rows : Int) - 1) * c.itemGap
    ⟨w, h, rows, lh, decide (w ≤ availW ∧ h ≤ availH)⟩

structure Stage where
  x : Axis
  y : Axis
  availW : Int
  availH : Int
  plotX : Int
  plotY : Int

def stageOf (c : XYConsts) (inp : Input) (items : List Item) (x0 y0 : Axis)
    (availW0 availH2 top : Int) : Stage :=
  if inp.horizontal then
    let x := verticalSpace c items x0 availW0 availH2
    let availW1 := availW0 - x.space.w
    let y := horizontalSpace c items y0 availW1 availH2
    ⟨x, y, availW1, availH2 - y.space.h, x.space.w, top + y.space.h⟩
  else
    let x := horizontalSpace c items x0 availW0 availH2
    let availH3 := availH2 - x.space.h
    let y := verticalSpace c items y0 availW0 availH3
    ⟨x, y, availW0 - y.space.w, availH3, y.space.w, top⟩

def fit (width height : Int) (r : Rect) : Rect :=
  ⟨clamp r.x 0 (max (width - r.w) 0), clamp r.y 0 (max (height - r.h) 0), r.w, r.h⟩

def hasBars (inp : Input) : Bool := inp.plots.any XPlot.isBar

def setAreas (c : XYConsts) (inp : Input) (plot : Rect) (top : Int) (x y : Axis) : Axis × Axis :=
  let ends : Axis × Axis :=
    if inp.horizontal then
      ({ x with area := ⟨0, plot.y, x.space.w, plot.h⟩, r0 := plot.y, r1 := plot.y + plot.h },
       { y with area := ⟨plot.x, top, plot.w, y.space.h⟩, r0 := plot.x, r1 := plot.x + plot.w })
    else
      ({ x with area := ⟨plot.x, plot.y + plot.h, plot.w, x.space.h⟩, r0 := plot.x,
                r1 := plot.x + plot.w },
       { y with area := ⟨0, plot.y, y.space.w, plot.h⟩, r0 := plot.y, r1 := plot.y + plot.h })
  (if hasBars inp then ends.1.raiseOuter c.barRatio else ends.1, ends.2)

structure Arranged where
  x : Axis
  y : Axis
  width : Int
  height : Int
  plot : Rect
  titleH : Int
  titleShown : Bool
  sideTitle : Option Nat
  sideShown : Bool
  legend : Rect
  legendOn : Bool
  legendLH : Int

/-- The plot rectangle, the legend and the axis areas, once the title, side title, stage and legend
have taken their room. -/
def arrangeWith (c : XYConsts) (inp : Input) (width height chartW0 chartH0 : Int)
    (titled : Int × Bool) (side : Int × Option Nat × Bool) (st : Stage) (leg : LegendInfo) :
    Arranged :=
  let top := titled.1 + side.1
  let availW2 := if leg.beside then st.availW - leg.w else st.availW
  let chartW := max (chartW0 + max availW2 0) c.edge
  let chartH := max (chartH0 + max st.availH 0) c.edge
  let plot : Rect := ⟨max (min st.plotX (width - chartW)) 0, max (min st.plotY (height - chartH)) 0,
    chartW, chartH⟩
  let legend : Rect :=
    if leg.beside then ⟨plot.x + plot.w, plot.y + max (Int.fdiv (plot.h - leg.h) 2) 0, leg.w, leg.h⟩
    else fit width height ⟨plot.x + plot.w - leg.w, plot.y, leg.w, leg.h⟩
  let axes := setAreas c inp plot top st.x st.y
  { x := axes.1, y := axes.2, width, height, plot, titleH := titled.1, titleShown := titled.2,
    sideTitle := side.2.1, sideShown := side.2.2, legend, legendOn := decide (0 < leg.rows),
    legendLH := leg.lh }

def arrange (c : XYConsts) (inp : Input) (items : List Item) (x0 y0 : Axis) : Arranged :=
  let width := c.width
  let height := c.height
  let chartW0 := Int.fdiv (width * c.reserved) 100
  let chartH0 := Int.fdiv (height * c.reserved) 100
  let titled := titleSpace c items (height - chartH0)
  let availH1 := height - chartH0 - titled.1
  let side := sideTitleSpace c items inp.horizontal availH1
  let availH2 := availH1 - side.1
  let st := stageOf c inp items x0 y0 (width - chartW0) availH2 (titled.1 + side.1)
  let leg := legendInfo c items st.availW chartH0
  arrangeWith c inp width height chartW0 chartH0 titled side st leg

/-! ### Placement -/

structure Placed where
  rect : Rect
  align : Align
  shown : Bool

def hidden : Placed := ⟨zeroRect, .middle, false⟩

def checkRect (r : Rect) : Except LayoutError Unit :=
  checkMagnitude [r.x, r.y, r.w, r.h]

def Arranged.insidePlot (a : Arranged) (r : Rect) : Rect :=
  ⟨clamp r.x a.plot.x (max (a.plot.x + a.plot.w - r.w) a.plot.x),
   clamp r.y a.plot.y (max (a.plot.y + a.plot.h - r.h) a.plot.y), r.w, r.h⟩

def Arranged.pointXY (a : Arranged) (c : XYConsts) (horizontal : Bool) (pt : XPoint) : Int × Int :=
  let cat := a.x.pointPos pt c.edge
  let val := a.y.valuePos pt.value c.edge
  if horizontal then (val, cat) else (cat, val)

def Arranged.titleRect (a : Arranged) (c : XYConsts) (t : TextBox) : Rect :=
  let half := Int.fdiv t.w 2
  let centre := clamp (Int.fdiv (2 * a.plot.x + a.plot.w) 2) half (a.width - half)
  ⟨centre - half, c.titlePad, t.w, t.h⟩

def Arranged.axisTitleRect (a : Arranged) (c : XYConsts) (i : Nat) (ax : Axis) (t : TextBox) :
    Option (Rect × Align) :=
  match ax.pos with
  | .left =>
    if a.sideShown && a.sideTitle == some i then
      some (⟨c.padX, a.titleH + c.axisTitlePad, t.w, t.h⟩, .start)
    else none
  | .bottom =>
    if ax.space.title == 0 then none
    else
      let centre := Int.fdiv (ax.r0 + ax.r1) 2
      some (⟨centre - Int.fdiv t.w 2, ax.area.y + ax.area.h - c.axisTitlePad - t.h, t.w, t.h⟩, .middle)
  | .top =>
    if ax.space.title == 0 then none
    else
      let centre := ax.area.x + Int.fdiv ax.area.w 2
      some (⟨centre - Int.fdiv t.w 2, ax.area.y + c.axisTitlePad, t.w, t.h⟩, .middle)

def Arranged.tickRect (c : XYConsts) (ax : Axis) (k : Nat) (t : TextBox) : Option (Rect × Align) :=
  if !ax.space.showLabel then none
  else
    let pos := ax.tickPos k c.edge
    let line := ax.space.line
    let tick := ax.space.tick
    match ax.pos with
    | .bottom =>
      some (⟨pos - Int.fdiv t.w 2, ax.area.y + c.padY + tick + line, t.w, t.h⟩, .middle)
    | .left =>
      some (⟨ax.area.x + ax.area.w - c.padX - tick - line - t.w, pos - Int.fdiv t.h 2, t.w, t.h⟩,
        .«end»)
    | .top =>
      some (⟨pos - Int.fdiv t.w 2, ax.area.y + ax.space.title + c.padY, t.w, t.h⟩, .middle)

def Arranged.legendRect (a : Arranged) (c : XYConsts) (plot : Nat) (t : TextBox) :
    Option (Rect × Align) :=
  if a.legendOn then
    let row := a.legend.y + c.legendPad + (plot : Int) * (a.legendLH + c.itemGap)
    some (⟨a.legend.x + c.legendPad + c.legendMarker + c.markerGap, row, t.w, t.h⟩, .start)
  else none

def Arranged.pointLabelRect (a : Arranged) (c : XYConsts) (inp : Input) (s : Spec) (t : TextBox) :
    Option (Rect × Align) :=
  let pt : XPoint := ((inp.plots[s.plot]?).bind (·.points[s.index]?)).getD
    ⟨false, 0, false, 0, 0, ""⟩
  let xy := a.pointXY c inp.horizontal pt
  if inp.horizontal then
    some (a.insidePlot ⟨xy.1 + c.pointOffset, xy.2 - Int.fdiv t.h 2, t.w, t.h⟩, .start)
  else
    some (a.insidePlot ⟨xy.1 - Int.fdiv t.w 2, xy.2 - c.pointOffset - Int.fdiv t.h 2, t.w, t.h⟩,
      .middle)

def Arranged.labelRect (a : Arranged) (c : XYConsts) (inp : Input) (i : Nat) (it : Item) :
    Option (Rect × Align) :=
  let t := it.box
  match it.spec.kind with
  | .title => if a.titleShown then some (a.titleRect c t, .middle) else none
  | .xTitle => a.axisTitleRect c i a.x t
  | .yTitle => a.axisTitleRect c i a.y t
  | .xTick => Arranged.tickRect c a.x it.spec.index t
  | .yTick => Arranged.tickRect c a.y it.spec.index t
  | .legend => a.legendRect c it.spec.plot t
  | .point => a.pointLabelRect c inp it.spec t

def isTick (k : Kind) : Bool := k == .xTick || k == .yTick

def overlapsTick (c : XYConsts) (cell : Bool) (items : List Item) (acc : List Placed) (i : Nat)
    (r : Rect) : Bool :=
  if !cell || !isTick ((items[i]?.map (·.spec.kind)).getD .title) then false
  else
    (acc.zipIdx.any fun (b, j) =>
      (items[j]?.map (·.spec.kind)) == (items[i]?.map (·.spec.kind)) && b.shown &&
        decide (r.x < b.rect.x + b.rect.w + c.edge ∧ b.rect.x < r.x + r.w + c.edge ∧
          r.y < b.rect.y + b.rect.h ∧ b.rect.y < r.y + r.h))

def placeAll (c : XYConsts) (cell : Bool) (inp : Input) (a : Arranged) (items : List Item) :
    Except LayoutError (List Placed) :=
  items.zipIdx.foldlM (fun (acc : List Placed) (it, i) =>
    match a.labelRect c inp i it with
    | none => pure (acc ++ [hidden])
    | some (r0, align) =>
      let r := fit a.width a.height r0
      if overlapsTick c cell items acc i r then pure (acc ++ [hidden])
      else do
        checkRect r
        pure (acc ++ [⟨r, align, true⟩])) []

/-! ### The plot boxes -/

def barWidth (a : Arranged) (c : XYConsts) (cell : Bool) : Int :=
  let w0 := Int.fdiv (min (2 * a.x.outer) a.x.tickDistance * (1000 - c.barPad)) 1000
  if cell then max w0 1 else w0

def barRect (a : Arranged) (c : XYConsts) (cell horizontal : Bool) (pt : XPoint) : Rect :=
  let cat := a.x.pointPos pt c.edge
  let val := a.y.valuePos pt.value c.edge
  let width := barWidth a c cell
  let start := cat - Int.fdiv width 2
  if horizontal then ⟨a.plot.x, start, val - a.plot.x + c.edge, width⟩
  else ⟨start, val, width, a.plot.y + a.plot.h - val⟩

def lineBounds (a : Arranged) (c : XYConsts) (horizontal : Bool) (pl : XPlot) : Rect :=
  let pts := (pl.points.filter (·.present)).map (a.pointXY c horizontal)
  match pts with
  | [] => ⟨a.plot.x, a.plot.y, 0, 0⟩
  | first :: rest =>
    let lox := rest.foldl (fun m p => min m p.1) first.1
    let loy := rest.foldl (fun m p => min m p.2) first.2
    let hix := rest.foldl (fun m p => max m p.1) first.1
    let hiy := rest.foldl (fun m p => max m p.2) first.2
    ⟨lox, loy, hix - lox + c.edge, hiy - loy + c.edge⟩

def boxRect (a : Arranged) (c : XYConsts) (cell : Bool) (inp : Input) (b : BoxSpec) : Rect :=
  if b.isPlot then a.plot
  else
    let pl : XPlot := (inp.plots[b.plot]?).getD ⟨0, "", []⟩
    if b.isLine then lineBounds a c inp.horizontal pl
    else barRect a c cell inp.horizontal ((pl.points[b.point]?).getD ⟨false, 0, false, 0, 0, ""⟩)

/-! ### The scene items -/

structure Seg where
  x0 : Int
  y0 : Int
  x1 : Int
  y1 : Int

def axisSegments (c : XYConsts) (ax : Axis) : List Seg :=
  let sp := ax.space
  let edge := c.edge
  match ax.pos with
  | .bottom =>
    let y := ax.area.y + Int.fdiv sp.line 2
    ⟨ax.r0, y, ax.r1 - edge, y⟩ ::
      (List.range ax.count).map fun k =>
        let x := ax.tickPos k edge
        ⟨x, y, x, ax.area.y + sp.line + sp.tick - edge⟩
  | .left =>
    let x := ax.area.x + ax.area.w - sp.line + Int.fdiv sp.line 2
    ⟨x, ax.r0, x, ax.r1 - edge⟩ ::
      (List.range ax.count).map fun k =>
        let y := ax.tickPos k edge
        ⟨x, y, ax.area.x + ax.area.w - sp.line - sp.tick, y⟩
  | .top =>
    let y := ax.area.y + ax.area.h - sp.line + Int.fdiv sp.line 2
    ⟨ax.r0, y, ax.r1 - edge, y⟩ ::
      (List.range ax.count).map fun k =>
        let x := ax.tickPos k edge
        ⟨x, y, x, ax.area.y + ax.area.h - sp.line - sp.tick⟩

def pointOf (x y : Int) : Except LayoutError Point := do
  checkMagnitude [x, y]
  return ⟨x, y⟩

def plain (style : String) : Paint := { style }

def fin12 (n : Nat) : Fin 12 := ⟨n % 12, Nat.mod_lt _ (by decide)⟩

def barShape (plot : Nat) : Paint := { style := "series", series := fin12 plot }

def lineShape (plot : Nat) : Paint :=
  { style := "series-line", series := fin12 plot, width := .emphasis,
    line := [LineStyle.solid, .dashed, .dotted].getD (plot % 3) .solid }

def axisPrimitives (c : XYConsts) (ax : Axis) : Except LayoutError (List Primitive) := do
  let mut out : List Primitive := []
  for (s, i) in (axisSegments c ax).zipIdx do
    let isLine := i == 0
    if (isLine && ax.space.line == 0) || (!isLine && ax.space.tick == 0) ||
        (s.x0 == s.x1 && s.y0 == s.y1) then
      continue
    let from_ ← pointOf s.x0 s.y0
    let to ← pointOf s.x1 s.y1
    out := out ++ [.polyline [from_, to] 0 (plain "rule")]
  return out

def runsOf (lines : List Measure.Line) : List (List TextRun) :=
  lines.map fun l => [⟨String.ofList l.text, false, false⟩]

def textRoleOf : Measure.Role → TextRole
  | .title => .title
  | .body => .body
  | .label => .label

def textItem (it : Item) (pl : Placed) : Primitive :=
  let style := if isTick it.spec.kind then "text-muted" else "text"
  .text { rect := pl.rect, role := textRoleOf it.role, size := it.size, align := pl.align, style,
          lines := runsOf it.box.lines }

def textItems (items : List Item) (placed : List Placed) (owner : String) : List Primitive :=
  (items.zip placed).filterMap fun (it, pl) =>
    if it.spec.owner == owner && pl.shown then some (textItem it pl) else none

def legendMarkers (a : Arranged) (c : XYConsts) (inp : Input) : Except LayoutError (List Primitive) :=
  if !a.legendOn then pure []
  else do
    let mut items : List Primitive := []
    for (pl, i) in inp.plots.zipIdx do
      let row := a.legend.y + c.legendPad + (i : Int) * (a.legendLH + c.itemGap)
      let x := a.legend.x + c.legendPad
      let y := row + Int.fdiv (a.legendLH - c.legendMarker) 2
      if pl.isBar then
        items := items ++ [.rect ⟨x, y, c.legendMarker, c.legendMarker⟩ (barShape i)]
      else
        let from_ ← pointOf x (y + Int.fdiv c.legendMarker 2)
        let to ← pointOf (x + c.legendMarker - c.edge) (y + Int.fdiv c.legendMarker 2)
        items := items ++ [.path [.M from_, .L to] (lineShape i)]
    return items

def lineRuns (pl : XPlot) : List (List XPoint) :=
  let step : List (List XPoint) × Bool → XPoint → List (List XPoint) × Bool := fun (runs, open_) pt =>
    if !pt.present then (runs, false)
    else if open_ then (runs.dropLast ++ [(runs.getLastD []) ++ [pt]], true)
    else (runs ++ [[pt]], true)
  (pl.points.foldl step ([], false)).1

def linePath (a : Arranged) (c : XYConsts) (inp : Input) (index : Nat) (pl : XPlot) :
    Except LayoutError Primitive := do
  let mut cmds : List PathCommand := []
  for run in lineRuns pl do
    for (pt, j) in run.zipIdx do
      let xy := a.pointXY c inp.horizontal pt
      let at_ ← pointOf xy.1 xy.2
      if j == 0 then cmds := cmds ++ [.M at_]
      if j > 0 || run.length == 1 then cmds := cmds ++ [.L at_]
  return .path cmds (lineShape index)

def boxItems (a : Arranged) (c : XYConsts) (inp : Input) (items : List Item) (placed : List Placed)
    (rects : List Rect) (b : BoxSpec) (i : Nat) : Except LayoutError (List Primitive) := do
  let pl : XPlot := (inp.plots[b.plot]?).getD ⟨0, "", []⟩
  let head : List Primitive ←
    if b.isPlot then legendMarkers a c inp
    else if b.isLine then do pure [← linePath a c inp b.plot pl]
    else pure [.rect (rects.getD i zeroRect) (barShape b.plot)]
  return head ++ textItems items placed b.id

def groupsOf (a : Arranged) (c : XYConsts) (inp : Input) (items : List Item) (placed : List Placed)
    (boxes : List BoxSpec) (rects : List Rect) : Except LayoutError (List Group) := do
  let xs ← axisPrimitives c a.x
  let ys ← axisPrimitives c a.y
  let axes := xs ++ ys
  let decor : List Group := if axes.isEmpty then [] else [⟨.decor, "", axes⟩]
  let nodes ← boxes.zipIdx.mapM fun (b, i) => do
    let its ← boxItems a c inp items placed rects b i
    return (⟨.node, b.id, its⟩ : Group)
  return decor ++ nodes

/-! ### The result -/

structure Result where
  canvas : Size
  boxes : List BoxSpec
  boxRects : List Rect
  items : List Item
  placed : List Placed
  groups : List Group
  capped : Bool

structure Prep where
  c : XYConsts
  x0 : Axis
  y0 : Axis
  capped : Bool
  items : List Item

/-- The constants with the canvas sides and the plot reserve that the config keys set. -/
def adjustedConsts (profile : Profile) (inp : Input) (c0 : XYConsts) : XYConsts :=
  { c0 with
    width := match inp.width with
      | some n => if profile == .cell then Measure.ceilDiv n 8 else n * 64
      | none => c0.width
    height := match inp.height with
      | some n => if profile == .cell then Measure.ceilDiv n 16 else n * 64
      | none => c0.height
    reserved := inp.reserved.getD c0.reserved }

def categoryAxis (inp : Input) (a : Axis) : Axis :=
  { a with pos := if inp.horizontal then Pos.left else Pos.bottom,
           showLabels := inp.showLabel.getD true, fontSize := inp.fontSize.getD 14 }

def valueAxis (inp : Input) (a : Axis) : Axis :=
  { a with pos := if inp.horizontal then Pos.top else Pos.left }

def prepare (profile : Profile) (inp : Input) : Except LayoutError Prep := do
  let c0 ← XYConsts.load profile
  let c := adjustedConsts profile inp c0
  let axes ← newAxes inp
  checkMagnitude (inp.plots.flatMap fun pl => pl.points.flatMap fun pt => [pt.value, pt.x])
  let x0 := categoryAxis inp axes.1
  let y0 := valueAxis inp axes.2.1
  let items ← measureAll c (profile == .cell) x0 (labelSpecs inp x0 y0)
  return ⟨c, x0, y0, axes.2.2, items⟩

def checkRects (rects : List Rect) : Except LayoutError Unit :=
  checkMagnitude (rects.flatMap fun r => [r.x, r.y, r.w, r.h])

def finish (profile : Profile) (inp : Input) (p : Prep) : Except LayoutError Result :=
  let cell := profile == .cell
  let a := arrange p.c inp p.items p.x0 p.y0
  let boxes := boxSpecs inp
  let rects := boxes.map (boxRect a p.c cell inp)
  (placeAll p.c cell inp a p.items).bind fun placed =>
  (checkMagnitude [a.width, a.height]).bind fun _ =>
  (checkRects rects).bind fun _ =>
  (groupsOf a p.c inp p.items placed boxes rects).bind fun groups =>
  .ok ⟨⟨a.width, a.height⟩, boxes, rects, p.items, placed, groups, p.capped⟩

def layout (profile : Profile) (inp : Input) : Except LayoutError Result :=
  (prepare profile inp).bind (finish profile inp)

end XY
end Chart
end Elegant

import Elegant.Model
import Elegant.Scene
import Elegant.Measure
import Elegant.StyledMeasure
import Elegant.GridConsts
import Elegant.GridRoute

set_option autoImplicit false

/-! Lean reference of the grid layout family for the block kind (`spec/layout/grid.md`, grid-05 to
grid-11 and grid-61 to grid-67): the column tracks of every composite, the child rectangles,
the lattice routing of the edges, and the label placement. It computes the same integers as the
Go family `grid.Block`.

The family reads its boxes in pre-order: a box lists its parent before itself. The boxes are
described by `GBox`, the root composite is implicit (parent `-1`), and every value is measured
in the unit of the profile. All sizes are computed by pure functions; the overflow conditions
of the checked arithmetic are collected into Boolean guards. -/

namespace Elegant
namespace Grid

inductive Kind where
  | leaf | space | composite
  deriving DecidableEq, Repr, Inhabited

structure GBox where
  parent : Int
  kind : Kind
  span : Int
  columns : Int
  size : Size
  deriving DecidableEq, Repr, Inhabited

structure GInput where
  columns : Int
  boxes : List GBox
  edges : List Edge
  deriving Repr

structure GParams where
  padding : Int
  bendCost : Int
  lineThickness : Int
  deriving DecidableEq, Repr

/-- The rectangles of the boxes in input order, the routes, the label rectangles, and the canvas. -/
structure GLayout where
  rects : List Rect
  routes : List (List Point)
  labels : List Rect
  canvas : Size
  deriving Repr

def ceilDiv (a b : Int) : Int := Int.fdiv (a + b - 1) b

def effective (span : Int) : Int := max span 1

/-! ### Tracks -/

structure Kid where
  child : Nat
  span : Int
  w : Int
  h : Int
  deriving DecidableEq, Repr

structure Slot where
  child : Nat
  col : Int
  row : Int
  eff : Int
  w : Int
  h : Int
  deriving DecidableEq, Repr, Inhabited

structure Track where
  slots : List Slot
  ncols : Int
  nrows : Int
  unit : Int
  rows : List Int
  width : Int
  height : Int
  deriving DecidableEq, Repr, Inhabited

def slotCol (columns pos : Int) : Int := if 0 < columns then Int.fmod pos columns else pos

def slotRow (columns pos : Int) : Int := if 0 < columns then Int.fdiv pos columns else 0

def slotEff (columns pos span : Int) : Int :=
  if 0 < columns then min (effective span) (columns - slotCol columns pos) else effective span

/-- The slots of the kids in order. `columns > 0` wraps at that many columns and clips a span
to the rest of its row; otherwise all kids share one row. -/
def slotsFrom (columns : Int) : Int → List Kid → List Slot
  | _, [] => []
  | pos, k :: ks =>
    ⟨k.child, slotCol columns pos, slotRow columns pos, slotEff columns pos k.span, k.w, k.h⟩ ::
      slotsFrom columns (pos + slotEff columns pos k.span) ks

def ncolsOf (slots : List Slot) : Int := slots.foldl (fun m s => max m (s.col + s.eff)) 0

def nrowsOf (slots : List Slot) : Int := slots.foldl (fun m s => max m (s.row + 1)) 0

def unitOf (slots : List Slot) : Int := slots.foldl (fun m s => max m (ceilDiv s.w s.eff)) 0

def rowsOf (slots : List Slot) (nrows : Int) : List Int :=
  (List.range nrows.toNat).map fun (r : Nat) =>
    slots.foldl (fun m s => if s.row = (r : Int) then max m s.h else m) 0

def trackOf (gapX gapY columns : Int) (kids : List Kid) : Track :=
  let slots := slotsFrom columns 0 kids
  let rows := rowsOf slots (nrowsOf slots)
  ⟨slots, ncolsOf slots, nrowsOf slots, unitOf slots, rows,
    ncolsOf slots * unitOf slots + (ncolsOf slots + 1) * gapX,
    rows.sum + (nrowsOf slots + 1) * gapY⟩

def maxTracks : Int := 16384

/-- The checked arithmetic of the track sizes stays in range. -/
def trackOk (gapX gapY : Int) (t : Track) : Bool :=
  decide (t.ncols ≤ maxTracks) && decide (t.nrows ≤ maxTracks) &&
    decide (t.ncols * t.unit ≤ COORD_LIMIT) && decide ((t.ncols + 1) * gapX ≤ COORD_LIMIT) &&
    decide (t.width ≤ COORD_LIMIT) && decide ((t.nrows + 1) * gapY ≤ COORD_LIMIT) &&
    decide (t.height ≤ COORD_LIMIT)

/-! ### The tree of boxes -/

structure Ctx where
  inp : GInput
  gapX : Int
  gapY : Int

def Ctx.n (c : Ctx) : Nat := c.inp.boxes.length

def Ctx.box (c : Ctx) (i : Nat) : GBox := c.inp.boxes.getD i default

/-- The slot a box hangs on: its parent, or the root (index `n`). -/
def Ctx.slotOf (c : Ctx) (i : Nat) : Nat :=
  if (c.box i).parent < 0 then c.n else (c.box i).parent.toNat

def Ctx.rootKids (c : Ctx) : List Nat :=
  (List.range c.n).filter fun k => decide (c.slotOf k = c.n)

/-- The children of box `i`; a child comes after its parent. -/
def Ctx.kidsOf (c : Ctx) (i : Nat) : List Nat :=
  (List.range' (i + 1) (c.n - (i + 1))).filter fun k => decide (c.slotOf k = i)

theorem Ctx.kidsOf_mem {c : Ctx} {i k : Nat} (h : k ∈ c.kidsOf i) : i < k ∧ k < c.n := by
  unfold Ctx.kidsOf at h
  rw [List.mem_filter, List.mem_range'] at h
  omega

def Ctx.kidOf (c : Ctx) (sz : Int × Int) (k : Nat) : Kid :=
  match (c.box k).kind with
  | .space => ⟨k, (c.box k).span, 0, 0⟩
  | _ => ⟨k, (c.box k).span, sz.1, sz.2⟩

/-- The track plan of composite `i`, from the plans of its composite children. -/
def Ctx.plan (c : Ctx) (i : Nat) : Track :=
  trackOf c.gapX c.gapY (max (c.box i).columns 0)
    ((c.kidsOf i).attach.map fun ⟨k, _⟩ =>
      c.kidOf (match (c.box k).kind with
        | .composite => ((c.plan k).width, (c.plan k).height)
        | _ => ((c.box k).size.w, (c.box k).size.h)) k)
termination_by c.n - i
decreasing_by
  have := Ctx.kidsOf_mem ‹_›
  omega

/-- The measured size of a child: the plan size of a composite, the box size otherwise. -/
def Ctx.size (c : Ctx) (k : Nat) : Int × Int :=
  match (c.box k).kind with
  | .composite => ((c.plan k).width, (c.plan k).height)
  | _ => ((c.box k).size.w, (c.box k).size.h)

def Ctx.rootPlan (c : Ctx) : Track :=
  trackOf c.gapX c.gapY (max c.inp.columns 0) (c.rootKids.map fun k => c.kidOf (c.size k) k)

def Ctx.rootFrame (c : Ctx) : Rect := ⟨0, 0, c.rootPlan.width, c.rootPlan.height⟩

def rowTop (frameY gapY : Int) (rows : List Int) (r : Nat) : Int :=
  frameY + ((rows.take r).map fun h => h + gapY).sum

def childRect (gapX gapY : Int) (frame : Rect) (t : Track) (s : Slot) : Rect :=
  let r := s.row.toNat
  ⟨frame.x + gapX + s.col * (t.unit + gapX), rowTop frame.y gapY t.rows r + gapY,
    t.unit * s.eff + gapX * (s.eff - 1), t.rows.getD r 0⟩

def slotFor (t : Track) (i : Nat) : Slot := (t.slots.find? fun s => s.child = i).getD default

/-- The rectangle of box `i`, placed in the frame of its parent. -/
def Ctx.rect (c : Ctx) (i : Nat) : Rect :=
  if c.slotOf i = c.n then childRect c.gapX c.gapY c.rootFrame c.rootPlan (slotFor c.rootPlan i)
  else if _h : c.slotOf i < i then
    childRect c.gapX c.gapY (c.rect (c.slotOf i)) (c.plan (c.slotOf i)) (slotFor (c.plan (c.slotOf i)) i)
  else default
termination_by i

/-! ### Guards -/

def GBox.sizeOk (b : GBox) : Bool := decide (0 ≤ b.size.w) && decide (0 ≤ b.size.h)

/-- Every parent is `-1` or an earlier composite; sizes and edges are in range. -/
def GInput.valid (inp : GInput) (padding : Int) : Bool :=
  decide (0 ≤ padding) &&
    (inp.boxes.zipIdx.all fun (b, i) =>
      b.sizeOk && decide (-1 ≤ b.parent) && decide (b.parent < (i : Int)) &&
        (decide (b.parent < 0) || decide ((inp.boxes.getD b.parent.toNat default).kind = Kind.composite))) &&
    (inp.edges.all fun e =>
      decide (e.fromBox < inp.boxes.length) && decide (e.toBox < inp.boxes.length) &&
        decide (0 ≤ e.label.w) && decide (0 ≤ e.label.h))

def maxDepth : Nat := 66

/-- The nesting depth of every box: a child of the root has depth 1. -/
def GInput.depths (inp : GInput) : List Nat :=
  inp.boxes.foldl (fun acc b => acc ++ [if b.parent < 0 then 1 else acc.getD b.parent.toNat 0 + 1]) []

def GInput.depthOk (inp : GInput) : Bool :=
  (inp.boxes.zip inp.depths).all fun (b, d) => b.kind != Kind.composite || decide (d ≤ maxDepth)

def Ctx.measureOk (c : Ctx) : Bool :=
  trackOk c.gapX c.gapY c.rootPlan &&
    (List.range c.n).all fun i =>
      (c.box i).kind != Kind.composite || trackOk c.gapX c.gapY (c.plan i)

def Ctx.placeOk (c : Ctx) : Bool :=
  (List.range c.n).all fun i =>
    decide ((c.rect i).y + (c.rect i).h ≤ COORD_LIMIT) &&
      decide ((c.rect i).x + (c.rect i).w ≤ COORD_LIMIT)

/-! ### The lattice lines -/

def Ctx.linesOf (c : Ctx) (pad : Int) (frame : Rect) (t : Track) : List Int × List Int :=
  ((List.range (t.ncols.toNat + 1)).map fun (j : Nat) => frame.x + (j : Int) * (t.unit + c.gapX) + pad,
   (List.range (t.nrows.toNat + 1)).map fun (r : Nat) => rowTop frame.y c.gapY t.rows r + pad)

def Ctx.allLines (c : Ctx) (pad : Int) : List Int × List Int :=
  let root := c.linesOf pad c.rootFrame c.rootPlan
  let comps := ((List.range c.n).filter fun i => (c.box i).kind = Kind.composite).map fun i =>
    c.linesOf pad (c.rect i) (c.plan i)
  (root.1 ++ (comps.map (·.1)).flatten, root.2 ++ (comps.map (·.2)).flatten)

/-! ### The family entry -/

def Ctx.routeIn (c : Ctx) (p : GParams) : RouteIn :=
  let ls := c.allLines p.padding
  let ids := List.range c.n
  ⟨p.padding, p.bendCost, p.lineThickness, c.gapX, c.gapY, ls.1, ls.2, ids.map c.rect,
    (ids.filter fun i => (c.box i).kind = Kind.leaf).map c.rect,
    (ids.filter fun i => (c.box i).kind = Kind.composite).map c.rect, c.inp.edges⟩

def gapsOf (inp : GInput) (padding : Int) : Int × Int :=
  let lw := inp.edges.foldl (fun m e => max m e.label.w) 0
  let lh := inp.edges.foldl (fun m e => max m e.label.h) 0
  let corridor := if inp.edges.isEmpty then padding else 2 * padding
  (corridor + lw, corridor + lh)

def block (inp : GInput) (p : GParams) : Except LayoutError GLayout :=
  if !inp.valid p.padding then .error .domain
  else
    let gaps := gapsOf inp p.padding
    let c : Ctx := ⟨inp, gaps.1, gaps.2⟩
    if !inp.depthOk then .error .domain
    else if !c.measureOk then .error .overflow
    else if !c.placeOk then .error .overflow
    else
      let rin := c.routeIn p
      match routes rin with
      | .error e => .error e
      | .ok rts =>
        match placeAll rin rts c.rootFrame with
        | .error e => .error e
        | .ok (labels, canvas) =>
          .ok ⟨rin.rects, rts, labels, ⟨canvas.w, canvas.h⟩⟩

/-! ### The block adapter: model dump to grid input to scene -/

structure Spec where
  type : String
  columns : Int
  span : Int
  directions : List String
  deriving Repr, Inhabited

def autoColumns : Int := -1

/-- A decimal int32 literal with an optional sign, as Go's `strconv.ParseInt(text, 10, 32)`. -/
def parseInt32 (text : String) : Option Int :=
  let cs := text.toList
  let (neg, ds) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | _ => (false, cs)
  if ds.isEmpty || !ds.all Char.isDigit then none
  else
    let v : Int := ((String.ofList ds).toNat?).getD 0
    let v := if neg then -v else v
    if I32_MIN ≤ v ∧ v ≤ I32_MAX then some v else none

def parseCount (text : String) (fallback : Int) : Int := (parseInt32 text).getD fallback

def Spec.parse (shape : String) : Spec :=
  match shape.splitOn ";" with
  | [] => ⟨"rect", autoColumns, 1, []⟩
  | head :: fields =>
    fields.foldl (fun s f =>
      let key := String.ofList (f.toList.takeWhile (· != '='))
      let value := String.ofList ((f.toList.dropWhile (· != '=')).drop 1)
      if key == "columns" then { s with columns := parseCount value s.columns }
      else if key == "span" then { s with span := parseCount value s.span }
      else if key == "directions" then { s with directions := value.splitOn "," }
      else s) ⟨if head.isEmpty then "rect" else head, autoColumns, 1, []⟩

def rootOk (m : Model) : Bool :=
  match m.boxes.head? with
  | some b => b.role == .group && b.parent == "" && (Spec.parse b.shape).type == "composite"
  | none => false

/-- Space records reserve grid tracks but are not obstacles. The native block
frontend therefore always declares them nonexclusive. Reject inconsistent
developer models before measuring or laying out any geometry. -/
def spaceBoxesNonexclusive (m : Model) : Bool :=
  m.boxes.all fun b =>
    b.role != .node || (Spec.parse b.shape).type != "space" || !b.exclusive

/-- The text of a box: its first owned label, else its non-empty text, else its id. -/
def boxText (m : Model) (b : ModelBox) : String :=
  match m.labels.find? fun l => l.owner == b.id with
  | some l => l.text
  | none => match b.text with
    | some t => if t.isEmpty then b.id else t
    | none => b.id

/-- The last box with this id. -/
def indexOf (boxes : List ModelBox) (id : String) : Option Nat :=
  (boxes.zipIdx.reverse.find? fun (b, _) => b.id == id).map (·.2)

def scalePadding (profile : Profile) (px : Int) : Int :=
  match profile with
  | .cell => max 1 (Int.fdiv (px + 7) 8)
  | .vector => px * 64

def configInt32 : ConfigValue → Option Int
  | .integer i => if I32_MIN ≤ i ∧ i ≤ I32_MAX then some i else none
  | .string s => parseInt32 s
  | .boolean _ => none

/-- The `padding` config key replaces the default padding when it is a non-negative int32. -/
def paddingOf (m : Model) (dflt : Int) : Int :=
  m.options.config.foldl (fun pad (kv : String × ConfigValue) =>
    if kv.1 == "padding" then
      match configInt32 kv.2 with
      | some v => if 0 ≤ v then scalePadding m.profile v else pad
      | none => pad
    else pad) dflt

def metricOf (profile : Profile) (fontFamily : Bool := false) : Except LayoutError Measure.Metric :=
  match profile with
  | .cell => pure Measure.Metric.cell
  | .vector => Measure.Role.label.metric fontFamily

def measureText (metric : Measure.Metric) (text : String) :
    Except LayoutError (List Measure.Line) :=
  match StyledMeasure.wrap metric I32_MAX text.toList with
  | .ok lines => .ok lines
  | .error _ => .error .overflow

def extentOf (lineHeight : Int) (lines : List Measure.Line) : Size :=
  ⟨min (lines.foldl (fun w l => max w l.width) 0) COORD_LIMIT,
    min ((lines.length : Int) * lineHeight) COORD_LIMIT⟩

structure BlockPlan where
  m : Model
  consts : BlockConsts
  padding : Int
  specs : List Spec
  boxLines : List (List Measure.Line)
  labelLines : List (List Measure.Line)
  input : GInput

def BlockPlan.params (pl : BlockPlan) : GParams :=
  ⟨pl.padding, pl.consts.bendCost, pl.consts.lineThickness⟩

def gridBox (m : Model) (consts : BlockConsts) (padding : Int) (specs : List Spec)
    (boxLines : List (List Measure.Line)) (i : Nat) : Except LayoutError GBox := do
  let b ← match m.boxes[i]? with
    | some b => pure b
    | none => throw .domain
  let spec := specs.getD i default
  let parent ← match indexOf m.boxes b.parent with
    | some p => if b.parent == "" then throw .domain else pure p
    | none => throw .domain
  let kind := if b.role == .group then Kind.composite
    else if spec.type == "space" then Kind.space else Kind.leaf
  let text := extentOf consts.lineHeight (boxLines.getD i [])
  let size : Size := if kind == Kind.leaf then
      ⟨min (text.w + 2 * padding) COORD_LIMIT, min (text.h + 2 * padding) COORD_LIMIT⟩
    else default
  return ⟨(parent : Int) - 1, kind, spec.span, spec.columns, size⟩

def gridEdge (m : Model) (consts : BlockConsts) (labelLines : List (List Measure.Line))
    (r : ModelRoute) : Except LayoutError Edge := do
  let src ← match indexOf m.boxes r.fromId with
    | some p => if p == 0 then throw .domain else pure p
    | none => throw .domain
  let dst ← match indexOf m.boxes r.toId with
    | some p => if p == 0 then throw .domain else pure p
    | none => throw .domain
  let label := match m.labels.findIdx? fun l => l.owner == r.id with
    | some j => extentOf consts.lineHeight (labelLines.getD j [])
    | none => default
  return ⟨src - 1, dst - 1, label⟩

def BlockPlan.build (m : Model) : Except LayoutError BlockPlan := do
  if !rootOk m then throw .domain
  if !spaceBoxesNonexclusive m then throw .domain
  let consts ← BlockConsts.load m.profile
  let padding := paddingOf m consts.padding
  let specs := m.boxes.map fun b => Spec.parse b.shape
  let metric ← metricOf m.profile m.options.fontFamily
  let boxLines ← (m.boxes.zip specs).mapM fun (b, s) =>
    if b.role == .node && s.type != "space" then measureText metric (boxText m b) else pure []
  let labelLines ← m.labels.mapM fun l => measureText metric l.text
  let boxes ← (List.range (m.boxes.length - 1)).mapM fun k =>
    gridBox m consts padding specs boxLines (k + 1)
  let edges ← m.routes.mapM (gridEdge m consts labelLines)
  return ⟨m, consts, padding, specs, boxLines, labelLines,
    ⟨(specs.getD 0 default).columns, boxes, edges⟩⟩

/-! ### Painting -/

def runsOf (lines : List Measure.Line) : List (List TextRun) :=
  lines.map fun l => [⟨String.ofList l.text, false, false⟩]

def lineTexts (lines : List Measure.Line) : List String := lines.map fun l => String.ofList l.text

structure Heads where
  up : Bool
  right : Bool
  down : Bool
  left : Bool

def headsOf (ds : List String) : Heads :=
  ⟨ds.any (· == "up") || ds.any (· == "y"), ds.any (· == "right") || ds.any (· == "x"),
    ds.any (· == "down") || ds.any (· == "y"), ds.any (· == "left") || ds.any (· == "x")⟩

def axisOf (a b : Point) : MarkerAxis :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  let horizontal := decide (dy.natAbs ≤ dx.natAbs)
  if horizontal then (if dx < 0 then .negativeX else .positiveX)
  else if dy < 0 then .negativeY else .positiveY

def polygonPoints (typ : String) (r : Rect) : Option (List Point) :=
  let slant := min (Int.fdiv r.h 4) (Int.fdiv r.w 4)
  let right := r.x + r.w
  let bottom := r.y + r.h
  let midX := r.x + Int.fdiv r.w 2
  let midY := r.y + Int.fdiv r.h 2
  match typ with
  | "diamond" => some [⟨midX, r.y⟩, ⟨right, midY⟩, ⟨midX, bottom⟩, ⟨r.x, midY⟩]
  | "hexagon" => some [⟨r.x + slant, r.y⟩, ⟨right - slant, r.y⟩, ⟨right, midY⟩,
      ⟨right - slant, bottom⟩, ⟨r.x + slant, bottom⟩, ⟨r.x, midY⟩]
  | "lean_right" => some [⟨r.x + slant, r.y⟩, ⟨right, r.y⟩, ⟨right - slant, bottom⟩, ⟨r.x, bottom⟩]
  | "lean_left" => some [⟨r.x, r.y⟩, ⟨right - slant, r.y⟩, ⟨right, bottom⟩, ⟨r.x + slant, bottom⟩]
  | "trapezoid" => some [⟨r.x + slant, r.y⟩, ⟨right - slant, r.y⟩, ⟨right, bottom⟩, ⟨r.x, bottom⟩]
  | "inv_trapezoid" => some [⟨r.x, r.y⟩, ⟨right, r.y⟩, ⟨right - slant, bottom⟩, ⟨r.x + slant, bottom⟩]
  | "odd" => some [⟨r.x, r.y⟩, ⟨right, r.y⟩, ⟨right, bottom⟩, ⟨r.x, bottom⟩, ⟨r.x + slant, midY⟩]
  | _ => none

def arrowPoints (heads : Heads) (r : Rect) : List Point :=
  let depth := Int.fdiv (min r.w r.h) 4
  let right0 := r.x + r.w
  let bottom0 := r.y + r.h
  let midX := r.x + Int.fdiv r.w 2
  let midY := r.y + Int.fdiv r.h 2
  let left := if heads.left then r.x + depth else r.x
  let right := if heads.right then right0 - depth else right0
  let top := if heads.up then r.y + depth else r.y
  let bottom := if heads.down then bottom0 - depth else bottom0
  [⟨left, top⟩] ++ (if heads.up then [⟨midX, r.y⟩] else []) ++ [⟨right, top⟩] ++
    (if heads.right then [⟨right0, midY⟩] else []) ++ [⟨right, bottom⟩] ++
    (if heads.down then [⟨midX, bottom0⟩] else []) ++ [⟨left, bottom⟩] ++
    (if heads.left then [⟨r.x, midY⟩] else [])

def arrowMarkers (heads : Heads) (r : Rect) : List Primitive :=
  let cx := r.x + Int.fdiv r.w 2
  let cy := r.y + Int.fdiv r.h 2
  (if heads.up then [Primitive.markerRef "point" ⟨cx, r.y⟩ .negativeY] else []) ++
    (if heads.right then [Primitive.markerRef "point" ⟨r.x + r.w - 1, cy⟩ .positiveX] else []) ++
    (if heads.down then [Primitive.markerRef "point" ⟨cx, r.y + r.h - 1⟩ .positiveY] else []) ++
    (if heads.left then [Primitive.markerRef "point" ⟨r.x, cy⟩ .negativeX] else [])

def cylinderPath (r : Rect) (radius : Int) : Primitive :=
  let right := r.x + r.w
  let bottom := r.y + r.h
  let centre := r.x + Int.fdiv r.w 2
  let dx := Int.fdiv (r.w * 552) 2000
  let dy := Int.fdiv (radius * 552) 1000
  .path [.M ⟨r.x, r.y + radius⟩, .L ⟨r.x, bottom - radius⟩,
    .C ⟨r.x, bottom - radius + dy⟩ ⟨centre - dx, bottom⟩ ⟨centre, bottom⟩,
    .C ⟨centre + dx, bottom⟩ ⟨right, bottom - radius + dy⟩ ⟨right, bottom - radius⟩,
    .L ⟨right, r.y + radius⟩,
    .C ⟨right, r.y + radius - dy⟩ ⟨centre + dx, r.y⟩ ⟨centre, r.y⟩,
    .C ⟨centre - dx, r.y⟩ ⟨r.x, r.y + radius - dy⟩ ⟨r.x, r.y + radius⟩, .Z] { style := "node" }

def cylinderItems (profile : Profile) (r : Rect) : List Primitive :=
  let radius := max 0 (min (Int.fdiv (r.w * 1600) (8000 + r.w)) (min (Int.fdiv r.h 4) (Int.fdiv r.h 2)))
  let cx := r.x + Int.fdiv r.w 2
  let node : Paint := { style := "node" }
  match profile with
  | .cell =>
    [.roundRect r 0 node, .ellipse cx (r.y + radius) (Int.fdiv (max (r.w - 1) 0) 2) radius node,
      .symbolRef "database" ⟨cx, r.y⟩ "node"]
  | .vector =>
    [cylinderPath r radius, .ellipse cx (r.y + radius) (Int.fdiv r.w 2) radius node]

def cellOutline (spec : Spec) (r : Rect) : List Primitive :=
  let node : Paint := { style := "node" }
  match spec.type with
  | "roundedRect" | "stadium" | "circle" => [.roundRect r 0 node]
  | "cylinder" => cylinderItems .cell r
  | "doublecircle" => [.rect r { style := "node", line := .double }]
  | "block_arrow" => .rect r node :: arrowMarkers (headsOf spec.directions) r
  | _ => [.rect r node]

def ellipseOf (r : Rect) (inset : Int) : Primitive :=
  .ellipse (r.x + Int.fdiv r.w 2) (r.y + Int.fdiv r.h 2) (Int.fdiv r.w 2 - inset)
    (Int.fdiv r.h 2 - inset) { style := "node" }

def vectorOutline (corner : Int) (spec : Spec) (r : Rect) : List Primitive :=
  let node : Paint := { style := "node" }
  match polygonPoints spec.type r with
  | some pts => [.polygon pts node]
  | none =>
    match spec.type with
    | "roundedRect" => [.roundRect r (min corner (min (Int.fdiv r.w 2) (Int.fdiv r.h 2))) node]
    | "stadium" => [.roundRect r (Int.fdiv (min r.w r.h) 2) node]
    | "circle" => [ellipseOf r 0]
    | "doublecircle" =>
      [ellipseOf r 0, ellipseOf r (min 256 (min (Int.fdiv r.w 4) (Int.fdiv r.h 4)))]
    | "cylinder" => cylinderItems .vector r
    | "subroutine" =>
      let inset := min 512 (Int.fdiv r.w 4)
      [.rect r node] ++ [r.x + inset, r.x + r.w - inset].map fun x =>
        Primitive.polyline [⟨x, r.y⟩, ⟨x, r.y + r.h⟩] 0 { style := "rule" }
    | "block_arrow" => [.polygon (arrowPoints (headsOf spec.directions) r) node]
    | _ => [.rect r node]

def outlineOf (profile : Profile) (corner : Int) (spec : Spec) (r : Rect) : List Primitive :=
  match profile with
  | .cell => cellOutline spec r
  | .vector => vectorOutline corner spec r

def textItem (rect : Rect) (lines : List Measure.Line) : Primitive :=
  .text ⟨rect, .label, 14, .middle, "text", 0, runsOf lines⟩

def nodeItems (profile : Profile) (c : BlockConsts) (spec : Spec) (r : Rect)
    (lines : List Measure.Line) : List Primitive :=
  let textH := (lines.length : Int) * c.lineHeight
  outlineOf profile c.cornerRadius spec r ++
    [textItem ⟨r.x, r.y + Int.fdiv (r.h - textH) 2, r.w, textH⟩ lines]

def routeItems (c : BlockConsts) (r : ModelRoute) (points : List Point) : List Primitive :=
  let shape : Paint :=
    { style := "edge", width := if r.stroke == "thick" then .emphasis else .normal,
      line := if r.stroke == "dotted" then .dotted else .solid }
  let startMarker := if r.markerStart == "none" then "" else r.markerStart
  let endMarker := if r.markerEnd == "none" then "" else r.markerEnd
  let last := points.length - 1
  [.polyline points c.cornerRadius shape] ++
    (if startMarker == "" then [] else
      [.markerRef startMarker (points.getD 0 default)
        (axisOf (points.getD 1 default) (points.getD 0 default))]) ++
    (if endMarker == "" then [] else
      [.markerRef endMarker (points.getD last default)
        (axisOf (points.getD (last - 1) default) (points.getD last default))])

def BlockPlan.scene (pl : BlockPlan) (res : GLayout) : Scene :=
  let m := pl.m
  let canvasRect : Rect := ⟨0, 0, res.canvas.w, res.canvas.h⟩
  let rects := canvasRect :: res.rects
  let boxes : List Box := (m.boxes.zip rects).map fun (b, r) =>
    ⟨b.id, b.role.id, r, b.parent, b.exclusive⟩
  let routePos (owner : String) : Nat := (m.routes.findIdx? fun r => r.id == owner).getD m.routes.length
  let routes : List Route := (m.routes.zip res.routes).map fun (r, pts) =>
    ⟨r.id, r.fromId, r.toId, true, pts⟩
  let labels : List SceneLabel := (m.labels.zip pl.labelLines).map fun (l, lines) =>
    ⟨⟨l.id, l.owner, res.labels.getD (routePos l.owner) default, lineTexts lines⟩, l.text⟩
  let profile := m.profile
  let rectOf (i : Nat) : Rect := rects.getD i default
  let frames : List Group := ((m.boxes.zipIdx).filter fun (b, _) => b.role == .group).map fun (b, i) =>
    ⟨.group, b.id, if i == 0 then [] else [.rect (rectOf i) { style := "group" }]⟩
  let edges : List Group := (m.routes.zip res.routes).map fun (r, pts) =>
    let drawn := if 2 ≤ pts.length then routeItems pl.consts r pts else []
    let label := match m.labels.findIdx? fun l => l.owner == r.id with
      | some j => [textItem (res.labels.getD (routePos r.id) default) (pl.labelLines.getD j [])]
      | none => []
    ⟨.edge, r.id, drawn ++ label⟩
  let nodes : List Group := ((m.boxes.zipIdx).filter fun (b, i) =>
      b.role == .node && (pl.specs.getD i default).type != "space").map fun (b, i) =>
    ⟨.node, b.id, nodeItems profile pl.consts (pl.specs.getD i default) (rectOf i)
      (pl.boxLines.getD i [])⟩
  { kind := "block", profile := profile, options := { m.options with profile := profile, direction := .TB },
    canvas := res.canvas, boxes := boxes, routes := routes, labels := labels,
    items := frames ++ edges ++ nodes }

/-- The block layout of a model-stage dump. -/
def layout (m : Model) : Except LayoutError Scene := do
  let pl ← BlockPlan.build m
  let res ← block pl.input pl.params
  return pl.scene res
end Grid
end Elegant

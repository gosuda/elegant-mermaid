import Elegant.Kinds.Common
import Elegant.Chart.Scale
import ElegantGeometry.Trig

set_option autoImplicit false

namespace Elegant.Chart.Radar

structure Curve where
  label : String := ""
  values : List Int := []
  deriving Repr, DecidableEq

structure Input where
  title : String := ""
  axes : List String := []
  curves : List Curve := []
  circle : Bool := false
  showLegend : Bool := false
  ticks : Int := 0
  maximum : Option Int := none
  minimum : Int := 0
  deriving Repr, DecidableEq

def angle (index count : Int) : Int :=
  Int.fmod (Int.fdiv (index * 65536) count - 16384) 65536

def valueRadius (radius lo hi value : Int) : Int :=
  Int.fdiv (radius * (clamp value lo hi - lo)) (hi - lo)

def polar (radius theta : Int) : Point :=
  ⟨Int.fdiv (radius * cosQ15 theta) 32768, Int.fdiv (radius * sinQ15 theta) 32768⟩

structure Constants where
  (width height margin gapX gapY legendRow tension marker markerGap anchor marginTop marginRight : Int)

def config (o : Options) (key : String) (fallback : Int) : Int :=
  (o.config.findSome? fun (k, v) =>
    if k == key then match v with | .integer n => some n | _ => none else none).getD fallback

def constants (o : Options) : Constants :=
  let margin := LayoutConst.radar_margin.get .vector
  ⟨config o "width" (Int.fdiv (LayoutConst.radar_width.get .vector) 64) * 64,
   config o "height" (Int.fdiv (LayoutConst.radar_height.get .vector) 64) * 64,
   margin, LayoutConst.radar_label_gap_x.get .vector, LayoutConst.radar_label_gap_y.get .vector,
   LayoutConst.radar_legend_row.get .vector,
   config o "curveTension" (LayoutConst.radar_curve_tension.get .vector),
   LayoutConst.radar_legend_marker.get .vector, LayoutConst.radar_legend_text_gap.get .vector,
   LayoutConst.radar_anchor_q15.get .vector,
   config o "marginTop" (Int.fdiv margin 64) * 64,
   config o "marginRight" (Int.fdiv margin 64) * 64⟩

structure Caption where
  id : String
  kind : Nat
  index : Nat
  text : String
  lines : List Measure.Line
  (width height : Int)
  rect : Rect := ⟨0, 0, 0, 0⟩
  align : Align := .middle
  shown : Bool := false

def measureCaption (id text : String) (kind index : Nat) : Except LayoutError Caption := do
  let metric ← if kind = 0 then Measure.Role.title.metric else Measure.Role.label.metric
  let lines ← Kinds.Common.unwrapped metric text
  return {
    id, kind, index, text, lines
    width := Kinds.Common.widest lines
    height := (lines.length : Int) * (if kind = 0 then 1536 else 1280) }

def captions (inp : Input) : Except LayoutError (List Caption) := do
  let title ← if inp.title == "" then pure [] else do
    let t ← measureCaption "title" inp.title 0 0
    pure [t]
  let axes ← inp.axes.zipIdx.mapM fun (text, i) => measureCaption ("axis." ++ toString i) text 1 i
  let legend ← inp.curves.zipIdx.mapM fun (curve, i) =>
    measureCaption ("legend." ++ toString i) curve.label 2 i
  return title ++ axes ++ legend

def vertices (count : Nat) (radius : Int) : List Point :=
  (List.range count).map fun (i : Nat) => polar radius (angle i count)

def curvePoints (count : Nat) (radius lo hi : Int) (curve : Curve) : List Point :=
  curve.values.zipIdx.map fun (v, i) => polar (valueRadius radius lo hi v) (angle i count)

def smooth (tension : Int) (points : List Point) : List (Point × Point × Point) :=
  let n := points.length
  points.zipIdx.map fun (p1, i) =>
    let p0 := points.getD ((i + n - 1) % n) ⟨0, 0⟩
    let p2 := points.getD ((i + 1) % n) ⟨0, 0⟩
    let p3 := points.getD ((i + 2) % n) ⟨0, 0⟩
    (⟨p1.x + Int.fdiv ((p2.x - p0.x) * tension) 1000,
      p1.y + Int.fdiv ((p2.y - p0.y) * tension) 1000⟩,
     ⟨p2.x - Int.fdiv ((p3.x - p1.x) * tension) 1000,
      p2.y - Int.fdiv ((p3.y - p1.y) * tension) 1000⟩, p2)

def legendOrigin (c : Constants) : Point :=
  ⟨Int.fdiv ((Int.fdiv c.width 2 + c.marginRight) * 3) 4,
   Int.fdiv (-(Int.fdiv c.height 2 + c.marginTop) * 3) 4⟩

def legendRow (c : Constants) (i : Nat) : Point :=
  let o := legendOrigin c
  ⟨o.x, o.y + (i : Int) * c.legendRow⟩

def placeCaption (inp : Input) (c : Constants) (radius : Int) (frame : Rect) (t : Caption) : Caption :=
  let visible := decide (t.width > 0)
  if t.kind = 0 then
    { t with rect := ⟨-Int.fdiv t.width 2, frame.y - t.height, t.width, t.height⟩, shown := visible }
  else if t.kind = 1 then
    let theta := angle t.index inp.axes.length
    let cosine := cosQ15 theta
    let sine := sinQ15 theta
    let x := Int.fdiv ((radius + c.gapX) * cosine) 32768
    let y := Int.fdiv ((radius + c.gapY) * sine) 32768
    let align := if cosine ≥ c.anchor then Align.start else if cosine ≤ -c.anchor then Align.end else Align.middle
    let left := if align == .start then x else if align == .end then x - t.width else x - Int.fdiv t.width 2
    let top := if sine ≥ c.anchor then y else if sine ≤ -c.anchor then y - t.height else y - Int.fdiv t.height 2
    { t with rect := ⟨left, top, t.width, t.height⟩, align, shown := visible }
  else
    let row := legendRow c t.index
    { t with
      rect := ⟨row.x + c.marker + c.markerGap, row.y, t.width, t.height⟩
      align := .start
      shown := visible && inp.showLegend && !inp.curves.isEmpty }

def bounds (points : List Point) : Rect :=
  let first := points.headD ⟨0, 0⟩
  let extrema := points.foldl (fun (a : Int × Int × Int × Int) p =>
    (min a.1 p.x, min a.2.1 p.y, max a.2.2.1 p.x, max a.2.2.2 p.y))
    (first.x, first.y, first.x, first.y)
  ⟨extrema.1, extrema.2.1, extrema.2.2.1 - extrema.1, extrema.2.2.2 - extrema.2.1⟩

def corners (r : Rect) : List Point := [⟨r.x, r.y⟩, ⟨r.x + r.w, r.y + r.h⟩]

def shiftPoint (dx dy : Int) (p : Point) : Point := ⟨p.x + dx, p.y + dy⟩
def shiftRect (dx dy : Int) (r : Rect) : Rect := ⟨r.x + dx, r.y + dy, r.w, r.h⟩

def textItem (t : Caption) : Primitive :=
  .text {
    rect := t.rect
    role := if t.kind = 0 then .title else .label
    size := if t.kind = 0 then 16 else 14
    align := t.align
    style := "text"
    lines := t.lines.map fun line => [⟨String.ofList line.text, false, false⟩] }

def seriesPaint (style : String) (index : Nat) : Paint :=
  { style, series := ⟨index % 12, Nat.mod_lt _ (by decide)⟩ }

def checkRange (values : List Int) : Except LayoutError Unit :=
  if values.all (fun v => decide (-I32_MAX ≤ v ∧ v ≤ I32_MAX)) then pure () else .error .overflow

structure Plan where
  c : Constants
  inp : Input
  (radius hi extent : Int)
  plot : Rect
  texts : List Caption
  curves : List (Nat × List Point)
  markers : List (Nat × Rect)
  allPoints : List Point
  enclosing : Rect

def plan (c : Constants) (inp : Input) (hi : Int) (texts : List Caption) : Plan :=
  let radius := Int.fdiv (min c.width c.height) 2
  let ticks := clamp inp.ticks 0 32000
  let rings := (List.range (Int.fdiv (ticks + 999) 1000).toNat).map fun (i : Nat) =>
    Int.fdiv (radius * ((i : Int) + 1) * 1000) ticks
  let extent := rings.foldl max radius
  let frame : Rect := ⟨-(Int.fdiv c.width 2 + c.margin), -(Int.fdiv c.height 2 + c.marginTop),
    2 * Int.fdiv c.width 2 + c.margin + c.marginRight,
    2 * Int.fdiv c.height 2 + c.marginTop + c.margin⟩
  let plot : Rect := ⟨-extent, -extent, 2 * extent, 2 * extent⟩
  let texts := texts.map (placeCaption inp c radius frame)
  let drawn := inp.curves.zipIdx.filter fun (curve, _) =>
    !inp.axes.isEmpty && hi > inp.minimum && curve.values.length == inp.axes.length
  let curves := drawn.map fun (curve, i) => (i, curvePoints inp.axes.length radius inp.minimum hi curve)
  let markers := if inp.showLegend && !inp.curves.isEmpty then
    inp.curves.zipIdx.map fun (_, i) =>
      let p := legendRow c i
      (i, (⟨p.x, p.y, c.marker, c.marker⟩ : Rect)) else []
  let allPoints := [⟨0, 0⟩] ++ corners frame ++ corners plot ++
    (texts.filter (·.shown)).flatMap (fun t => corners t.rect) ++
    curves.flatMap (fun (_, ps) => ps ++ if inp.circle then
      (smooth c.tension ps).flatMap (fun b => [b.1, b.2.1]) else []) ++
    markers.flatMap (fun (_, r) => corners r)
  {
    c, inp, radius, hi, extent, plot, texts, curves, markers, allPoints
    enclosing := bounds allPoints }

def Plan.scene (p : Plan) (m : Model) : Scene :=
  let c := p.c
  let inp := p.inp
  let dx := -p.enclosing.x
  let dy := -p.enclosing.y
  let pointAt := shiftPoint dx dy
  let rectAt := shiftRect dx dy
  let texts := p.texts.map fun t => { t with rect := if t.shown then rectAt t.rect else ⟨0, 0, 0, 0⟩ }
  let boxes : List Box := ⟨"plot", "node", rectAt p.plot, "", false⟩ ::
    p.curves.map fun (i, ps) => ⟨"c" ++ toString i, "node", rectAt (bounds ps), "plot", false⟩
  let labels : List SceneLabel := texts.map fun t =>
    {
      id := t.id, owner := "plot", text := t.text, rect := t.rect
      lines := if t.shown then t.lines.map (fun l => String.ofList l.text) else [] }
  let rule : Paint := { style := "rule" }
  let ticks := clamp inp.ticks 0 32000
  let rings := (List.range (Int.fdiv (ticks + 999) 1000).toNat).map fun (i : Nat) =>
    Int.fdiv (p.radius * ((i : Int) + 1) * 1000) ticks
  let ringItems : List Primitive := rings.filterMap fun r =>
    if r = 0 then none else if inp.circle then some (.ellipse dx dy r r rule)
    else
      let ps := (vertices inp.axes.length r).map pointAt
      if 3 ≤ ps.length then some (.polygon ps rule)
      else if ps.length = 2 then some (.polyline ps 0 rule) else none
  let under := ringItems ++ if p.radius = 0 then [] else
    (vertices inp.axes.length p.radius).map fun tip => .polyline [pointAt ⟨0, 0⟩, pointAt tip] 0 rule
  let underGroups : List Group := if under.isEmpty then [] else [⟨.decor, "", under⟩]
  let plotGroup : Group := ⟨.node, "plot", (texts.filter fun t => t.kind == 1 && t.shown).map textItem⟩
  let curveGroups : List Group := p.curves.map fun (i, ps) =>
    let commands : List PathCommand := [.M (pointAt (ps.headD ⟨0, 0⟩))] ++
      (if inp.circle then (smooth c.tension ps).map fun b => .C (pointAt b.1) (pointAt b.2.1) (pointAt b.2.2)
       else (ps.drop 1).map fun pt => .L (pointAt pt)) ++ [.Z]
    ⟨.node, "c" ++ toString i, [.path commands (seriesPaint "series-tint" i)]⟩
  let over := (texts.filter fun t => t.kind == 0 && t.shown).map textItem ++
    p.markers.map (fun (i, r) => .rect (rectAt r) (seriesPaint "series" i)) ++
    (texts.filter fun t => t.kind == 2 && t.shown).map textItem
  let overGroups : List Group := if over.isEmpty then [] else [⟨.decor, "", over⟩]
  {
    kind := m.kind, profile := .vector
    options := { m.options with profile := .vector, direction := .TB }
    canvas := ⟨p.enclosing.w, p.enclosing.h⟩, boxes, labels
    items := underGroups ++ [plotGroup] ++ curveGroups ++ overGroups }

def layout (m : Model) (inp : Input) : Except LayoutError Scene := do
  let c := constants m.options
  if c.width < 0 ∨ c.height < 0 then throw .domain
  let values := inp.curves.flatMap (·.values)
  let hi := inp.maximum.getD ((values.foldl (fun acc v => some (max (acc.getD v) v)) none).getD inp.minimum)
  checkRange (inp.minimum :: hi :: values)
  if I32_MAX < hi - inp.minimum then throw .overflow
  let texts ← captions inp
  let p := plan c inp hi texts
  let scene := p.scene m
  checkRange (p.enclosing.w :: p.enclosing.h :: (scene.boxes.flatMap fun b =>
    [b.rect.x, b.rect.y, b.rect.w, b.rect.h, b.rect.x + b.rect.w, b.rect.y + b.rect.h]))
  checkRange (p.allPoints.flatMap fun pt => [pt.x - p.enclosing.x, pt.y - p.enclosing.y])
  checkRange (scene.labels.flatMap fun l =>
    [l.rect.x, l.rect.y, l.rect.w, l.rect.h, l.rect.x + l.rect.w, l.rect.y + l.rect.h])
  return scene

end Elegant.Chart.Radar

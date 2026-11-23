import Elegant.Chart.XY

set_option autoImplicit false

namespace Elegant.Chart.Quadrant

structure InputPoint where
  x : Int
  y : Int
  radius : Int

structure Constants where
  width : Int
  height : Int
  padX : Int
  padY : Int
  titleBand : Int
  xBand : Int
  yBand : Int
  titlePad : Int
  titleFont : Int
  xPad : Int
  xFont : Int
  yPad : Int
  yFont : Int
  radiusX : Int
  radiusY : Int
  textPad : Int
  labelFont : Int
  pointFont : Int
  topPad : Int
  edge : Int

def config (o : Options) (key : String) (fallback : Int) : Int :=
  ((o.config.findSome? fun (k, v) => match v with
    | .integer n => if k == key then some n else none
    | _ => none)).getD fallback

def unitsX (p : Profile) (n : Int) : Int :=
  if p == .cell then Int.fdiv (n + 7) 8 else n * 64

def unitsY (p : Profile) (n : Int) : Int :=
  if p == .cell then Int.fdiv (n + 15) 16 else n * 64

def constants (m : Model) : Constants := Id.run do
  let p := m.profile
  let o := m.options
  let xp := config o "xAxisLabelPadding" (LayoutConst.quadrant_axis_label_padding_px.get p)
  let yp := config o "yAxisLabelPadding" (LayoutConst.quadrant_axis_label_padding_px.get p)
  let tp := config o "titlePadding" (LayoutConst.quadrant_title_padding_px.get p)
  let xf := config o "xAxisLabelFontSize" (LayoutConst.quadrant_axis_font_px.get p)
  let yf := config o "yAxisLabelFontSize" (LayoutConst.quadrant_axis_font_px.get p)
  let tf := config o "titleFontSize" (LayoutConst.quadrant_title_font_px.get p)
  let has (a b : String) := o.config.any fun kv => kv.1 == a || kv.1 == b
  return {
    width := unitsX p (config o "chartWidth" 500)
    height := unitsY p (config o "chartHeight" 500)
    padX := unitsX p (config o "quadrantPadding" 5)
    padY := unitsY p (config o "quadrantPadding" 5)
    titleBand := if has "titlePadding" "titleFontSize" then unitsY p (2 * tp + tf)
      else LayoutConst.quadrant_title_band.get p
    xBand := if has "xAxisLabelPadding" "xAxisLabelFontSize" then unitsY p (2 * xp + xf)
      else LayoutConst.quadrant_axis_band_y.get p
    yBand := if has "yAxisLabelPadding" "yAxisLabelFontSize" then unitsX p (2 * yp + yf)
      else LayoutConst.quadrant_axis_band_x.get p
    titlePad := unitsY p tp, titleFont := tf
    xPad := unitsY p xp, xFont := xf, yPad := unitsX p yp, yFont := yf
    radiusX := unitsX p (config o "pointRadius" 5)
    radiusY := if p == .cell && !(o.config.any fun kv => kv.1 == "pointRadius") then 1
      else unitsY p (config o "pointRadius" 5)
    textPad := unitsX p (config o "pointTextPadding" 5)
    labelFont := LayoutConst.quadrant_label_font_px.get p
    pointFont := LayoutConst.quadrant_point_font_px.get p
    topPad := LayoutConst.quadrant_text_top_pad.get p
    edge := if p == .cell then 1 else 0 }

def pointInputs (m : Model) : List InputPoint :=
  m.regionSets.filterMap fun s => match s.regions with
    | x :: y :: radius :: _ => some ⟨x, y, radius - 1⟩
    | _ => none

def labelKind (l : ModelLabel) : Nat :=
  if l.id == "title" then 0 else if l.id == "x.left" then 1
  else if l.id == "x.right" then 2 else if l.id == "y.bottom" then 3
  else if l.id == "y.top" then 4 else if l.id.startsWith "q" then 5 else 6

def labelIndex (l : ModelLabel) : Nat :=
  let id := String.ofList ((l.id.splitOn ".").headD "").toList.tail
  let n := id.toNat?.getD 0
  if labelKind l == 5 then n - 1 else n

def style (c : Constants) (l : ModelLabel) : Measure.Role × Int :=
  match labelKind l with
  | 0 => (.title, c.titleFont)
  | 1 | 2 => (.label, c.xFont)
  | 3 | 4 => (.label, c.yFont)
  | 5 => (.label, c.labelFont)
  | _ => (.body, c.pointFont)

def measure (m : Model) (c : Constants) (l : ModelLabel) (target : Int) :
    Except LayoutError XY.TextBox := do
  let (role, size) := style c l
  let metric ← XY.metricOf (fontFamily := m.options.fontFamily) (m.profile == .cell) role size
  let lines ← StyledMeasure.wrap metric (if 0 < target ∧ target < I32_MAX then target else I32_MAX) l.text.toList
  return ⟨lines, lines.foldl (fun w line => max w line.width) 0,
    (lines.length : Int) * XY.lineHeight (m.profile == .cell) role size⟩

structure Geometry where
  canvas : Size
  plot : Rect
  tiles : List Rect
  inner : List Rect
  centres : List Point
  radii : List Point
  pointBoxes : List Rect

def within (r outer : Rect) : Rect :=
  let x := max r.x outer.x
  let y := max r.y outer.y
  ⟨x, y, max (min (r.x + r.w) (outer.x + outer.w) - x) 0,
    max (min (r.y + r.h) (outer.y + outer.h) - y) 0⟩

def centre (plot : Rect) (edge : Int) (p : InputPoint) : Point :=
  let w := max (plot.w - 3 * edge) 0
  let h := max (plot.h - 3 * edge) 0
  ⟨plot.x + edge + Int.fdiv (p.x * w) 1000,
    plot.y + edge + h - Int.fdiv (p.y * h) 1000⟩

def tile (plot : Rect) (i : Nat) : Rect :=
  let w := Int.fdiv plot.w 2
  let h := Int.fdiv plot.h 2
  let right := i == 0 || i == 3
  let bottom := i == 2 || i == 3
  ⟨if right then plot.x + w else plot.x, if bottom then plot.y + h else plot.y,
    if right then plot.w - w else w, if bottom then plot.h - h else h⟩

def innerTile (c : Constants) (r : Rect) (i : Nat) : Rect :=
  ⟨r.x + c.edge, r.y + c.edge,
    max (r.w - c.edge - (if i == 0 || i == 3 then c.edge else 0)) 0,
    max (r.h - c.edge - (if i == 2 || i == 3 then c.edge else 0)) 0⟩

def measureKinds (m : Model) (c : Constants) (target : Int) (kinds : List Nat) :
    Except LayoutError (Int × Int × Bool) := do
  let ts ← (m.labels.filter fun l => kinds.contains (labelKind l)).mapM fun l => measure m c l target
  return (ts.foldl (fun w t => max w t.w) 0, ts.foldl (fun h t => max h t.h) 0, !ts.isEmpty)

def arrange (m : Model) (c : Constants) (points : List InputPoint) : Except LayoutError Geometry := do
  let (_, th, ht) ← measureKinds m c (c.width - 2 * c.padX) [0]
  let title := if ht then max (c.titleBand + th - XY.lineHeight (m.profile == .cell) .title c.titleFont)
    (c.titlePad + th) else 0
  let (lw, _, hl) ← measureKinds m c (max (Int.fdiv c.width 2 - 2 * c.yPad - 2 * c.padX) 1) [3, 4]
  let left := if hl then max c.yBand (lw + 2 * c.yPad) else 0
  let w := max (c.width - 2 * c.padX - left) 2
  let has (k : Nat) := m.labels.any fun l => labelKind l == k
  let target := if has 1 && has 2 then Int.fdiv w 2 else w
  let (_, bh, hb) ← measureKinds m c (max target 1) [1, 2]
  let bottom := if hb then max (c.xBand + bh - XY.lineHeight (m.profile == .cell) .label c.xFont)
    (c.xPad + bh) else 0
  let h := max (c.height - 2 * c.padY - title - bottom) 2
  let plot : Rect := ⟨c.padX + left, c.padY + title, w, h⟩
  let tiles := (List.range 4).map (tile plot)
  let centres := points.map (centre plot c.edge)
  let radii := points.map fun p => if p.radius == -1 then (⟨c.radiusX, c.radiusY⟩ : Point)
    else ⟨unitsX m.profile p.radius, unitsY m.profile p.radius⟩
  let pointBoxes := (centres.zip radii).map fun (p, r) =>
    if m.profile == .cell && r.x ≤ 1 && r.y ≤ 1 then (⟨p.x, p.y, 1, 1⟩ : Rect)
    else within ⟨p.x - r.x, p.y - r.y, 2 * r.x + c.edge, 2 * r.y + c.edge⟩ plot
  return ⟨⟨2 * c.padX + left + w, 2 * c.padY + title + h + bottom⟩,
    plot, tiles, tiles.zipIdx.map (fun (r, i) => innerTile c r i), centres, radii, pointBoxes⟩

structure Placement where
  label : ModelLabel
  box : XY.TextBox
  rect : Rect
  align : Align

def overlaps (r s : Rect) : Bool :=
  decide (0 < r.w ∧ 0 < r.h ∧ 0 < s.w ∧ 0 < s.h ∧ r.x < s.x + s.w ∧
    s.x < r.x + r.w ∧ r.y < s.y + s.h ∧ s.y < r.y + r.h)

def inside (r outer : Rect) : Bool :=
  decide (outer.x ≤ r.x ∧ r.x + r.w ≤ outer.x + outer.w ∧
    outer.y ≤ r.y ∧ r.y + r.h ≤ outer.y + outer.h)

def spread (n : Int) : List Int :=
  0 :: (List.range n.toNat).flatMap fun (i : Nat) => [(Int.ofNat i) + 1, -((Int.ofNat i) + 1)]

def fit (outer r : Rect) : Rect :=
  { r with
    x := clamp r.x outer.x (max (outer.x + outer.w - r.w) outer.x)
    y := clamp r.y outer.y (max (outer.y + outer.h - r.h) outer.y) }

def free (c : Constants) (g : Geometry) (taken : List Rect) (r : Rect) : Bool :=
  inside r ⟨g.plot.x + c.edge, g.plot.y + c.edge,
    max (g.plot.w - 2 * c.edge) 0, max (g.plot.h - 2 * c.edge) 0⟩ &&
    !(taken.any (overlaps r))

def search (m : Model) (c : Constants) (g : Geometry) (taken : List Rect)
    (candidates : List (Rect × Align)) : (Rect × Align) × Bool :=
  let first := candidates.headD (⟨0, 0, 0, 0⟩, .start)
  if m.profile != .cell then (first, true)
  else match candidates.find? (fun p => free c g taken p.1) with
    | some p => (p, true)
    | none => (first, false)

def pointCandidates (m : Model) (c : Constants) (g : Geometry) (p r : Point)
    (t : XY.TextBox) : List (Rect × Align) :=
  let right := p.x + r.x + c.textPad
  let top := p.y - Int.fdiv t.h 2
  if m.profile != .cell then [(fit g.plot ⟨right, top, t.w, t.h⟩, .start)]
  else
    let left := p.x - (r.x + c.textPad - 1) - t.w
    let col := g.inner.getD (if p.x ≥ (g.tiles.getD 0 g.plot).x then 0 else 1) g.plot
    let x := clamp (p.x - Int.fdiv t.w 2) col.x (max (col.x + col.w - t.w) col.x)
    let offsets := spread g.plot.h
    (offsets.flatMap fun dy => [(⟨right, top + dy, t.w, t.h⟩, .start),
      (⟨left, top + dy, t.w, t.h⟩, .«end»)]) ++
    offsets.map (fun dy => (⟨x, top + dy, t.w, t.h⟩, .middle))

def placeLabel (m : Model) (c : Constants) (g : Geometry) (taken : List Rect)
    (l : ModelLabel) : Except LayoutError Placement := do
  let k := labelKind l
  let has (n : Nat) := m.labels.any fun a => labelKind a == n
  let pl := g.plot
  let canvas : Rect := ⟨0, 0, g.canvas.w, g.canvas.h⟩
  let idx := labelIndex l
  if k == 5 then
    let r := g.inner.getD idx pl
    let t ← measure m c l (max (r.w - 2 * c.padX) 1)
    let x := r.x + max (Int.fdiv (r.w - t.w) 2) 0
    let y := r.y + (if g.centres.isEmpty then max (Int.fdiv (r.h - t.h) 2) 0 else c.topPad)
    let (candidate, _) := search m c g taken ((spread r.h).map fun dy => (⟨x, y + dy, t.w, t.h⟩, .middle))
    return ⟨l, t, candidate.1, candidate.2⟩
  else if k == 6 then
    let p := g.centres.getD idx ⟨0, 0⟩
    let r := g.radii.getD idx ⟨0, 0⟩
    let t ← measure m c l 0
    let (candidate, found) := search m c g taken (pointCandidates m c g p r t)
    if found then return ⟨l, t, candidate.1, candidate.2⟩
    let col := g.inner.getD (if p.x ≥ (g.tiles.getD 0 pl).x then 0 else 1) pl
    let t ← measure m c l (max col.w 2)
    let (candidate, _) := search m c g taken (pointCandidates m c g p r t)
    return ⟨l, t, candidate.1, candidate.2⟩
  else
    let target := if k == 0 then c.width - 2 * c.padX
      else if k == 1 || k == 2 then max (if has 1 && has 2 then Int.fdiv pl.w 2 else pl.w) 1
      else max (Int.fdiv c.width 2 - 2 * c.yPad - 2 * c.padX) 1
    let t ← measure m c l target
    let (r, align) := if k == 0 then
        (fit canvas ⟨Int.fdiv (g.canvas.w - t.w) 2, c.titlePad, t.w, t.h⟩, Align.middle)
      else if k == 1 || k == 2 then
        let y := pl.y + pl.h + c.xPad
        if !(has 1 && has 2) then (fit canvas ⟨pl.x, y, t.w, t.h⟩, Align.start)
        else
          let lw := Int.fdiv pl.w 2
          let x := if k == 2 then pl.x + lw + Int.fdiv (pl.w - lw) 2 else pl.x + Int.fdiv lw 2
          (fit canvas ⟨x - Int.fdiv t.w 2, y, t.w, t.h⟩, Align.middle)
      else
        let y := if has 3 && has 4 then
            if k == 3 then pl.y + pl.h - Int.fdiv pl.h 4 - Int.fdiv t.h 2
            else pl.y + Int.fdiv pl.h 4 - Int.fdiv t.h 2
          else if k == 3 then pl.y + pl.h - t.h else pl.y
        (fit canvas ⟨pl.x - c.yPad - t.w, y, t.w, t.h⟩, Align.«end»)
    return ⟨l, t, r, align⟩

def place (m : Model) (c : Constants) (g : Geometry) : Except LayoutError (List Placement) := do
  let obstacles := if m.profile == .cell then
    [⟨(g.tiles.getD 0 g.plot).x, g.plot.y, 1, g.plot.h⟩,
      ⟨g.plot.x, (g.tiles.getD 2 g.plot).y, g.plot.w, 1⟩] ++ g.pointBoxes else []
  let ordered := (m.labels.filter fun l => labelKind l < 5) ++
    (m.labels.filter fun l => labelKind l == 5) ++ (m.labels.filter fun l => labelKind l == 6)
  let out ← ordered.foldlM (fun (out : List Placement) l => do
    let item ← placeLabel m c g (obstacles ++ out.map (·.rect)) l
    return out ++ [item]) []
  return m.labels.filterMap fun l => out.find? (fun p => p.label.id == l.id)

def textPrimitive (c : Constants) (p : Placement) : Primitive :=
  let (role, size) := style c p.label
  .text {
    rect := p.rect
    role := XY.textRoleOf role
    size := size
    align := p.align
    style := if 1 ≤ labelKind p.label ∧ labelKind p.label ≤ 4 then "text-muted" else "text"
    lines := XY.runsOf p.box.lines }

def tileIndexOf (id : String) : Option Nat :=
  if id == "q1" then some 0 else if id == "q2" then some 1
  else if id == "q3" then some 2 else if id == "q4" then some 3 else none

def pointIndexOf (id : String) : Option Nat :=
  match id.toList with
  | 'p' :: rest =>
    match (String.ofList rest).toNat? with
    | some n => if id == "p" ++ toString n then some n else none
    | none => none
  | _ => none

def boxRectFor (g : Geometry) (id : String) : Rect :=
  if id = "plot" then g.plot
  else match tileIndexOf id with
    | some i => g.tiles.getD i g.plot
    | none =>
      match pointIndexOf id with
      | some i => g.pointBoxes.getD i g.plot
      | none => g.plot

theorem boxRectFor_plot (g : Geometry) : boxRectFor g "plot" = g.plot := by
  simp [boxRectFor]

def shapesFor (g : Geometry) (c : Constants) (id : String) : List Primitive :=
  if id = "plot" then
    let pl := g.plot
    let x := (g.tiles.getD 0 pl).x
    let y := (g.tiles.getD 2 pl).y
    [.rect pl { style := "rule", width := .emphasis },
      .polyline [⟨x, pl.y⟩, ⟨x, pl.y + pl.h - c.edge⟩] 0 { style := "rule" },
      .polyline [⟨pl.x, y⟩, ⟨pl.x + pl.w - c.edge, y⟩] 0 { style := "rule" }]
  else match pointIndexOf id with
    | some i =>
      let p := g.centres.getD i ⟨0, 0⟩
      let r := g.radii.getD i ⟨0, 0⟩
      if 0 < r.x ∧ 0 < r.y then [.ellipse p.x p.y r.x r.y { style := "series" }] else []
    | none => []

def sceneOf (m : Model) (c : Constants) (g : Geometry) (ps : List Placement) : Scene :=
  let texts (owner : String) := (ps.filter fun p => p.label.owner == owner).map (textPrimitive c)
  let groups := m.boxes.map fun b =>
    ({ role := .node, owner := b.id, items := shapesFor g c b.id ++ texts b.id } : Group)
  { kind := m.kind, profile := m.profile, options := { m.options with direction := .TB },
    canvas := g.canvas,
    boxes := m.boxes.map fun b => ⟨b.id, b.role.id, boxRectFor g b.id, b.parent, b.exclusive⟩,
    labels := ps.map fun p => {
      id := p.label.id
      owner := p.label.owner
      text := p.label.text
      rect := p.rect
      lines := p.box.lines.map fun l => String.ofList l.text },
    items := { role := .decor, owner := "", items := g.tiles.map fun r => .rect r { style := "band" } } :: groups }

def layout (m : Model) : Except LayoutError Scene := do
  let c := constants m
  let points := pointInputs m
  if !(points.all fun p => decide (0 ≤ p.x ∧ p.x ≤ 1000 ∧ 0 ≤ p.y ∧ p.y ≤ 1000 ∧ -1 ≤ p.radius)) then throw .domain
  let g ← arrange m c points
  let ps ← place m c g
  let s := sceneOf m c g ps
  let rects := s.boxes.map (·.rect) ++ s.labels.map (·.rect)
  XY.checkMagnitude ([g.canvas.w, g.canvas.h] ++ rects.flatMap fun r => [r.x, r.y, r.w, r.h])
  return s

end Elegant.Chart.Quadrant

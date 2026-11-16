import Elegant.Gen.Markers
import Elegant.Gen.Styles
import Elegant.Text.Braille
import Elegant.Text.Place

set_option autoImplicit false

/-! Render of the text back end (`spec/render-cells.md`, requirements render-cells-01,
render-cells-07, render-cells-26 to render-cells-37, render-cells-62 to render-cells-67, and
render-cells-95 to render-cells-96).

A cell scene is drawn primitive by primitive in scene order; labels are placed afterwards in
declaration order; the canvas is serialised row by row. Colour is outside the Lean renderer.
The output is the text and the number of label clusters that could not be written. -/

namespace Elegant.Text

/-- `g'` follows `g` by drawing: the size is kept, every changed cell is on the canvas, and no
label changes. -/
def Canvas.Drawn (g g' : Canvas) : Prop :=
  g.Confined g' ∧ ∀ c r, (g'.cellAt c r).label = (g.cellAt c r).label

theorem drawn_refl (g : Canvas) : g.Drawn g :=
  ⟨confined_refl g, fun _ _ => rfl⟩

theorem drawn_trans {g g' g'' : Canvas} (h : g.Drawn g') (h' : g'.Drawn g'') : g.Drawn g'' :=
  ⟨confined_trans h.1 h'.1, fun c r => (h'.2 c r).trans (h.2 c r)⟩

theorem put_drawn (g : Canvas) (c r : Int) (f : Cell → Cell)
    (hf : ∀ v, (f v).label = v.label) : g.Drawn (g.put c r f) := by
  refine ⟨put_confined g c r f, fun c' r' => ?_⟩
  rw [cellAt_put]
  by_cases e : g.Inside c r ∧ c' = c ∧ r' = r
  · simp only [e]
    exact hf _
  · simp only [e, ↓reduceIte]

theorem foldl_drawn {α : Type} (step : Canvas → α → Canvas)
    (hstep : ∀ (g : Canvas) (a : α), g.Drawn (step g a)) :
    ∀ (l : List α) (g : Canvas), g.Drawn (l.foldl step g) := by
  intro l
  induction l with
  | nil => intro g; exact drawn_refl g
  | cons a l ih => intro g; exact drawn_trans (hstep g a) (ih (step g a))

theorem attach_drawn (g : Canvas) (c r : Int) (mask style : Nat) :
    g.Drawn (g.attach c r mask style) :=
  put_drawn g c r _ fun _ => rfl

theorem hSegment_drawn (g : Canvas) (x0 x1 y : Int) (style : Nat) :
    g.Drawn (g.hSegment x0 x1 y style) :=
  foldl_drawn _ (fun g _ => drawn_trans (attach_drawn g _ _ _ _) (attach_drawn _ _ _ _ _)) _ g

theorem vSegment_drawn (g : Canvas) (x y0 y1 : Int) (style : Nat) :
    g.Drawn (g.vSegment x y0 y1 style) :=
  foldl_drawn _ (fun g _ => drawn_trans (attach_drawn g _ _ _ _) (attach_drawn _ _ _ _ _)) _ g

theorem segment_drawn (g : Canvas) (a b : Int × Int) (style : Nat) :
    g.Drawn (g.segment a b style) := by
  unfold Canvas.segment
  split
  · exact hSegment_drawn g _ _ _ _
  · split
    · exact vSegment_drawn g _ _ _ _
    · exact drawn_refl g

theorem polyline_drawn (g : Canvas) (pts : List (Int × Int)) (style : Nat) :
    g.Drawn (g.polyline pts style) :=
  foldl_drawn (fun (g : Canvas) (e : (Int × Int) × (Int × Int)) => g.segment e.1 e.2 style)
    (fun g e => segment_drawn g e.1 e.2 style) _ g

theorem putSymbol_drawn (g : Canvas) (c r : Int) (s : Nat) : g.Drawn (g.putSymbol c r s) :=
  put_drawn g c r _ fun _ => rfl

namespace Render

/-- The `cell` column of the style row of a paint: 0 draws nothing, 1 strokes, 2 fills. A style
without a row strokes. -/
def paintCell (p : Paint) : Nat :=
  ((styles.find? fun s => s.name == p.style).map fun s => s.cell).getD 1

/-- The line style of an item: double, then dotted or dashed, then emphasis, then the base. -/
def lineStyle (p : Paint) (base : Nat) : Nat :=
  if p.line = .double then styleDouble
  else if p.line = .dashed ∨ p.line = .dotted then styleDotted
  else if p.width = .emphasis then styleHeavy
  else base

/-- Set the symbol of one cell to the glyph of a named symbol. A missing name sets nothing. -/
def symbolAt (charset : Charset) (g : Canvas) (pos : Point) (name : String) : Canvas :=
  g.putSymbol pos.x pos.y ((Join.symbol charset name).getD 0)

/-- The position of an axis in the glyph lists of a marker. -/
def axisIndex : MarkerAxis → Nat
  | .positiveX => 0
  | .negativeX => 1
  | .positiveY => 2
  | .negativeY => 3

/-- The glyph of a marker for an axis in a charset, when the marker has one. -/
def markerGlyph (charset : Charset) (name : String) (axis : MarkerAxis) : Option Nat :=
  (markers.find? fun m => m.name == name).bind fun m =>
    (if charset = .ascii then m.ascii else m.cell)[axisIndex axis]?

/-- A marker replaces the symbol of the cell at its end point by its direction glyph. -/
def drawMarker (charset : Charset) (g : Canvas) (name : String) (pos : Point)
    (axis : MarkerAxis) : Canvas :=
  match markerGlyph charset name axis with
  | some glyph => g.putSymbol pos.x pos.y glyph
  | none => g

/-- A point as the pair that the canvas segments read. -/
def pointPair (p : Point) : Int × Int := (p.x, p.y)

/-- A pair as a point. -/
def pairPoint (d : Braille.Dot) : Point := ⟨d.1, d.2⟩

/-- Set the braille dot of a dot position. -/
def putDot (g : Canvas) (d : Braille.Dot) : Canvas :=
  g.put (Int.fdiv d.1 2) (Int.fdiv d.2 4) fun v =>
    { v with dots := v.dots ||| Braille.bit d.1 d.2 }

/-- Stroke the polyline through the dot positions. -/
def dotLines (g : Canvas) (ds : List Braille.Dot) : Except LayoutError Canvas :=
  match Braille.strokeDots ds with
  | .ok dots => .ok (dots.foldl putDot g)
  | .error e => .error e

/-- The closed loop through the dots: the first dot is appended. -/
def closeLoop (ds : List Braille.Dot) : List Braille.Dot :=
  match ds with
  | [] => []
  | d :: _ => ds ++ [d]

/-- The four sides of a rectangle that is at least two cells wide and high. -/
def sides (g : Canvas) (r : Rect) (style : Nat) : Canvas :=
  let x1 := r.x + r.w - 1
  let y1 := r.y + r.h - 1
  (((g.segment (r.x, r.y) (x1, r.y) style).segment (r.x, y1) (x1, y1) style).segment
    (r.x, r.y) (r.x, y1) style).segment (x1, r.y) (x1, y1) style

/-- Every cell of a rectangle holds the eight dots. -/
def fillCells (g : Canvas) (r : Rect) : Canvas :=
  (List.range r.h.toNat).foldl
    (fun g (j : Nat) => (List.range r.w.toNat).foldl
      (fun g (i : Nat) =>
        g.put (r.x + (i : Int)) (r.y + (j : Int)) fun v => { v with dots := 255 }) g)
    g

/-- A rectangle one cell thick: dots when filled, a hollow symbol when one cell, else one
segment along its longer side. -/
def thinRect (charset : Charset) (g : Canvas) (r : Rect) (p : Paint) : Canvas :=
  if paintCell p = 2 then fillCells g r
  else if r.w = 1 ∧ r.h = 1 then symbolAt charset g ⟨r.x, r.y⟩ "box-hollow"
  else g.segment (r.x, r.y) (r.x + r.w - 1, r.y + r.h - 1) (lineStyle p styleLight)

/-- A rectangle or rounded rectangle; the base style is light or rounded. -/
def drawRectangle (charset : Charset) (g : Canvas) (r : Rect) (p : Paint) (base : Nat) :
    Except LayoutError Canvas :=
  match Braille.checkedPoint (r.x + r.w) (r.y + r.h) with
  | .error e => .error e
  | .ok _ =>
    if paintCell p = 0 ∨ r.w ≤ 0 ∨ r.h ≤ 0 then .ok g
    else if min r.w r.h = 1 then .ok (thinRect charset g r p)
    else .ok (sides g r (lineStyle p base))

/-- A polyline: orthogonal segments with their line style, or, when one segment is sloped, the
whole polyline as braille dots. -/
def drawPolyline (g : Canvas) (pts : List Point) (p : Paint) : Except LayoutError Canvas :=
  if paintCell p = 0 then .ok g
  else if Polyline.isOrthogonal pts then
    .ok (g.polyline (pts.map pointPair) (lineStyle p styleLight))
  else
    match pts.mapM Braille.cellDot with
    | .ok ds => dotLines g ds
    | .error e => .error e

/-- A polygon: one symbol when its extent is at most one cell, else its closed outline as
dots. -/
def drawPolygon (charset : Charset) (g : Canvas) (pts : List Point) (p : Paint) :
    Except LayoutError Canvas :=
  match Braille.bounds pts with
  | none => .ok g
  | some (x0, x1, y0, y1) =>
    if paintCell p = 0 then .ok g
    else if x1 - x0 ≤ 1 ∧ y1 - y0 ≤ 1 then
      .ok (symbolAt charset g ⟨x0, y0⟩ (if paintCell p = 2 then "diamond" else "diamond-hollow"))
    else
      match pts.mapM Braille.cellDot with
      | .ok ds => dotLines g (closeLoop ds)
      | .error e => .error e

/-- An ellipse: one symbol when both radii are at most 1, else its 64-gon in dot space. -/
def drawEllipse (charset : Charset) (g : Canvas) (cx cy rx ry : Int) (p : Paint) :
    Except LayoutError Canvas :=
  if paintCell p = 0 then .ok g
  else if rx ≤ 1 ∧ ry ≤ 1 then
    .ok (symbolAt charset g ⟨cx, cy⟩ (if paintCell p = 2 then "disc" else "ring"))
  else
    match Braille.cellDot ⟨cx, cy⟩ with
    | .error e => .error e
    | .ok center =>
      match Braille.checkedPoint (2 * rx) (4 * ry) with
      | .error e => .error e
      | .ok radii =>
        match Braille.ellipse (pairPoint center) radii.x radii.y with
        | .ok ps => dotLines g (closeLoop (ps.map pointPair))
        | .error e => .error e

/-- The canvas, the current dot, and the dot where the last subpath started. -/
abbrev PathState := Canvas × Braille.Dot × Braille.Dot

/-- Stroke the polyline through the dots, then continue with the given current and start dots. -/
def strokeThen (g : Canvas) (ds : List Braille.Dot) (current start : Braille.Dot) :
    Except LayoutError PathState :=
  match dotLines g ds with
  | .ok g' => .ok (g', current, start)
  | .error e => .error e

/-- Draw one path command in dot space. -/
def pathStep (st : PathState) (cmd : PathCommand) : Except LayoutError PathState :=
  match cmd with
  | .M p =>
    match Braille.cellDot p with
    | .ok d => .ok (st.1, d, d)
    | .error e => .error e
  | .L p =>
    match Braille.cellDot p with
    | .ok d => strokeThen st.1 [st.2.1, d] d st.2.2
    | .error e => .error e
  | .Z => strokeThen st.1 [st.2.1, st.2.2] st.2.2 st.2.2
  | .C c1 c2 p =>
    match Braille.cellDot c1 with
    | .error e => .error e
    | .ok a =>
      match Braille.cellDot c2 with
      | .error e => .error e
      | .ok b =>
        match Braille.cellDot p with
        | .error e => .error e
        | .ok d =>
          match Braille.cubic (pairPoint st.2.1) (pairPoint a) (pairPoint b) (pairPoint d) with
          | .ok ps => strokeThen st.1 (ps.map pointPair) d st.2.2
          | .error e => .error e
  | .A center radius a0 sweep =>
    match Braille.cellDot center with
    | .error e => .error e
    | .ok c =>
      match Braille.checkedPoint (2 * radius) 0 with
      | .error e => .error e
      | .ok rr =>
        match Braille.arc (pairPoint c) rr.x a0 sweep with
        | .ok ps =>
          strokeThen st.1 (ps.map pointPair) ((ps.getLast?.map pointPair).getD st.2.1) st.2.2
        | .error e => .error e

/-- A path: every command in dot space, starting from the dot `(0, 0)`. -/
def drawPath (g : Canvas) (cmds : List PathCommand) (p : Paint) : Except LayoutError Canvas :=
  if paintCell p = 0 then .ok g
  else
    match cmds.foldlM pathStep (g, (0, 0), (0, 0)) with
    | .ok st => .ok st.1
    | .error e => .error e

/-- Draw one primitive. A text draws nothing: labels are placed after every primitive. -/
def drawPrimitive (charset : Charset) (g : Canvas) : Primitive → Except LayoutError Canvas
  | .rect r p => drawRectangle charset g r p styleLight
  | .roundRect r _ p => drawRectangle charset g r p styleRounded
  | .ellipse cx cy rx ry p => drawEllipse charset g cx cy rx ry p
  | .polygon pts p => drawPolygon charset g pts p
  | .polyline pts _ p => drawPolyline g pts p
  | .path cmds p => drawPath g cmds p
  | .text _ => .ok g
  | .markerRef name pos axis => .ok (drawMarker charset g name pos axis)
  | .symbolRef name pos _ => .ok (symbolAt charset g pos name)

/-- Draw the primitives in order. -/
def drawAll (charset : Charset) (g : Canvas) (ps : List Primitive) : Except LayoutError Canvas :=
  ps.foldlM (drawPrimitive charset) g


/-- The primitives of a scene in scene order: the groups in order, each group's items in
order. -/
def scenePrimitives (s : Scene) : List Primitive :=
  s.items.flatMap (·.items)

/-- The labels of a scene in declaration order. -/
def sceneLabels (s : Scene) : List SceneText :=
  (scenePrimitives s).filterMap fun
    | .text t => some t
    | _ => none

/-- The blank canvas of the scene extent; a negative extent is a domain error. -/
def sceneCanvas (s : Scene) : Except LayoutError Canvas :=
  if 0 ≤ s.canvas.w ∧ 0 ≤ s.canvas.h then .ok (Canvas.new s.canvas.w.toNat s.canvas.h.toNat)
  else .error .domain

/-- The drawn canvas of a cell scene, before the labels are placed. -/
def drawCanvas (s : Scene) (charset : Charset) : Except LayoutError Canvas :=
  match sceneCanvas s with
  | .ok g => drawAll charset g (scenePrimitives s)
  | .error e => .error e

def vectorStroke (g : Canvas) (pts : List Point) : Except LayoutError Canvas := do
  let dots ← Braille.stroke pts
  return dots.foldl putDot g

def vectorFilled (p : Paint) : Bool :=
  ((styles.find? fun s => s.name == p.style).map
    fun s => s.cell == 2 && s.fill != "none").getD false

def vectorStroked (p : Paint) : Bool :=
  ((styles.find? fun s => s.name == p.style).map
    fun s => s.cell != 0 && s.stroke != "none").getD true

def vectorFill (g : Canvas) (rings : List (List Point)) : Except LayoutError Canvas :=
  (List.range (4 * g.H)).foldlM (fun g (j : Nat) =>
    (List.range (2 * g.W)).foldlM (fun g (i : Nat) => do
      let d : Braille.Dot := ((i : Int), (j : Int))
      let sample := Braille.sample d
      let inside ← rings.foldlM (fun parity ring => do
        let hit ← Braille.polygonInside ring sample.1 sample.2
        return bne parity hit) false
      return if inside then putDot g d else g) g) g

def vectorRings (g : Canvas) (rings : List (List Point)) (p : Paint)
    (closed : Bool := true) : Except LayoutError Canvas := do
  let g ← if vectorFilled p then vectorFill g rings else pure g
  if vectorStroked p then
    rings.foldlM (fun g ps => vectorStroke g
      (if closed then (closeLoop (ps.map pointPair)).map pairPoint else ps)) g
  else pure g

structure VectorPath where
  paths : List (List Point × Bool) := []
  current : Point := ⟨0, 0⟩
  start : Point := ⟨0, 0⟩

def vectorExtend (st : VectorPath) (ps : List Point) : VectorPath :=
  let paths := match st.paths.reverse with
    | [] => [(ps, false)]
    | (last, closed) :: rest => rest.reverse ++ [(last ++ ps, closed)]
  { st with paths := paths, current := ps.getLast?.getD st.current }

def vectorPathStep (st : VectorPath) (cmd : PathCommand) :
    Except LayoutError VectorPath := do
  match cmd with
  | .M p => return { st with paths := st.paths ++ [([p], false)], current := p, start := p }
  | .L p => return vectorExtend st [p]
  | .C a b p =>
    let ps ← Braille.cubic st.current a b p
    return vectorExtend st (ps.drop 1)
  | .A c r a sweep =>
    let ps ← Braille.arc c r a sweep
    return vectorExtend st ps
  | .Z =>
    let paths := match st.paths.reverse with
      | [] => []
      | (ps, _) :: rest => rest.reverse ++ [(ps, true)]
    return { st with paths := paths, current := st.start }

def vectorMarker (g : Canvas) (name : String) (pos : Point) (axis : MarkerAxis) :
    Except LayoutError Canvas := do
  match markers.find? (fun m => m.name == name) with
  | none => return g
  | some m =>
    let ps ← m.points.mapM fun v =>
      let x := v.1 - m.ref.1
      let y := v.2 - m.ref.2
      let q := match axis with
        | .positiveX => (x, y)
        | .negativeX => (-x, -y)
        | .positiveY => (-y, x)
        | .negativeY => (y, -x)
      Braille.checkedPoint (pos.x + q.1) (pos.y + q.2)
    let starts := 0 :: m.breaks
    let parts := starts.zip (m.breaks ++ [ps.length])
    let rings := parts.map fun (a, b) => (ps.drop a).take (b - a)
    vectorRings g rings
      { style := if m.paint = "filled" then "mark" else if m.paint = "hollow" then
          "mark-hollow" else "edge" } (m.paint != "open")

def drawVectorPrimitive (g : Canvas) : Primitive → Except LayoutError Canvas
  | .rect r p | .roundRect r _ p => do
    let far ← Braille.checkedPoint (r.x + r.w) (r.y + r.h)
    vectorRings g [[⟨r.x, r.y⟩, ⟨far.x, r.y⟩, far, ⟨r.x, far.y⟩]] p
  | .ellipse cx cy rx ry p => do
    if rx < 0 ∨ ry < 0 then return g
    let ps ← Braille.ellipse ⟨cx, cy⟩ rx ry
    vectorRings g [ps] p
  | .polygon ps p => vectorRings g [ps] p
  | .polyline ps _ p => if vectorStroked p then vectorStroke g ps else .ok g
  | .path cmds p => do
    let st ← cmds.foldlM vectorPathStep {}
    let g ← if vectorFilled p then vectorFill g (st.paths.map (·.1)) else pure g
    if vectorStroked p then
      st.paths.foldlM (fun g (ps, closed) =>
        vectorStroke g (if closed then
          (closeLoop (ps.map pointPair)).map pairPoint else ps)) g
    else pure g
  | .markerRef name pos axis => vectorMarker g name pos axis
  | .symbolRef _ _ _ => .error .domain
  | .text _ => .ok g

def vectorLabels (ts : List SceneText) : List SceneText :=
  ts.flatMap fun t =>
    t.lines.zipIdx |>.map fun (line, k) =>
      let x := Int.fdiv t.rect.x 512
      let w := Int.fdiv (t.rect.x + t.rect.w + 511) 512 - x
      let lh := if t.role = .title then 1536 else 1280
      let rect : Rect := ⟨x, Int.fdiv (t.rect.y + (k : Int) * lh) 1024, w, 1⟩
      { t with rect := rect, lines := [line] }

def renderVectorCanvas (s : Scene) : Except LayoutError (Canvas × Nat) := do
  if s.canvas.w < 0 ∨ s.canvas.h < 0 then throw .domain
  let g := Canvas.new (Int.fdiv (s.canvas.w + 511) 512).toNat
    (Int.fdiv (s.canvas.h + 1023) 1024).toNat
  let g ← (scenePrimitives s).foldlM drawVectorPrimitive g
  return Place.placeAll g (vectorLabels (sceneLabels s))

/-- Draw the supplied geometry without clamping it. Canvas writes clip individually;
drawing errors retain their checked-error precedence before label placement. -/
def renderCanvas (s : Scene) (charset : Charset) : Except LayoutError (Canvas × Nat) :=
  if s.profile = .cell then
    match drawCanvas s charset with
    | .ok g => .ok (Place.placeAll g (sceneLabels s))
    | .error e => .error e
  else renderVectorCanvas s

/-- The renderer depends only on its display list, profile, and canvas, never on canonical
relations, ownership metadata, or layout options. -/
theorem renderCanvas_eq_of_inputs (s t : Scene) (charset : Charset)
    (hi : s.items = t.items) (hp : s.profile = t.profile) (hc : s.canvas = t.canvas) :
    renderCanvas s charset = renderCanvas t charset := by
  simp only [renderCanvas, drawCanvas, sceneCanvas, scenePrimitives, sceneLabels,
    renderVectorCanvas, hi, hp, hc]

/-- The text of one cell: nothing for a continuation, the cluster of a label, the symbol, the
arm glyph, or the braille glyph, which is a space for a blank cell. -/
def cellText (charset : Charset) (v : Cell) : String :=
  match v.label with
  | .cont => ""
  | .cluster text _ => Place.terminalText text
  | .empty =>
    String.singleton (Place.terminalChar (Char.ofNat
      (if v.symbol ≠ 0 then v.symbol
       else if v.mask ≠ 0 then Join.glyph charset v.style v.mask
       else Braille.glyph charset v.dots)))

/-- The cell texts of one row. -/
def rowTexts (charset : Charset) (g : Canvas) (r : Nat) : List String :=
  (List.range g.W).map fun (c : Nat) => cellText charset (g.cellAt (c : Int) (r : Int))

/-- Drop the trailing single-space texts. -/
def trimTrailing (ts : List String) : List String :=
  (ts.reverse.dropWhile fun t => t == " ").reverse

/-- One row: its texts without trailing spaces, then a line feed. -/
def rowText (charset : Charset) (g : Canvas) (r : Nat) : String :=
  String.join (trimTrailing (rowTexts charset g r)) ++ "\n"

/-- The rows of a canvas. A canvas with no rows is the empty string. -/
def serialise (charset : Charset) (g : Canvas) : String :=
  String.join ((List.range g.H).map (rowText charset g))

end Render

/-- Render a cell scene as text in a charset, with the number of label clusters that could not
be written. -/
def render (s : Scene) (charset : Charset) : Except LayoutError (String × Nat) :=
  match Render.renderCanvas s charset with
  | .ok (g, n) => .ok (Render.serialise charset g, n)
  | .error e => .error e

namespace Render

theorem symbolAt_drawn (charset : Charset) (g : Canvas) (pos : Point) (name : String) :
    g.Drawn (symbolAt charset g pos name) :=
  putSymbol_drawn g _ _ _

theorem drawMarker_drawn (charset : Charset) (g : Canvas) (name : String) (pos : Point)
    (axis : MarkerAxis) : g.Drawn (drawMarker charset g name pos axis) := by
  unfold drawMarker
  split
  · exact putSymbol_drawn g _ _ _
  · exact drawn_refl g

theorem putDot_drawn (g : Canvas) (d : Braille.Dot) : g.Drawn (putDot g d) :=
  put_drawn g _ _ _ fun _ => rfl

theorem sides_drawn (g : Canvas) (r : Rect) (style : Nat) : g.Drawn (sides g r style) :=
  drawn_trans (drawn_trans (drawn_trans (segment_drawn g _ _ _) (segment_drawn _ _ _ _))
    (segment_drawn _ _ _ _)) (segment_drawn _ _ _ _)

theorem fillCells_drawn (g : Canvas) (r : Rect) : g.Drawn (fillCells g r) := by
  unfold fillCells
  refine foldl_drawn _ (fun g _ => ?_) _ g
  refine foldl_drawn _ (fun g _ => ?_) _ g
  exact put_drawn g _ _ _ (fun _ => rfl)

theorem thinRect_drawn (charset : Charset) (g : Canvas) (r : Rect) (p : Paint) :
    g.Drawn (thinRect charset g r p) := by
  unfold thinRect
  split
  · exact fillCells_drawn g r
  · split
    · exact symbolAt_drawn charset g _ _
    · exact segment_drawn g _ _ _

theorem dotLines_drawn {g g' : Canvas} {ds : List Braille.Dot}
    (h : dotLines g ds = .ok g') : g.Drawn g' := by
  unfold dotLines at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact foldl_drawn putDot putDot_drawn _ g
  · simp at h

theorem drawRectangle_drawn {charset : Charset} {g g' : Canvas} {r : Rect} {p : Paint}
    {base : Nat} (h : drawRectangle charset g r p base = .ok g') : g.Drawn g' := by
  unfold drawRectangle at h
  split at h
  · simp at h
  · split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact drawn_refl g
    · split at h
      · simp only [Except.ok.injEq] at h
        subst h
        exact thinRect_drawn charset g r p
      · simp only [Except.ok.injEq] at h
        subst h
        exact sides_drawn g r _

theorem drawPolyline_drawn {g g' : Canvas} {pts : List Point} {p : Paint}
    (h : drawPolyline g pts p = .ok g') : g.Drawn g' := by
  unfold drawPolyline at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact drawn_refl g
  · split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact polyline_drawn g _ _
    · split at h
      · exact dotLines_drawn h
      · simp at h

theorem drawPolygon_drawn {charset : Charset} {g g' : Canvas} {pts : List Point} {p : Paint}
    (h : drawPolygon charset g pts p = .ok g') : g.Drawn g' := by
  unfold drawPolygon at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact drawn_refl g
  · split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact drawn_refl g
    · split at h
      · simp only [Except.ok.injEq] at h
        subst h
        exact symbolAt_drawn charset g _ _
      · split at h
        · exact dotLines_drawn h
        · simp at h

theorem drawEllipse_drawn {charset : Charset} {g g' : Canvas} {cx cy rx ry : Int} {p : Paint}
    (h : drawEllipse charset g cx cy rx ry p = .ok g') : g.Drawn g' := by
  unfold drawEllipse at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact drawn_refl g
  · split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact symbolAt_drawn charset g _ _
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · exact dotLines_drawn h
          · simp at h

theorem strokeThen_drawn {g : Canvas} {ds : List Braille.Dot} {current start : Braille.Dot}
    {st : PathState} (h : strokeThen g ds current start = .ok st) : g.Drawn st.1 := by
  unfold strokeThen at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact dotLines_drawn ‹_›
  · simp at h

theorem pathStep_drawn {st st' : PathState} {cmd : PathCommand}
    (h : pathStep st cmd = .ok st') : st.1.Drawn st'.1 := by
  cases cmd with
  | M p =>
    simp only [pathStep] at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact drawn_refl _
    · simp at h
  | L p =>
    simp only [pathStep] at h
    split at h
    · exact strokeThen_drawn h
    · simp at h
  | Z =>
    simp only [pathStep] at h
    exact strokeThen_drawn h
  | C c1 c2 p =>
    simp only [pathStep] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · exact strokeThen_drawn h
          · simp at h
  | A center radius a0 sweep =>
    simp only [pathStep] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · exact strokeThen_drawn h
        · simp at h

theorem foldlM_pathStep_drawn (cmds : List PathCommand) :
    ∀ (st st' : PathState), cmds.foldlM pathStep st = .ok st' → st.1.Drawn st'.1 := by
  induction cmds with
  | nil =>
    intro st st' h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact drawn_refl _
  | cons cmd cmds ih =>
    intro st st' h
    rw [List.foldlM_cons] at h
    cases hs : pathStep st cmd with
    | error e => simp [hs, bind, Except.bind] at h
    | ok st1 =>
      simp only [hs, bind, Except.bind] at h
      exact drawn_trans (pathStep_drawn hs) (ih st1 st' h)

theorem drawPath_drawn {g g' : Canvas} {cmds : List PathCommand} {p : Paint}
    (h : drawPath g cmds p = .ok g') : g.Drawn g' := by
  unfold drawPath at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact drawn_refl g
  · split at h
    · rename_i st hst
      simp only [Except.ok.injEq] at h
      subst h
      exact foldlM_pathStep_drawn cmds _ _ hst
    · simp at h

theorem drawPrimitive_drawn {charset : Charset} {g g' : Canvas} {p : Primitive}
    (h : drawPrimitive charset g p = .ok g') : g.Drawn g' := by
  cases p with
  | rect r q => exact drawRectangle_drawn h
  | roundRect r _ q => exact drawRectangle_drawn h
  | ellipse cx cy rx ry q => exact drawEllipse_drawn h
  | polygon pts q => exact drawPolygon_drawn h
  | polyline pts _ q => exact drawPolyline_drawn h
  | path cmds q => exact drawPath_drawn h
  | text t =>
    simp only [drawPrimitive, Except.ok.injEq] at h
    subst h
    exact drawn_refl g
  | markerRef name pos axis =>
    simp only [drawPrimitive, Except.ok.injEq] at h
    subst h
    exact drawMarker_drawn charset g name pos axis
  | symbolRef name pos _ =>
    simp only [drawPrimitive, Except.ok.injEq] at h
    subst h
    exact symbolAt_drawn charset g pos name

theorem drawAll_drawn (charset : Charset) (ps : List Primitive) :
    ∀ (g g' : Canvas), drawAll charset g ps = .ok g' → g.Drawn g' := by
  unfold drawAll
  induction ps with
  | nil =>
    intro g g' h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact drawn_refl _
  | cons p ps ih =>
    intro g g' h
    rw [List.foldlM_cons] at h
    cases hs : drawPrimitive charset g p with
    | error e => simp [hs, bind, Except.bind] at h
    | ok g1 =>
      simp only [hs, bind, Except.bind] at h
      exact drawn_trans (drawPrimitive_drawn hs) (ih g1 g' h)

theorem sceneCanvas_ok {s : Scene} {g : Canvas} (h : sceneCanvas s = .ok g) :
    0 ≤ s.canvas.w ∧ 0 ≤ s.canvas.h ∧ g = Canvas.new s.canvas.w.toNat s.canvas.h.toNat := by
  unfold sceneCanvas at h
  split at h
  · rename_i hc
    simp only [Except.ok.injEq] at h
    exact ⟨hc.1, hc.2, h.symm⟩
  · simp at h

theorem renderCanvas_ok {s : Scene} {charset : Charset} (hp : s.profile = .cell)
    {g : Canvas} {n : Nat} (h : renderCanvas s charset = .ok (g, n)) :
    ∃ g0 g1, sceneCanvas s = .ok g0 ∧ drawAll charset g0 (scenePrimitives s) = .ok g1 ∧
      Place.placeAll g1 (sceneLabels s) = (g, n) := by
  unfold renderCanvas at h
  simp only [hp, ↓reduceIte] at h
  split at h
  · rename_i g1 hd
    simp only [Except.ok.injEq] at h
    unfold drawCanvas at hd
    split at hd
    · rename_i g0 h0
      exact ⟨g0, g1, h0, hd, h⟩
    · simp at hd
  · simp at h


/-- A primitive is cell-supported when it belongs to the actual classes emitted by the cell
layout engines (rectangles, rounded rectangles, orthogonal polylines, text, markers, symbols)
or has unpainted stroke and fill (`paintCell = 0`). -/
def _root_.Elegant.Primitive.CellSupported : Primitive → Prop
  | .rect _ _ => True
  | .roundRect _ _ _ => True
  | .polyline pts _ q => Polyline.isOrthogonal pts = true ∨ Render.paintCell q = 0
  | .polygon _ q => Render.paintCell q = 0
  | .ellipse _ _ _ _ q => Render.paintCell q = 0
  | .path _ q => Render.paintCell q = 0
  | .text _ => True
  | .markerRef _ _ _ => True
  | .symbolRef _ _ _ => True

/-- Every primitive emitted in the scene display list is cell-supported. -/
def _root_.Elegant.Scene.CellSupported (s : Scene) : Prop :=
  ∀ p ∈ scenePrimitives s, p.CellSupported

theorem drawRectangle_ok (charset : Charset) (g : Canvas) (r : Rect) (p : Paint) (base : Nat)
    (hx : 0 ≤ r.x) (hy : 0 ≤ r.y) (hw : 0 ≤ r.w) (hh : 0 ≤ r.h)
    (hxm : r.x + r.w ≤ I32_MAX) (hym : r.y + r.h ≤ I32_MAX) :
    ∃ g', drawRectangle charset g r p base = .ok g' := by
  unfold drawRectangle
  have hcp : Braille.checkedPoint (r.x + r.w) (r.y + r.h) = .ok ⟨r.x + r.w, r.y + r.h⟩ := by
    unfold Braille.checkedPoint
    have h1 : I32_MIN ≤ r.x + r.w := by unfold I32_MIN; omega
    have h2 : I32_MIN ≤ r.y + r.h := by unfold I32_MIN; omega
    have h3 : r.x + r.w ≤ I32_MAX := hxm
    have h4 : r.y + r.h ≤ I32_MAX := hym
    have hc : I32_MIN ≤ r.x + r.w ∧ r.x + r.w ≤ I32_MAX ∧
        I32_MIN ≤ r.y + r.h ∧ r.y + r.h ≤ I32_MAX := ⟨h1, h3, h2, h4⟩
    rw [ite_eq_left hc]
  rw [hcp]
  dsimp only
  by_cases h0 : paintCell p = 0 ∨ r.w ≤ 0 ∨ r.h ≤ 0
  · rw [ite_eq_left h0]
    exact ⟨g, rfl⟩
  · rw [ite_eq_right h0]
    by_cases h1 : min r.w r.h = 1
    · rw [ite_eq_left h1]
      exact ⟨thinRect charset g r p, rfl⟩
    · rw [ite_eq_right h1]
      exact ⟨sides g r (lineStyle p base), rfl⟩

theorem drawPolyline_orthogonal_ok (g : Canvas) (pts : List Point) (p : Paint)
    (ho : Polyline.isOrthogonal pts = true ∨ paintCell p = 0) :
    ∃ g', drawPolyline g pts p = .ok g' := by
  unfold drawPolyline
  by_cases hp : paintCell p = 0
  · rw [ite_eq_left hp]
    exact ⟨g, rfl⟩
  · rw [ite_eq_right hp]
    cases ho with
    | inl horth =>
      rw [ite_eq_left horth]
      exact ⟨_, rfl⟩
    | inr hp0 =>
      exact False.elim (hp hp0)

theorem drawPolygon_paintZero_ok (charset : Charset) (g : Canvas) (pts : List Point) (p : Paint)
    (hp : paintCell p = 0) : drawPolygon charset g pts p = .ok g := by
  unfold drawPolygon
  cases Braille.bounds pts with
  | none => rfl
  | some bounds =>
    rcases bounds with ⟨x0, x1, y0, y1⟩
    dsimp only
    rw [ite_eq_left hp]

theorem drawEllipse_paintZero_ok (charset : Charset) (g : Canvas) (cx cy rx ry : Int) (p : Paint)
    (hp : paintCell p = 0) : drawEllipse charset g cx cy rx ry p = .ok g := by
  unfold drawEllipse
  rw [ite_eq_left hp]

theorem drawPath_paintZero_ok (g : Canvas) (cmds : List PathCommand) (p : Paint)
    (hp : paintCell p = 0) : drawPath g cmds p = .ok g := by
  unfold drawPath
  rw [ite_eq_left hp]

theorem drawPrimitive_ok (charset : Charset) (g : Canvas) (p : Primitive) (extent : Size)
    (hb : p.cellBounds extent = true) (hw : extent.w ≤ I32_MAX) (hh : extent.h ≤ I32_MAX)
    (hs : p.CellSupported) :
    ∃ g', drawPrimitive charset g p = .ok g' := by
  cases p with
  | text t =>
    exact ⟨g, rfl⟩
  | markerRef name pos axis =>
    exact ⟨drawMarker charset g name pos axis, rfl⟩
  | symbolRef name pos style =>
    exact ⟨symbolAt charset g pos name, rfl⟩
  | rect r q =>
    simp only [Primitive.cellBounds, Size.containsCellRect, decide_eq_true_iff] at hb
    have hxm : r.x + r.w ≤ I32_MAX := by omega
    have hym : r.y + r.h ≤ I32_MAX := by omega
    exact drawRectangle_ok charset g r q styleLight hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hxm hym
  | roundRect r cr q =>
    simp only [Primitive.cellBounds, Size.containsCellRect, decide_eq_true_iff] at hb
    have hxm : r.x + r.w ≤ I32_MAX := by omega
    have hym : r.y + r.h ≤ I32_MAX := by omega
    exact drawRectangle_ok charset g r q styleRounded hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hxm hym
  | polyline pts cr q =>
    exact drawPolyline_orthogonal_ok g pts q hs
  | polygon pts q =>
    exact ⟨g, drawPolygon_paintZero_ok charset g pts q hs⟩
  | ellipse cx cy rx ry q =>
    exact ⟨g, drawEllipse_paintZero_ok charset g cx cy rx ry q hs⟩
  | path cmds q =>
    exact ⟨g, drawPath_paintZero_ok g cmds q hs⟩

theorem drawAll_ok (charset : Charset) (ps : List Primitive) (extent : Size)
    (hb : ∀ p ∈ ps, p.cellBounds extent = true)
    (hw : extent.w ≤ I32_MAX) (hh : extent.h ≤ I32_MAX)
    (hs : ∀ p ∈ ps, p.CellSupported) (g : Canvas) :
    ∃ g', drawAll charset g ps = .ok g' := by
  induction ps generalizing g with
  | nil =>
    exact ⟨g, rfl⟩
  | cons p ps ih =>
    have hpb : p.cellBounds extent = true := hb p List.mem_cons_self
    have hps : p.CellSupported := hs p List.mem_cons_self
    obtain ⟨g1, hg1⟩ := drawPrimitive_ok charset g p extent hpb hw hh hps
    have hb_rest : ∀ q ∈ ps, q.cellBounds extent = true :=
      fun q hq => hb q (List.mem_cons_of_mem p hq)
    have hs_rest : ∀ q ∈ ps, q.CellSupported :=
      fun q hq => hs q (List.mem_cons_of_mem p hq)
    obtain ⟨g', hg'⟩ := ih hb_rest hs_rest g1
    refine ⟨g', ?_⟩
    change (p :: ps).foldlM (drawPrimitive charset) g = .ok g'
    rw [List.foldlM_cons, hg1]
    dsimp only [bind, Except.bind]
    exact hg'

theorem drawCanvas_ok (s : Scene) (charset : Charset)
    (hb : s.PrimitiveBounds)
    (hw : s.canvas.w ≤ I32_MAX) (hh : s.canvas.h ≤ I32_MAX)
    (hs : s.CellSupported) :
    ∃ g', drawCanvas s charset = .ok g' := by
  have hpb := hb
  simp only [Scene.PrimitiveBounds, Scene.primitiveBoundsCheck, Bool.and_eq_true_iff,
    decide_eq_true_iff] at hpb
  obtain ⟨⟨hw0, hh0⟩, _⟩ := hpb
  have hcanvas : sceneCanvas s = .ok (Canvas.new s.canvas.w.toNat s.canvas.h.toNat) := by
    unfold sceneCanvas
    have hc : 0 ≤ s.canvas.w ∧ 0 ≤ s.canvas.h := ⟨hw0, hh0⟩
    simp [hc]
  have hprims : ∀ p ∈ scenePrimitives s, p.cellBounds s.canvas = true := by
    intro p hp
    simp only [scenePrimitives, List.mem_flatMap] at hp
    obtain ⟨grp, hgrp, hp_grp⟩ := hp
    exact Scene.primitiveBounds_item hb hgrp hp_grp
  have hsupp : ∀ p ∈ scenePrimitives s, p.CellSupported := hs
  obtain ⟨g1, hg1⟩ := drawAll_ok charset (scenePrimitives s) s.canvas hprims hw hh hsupp
    (Canvas.new s.canvas.w.toNat s.canvas.h.toNat)
  refine ⟨g1, ?_⟩
  unfold drawCanvas
  rw [hcanvas]
  exact hg1

/-- Input-invariant-to-success theorem for actual emitted cell scenes:
when the canvas fits within int32 and primitives belong to the emitted cell classes,
the public renderer succeeds on any scene satisfying `PrimitiveBounds`. -/
theorem renderCanvas_of_cellSupported (s : Scene) (charset : Charset)
    (hp : s.profile = .cell)
    (hb : s.PrimitiveBounds)
    (hw : s.canvas.w ≤ I32_MAX) (hh : s.canvas.h ≤ I32_MAX)
    (hs : s.CellSupported) :
    ∃ g n, renderCanvas s charset = .ok (g, n) := by
  obtain ⟨g1, hg1⟩ := drawCanvas_ok s charset hb hw hh hs
  unfold renderCanvas
  simp only [hp, ↓reduceIte]
  rw [hg1]
  exact ⟨_, _, rfl⟩

/-- Obstruction to unconditioned totality: a scene can satisfy `PrimitiveBounds` yet fail
`renderCanvas` because checked arithmetic overflows on extents larger than `I32_MAX`. -/
theorem renderCanvas_counterexample :
    ∃ s : Scene, s.profile = .cell ∧ s.PrimitiveBounds ∧
      renderCanvas s .unicode = .error .overflow :=
  ⟨{ kind := "counter", profile := .cell, canvas := ⟨3000000000, 0⟩,
     items := [⟨.decor, "", [.rect ⟨2500000000, 0, 10, 0⟩ { style := "node" }]⟩] },
   rfl, rfl, rfl⟩

/-- Universal totality across arbitrary scenes without canvas bounds is unprovable. -/
theorem not_renderCanvas_totality_of_primitiveBounds :
    ¬ (∀ (s : Scene) (charset : Charset), s.profile = .cell → s.PrimitiveBounds →
        ∃ g n, renderCanvas s charset = .ok (g, n)) := by
  intro h
  obtain ⟨s, hp, hb, herr⟩ := renderCanvas_counterexample
  obtain ⟨g, n, hok⟩ := h s .unicode hp hb
  rw [herr] at hok
  cases hok

end Render

theorem new_cellAt (w h : Nat) (c r : Int) : (Canvas.new w h).cellAt c r = Cell.empty := by
  unfold Canvas.cellAt
  split
  · simp [Canvas.new, Array.getElem?_replicate]
    split <;> rfl
  · rfl

/-- In the cell profile the canvas of a rendered scene has the width and height of the scene
extent: one scene unit is one cell. -/
theorem canvas_size_eq_scene_extent (s : Scene) (charset : Charset) (hp : s.profile = .cell)
    (g : Canvas) (n : Nat) (h : Render.renderCanvas s charset = .ok (g, n)) :
    (g.W : Int) = s.canvas.w ∧ (g.H : Int) = s.canvas.h := by
  obtain ⟨g0, g1, h0, h1, h2⟩ := Render.renderCanvas_ok hp h
  obtain ⟨hw, hh, hg0⟩ := Render.sceneCanvas_ok h0
  have hdr := (Render.drawAll_drawn charset _ g0 g1 h1).1
  have hgeq : g = Place.placeCanvas g1 (Render.sceneLabels s) := (congrArg Prod.fst h2).symm
  have hpl := Place.placeCanvas_placing (Render.sceneLabels s) g1
  subst hgeq
  subst hg0
  have hW : (Place.placeCanvas g1 (Render.sceneLabels s)).W = s.canvas.w.toNat :=
    hpl.1.trans hdr.1
  have hH : (Place.placeCanvas g1 (Render.sceneLabels s)).H = s.canvas.h.toNat :=
    hpl.2.1.trans hdr.2.1
  rw [hW, hH]
  exact ⟨Int.toNat_of_nonneg hw, Int.toNat_of_nonneg hh⟩

/-- Successful cell rendering preserves canvas dimensions, confines every changed cell,
and gives each occupied label cell a unique owner. Input control hulls need not lie
inside the canvas: attempted writes outside it are clipped by `Canvas.put`. -/
theorem text_valid (s : Scene) (charset : Charset) (hp : s.profile = .cell)
    (_hv : HardConstraints s.layoutDump) (g : Canvas) (n : Nat)
    (h : Render.renderCanvas s charset = .ok (g, n)) :
    ((g.W : Int) = s.canvas.w ∧ (g.H : Int) = s.canvas.h) ∧
      (Canvas.new g.W g.H).Confined g ∧
      ∃ g1, Render.drawCanvas s charset = .ok g1 ∧
        Place.placeAll g1 (Render.sceneLabels s) = (g, n) ∧
        ∀ c r, (g.cellAt c r).label ≠ Label.empty →
          ∃ i, i < (Render.sceneLabels s).length ∧
            Place.Placed g1 (Render.sceneLabels s) i c r ∧
            ∀ j, Place.Placed g1 (Render.sceneLabels s) j c r → j = i := by
  obtain ⟨g0, g1, h0, h1, h2⟩ := Render.renderCanvas_ok hp h
  obtain ⟨hw, hh, hg0⟩ := Render.sceneCanvas_ok h0
  have hdr := Render.drawAll_drawn charset _ g0 g1 h1
  have hgeq : g = Place.placeCanvas g1 (Render.sceneLabels s) := (congrArg Prod.fst h2).symm
  have hpl := Place.placeCanvas_placing (Render.sceneLabels s) g1
  refine ⟨canvas_size_eq_scene_extent s charset hp g n h, ?_, g1, ?_, h2, ?_⟩
  · have hc := confined_trans hdr.1 hpl.confined
    have hW : g.W = g0.W := by rw [hgeq]; exact hpl.1.trans hdr.1.1
    have hH : g.H = g0.H := by rw [hgeq]; exact hpl.2.1.trans hdr.1.2.1
    rw [hW, hH, hg0]
    rw [hgeq]
    rw [hg0] at hc
    exact hc
  · unfold Render.drawCanvas
    rw [h0]
    exact h1
  · intro c r hne
    have hg1 : ∀ c r, (g1.cellAt c r).label = Label.empty := fun c r => by
      rw [hdr.2 c r, hg0, new_cellAt]
      rfl
    have hlab : ((Place.placeAll g1 (Render.sceneLabels s)).1.cellAt c r).label ≠ Label.empty := by
      rw [h2]
      exact hne
    obtain ⟨i, hi, hpl', huniq, _⟩ := Place.place_labels_disjoint g1 (Render.sceneLabels s) hg1 c r hlab
    exact ⟨i, hi, hpl', huniq⟩

/-- A successful cell rendering never overwrites border masks or symbols with label text:
any cell that holds label text had no border mask and no symbol after drawing, and label
placement leaves every border mask and symbol unchanged. -/
theorem renderCanvas_label_never_overwrites_border (s : Scene) (charset : Charset)
    (hp : s.profile = .cell) (g : Canvas) (n : Nat)
    (h : Render.renderCanvas s charset = .ok (g, n)) :
    ∃ g1, Render.drawCanvas s charset = .ok g1 ∧
      Place.placeAll g1 (Render.sceneLabels s) = (g, n) ∧
      ∀ c r, ((g.cellAt c r).label ≠ Label.empty →
          (g1.cellAt c r).mask = 0 ∧ (g1.cellAt c r).symbol = 0) ∧
        (g.cellAt c r).mask = (g1.cellAt c r).mask ∧
        (g.cellAt c r).symbol = (g1.cellAt c r).symbol := by
  obtain ⟨g0, g1, h0, h1, h2⟩ := Render.renderCanvas_ok hp h
  obtain ⟨_, _, hg0⟩ := Render.sceneCanvas_ok h0
  have hdr := Render.drawAll_drawn charset _ g0 g1 h1
  have hg1 : ∀ c r, (g1.cellAt c r).label = Label.empty := fun c r => by
    rw [hdr.2 c r, hg0, new_cellAt]
    rfl
  have hgeq : (Place.placeAll g1 (Render.sceneLabels s)).1 = g := congrArg Prod.fst h2
  refine ⟨g1, ?_, h2, fun c r => ?_⟩
  · unfold Render.drawCanvas
    rw [h0]
    exact h1
  · have hborder := Place.label_never_overwrites_border g1 (Render.sceneLabels s) hg1 c r
    rw [hgeq] at hborder
    exact hborder

/-- A canvas with no rows serialises to no bytes. -/
theorem serialise_zero_rows (charset : Charset) (g : Canvas) (h : g.H = 0) :
    Render.serialise charset g = "" := by
  simp [Render.serialise, h]

/-- Input-invariant-to-success theorem: for any cell-profile scene satisfying the
primitive bounds invariant whose canvas fits int32 and whose primitives belong to the
classes emitted by cell layout engines, public canvas rendering succeeds. -/
theorem renderCanvas_of_cellSupported (s : Scene) (charset : Charset)
    (hp : s.profile = .cell)
    (hb : s.PrimitiveBounds)
    (hw : s.canvas.w ≤ I32_MAX) (hh : s.canvas.h ≤ I32_MAX)
    (hs : s.CellSupported) :
    ∃ g n, Render.renderCanvas s charset = .ok (g, n) :=
  Render.renderCanvas_of_cellSupported s charset hp hb hw hh hs

/-- End-to-end rendered-cell validity from sufficient input premises:
a bounded cell-supported scene succeeds and produces a confined canvas with uniquely
owned labels and preserved extents, without assuming successful rendering. -/
theorem text_valid_of_cellSupported (s : Scene) (charset : Charset) (hp : s.profile = .cell)
    (hv : HardConstraints s.layoutDump)
    (hb : s.PrimitiveBounds)
    (hw : s.canvas.w ≤ I32_MAX) (hh : s.canvas.h ≤ I32_MAX)
    (hs : s.CellSupported) :
    ∃ g n,
      ((g.W : Int) = s.canvas.w ∧ (g.H : Int) = s.canvas.h) ∧
      (Canvas.new g.W g.H).Confined g ∧
      ∃ g1, Render.drawCanvas s charset = .ok g1 ∧
        Place.placeAll g1 (Render.sceneLabels s) = (g, n) ∧
        ∀ c r, (g.cellAt c r).label ≠ Label.empty →
          ∃ i, i < (Render.sceneLabels s).length ∧
            Place.Placed g1 (Render.sceneLabels s) i c r ∧
            ∀ j, Place.Placed g1 (Render.sceneLabels s) j c r → j = i := by
  obtain ⟨g, n, h_ok⟩ := renderCanvas_of_cellSupported s charset hp hb hw hh hs
  have tv := text_valid s charset hp hv g n h_ok
  exact ⟨g, n, tv.1, tv.2.1, tv.2.2⟩

/-- End-to-end border non-overwriting corollary from input premises only:
a cell-profile scene satisfying the primitive bounds invariant, int32 canvas extent,
and emitted cell primitive classes succeeds in rendering, never overwriting border masks
or symbols with label text. -/
theorem renderCanvas_label_never_overwrites_border_of_cellSupported
    (s : Scene) (charset : Charset) (hp : s.profile = .cell)
    (hb : s.PrimitiveBounds)
    (hw : s.canvas.w ≤ I32_MAX) (hh : s.canvas.h ≤ I32_MAX)
    (hs : s.CellSupported) :
    ∃ g n, ∃ g1, Render.drawCanvas s charset = .ok g1 ∧
      Place.placeAll g1 (Render.sceneLabels s) = (g, n) ∧
      ∀ c r, ((g.cellAt c r).label ≠ Label.empty →
          (g1.cellAt c r).mask = 0 ∧ (g1.cellAt c r).symbol = 0) ∧
        (g.cellAt c r).mask = (g1.cellAt c r).mask ∧
        (g.cellAt c r).symbol = (g1.cellAt c r).symbol := by
  obtain ⟨g, n, h_ok⟩ := renderCanvas_of_cellSupported s charset hp hb hw hh hs
  have hborder := renderCanvas_label_never_overwrites_border s charset hp g n h_ok
  exact ⟨g, n, hborder⟩

/-- Obstruction to unconditioned totality: a scene can satisfy `PrimitiveBounds` yet fail
`renderCanvas` because `drawCanvas` executes before the bounds check and integer overflow
guards in `checkedPoint` trigger on canvas extents larger than `I32_MAX`. -/
theorem renderCanvas_counterexample :
    ∃ s : Scene, s.profile = .cell ∧ s.PrimitiveBounds ∧
      Render.renderCanvas s .unicode = .error .overflow :=
  Render.renderCanvas_counterexample

theorem not_renderCanvas_totality_of_primitiveBounds :
    ¬ (∀ (s : Scene) (charset : Charset), s.profile = .cell → s.PrimitiveBounds →
        ∃ g n, Render.renderCanvas s charset = .ok (g, n)) :=
  Render.not_renderCanvas_totality_of_primitiveBounds

section Oracles

private def cellScene (w h : Int) (items : List Primitive) : Scene :=
  { kind := "test", profile := .cell, canvas := ⟨w, h⟩, items := [⟨.decor, "", items⟩] }

private def edge (ps : List Point) : Primitive := .polyline ps 0 { style := "edge" }

private def labelAt (x y w : Int) (text : String) : Primitive :=
  .text { rect := ⟨x, y, w, 1⟩, role := .label, size := 14, align := .middle, style := "text",
          lines := [[{ text := text }]] }

private def pt (x y : Int) : Point := ⟨x, y⟩

private def rendered (s : Scene) (charset : Charset) : Option (String × Nat) :=
  (render s charset).toOption

private def nodeBox : Primitive := .rect ⟨0, 0, 7, 3⟩ { style := "node" }

private def dashedEmphasis : Paint := { style := "edge", line := .dashed, width := .emphasis }

#guard rendered (cellScene 7 3 [nodeBox, labelAt 0 1 7 "Hi"]) .unicode ==
  some ("┌─────┐\n│ Hi  │\n└─────┘\n", 0)
#guard rendered (cellScene 5 4 [edge [pt 0 0, pt 3 0, pt 3 2]]) .unicode ==
  some ("╶──┐\n   │\n   ╵\n\n", 0)
#guard rendered (cellScene 5 3 [edge [pt 0 0, pt 4 0], edge [pt 2 0, pt 2 2]]) .unicode ==
  some ("╶─┬─╴\n  │\n  ╵\n", 0)
#guard rendered (cellScene 5 3 [edge [pt 0 1, pt 4 1], edge [pt 2 0, pt 2 2]]) .unicode ==
  some ("  ╷\n╶─┼─╴\n  ╵\n", 0)
#guard rendered (cellScene 7 3 [.roundRect ⟨0, 0, 7, 3⟩ 0 { style := "node" }]) .unicode ==
  some ("╭─────╮\n│     │\n╰─────╯\n", 0)
#guard rendered (cellScene 10 3 [.rect ⟨0, 0, 10, 3⟩ { style := "node" }, labelAt 0 1 10 "日本語"])
    .unicode == some ("┌────────┐\n│ 日本語 │\n└────────┘\n", 0)
#guard rendered (cellScene 3 1 [edge [pt 0 0, pt 2 0], labelAt 0 0 3 "abc"]) .unicode ==
  some ("╶─╴\n", 3)
#guard rendered (cellScene 6 4 [edge [pt 0 0, pt 3 0, pt 4 2]]) .unicode ==
  some ("⠤⠤⠤⡄\n   ⢸\n    ⠇\n\n", 0)
#guard rendered (cellScene 6 4 [edge [pt 0 0, pt 3 0, pt 4 2]]) .ascii ==
  some ("####\n   #\n    #\n\n", 0)
#guard rendered (cellScene 3 1 [edge [pt 0 0, pt 2 0], .markerRef "point" (pt 2 0) .positiveX])
    .unicode == some ("╶─▶\n", 0)
#guard rendered (cellScene 3 1 [edge [pt 0 0, pt 2 0], .markerRef "point" (pt 0 0) .negativeX])
    .unicode == some ("◀─╴\n", 0)
#guard rendered (cellScene 1 3 [edge [pt 0 0, pt 0 2], .markerRef "point" (pt 0 2) .positiveY])
    .unicode == some ("╷\n│\n▼\n", 0)
#guard rendered (cellScene 1 3 [edge [pt 0 0, pt 0 2], .markerRef "point" (pt 0 0) .negativeY])
    .unicode == some ("▲\n│\n╵\n", 0)
#guard rendered (cellScene 3 1 [edge [pt 0 0, pt 2 0], .markerRef "point" (pt 2 0) .positiveX])
    .ascii == some ("-->\n", 0)
#guard rendered (cellScene 5 1 [.polyline [pt 0 0, pt 4 0] 0 dashedEmphasis]) .unicode ==
  some ("╶┄┄┄╴\n", 0)
#guard rendered (cellScene 5 1 [.polyline [pt 0 0, pt 4 0] 0 dashedEmphasis]) .ascii ==
  some (".....\n", 0)
#guard rendered { cellScene 513 1025 [] with profile := .vector } .unicode == some ("\n\n", 0)
#guard rendered (cellScene 0 0 []) .unicode == some ("", 0)
#guard rendered (cellScene (-1) 3 []) .unicode == none
#guard rendered (cellScene 1 1 [.symbolRef "disc" (pt 10 10) "ink"]) .unicode == some ("\n", 0)
#guard rendered (cellScene 1 1 [.symbolRef "disc" (pt 0 0) "ink"]) .unicode ==
  some ("●\n", 0)
#guard (cellScene 3000000000 0 [.rect ⟨2500000000, 0, 10, 0⟩ { style := "node" }]).primitiveBoundsCheck == true
#guard rendered (cellScene 3000000000 0 [.rect ⟨2500000000, 0, 10, 0⟩ { style := "node" }]) .unicode == none

end Oracles

end Elegant.Text

namespace Elegant.Text
-- These executable guards contain data controls only; row LF is renderer-owned.
#guard Place.terminalText (String.ofList [Char.ofNat 0, Char.ofNat 31,
  Char.ofNat 127, Char.ofNat 128, Char.ofNat 159, 'A', '界']) = "�����A界"
#guard Render.cellText .unicode { label := .cluster (String.singleton (Char.ofNat 27)) .one } = "�"
#guard Render.cellText .ascii { symbol := 155 } = "�"
#guard Render.serialise .unicode (Canvas.new 0 1) = "\n"

end Elegant.Text

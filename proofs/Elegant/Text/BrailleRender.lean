import Elegant.Text.Render

set_option autoImplicit false

/-! Braille raster of a vector scene (`spec/render-cells.md`, requirements render-cells-49,
render-cells-98 to render-cells-113).

A scene under the vector profile is drawn as dots: every shape becomes a fill, an outline, or
both, by the `cell` column of its style row. Labels are placed afterwards on the same canvas.
The canvas has `ceil_div(w, 512)` columns and `ceil_div(h, 1024)` rows. Colour is outside the
Lean renderer. -/

namespace Elegant.Text.Braille

/-- Even-odd test over several rings: the sample is inside when an odd number of rings hold it. -/
def ringsInside (rings : List (List Point)) (px py : Int) : Except LayoutError Bool :=
  rings.foldlM (fun acc ring =>
    match polygonInside ring px py with
    | .ok inside => .ok (bne acc inside)
    | .error e => .error e) false

/-- The dots of the list whose sample point is inside the rings. -/
def keepInsideRings (rings : List (List Point)) : List Dot → Except LayoutError (List Dot)
  | [] => .ok []
  | d :: ds =>
    match ringsInside rings (sample d).1 (sample d).2 with
    | .error e => .error e
    | .ok inside =>
      match keepInsideRings rings ds with
      | .error e => .error e
      | .ok rest => .ok (if inside then d :: rest else rest)

/-- The dots whose sample point is inside the rings. The candidates are the dots whose cell
covers the bounding box of all vertices. -/
def fillRings (rings : List (List Point)) : Except LayoutError (List Dot) :=
  match bounds rings.flatten with
  | none => .ok []
  | some (x0, x1, y0, y1) =>
    keepInsideRings rings
      ((intRange (Int.fdiv y0 256) (Int.fdiv y1 256)).flatMap fun j =>
        (intRange (Int.fdiv x0 256) (Int.fdiv x1 256)).map fun i => (i, j))

theorem ringsInside_some_ring {rings : List (List Point)} {px py : Int}
    (h : ringsInside rings px py = .ok true) :
    ∃ ring ∈ rings, polygonInside ring px py = .ok true := by
  unfold ringsInside at h
  suffices H : ∀ (rs : List (List Point)) (acc : Bool),
      rs.foldlM (fun (acc : Bool) (ring : List Point) =>
        (match polygonInside ring px py with
          | Except.ok inside => Except.ok (bne acc inside)
          | Except.error e => Except.error e : Except LayoutError Bool)) acc = .ok true →
      acc = true ∨ ∃ ring ∈ rs, polygonInside ring px py = .ok true by
    rcases H rings false h with h0 | h0
    · exact absurd h0 (by decide)
    · exact h0
  intro rs
  induction rs with
  | nil =>
    intro acc hacc
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hacc
    exact Or.inl hacc
  | cons ring rs ih =>
    intro acc hacc
    rw [List.foldlM_cons] at hacc
    cases hp : polygonInside ring px py with
    | error e => simp [hp, bind, Except.bind] at hacc
    | ok inside =>
      simp only [hp, bind, Except.bind] at hacc
      rcases ih _ hacc with h1 | ⟨r', hr', h2⟩
      · cases inside
        · left
          simpa using h1
        · right
          exact ⟨ring, List.mem_cons_self, hp⟩
      · right
        exact ⟨r', List.mem_cons_of_mem _ hr', h2⟩

theorem keepInsideRings_mem (rings : List (List Point)) :
    ∀ (ds r : List Dot), keepInsideRings rings ds = .ok r →
      ∀ d ∈ r, ringsInside rings (sample d).1 (sample d).2 = .ok true := by
  intro ds
  induction ds with
  | nil =>
    intro r h d hd
    simp only [keepInsideRings, Except.ok.injEq] at h
    subst h
    simp at hd
  | cons d0 ds ih =>
    intro r h d hd
    unfold keepInsideRings at h
    cases hp : ringsInside rings (sample d0).1 (sample d0).2 with
    | error e => simp [hp] at h
    | ok inside =>
      cases hk : keepInsideRings rings ds with
      | error e => simp [hp, hk] at h
      | ok rest =>
        simp only [hp, hk, Except.ok.injEq] at h
        subst h
        cases inside with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hd
          exact ih rest hk d hd
        | true =>
          simp only [↓reduceIte, List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact hp
          · exact ih rest hk d hd

/-- A dot set by a ring fill has its sample point inside the bounding box of the vertices of one
ring. -/
theorem fillRings_in_ring_bbox (rings : List (List Point)) (dots : List Dot)
    (h : fillRings rings = .ok dots) (d : Dot) (hd : d ∈ dots) :
    ∃ ring ∈ rings, InBBox ring (sample d).1 (sample d).2 := by
  unfold fillRings at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    simp at hd
  · obtain ⟨ring, hr, hp⟩ := ringsInside_some_ring (keepInsideRings_mem rings _ dots h d hd)
    exact ⟨ring, hr, polygonInside_between hp⟩

end Elegant.Text.Braille

namespace Elegant.Text.BrailleScene

/-- The fill and the outline that the style row of a paint asks for. A style without a row
strokes only. -/
def parts (p : Paint) : Bool × Bool :=
  match styles.find? fun s => s.name == p.style with
  | some s => (decide (s.cell = 2) && s.fill != "none", decide (s.cell ≠ 0) && s.stroke != "none")
  | none => (false, true)

/-- The ring of the dots of a polygon, closed by the first vertex. -/
def closeRing (pts : List Point) : List Point :=
  pts ++ pts.take 1

/-- The four corners of a rectangle in units. -/
def corners (r : Rect) : List Point :=
  [⟨r.x, r.y⟩, ⟨r.x + r.w, r.y⟩, ⟨r.x + r.w, r.y + r.h⟩, ⟨r.x, r.y + r.h⟩]

/-- Set the dots of the list on the canvas. -/
def putDots (g : Canvas) (ds : List Braille.Dot) : Canvas :=
  ds.foldl Render.putDot g

/-- Stroke the polyline through the vertices, given in units. -/
def strokeOn (g : Canvas) (pts : List Point) : Except LayoutError Canvas :=
  match Braille.stroke pts with
  | .ok dots => .ok (putDots g dots)
  | .error e => .error e

/-- Fill the rings, given in units, with the even-odd rule. -/
def fillOn (g : Canvas) (rings : List (List Point)) : Except LayoutError Canvas :=
  match Braille.fillRings rings with
  | .ok dots => .ok (putDots g dots)
  | .error e => .error e

/-- Fill the rings when the style fills, then stroke each closed ring when the style strokes. -/
def polygonsOn (g : Canvas) (rings : List (List Point)) (p : Paint) :
    Except LayoutError Canvas :=
  match (if (parts p).1 then fillOn g rings else .ok g) with
  | .error e => .error e
  | .ok g1 =>
    if (parts p).2 then rings.foldlM (fun acc ring => strokeOn acc (closeRing ring)) g1
    else .ok g1

/-- Stroke an open polyline when the style strokes. -/
def openOn (g : Canvas) (pts : List Point) (p : Paint) : Except LayoutError Canvas :=
  if (parts p).2 then strokeOn g pts else .ok g

/-- A rectangle: its corner polygon. A negative size draws nothing. -/
def rectOn (g : Canvas) (r : Rect) (p : Paint) : Except LayoutError Canvas :=
  match Braille.checkedPoint (r.x + r.w) (r.y + r.h) with
  | .error e => .error e
  | .ok _ => if r.w < 0 ∨ r.h < 0 then .ok g else polygonsOn g [corners r] p

/-- An ellipse: its 64-vertex polygon. A negative radius draws nothing. -/
def ellipseOn (g : Canvas) (cx cy rx ry : Int) (p : Paint) : Except LayoutError Canvas :=
  if rx < 0 ∨ ry < 0 then .ok g
  else
    match Braille.ellipse ⟨cx, cy⟩ rx ry with
    | .ok ring => polygonsOn g [ring] p
    | .error e => .error e

/-- A subpath of a path and whether `Z` closed it. -/
structure Subpath where
  pts : List Point
  closed : Bool

/-- The path state: finished subpaths, the open subpath, the current point, and the start. -/
structure Walk where
  done : List Subpath := []
  cur : Option (List Point) := none
  current : Point := ⟨0, 0⟩
  start : Point := ⟨0, 0⟩

/-- Move the open subpath, if any, to the finished subpaths unclosed. -/
def Walk.flush (w : Walk) : Walk :=
  match w.cur with
  | some pts => { w with done := w.done ++ [⟨pts, false⟩], cur := none }
  | none => w

/-- Append vertices to the open subpath, opening one at the current point when none is open. -/
def Walk.extend (w : Walk) (pts : List Point) : Walk :=
  { w with cur := some (w.cur.getD [w.current] ++ pts), current := pts.getLast?.getD w.current }

/-- One path command. -/
def Walk.step (w : Walk) : PathCommand → Except LayoutError Walk
  | .M p => .ok { w.flush with cur := some [p], current := p, start := p }
  | .L p => .ok (w.extend [p])
  | .C c1 c2 p =>
    match Braille.cubic w.current c1 c2 p with
    | .ok pts => .ok (w.extend pts.tail)
    | .error e => .error e
  | .A center radius a0 sweep =>
    match Braille.arc center radius a0 sweep with
    | .ok pts => .ok (w.extend pts)
    | .error e => .error e
  | .Z =>
    match w.cur with
    | some pts => .ok { w with done := w.done ++ [⟨pts, true⟩], cur := none, current := w.start }
    | none => .ok { w with current := w.start }

/-- A path: fill all subpaths together, then stroke each. -/
def pathOn (g : Canvas) (cmds : List PathCommand) (p : Paint) : Except LayoutError Canvas :=
  match cmds.foldlM Walk.step ({} : Walk) with
  | .error e => .error e
  | .ok w =>
    let subs := w.flush.done
    match (if (parts p).1 then fillOn g (subs.map (·.pts)) else .ok g) with
    | .error e => .error e
    | .ok g1 =>
      if (parts p).2 then
        subs.foldlM (fun acc s => strokeOn acc (if s.closed then closeRing s.pts else s.pts)) g1
      else .ok g1

/-- A marker vertex: the point minus the reference, rotated by the axis, plus the end point. -/
def markerVertex (ref : Int × Int) (pos : Point) (axis : MarkerAxis) (p : Int × Int) :
    Except LayoutError Point :=
  let x := p.1 - ref.1
  let y := p.2 - ref.2
  match axis with
  | .positiveX => Braille.checkedPoint (x + pos.x) (y + pos.y)
  | .negativeX => Braille.checkedPoint (-x + pos.x) (-y + pos.y)
  | .positiveY => Braille.checkedPoint (-y + pos.x) (x + pos.y)
  | .negativeY => Braille.checkedPoint (y + pos.x) (-x + pos.y)

/-- Split the vertices at the cumulative end indices of the breaks. -/
def splitParts (pts : List Point) (consumed : Nat) : List Nat → List (List Point)
  | [] => [pts]
  | b :: bs => pts.take (b - consumed) :: splitParts (pts.drop (b - consumed)) b bs

/-- A marker: its contours as polygons for a filled or hollow marker, as open polylines for an
open marker. A marker outside the table, or with fewer than 2 points, is a domain error. -/
def markerOn (g : Canvas) (name : String) (pos : Point) (axis : MarkerAxis) :
    Except LayoutError Canvas :=
  match markers.find? fun m => m.name == name with
  | none => .error .domain
  | some m =>
    if m.points.length < 2 then .error .domain
    else
      match m.points.mapM (markerVertex m.ref pos axis) with
      | .error e => .error e
      | .ok pts =>
        let style := if m.paint == "hollow" then "mark-hollow" else if m.paint == "open" then "edge"
          else "mark"
        let paint : Paint := { style := style }
        let contours := splitParts pts 0 m.breaks
        if m.paint == "open" then contours.foldlM (fun acc c => openOn acc c paint) g
        else polygonsOn g contours paint

/-- Draw one primitive. A text draws nothing: labels are placed after every shape. A symbol is a
domain error. -/
def drawPrimitive (g : Canvas) : Primitive → Except LayoutError Canvas
  | .rect r p => rectOn g r p
  | .roundRect r _ p => rectOn g r p
  | .ellipse cx cy rx ry p => ellipseOn g cx cy rx ry p
  | .polygon pts p => polygonsOn g [pts] p
  | .polyline pts _ p => openOn g pts p
  | .path cmds p => pathOn g cmds p
  | .text _ => .ok g
  | .markerRef name pos axis => markerOn g name pos axis
  | .symbolRef _ _ _ => .error .domain

/-- The role line height in units. -/
def lineUnits : TextRole → Int
  | .title => 1536
  | .label => 1280
  | .body => 1280

/-- `ceil_div(a, b)` for `b > 0`. -/
def ceilDiv (a b : Int) : Int :=
  Int.fdiv (a + b - 1) b

/-- Line `k` of a text as a one-line cell text: the box starts at the column of the box in
units, is as wide as the columns it covers, and sits on the row that holds the top of the
line. -/
def cellLine (t : SceneText) (k : Nat) (runs : List TextRun) : SceneText :=
  let first := Int.fdiv t.rect.x 512
  { t with
    rect := ⟨first, Int.fdiv (t.rect.y + (k : Int) * lineUnits t.role) 1024,
      ceilDiv (t.rect.x + t.rect.w) 512 - first, 1⟩
    lines := [runs] }

/-- The one-line cell texts of the lines of a text, from line index `k`. -/
def cellLinesFrom (t : SceneText) : Nat → List (List TextRun) → List SceneText
  | _, [] => []
  | k, runs :: rest => cellLine t k runs :: cellLinesFrom t (k + 1) rest

/-- The labels of a vector scene as one-line cell texts, in declaration order. -/
def brailleLabels (s : Scene) : List SceneText :=
  (Render.sceneLabels s).flatMap fun t => cellLinesFrom t 0 t.lines

/-- The blank canvas of a vector scene: `ceil_div(w, 512)` columns and `ceil_div(h, 1024)` rows.
A negative extent is a domain error. -/
def brailleCanvas (s : Scene) : Except LayoutError Canvas :=
  if 0 ≤ s.canvas.w ∧ 0 ≤ s.canvas.h then
    .ok (Canvas.new (ceilDiv s.canvas.w 512).toNat (ceilDiv s.canvas.h 1024).toNat)
  else .error .domain

/-- The drawn canvas of a vector scene, before the labels are placed. -/
def drawCanvas (s : Scene) : Except LayoutError Canvas :=
  match brailleCanvas s with
  | .ok g => (Render.scenePrimitives s).foldlM drawPrimitive g
  | .error e => .error e

/-- The canvas of a vector scene after drawing and label placement, with the number of label
clusters that could not be written. Another profile is a domain error. -/
def renderCanvas (s : Scene) : Except LayoutError (Canvas × Nat) :=
  if s.profile = .vector then
    match drawCanvas s with
    | .ok g => .ok (Place.placeAll g (brailleLabels s))
    | .error e => .error e
  else .error .domain

end Elegant.Text.BrailleScene

namespace Elegant.Text

/-- Render a vector scene as braille text in a charset, with the number of label clusters that
could not be written. -/
def renderBraille (s : Scene) (charset : Charset) : Except LayoutError (String × Nat) :=
  match BrailleScene.renderCanvas s with
  | .ok (g, n) => .ok (Render.serialise charset g, n)
  | .error e => .error e

/-- Render a scene as text: a cell scene with the cell mapping, a vector scene with the braille
raster. -/
def renderScene (s : Scene) (charset : Charset) : Except LayoutError (String × Nat) :=
  match s.profile with
  | .cell => render s charset
  | .vector => renderBraille s charset

end Elegant.Text

namespace Elegant.Text

/-- `g'` follows `g` by dot writes: the size is kept, every changed cell is on the canvas, and
no arm mask, symbol, or label changes. -/
def Canvas.Dotting (g g' : Canvas) : Prop :=
  g.Confined g' ∧ ∀ c r, (g'.cellAt c r).mask = (g.cellAt c r).mask ∧
    (g'.cellAt c r).symbol = (g.cellAt c r).symbol ∧
    (g'.cellAt c r).label = (g.cellAt c r).label

theorem dotting_refl (g : Canvas) : g.Dotting g :=
  ⟨confined_refl g, fun _ _ => ⟨rfl, rfl, rfl⟩⟩

theorem dotting_trans {g g' g'' : Canvas} (h : g.Dotting g') (h' : g'.Dotting g'') :
    g.Dotting g'' := by
  refine ⟨confined_trans h.1 h'.1, fun c r => ?_⟩
  obtain ⟨a1, a2, a3⟩ := h.2 c r
  obtain ⟨b1, b2, b3⟩ := h'.2 c r
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3⟩

theorem putDot_dotting (g : Canvas) (d : Braille.Dot) : g.Dotting (Render.putDot g d) := by
  unfold Render.putDot
  refine ⟨put_confined g _ _ _, fun c' r' => ?_⟩
  rw [cellAt_put]
  by_cases e : g.Inside (Int.fdiv d.1 2) (Int.fdiv d.2 4) ∧ c' = Int.fdiv d.1 2 ∧
      r' = Int.fdiv d.2 4
  · simp only [e]
    exact ⟨rfl, rfl, rfl⟩
  · simp [e]

theorem foldl_dotting {α : Type} (step : Canvas → α → Canvas)
    (hstep : ∀ (g : Canvas) (a : α), g.Dotting (step g a)) :
    ∀ (l : List α) (g : Canvas), g.Dotting (l.foldl step g) := by
  intro l
  induction l with
  | nil => intro g; exact dotting_refl g
  | cons a l ih => intro g; exact dotting_trans (hstep g a) (ih (step g a))

theorem foldlM_dotting {α : Type} (f : Canvas → α → Except LayoutError Canvas)
    (hf : ∀ (g : Canvas) (a : α) (g' : Canvas), f g a = .ok g' → g.Dotting g') :
    ∀ (l : List α) (g g' : Canvas), l.foldlM f g = .ok g' → g.Dotting g' := by
  intro l
  induction l with
  | nil =>
    intro g g' h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact dotting_refl g
  | cons a l ih =>
    intro g g' h
    rw [List.foldlM_cons] at h
    cases hfa : f g a with
    | error e => simp [hfa, bind, Except.bind] at h
    | ok g1 =>
      simp only [hfa, bind, Except.bind] at h
      exact dotting_trans (hf g a g1 hfa) (ih g1 g' h)

theorem ite_dotting {b : Prop} [Decidable b] {g g' : Canvas} {m : Except LayoutError Canvas}
    (hm : m = .ok g' → g.Dotting g') (h : (if b then m else .ok g) = .ok g') : g.Dotting g' := by
  by_cases hb : b
  · simp only [hb, ↓reduceIte] at h
    exact hm h
  · simp only [hb, ↓reduceIte, Except.ok.injEq] at h
    subst h
    exact dotting_refl g

namespace BrailleScene

theorem putDots_dotting (g : Canvas) (ds : List Braille.Dot) : g.Dotting (putDots g ds) :=
  foldl_dotting Render.putDot putDot_dotting ds g

theorem strokeOn_dotting {g g' : Canvas} {pts : List Point} (h : strokeOn g pts = .ok g') :
    g.Dotting g' := by
  unfold strokeOn at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact putDots_dotting g _
  · simp at h

theorem fillOn_dotting {g g' : Canvas} {rings : List (List Point)}
    (h : fillOn g rings = .ok g') : g.Dotting g' := by
  unfold fillOn at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact putDots_dotting g _
  · simp at h

theorem polygonsOn_dotting {g g' : Canvas} {rings : List (List Point)} {p : Paint}
    (h : polygonsOn g rings p = .ok g') : g.Dotting g' := by
  unfold polygonsOn at h
  split at h
  · simp at h
  · rename_i g1 hg1
    have h1 : g.Dotting g1 := ite_dotting (fun hm => fillOn_dotting hm) hg1
    exact dotting_trans h1 (ite_dotting (fun hm => foldlM_dotting _
      (fun acc ring acc' ha => strokeOn_dotting ha) rings g1 g' hm) h)

theorem openOn_dotting {g g' : Canvas} {pts : List Point} {p : Paint}
    (h : openOn g pts p = .ok g') : g.Dotting g' := by
  unfold openOn at h
  exact ite_dotting (fun hm => strokeOn_dotting hm) h

theorem rectOn_dotting {g g' : Canvas} {r : Rect} {p : Paint} (h : rectOn g r p = .ok g') :
    g.Dotting g' := by
  unfold rectOn at h
  split at h
  · simp at h
  · by_cases hn : r.w < 0 ∨ r.h < 0
    · simp only [hn, ↓reduceIte, Except.ok.injEq] at h
      subst h
      exact dotting_refl g
    · simp only [hn, ↓reduceIte] at h
      exact polygonsOn_dotting h

theorem ellipseOn_dotting {g g' : Canvas} {cx cy rx ry : Int} {p : Paint}
    (h : ellipseOn g cx cy rx ry p = .ok g') : g.Dotting g' := by
  unfold ellipseOn at h
  by_cases hn : rx < 0 ∨ ry < 0
  · simp only [hn, ↓reduceIte, Except.ok.injEq] at h
    subst h
    exact dotting_refl g
  · simp only [hn, ↓reduceIte] at h
    split at h
    · exact polygonsOn_dotting h
    · simp at h

theorem pathOn_dotting {g g' : Canvas} {cmds : List PathCommand} {p : Paint}
    (h : pathOn g cmds p = .ok g') : g.Dotting g' := by
  unfold pathOn at h
  split at h
  · simp at h
  · rename_i w _
    dsimp only at h
    split at h
    · simp at h
    · rename_i g1 hg1
      have h1 : g.Dotting g1 := ite_dotting (fun hm => fillOn_dotting hm) hg1
      exact dotting_trans h1 (ite_dotting (fun hm => foldlM_dotting _
        (fun acc s acc' ha => strokeOn_dotting ha) _ g1 g' hm) h)

theorem markerOn_dotting {g g' : Canvas} {name : String} {pos : Point} {axis : MarkerAxis}
    (h : markerOn g name pos axis = .ok g') : g.Dotting g' := by
  unfold markerOn at h
  split at h
  · simp at h
  · rename_i m _
    by_cases hp : m.points.length < 2
    · simp [hp] at h
    · simp only [hp, ↓reduceIte] at h
      split at h
      · simp at h
      · by_cases ho : (m.paint == "open") = true
        · simp only [ho, ↓reduceIte] at h
          exact foldlM_dotting _ (fun acc c acc' ha => openOn_dotting ha) _ g g' h
        · simp only [ho] at h
          exact polygonsOn_dotting h

theorem drawPrimitive_dotting {g g' : Canvas} {p : Primitive} (h : drawPrimitive g p = .ok g') :
    g.Dotting g' := by
  cases p with
  | rect r p => exact rectOn_dotting h
  | roundRect r _ p => exact rectOn_dotting h
  | ellipse cx cy rx ry p => exact ellipseOn_dotting h
  | polygon pts p => exact polygonsOn_dotting h
  | polyline pts _ p => exact openOn_dotting h
  | path cmds p => exact pathOn_dotting h
  | text _ =>
    simp only [drawPrimitive, Except.ok.injEq] at h
    subst h
    exact dotting_refl g
  | markerRef name pos axis => exact markerOn_dotting h
  | symbolRef _ _ _ => simp [drawPrimitive] at h

theorem brailleCanvas_eq {s : Scene} {g : Canvas} (h : brailleCanvas s = .ok g) :
    g = Canvas.new (ceilDiv s.canvas.w 512).toNat (ceilDiv s.canvas.h 1024).toNat := by
  unfold brailleCanvas at h
  split at h
  · simp only [Except.ok.injEq] at h
    exact h.symm
  · simp at h

/-- The canvas of a vector scene has `ceil_div(w, 512)` columns and `ceil_div(h, 1024)` rows. -/
theorem braille_canvas_dims {s : Scene} {g : Canvas} (h : brailleCanvas s = .ok g) :
    g.W = (ceilDiv s.canvas.w 512).toNat ∧ g.H = (ceilDiv s.canvas.h 1024).toNat := by
  rw [brailleCanvas_eq h]
  exact ⟨rfl, rfl⟩

theorem drawCanvas_dotting {s : Scene} {g : Canvas} (h : drawCanvas s = .ok g) :
    ∃ g0, brailleCanvas s = .ok g0 ∧ g0.Dotting g := by
  unfold drawCanvas at h
  split at h
  · rename_i g0 hg0
    exact ⟨g0, hg0, foldlM_dotting drawPrimitive
      (fun acc a acc' ha => drawPrimitive_dotting ha) _ g0 g h⟩
  · simp at h

/-- Drawing writes dots only: every cell of the drawn canvas has no arm mask, no symbol, and no
label. -/
theorem braille_draw_plain {s : Scene} {g : Canvas} (h : drawCanvas s = .ok g) (c r : Int) :
    (g.cellAt c r).mask = 0 ∧ (g.cellAt c r).symbol = 0 ∧
      (g.cellAt c r).label = Label.empty := by
  obtain ⟨g0, hg0, hd⟩ := drawCanvas_dotting h
  obtain ⟨hm, hs, hl⟩ := hd.2 c r
  rw [brailleCanvas_eq hg0, new_cellAt] at hm hs hl
  exact ⟨hm.trans rfl, hs.trans rfl, hl.trans rfl⟩

/-- After the labels are placed on a drawn vector canvas, no cell holds text from two labels. -/
theorem braille_labels_disjoint {s : Scene} {g : Canvas} (h : drawCanvas s = .ok g) (c r : Int)
    (hl : ((Place.placeAll g (brailleLabels s)).1.cellAt c r).label ≠ Label.empty) :
    ∃ i, i < (brailleLabels s).length ∧ Place.Placed g (brailleLabels s) i c r ∧
      ∀ j, Place.Placed g (brailleLabels s) j c r → j = i := by
  obtain ⟨i, hi, hp, hu, _⟩ := Place.place_labels_disjoint g (brailleLabels s)
    (fun c r => (braille_draw_plain h c r).2.2) c r hl
  exact ⟨i, hi, hp, hu⟩

/-- A rendered vector canvas has the extent of the scene in columns and rows, no cell with an
arm mask or a symbol, and no cell with text from two labels. -/
theorem braille_text_valid {s : Scene} {g : Canvas} {n : Nat}
    (h : renderCanvas s = .ok (g, n)) :
    g.W = (ceilDiv s.canvas.w 512).toNat ∧ g.H = (ceilDiv s.canvas.h 1024).toNat ∧
      (∀ c r, (g.cellAt c r).mask = 0 ∧ (g.cellAt c r).symbol = 0) ∧
      ∃ gd, drawCanvas s = .ok gd ∧ ∀ c r, (g.cellAt c r).label ≠ Label.empty →
        ∃ i, i < (brailleLabels s).length ∧ Place.Placed gd (brailleLabels s) i c r ∧
          ∀ j, Place.Placed gd (brailleLabels s) j c r → j = i := by
  unfold renderCanvas at h
  split at h
  · split at h
    · rename_i gd hgd
      simp only [Except.ok.injEq] at h
      have hg : (Place.placeAll gd (brailleLabels s)).1 = g := congrArg Prod.fst h
      obtain ⟨g0, hg0, hd⟩ := drawCanvas_dotting hgd
      obtain ⟨hw, hh, hc⟩ := Place.placeCanvas_placing (brailleLabels s) gd
      have hdim := braille_canvas_dims hg0
      refine ⟨?_, ?_, fun c r => ?_, gd, hgd, fun c r hne => ?_⟩
      · rw [← hg]
        show (Place.placeCanvas gd (brailleLabels s)).W = _
        rw [hw, hd.1.1, hdim.1]
      · rw [← hg]
        show (Place.placeCanvas gd (brailleLabels s)).H = _
        rw [hh, hd.1.2.1, hdim.2]
      · obtain ⟨m, _, _, y, _, _⟩ := hc c r
        rw [← hg]
        have hp := braille_draw_plain hgd c r
        exact ⟨m.trans hp.1, y.trans hp.2.1⟩
      · rw [← hg] at hne
        exact braille_labels_disjoint hgd c r hne
    · simp at h
  · simp at h

end BrailleScene

end Elegant.Text

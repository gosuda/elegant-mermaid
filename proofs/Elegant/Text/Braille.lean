import ElegantGeometry.Basic
import ElegantGeometry.Trig
import Elegant.Text.Join

set_option autoImplicit false

/-! Braille raster of the text back end (`spec/render-cells.md`, requirements
render-cells-49 to render-cells-61 and render-cells-92 to render-cells-94).

Every rasteriser returns its dots as a list of `(dot column, dot row)` pairs. A dot may lie
off the canvas; the canvas drops it. The vertices of a shape are integer points in the
coordinates of the caller: units of 1/64 px for a vector scene, dots for a cell scene. -/

namespace Elegant.Text.Braille

/-- A dot as `(column, row)` in the dot grid. -/
abbrev Dot := Int × Int

/-- The smallest int64 value. -/
def I64_MIN : Int := -9223372036854775808

/-- The largest int64 value. -/
def I64_MAX : Int := 9223372036854775807

/-- The value fits int64, else the kernel overflow error. -/
def checkI64 (v : Int) : Except LayoutError Int :=
  if I64_MIN ≤ v ∧ v ≤ I64_MAX then .ok v else .error .overflow

/-- The value fits int32, else the kernel overflow error. -/
def checkI32 (v : Int) : Except LayoutError Int :=
  if I32_MIN ≤ v ∧ v ≤ I32_MAX then .ok v else .error .overflow

/-- A checked int64 product. -/
def mul (a b : Int) : Except LayoutError Int :=
  checkI64 (a * b)

/-- A checked int64 sum. -/
def add (a b : Int) : Except LayoutError Int :=
  checkI64 (a + b)

/-- A point whose coordinates fit int32. -/
def checkedPoint (x y : Int) : Except LayoutError Point :=
  if I32_MIN ≤ x ∧ x ≤ I32_MAX ∧ I32_MIN ≤ y ∧ y ≤ I32_MAX then .ok ⟨x, y⟩
  else .error .overflow

/-- The braille bit of dot `(i, j)` inside its cell:
`(0,0)` 0x01, `(0,1)` 0x02, `(0,2)` 0x04, `(1,0)` 0x08, `(1,1)` 0x10, `(1,2)` 0x20,
`(0,3)` 0x40, `(1,3)` 0x80. -/
def bit (i j : Int) : Nat :=
  ([[0x01, 0x02, 0x04, 0x40], [0x08, 0x10, 0x20, 0x80]].getD (Int.fmod i 2).toNat []).getD
    (Int.fmod j 4).toNat 0

/-- The glyph of a cell with the given dots: U+0020 for none, U+2800 plus the dots in the
unicode charset, and `#` in the ascii charset. -/
def glyph (charset : Charset) (dots : Nat) : Nat :=
  if dots = 0 then 0x20
  else match charset with
    | .unicode => 0x2800 + (dots &&& 0xFF)
    | .ascii => 0x23

/-- The eight dot positions of one cell, by column then row. -/
def cellDots : List Dot :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (0, 3), (1, 3)]

/-- The dots that a glyph of the braille block shows: the OR of the dot bits of the
positions whose bit is set in `g - 0x2800`. -/
def bitsOf (g : Nat) : Nat :=
  cellDots.foldl
    (fun acc d => if (bit d.1 d.2 &&& (g - 0x2800)) != 0 then acc ||| bit d.1 d.2 else acc) 0

/-- The point `(x, y)` in cells as the dot `(2x, 4y + 2)`, as the cell profile maps it. -/
def cellDot (p : Point) : Except LayoutError Dot :=
  match checkedPoint (2 * p.x) (4 * p.y + 2) with
  | .ok q => .ok (q.x, q.y)
  | .error e => .error e

/-- A vertex in units as the dot that holds it. -/
def unitDot (p : Point) : Dot :=
  (Int.fdiv p.x 256, Int.fdiv p.y 256)

/-- The vertices of an arc with integer centre, radius, start angle, and sweep, the angles
in 1/65536 turn. -/
def arc (center : Point) (radius start sweep : Int) : Except LayoutError (List Point) :=
  let n : Nat := max 4 ((sweep.natAbs + 1023) / 1024)
  (List.range (n + 1)).mapM fun (k : Nat) =>
    let a := start + Int.fdiv (sweep * (k : Int)) (n : Int)
    checkedPoint (center.x + Int.fdiv (2 * radius * cosQ15 a + 32768) 65536)
      (center.y + Int.fdiv (2 * radius * sinQ15 a + 32768) 65536)

/-- The 64 vertices of an ellipse with integer centre and radii. -/
def ellipse (center : Point) (rx ry : Int) : Except LayoutError (List Point) :=
  (List.range 64).mapM fun (j : Nat) =>
    let a : Int := (j : Int) * 1024
    checkedPoint (center.x + Int.fdiv (rx * cosQ15 a) 32768)
      (center.y - Int.fdiv (ry * sinQ15 a) 32768)

/-- One axis of the cubic: the Bernstein sum over sixteenths, rounded half up. -/
def cubicAxis (v0 v1 v2 v3 k : Int) : Int :=
  let t := 16 - k
  Int.fdiv (t * t * t * v0 + 3 * k * t * t * v1 + 3 * k * k * t * v2 + k * k * k * v3 + 2048)
    4096

/-- The 17 vertices of the 16 straight segments of a cubic. -/
def cubic (p0 p1 p2 p3 : Point) : Except LayoutError (List Point) :=
  (List.range 17).mapM fun (k : Nat) =>
    let kk : Int := (k : Int)
    checkedPoint (cubicAxis p0.x p1.x p2.x p3.x kk) (cubicAxis p0.y p1.y p2.y p3.y kk)

/-- Integer Bresenham from `(x, y)` towards `(tx, ty)`: set the dot, stop at the target,
otherwise step. `dx` is `|tx - x0|`, `dy` is `-|ty - y0|`, `err` starts at `dx + dy`, and the
fuel is `|dx| + |dy| + 1`. -/
def bresenham (tx ty dx dy sx sy : Int) : Nat → Int → Int → Int → List Dot
  | 0, _, _, _ => []
  | fuel + 1, x, y, err =>
    (x, y) :: (if x = tx ∧ y = ty then [] else
      bresenham tx ty dx dy sx sy fuel
        (if 2 * err ≥ dy then x + sx else x)
        (if 2 * err ≤ dx then y + sy else y)
        ((if 2 * err ≥ dy then err + dy else err) + (if 2 * err ≤ dx then dx else 0)))

/-- The dots of the Bresenham line between two dots. Coordinates outside int32 overflow. -/
def line (a b : Dot) : Except LayoutError (List Dot) :=
  if I32_MIN ≤ a.1 ∧ a.1 ≤ I32_MAX ∧ I32_MIN ≤ a.2 ∧ a.2 ≤ I32_MAX ∧
      I32_MIN ≤ b.1 ∧ b.1 ≤ I32_MAX ∧ I32_MIN ≤ b.2 ∧ b.2 ≤ I32_MAX then
    let dx : Int := ((b.1 - a.1).natAbs : Int)
    let dy : Int := -((b.2 - a.2).natAbs : Int)
    .ok (bresenham b.1 b.2 dx dy (if a.1 < b.1 then 1 else -1) (if a.2 < b.2 then 1 else -1)
      (dx - dy + 1).toNat a.1 a.2 (dx + dy))
  else .error .overflow

/-- The dots of a polyline given in dot space, one Bresenham line per pair of vertices. -/
def strokeDots (pts : List Dot) : Except LayoutError (List Dot) :=
  match (consecutivePairs pts).mapM fun e => line e.1 e.2 with
  | .ok ls => .ok ls.flatten
  | .error e => .error e

/-- The dots of a polyline given in units: each vertex maps to the dot `floor_div(v, 256)`. -/
def stroke (pts : List Point) : Except LayoutError (List Dot) :=
  strokeDots (pts.map unitDot)

/-- The dots of a polyline given in cells, each vertex mapped by `cellDot`. -/
def strokeCells (pts : List Point) : Except LayoutError (List Dot) :=
  match pts.mapM cellDot with
  | .ok ds => strokeDots ds
  | .error e => .error e

/-- The edges of the closed polygon, including the edge from the last vertex to the first. -/
def edges (pts : List Point) : List (Point × Point) :=
  match pts with
  | [] => []
  | v :: _ => consecutivePairs (pts ++ [v])

/-- The half-open crossing test of one edge for the sample `(px, py)`, with checked int64
products. -/
def crosses (a b : Point) (px py : Int) : Except LayoutError Bool :=
  if (a.y ≤ py ∧ py < b.y) ∨ (b.y ≤ py ∧ py < a.y) then
    match mul (b.x - a.x) (py - a.y) with
    | .error e => .error e
    | .ok u =>
      match mul (a.x - px) (b.y - a.y) with
      | .error e => .error e
      | .ok v =>
        match add u v with
        | .error e => .error e
        | .ok s =>
          match mul s (b.y - a.y) with
          | .error e => .error e
          | .ok n => .ok (decide (0 < n))
  else .ok false

/-- One edge of the even-odd test: flip the parity when the edge is counted. -/
def crossStep (px py : Int) (acc : Bool) (e : Point × Point) : Except LayoutError Bool :=
  match crosses e.1 e.2 px py with
  | .ok c => .ok (bne acc c)
  | .error err => .error err

/-- Even-odd test: the sample is inside when an odd number of edges are counted. -/
def polygonInside (pts : List Point) (px py : Int) : Except LayoutError Bool :=
  (edges pts).foldlM (crossStep px py) false

/-- The integers from `lo` to `hi` inclusive. -/
def intRange (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map fun (k : Nat) => lo + (k : Int)

/-- The sample point of dot `(i, j)` is `(256 i + 128, 256 j + 128)` in units. -/
def sample (d : Dot) : Int × Int :=
  (256 * d.1 + 128, 256 * d.2 + 128)

/-- The dots of the list whose sample point is inside the polygon. -/
def keepInside (pts : List Point) : List Dot → Except LayoutError (List Dot)
  | [] => .ok []
  | d :: ds =>
    match polygonInside pts (sample d).1 (sample d).2 with
    | .error e => .error e
    | .ok inside =>
      match keepInside pts ds with
      | .error e => .error e
      | .ok rest => .ok (if inside then d :: rest else rest)

/-- The extreme vertex coordinates `(min x, max x, min y, max y)` of a non-empty list. -/
def bounds : List Point → Option (Int × Int × Int × Int)
  | [] => none
  | p :: ps =>
    some (ps.foldl
      (fun m q => (min m.1 q.x, max m.2.1 q.x, min m.2.2.1 q.y, max m.2.2.2 q.y))
      (p.x, p.x, p.y, p.y))

/-- The dots whose sample point is inside the polygon. The candidates are the dots whose cell
covers the bounding box of the vertices; every dot that is set has its sample point inside
that box. -/
def fill (pts : List Point) : Except LayoutError (List Dot) :=
  match bounds pts with
  | none => .ok []
  | some (x0, x1, y0, y1) =>
    keepInside pts
      ((intRange (Int.fdiv y0 256) (Int.fdiv y1 256)).flatMap fun j =>
        (intRange (Int.fdiv x0 256) (Int.fdiv x1 256)).map fun i => (i, j))

set_option maxRecDepth 100000 in
/-- Every cell of 1 to 255 dots prints the braille glyph that shows exactly those dots, and
a cell with no dots prints U+0020. -/
theorem braille_bit_roundtrip :
    ∀ b, b < 256 →
      (b = 0 → glyph .unicode b = 0x20) ∧ (b ≠ 0 → bitsOf (glyph .unicode b) = b) := by
  decide

/-- Consecutive dots of a list are within one column and one row of each other. -/
def Connected : List Dot → Prop
  | p :: q :: t =>
    q.1 ≤ p.1 + 1 ∧ p.1 ≤ q.1 + 1 ∧ q.2 ≤ p.2 + 1 ∧ p.2 ≤ q.2 + 1 ∧ Connected (q :: t)
  | _ => True

theorem step_arith (a b dx D err : Int) (hdx : 0 ≤ dx) (hD : 0 ≤ D) (ha0 : 0 ≤ a)
    (hadx : a ≤ dx) (hb0 : 0 ≤ b) (hbD : b ≤ D) (herr : err = dx - D + a * D - b * dx)
    (hne : ¬(a = 0 ∧ b = 0)) :
    (2 * err ≥ -D → 1 ≤ a) ∧ (2 * err ≤ dx → 1 ≤ b) ∧ (2 * err ≥ -D ∨ 2 * err ≤ dx) := by
  refine ⟨fun hX => ?_, fun hY => ?_, by omega⟩
  · by_cases hlt : 1 ≤ a
    · exact hlt
    · exfalso
      have ha : a = 0 := by omega
      have hb : 1 ≤ b := by omega
      have h1 : dx ≤ b * dx := by
        have := Int.mul_le_mul_of_nonneg_right hb hdx
        simpa using this
      subst ha
      simp at herr
      omega
  · by_cases hlt : 1 ≤ b
    · exact hlt
    · exfalso
      have hb : b = 0 := by omega
      have ha : 1 ≤ a := by omega
      have h1 : D ≤ a * D := by
        have := Int.mul_le_mul_of_nonneg_right ha hD
        simpa using this
      subst hb
      simp at herr
      omega

theorem err_x (a b dx D err : Int) (herr : err = dx - D + a * D - b * dx) :
    err + -D = dx - D + (a - 1) * D - b * dx := by
  rw [herr, Int.sub_mul, Int.one_mul]
  omega

theorem err_y (a b dx D err : Int) (herr : err = dx - D + a * D - b * dx) :
    err + dx = dx - D + a * D - (b - 1) * dx := by
  rw [herr, Int.sub_mul, Int.one_mul]
  omega

theorem err_xy (a b dx D err : Int) (herr : err = dx - D + a * D - b * dx) :
    err + -D + dx = dx - D + (a - 1) * D - (b - 1) * dx := by
  rw [herr, Int.sub_mul, Int.sub_mul, Int.one_mul, Int.one_mul]
  omega

theorem bresenham_run (tx ty dx D sx sy : Int) (hdx : 0 ≤ dx) (hD : 0 ≤ D)
    (hsx : sx = 1 ∨ sx = -1) (hsy : sy = 1 ∨ sy = -1) :
    ∀ (fuel : Nat) (x y err a b : Int), sx * (tx - x) = a → sy * (ty - y) = b →
      0 ≤ a → a ≤ dx → 0 ≤ b → b ≤ D → err = dx - D + a * D - b * dx → a + b < fuel →
      ∃ t, bresenham tx ty dx (-D) sx sy fuel x y err = (x, y) :: t ∧
        Connected ((x, y) :: t) ∧ (tx, ty) ∈ (x, y) :: t := by
  intro fuel
  induction fuel with
  | zero =>
    intro x y err a b _ _ ha0 _ hb0 _ _ hfuel
    omega
  | succ f ih =>
    intro x y err a b hxa hyb ha0 hadx hb0 hbD herr hfuel
    by_cases hend : x = tx ∧ y = ty
    · refine ⟨[], ?_, ?_, ?_⟩
      · simp [bresenham, hend]
      · simp [Connected]
      · simp [hend.1, hend.2]
    · have hne : ¬(a = 0 ∧ b = 0) := by
        rintro ⟨rfl, rfl⟩
        apply hend
        rcases hsx with rfl | rfl <;> rcases hsy with rfl | rfl <;> omega
      obtain ⟨hX1, hY1, hXY⟩ := step_arith a b dx D err hdx hD ha0 hadx hb0 hbD herr hne
      by_cases hX : 2 * err ≥ -D <;> by_cases hY : 2 * err ≤ dx
      · have ha1 := hX1 hX
        have hb1 := hY1 hY
        obtain ⟨t, ht, hc, hm⟩ := ih (x + sx) (y + sy) (err + -D + dx) (a - 1) (b - 1)
          (by rcases hsx with rfl | rfl <;> omega) (by rcases hsy with rfl | rfl <;> omega)
          (by omega) (by omega) (by omega) (by omega) (err_xy a b dx D err herr) (by omega)
        refine ⟨(x + sx, y + sy) :: t, ?_, ?_, ?_⟩
        · simp only [bresenham, hend, hX, hY, ↓reduceIte]
          rw [ht]
        · refine ⟨?_, ?_, ?_, ?_, hc⟩ <;> simp <;> rcases hsx with rfl | rfl <;>
            rcases hsy with rfl | rfl <;> omega
        · exact List.mem_cons_of_mem _ hm
      · have ha1 := hX1 hX
        obtain ⟨t, ht, hc, hm⟩ := ih (x + sx) y (err + -D) (a - 1) b
          (by rcases hsx with rfl | rfl <;> omega) hyb
          (by omega) (by omega) (by omega) (by omega) (err_x a b dx D err herr) (by omega)
        refine ⟨(x + sx, y) :: t, ?_, ?_, ?_⟩
        · simp only [bresenham, hend, hX, hY, ↓reduceIte, Int.add_zero]
          rw [ht]
        · refine ⟨?_, ?_, ?_, ?_, hc⟩ <;> simp <;> rcases hsx with rfl | rfl <;> omega
        · exact List.mem_cons_of_mem _ hm
      · have hb1 := hY1 hY
        obtain ⟨t, ht, hc, hm⟩ := ih x (y + sy) (err + dx) a (b - 1) hxa
          (by rcases hsy with rfl | rfl <;> omega)
          (by omega) (by omega) (by omega) (by omega) (err_y a b dx D err herr) (by omega)
        refine ⟨(x, y + sy) :: t, ?_, ?_, ?_⟩
        · simp only [bresenham, hend, hX, hY, ↓reduceIte]
          rw [ht]
        · refine ⟨?_, ?_, ?_, ?_, hc⟩ <;> simp <;> rcases hsy with rfl | rfl <;> omega
        · exact List.mem_cons_of_mem _ hm
      · omega

/-- The Bresenham dots contain both endpoints, and consecutive dots differ by at most one
column and one row. -/
theorem line_raster_connected (a b : Dot) (ds : List Dot) (h : line a b = .ok ds) :
    a ∈ ds ∧ b ∈ ds ∧ Connected ds := by
  unfold line at h
  split at h
  · simp only [Except.ok.injEq] at h
    have hmul := Int.mul_comm ((b.1 - a.1).natAbs : Int) ((b.2 - a.2).natAbs : Int)
    obtain ⟨t, ht, hc, hm⟩ := bresenham_run b.1 b.2 ((b.1 - a.1).natAbs : Int)
      ((b.2 - a.2).natAbs : Int) (if a.1 < b.1 then 1 else -1) (if a.2 < b.2 then 1 else -1)
      (by omega) (by omega) (by split <;> simp) (by split <;> simp)
      (((b.1 - a.1).natAbs : Int) - -((b.2 - a.2).natAbs : Int) + 1).toNat a.1 a.2
      (((b.1 - a.1).natAbs : Int) + -((b.2 - a.2).natAbs : Int)) ((b.1 - a.1).natAbs : Int)
      ((b.2 - a.2).natAbs : Int) (by split <;> omega) (by split <;> omega)
      (by omega) (by omega) (by omega) (by omega) (by rw [hmul]; omega) (by omega)
    rw [← h, ht]
    exact ⟨List.mem_cons_self, hm, hc⟩
  · simp at h

/-- The pure value of the crossing test of one edge. -/
def crossP (a b : Point) (px py : Int) : Bool :=
  decide (((a.y ≤ py ∧ py < b.y) ∨ (b.y ≤ py ∧ py < a.y)) ∧
    0 < ((b.x - a.x) * (py - a.y) + (a.x - px) * (b.y - a.y)) * (b.y - a.y))

theorem mul_ok {a b v : Int} (h : mul a b = .ok v) : v = a * b := by
  unfold mul checkI64 at h
  split at h
  · simp only [Except.ok.injEq] at h
    exact h.symm
  · simp at h

theorem add_ok {a b v : Int} (h : add a b = .ok v) : v = a + b := by
  unfold add checkI64 at h
  split at h
  · simp only [Except.ok.injEq] at h
    exact h.symm
  · simp at h

theorem crosses_ok {a b : Point} {px py : Int} {r : Bool} (h : crosses a b px py = .ok r) :
    r = crossP a b px py := by
  unfold crosses at h
  by_cases hy : (a.y ≤ py ∧ py < b.y) ∨ (b.y ≤ py ∧ py < a.y)
  · simp only [hy, ↓reduceIte] at h
    cases h1 : mul (b.x - a.x) (py - a.y) with
    | error e => simp [h1] at h
    | ok u =>
      cases h2 : mul (a.x - px) (b.y - a.y) with
      | error e => simp [h1, h2] at h
      | ok v =>
        cases h3 : add u v with
        | error e => simp [h1, h2, h3] at h
        | ok s =>
          cases h4 : mul s (b.y - a.y) with
          | error e => simp [h1, h2, h3, h4] at h
          | ok n =>
            simp only [h1, h2, h3, h4, Except.ok.injEq] at h
            have eu := mul_ok h1
            have ev := mul_ok h2
            have es := add_ok h3
            have en := mul_ok h4
            subst h
            unfold crossP
            simp [hy, en, es, eu, ev]
  · simp only [hy, ↓reduceIte, Except.ok.injEq] at h
    subst h
    unfold crossP
    simp [hy]

theorem foldlM_cross (px py : Int) :
    ∀ (es : List (Point × Point)) (acc r : Bool), es.foldlM (crossStep px py) acc = .ok r →
      r = es.foldl (fun acc e => bne acc (crossP e.1 e.2 px py)) acc := by
  intro es
  induction es with
  | nil =>
    intro acc r h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    simp [h]
  | cons e es ih =>
    intro acc r h
    rw [List.foldlM_cons] at h
    unfold crossStep at h
    cases hc : crosses e.1 e.2 px py with
    | error err => simp [hc, bind, Except.bind] at h
    | ok c =>
      simp only [hc, bind, Except.bind] at h
      have := ih (bne acc c) r h
      rw [this, List.foldl_cons, crosses_ok hc]

theorem polygonInside_pure {pts : List Point} {px py : Int} {r : Bool}
    (h : polygonInside pts px py = .ok r) :
    r = (edges pts).foldl (fun acc e => bne acc (crossP e.1 e.2 px py)) false :=
  foldlM_cross px py (edges pts) false r h

theorem intercept_right (x1 x2 px t d : Int) (ht : 0 ≤ t) (htd : t < d)
    (hpx : max x1 x2 ≤ px) :
    (x2 - x1) * t + (x1 - px) * d ≤ 0 := by
  have h1 : (x2 - x1) * t ≤ (px - x1) * t := Int.mul_le_mul_of_nonneg_right (by omega) ht
  have h2 : (px - x1) * t ≤ (px - x1) * d := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  have h3 : (x1 - px) * d = -((px - x1) * d) := by rw [← Int.neg_sub, Int.neg_mul]
  omega

theorem intercept_right' (x1 x2 px t d : Int) (ht : t < 0) (hdt : d ≤ t)
    (hpx : max x1 x2 ≤ px) :
    0 ≤ (x2 - x1) * t + (x1 - px) * d := by
  have h1 : (px - x1) * t ≤ (x2 - x1) * t :=
    Int.mul_le_mul_of_nonpos_right (by omega) (by omega)
  have h2 : (px - x1) * d ≤ (px - x1) * t := Int.mul_le_mul_of_nonneg_left hdt (by omega)
  have h3 : (x1 - px) * d = -((px - x1) * d) := by rw [← Int.neg_sub, Int.neg_mul]
  omega

/-- A counted edge crosses the scanline to the right of the sample. -/
theorem crossP_true_right {a b : Point} {px py : Int} (h : crossP a b px py = true) :
    ((a.y ≤ py ∧ py < b.y) ∨ (b.y ≤ py ∧ py < a.y)) ∧ px < max a.x b.x := by
  unfold crossP at h
  rw [decide_eq_true_eq] at h
  obtain ⟨hy, hn⟩ := h
  refine ⟨hy, ?_⟩
  by_cases hpx : max a.x b.x ≤ px
  · exfalso
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := intercept_right a.x b.x px (py - a.y) (b.y - a.y) (by omega) (by omega) hpx
      have h3 : ((b.x - a.x) * (py - a.y) + (a.x - px) * (b.y - a.y)) * (b.y - a.y) ≤ 0 := by
        have := Int.mul_le_mul_of_nonneg_right this (show 0 ≤ b.y - a.y by omega)
        omega
      omega
    · have := intercept_right' a.x b.x px (py - a.y) (b.y - a.y) (by omega) (by omega) hpx
      have h3 : ((b.x - a.x) * (py - a.y) + (a.x - px) * (b.y - a.y)) * (b.y - a.y) ≤ 0 := by
        have := Int.mul_le_mul_of_nonpos_right this (show b.y - a.y ≤ 0 by omega)
        omega
      omega
  · omega

/-- An edge that spans the scanline, with both ends to the right of the sample, is counted. -/
theorem crossP_true_left {a b : Point} {px py : Int} (ha : px < a.x) (hb : px < b.x)
    (hy : (a.y ≤ py ∧ py < b.y) ∨ (b.y ≤ py ∧ py < a.y)) : crossP a b px py = true := by
  unfold crossP
  rw [decide_eq_true_eq]
  refine ⟨hy, ?_⟩
  have hid : (b.x - a.x) * (py - a.y) + (a.x - px) * (b.y - a.y) =
      (a.x - px) * (b.y - py) + (b.x - px) * (py - a.y) := by
    grind
  rw [hid]
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have p1 : 1 * 1 ≤ (a.x - px) * (b.y - py) :=
      Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
    have p2 : 0 ≤ (b.x - px) * (py - a.y) := Int.mul_nonneg (by omega) (by omega)
    exact Int.mul_pos (by omega) (by omega)
  · have p1 : (a.x - px) * (b.y - py) ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    have p2 : (b.x - px) * (py - a.y) ≤ 1 * (py - a.y) :=
      Int.mul_le_mul_of_nonpos_right (by omega) (by omega)
    exact Int.mul_pos_of_neg_of_neg (by omega) (by omega)

theorem crossP_eq_parity {a b : Point} {px py : Int} (ha : px < a.x) (hb : px < b.x) :
    crossP a b px py = bne (decide (a.y ≤ py)) (decide (b.y ≤ py)) := by
  by_cases hy : (a.y ≤ py ∧ py < b.y) ∨ (b.y ≤ py ∧ py < a.y)
  · rw [crossP_true_left ha hb hy]
    by_cases h1 : a.y ≤ py <;> by_cases h2 : b.y ≤ py <;> simp [h1, h2] <;> omega
  · have : crossP a b px py = false := by
      unfold crossP
      simp [hy]
    rw [this]
    by_cases h1 : a.y ≤ py <;> by_cases h2 : b.y ≤ py <;> simp [h1, h2] <;> omega

/-- The last element of the non-empty list `a :: t`. -/
def lastOf {α : Type} : α → List α → α
  | a, [] => a
  | _, c :: t => lastOf c t

theorem lastOf_append_singleton {α : Type} (x : α) : ∀ (t : List α) (a : α),
    lastOf a (t ++ [x]) = x := by
  intro t
  induction t with
  | nil => intro a; rfl
  | cons c t ih => intro a; exact ih c

theorem bne_chain (b x y z : Bool) : bne (bne b (bne x y)) (bne y z) = bne b (bne x z) := by
  cases b <;> cases x <;> cases y <;> cases z <;> rfl

theorem parity_pairs (s : Point → Bool) : ∀ (t : List Point) (a : Point) (b : Bool),
    (consecutivePairs (a :: t)).foldl (fun acc e => bne acc (bne (s e.1) (s e.2))) b =
      bne b (bne (s a) (s (lastOf a t))) := by
  intro t
  induction t with
  | nil =>
    intro a b
    simp [consecutivePairs, lastOf]
  | cons c t ih =>
    intro a b
    simp only [consecutivePairs, List.foldl_cons, lastOf]
    rw [ih c (bne b (bne (s a) (s c)))]
    exact bne_chain b (s a) (s c) (s (lastOf c t))

theorem mem_consecutivePairs {α : Type} : ∀ (l : List α) (e : α × α),
    e ∈ consecutivePairs l → e.1 ∈ l ∧ e.2 ∈ l := by
  intro l
  induction l with
  | nil => intro e h; simp [consecutivePairs] at h
  | cons a rest ih =>
    intro e h
    cases rest with
    | nil => simp [consecutivePairs] at h
    | cons b t =>
      simp only [consecutivePairs, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · have := ih e h
        exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩

theorem mem_edges {pts : List Point} {e : Point × Point} (h : e ∈ edges pts) :
    e.1 ∈ pts ∧ e.2 ∈ pts := by
  cases pts with
  | nil => simp [edges] at h
  | cons v rest =>
    have := mem_consecutivePairs _ e h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at this
    simp only [List.mem_cons]
    exact ⟨this.1.elim id Or.inl, this.2.elim id Or.inl⟩

theorem edges_parity (py : Int) (pts : List Point) :
    (edges pts).foldl
      (fun acc e => bne acc (bne (decide (e.1.y ≤ py)) (decide (e.2.y ≤ py)))) false = false := by
  cases pts with
  | nil => rfl
  | cons v rest =>
    show (consecutivePairs ((v :: rest) ++ [v])).foldl _ false = false
    rw [List.cons_append, parity_pairs (fun p => decide (p.y ≤ py)) (rest ++ [v]) v false,
      lastOf_append_singleton]
    cases decide (v.y ≤ py) <;> rfl

theorem foldl_bne_congr {α : Type} (f g : α → Bool) :
    ∀ (es : List α) (b : Bool), (∀ e ∈ es, f e = g e) →
      es.foldl (fun acc e => bne acc (f e)) b = es.foldl (fun acc e => bne acc (g e)) b := by
  intro es
  induction es with
  | nil => intro b _; rfl
  | cons e es ih =>
    intro b h
    simp only [List.foldl_cons]
    rw [h e (List.mem_cons_self), ih (bne b (g e)) (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]

theorem foldl_bne_false {α : Type} (f : α → Bool) :
    ∀ (es : List α) (b : Bool), (∀ e ∈ es, f e = false) →
      es.foldl (fun acc e => bne acc (f e)) b = b := by
  intro es
  induction es with
  | nil => intro b _; rfl
  | cons e es ih =>
    intro b h
    simp only [List.foldl_cons]
    rw [h e (List.mem_cons_self)]
    simpa using ih b (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-- The point lies between the extreme vertex coordinates of the polygon on both axes. -/
def InBBox (pts : List Point) (px py : Int) : Prop :=
  (∃ p ∈ pts, p.x ≤ px) ∧ (∃ p ∈ pts, px ≤ p.x) ∧
    (∃ p ∈ pts, p.y ≤ py) ∧ (∃ p ∈ pts, py ≤ p.y)

theorem counted_edge {pts : List Point} {px py : Int} (h : polygonInside pts px py = .ok true) :
    ∃ e ∈ edges pts, crossP e.1 e.2 px py = true := by
  have hf := polygonInside_pure h
  by_cases hex : ∃ e ∈ edges pts, crossP e.1 e.2 px py = true
  · exact hex
  · exfalso
    have hall : ∀ e ∈ edges pts, crossP e.1 e.2 px py = false := fun e he => by
      by_cases hh : crossP e.1 e.2 px py = true
      · exact absurd ⟨e, he, hh⟩ hex
      · simpa using hh
    rw [foldl_bne_false _ (edges pts) false hall] at hf
    exact absurd hf (by decide)

theorem vertex_left {pts : List Point} {px py : Int} (h : polygonInside pts px py = .ok true) :
    ∃ p ∈ pts, p.x ≤ px := by
  have hf := polygonInside_pure h
  by_cases hlow : ∃ p ∈ pts, p.x ≤ px
  · exact hlow
  · exfalso
    have hall : ∀ p ∈ pts, px < p.x := fun p hp => by
      by_cases hh : p.x ≤ px
      · exact absurd ⟨p, hp, hh⟩ hlow
      · omega
    have hcong := foldl_bne_congr (fun e : Point × Point => crossP e.1 e.2 px py)
      (fun e : Point × Point => bne (decide (e.1.y ≤ py)) (decide (e.2.y ≤ py))) (edges pts)
      false fun e' he' =>
        crossP_eq_parity (a := e'.1) (b := e'.2) (hall _ (mem_edges he').1)
          (hall _ (mem_edges he').2)
    rw [hcong, edges_parity] at hf
    exact absurd hf (by decide)

theorem polygonInside_between {pts : List Point} {px py : Int}
    (h : polygonInside pts px py = .ok true) : InBBox pts px py := by
  obtain ⟨e, he, hc⟩ := counted_edge h
  obtain ⟨hy, hx⟩ := crossP_true_right hc
  obtain ⟨h1, h2⟩ := mem_edges he
  refine ⟨vertex_left h, ?_, ?_, ?_⟩
  · by_cases hab : px < e.1.x
    · exact ⟨e.1, h1, by omega⟩
    · exact ⟨e.2, h2, by omega⟩
  · rcases hy with ⟨k1, _⟩ | ⟨k1, _⟩
    · exact ⟨e.1, h1, k1⟩
    · exact ⟨e.2, h2, k1⟩
  · rcases hy with ⟨_, k2⟩ | ⟨_, k2⟩
    · exact ⟨e.2, h2, by omega⟩
    · exact ⟨e.1, h1, by omega⟩

theorem keepInside_mem (pts : List Point) : ∀ (ds r : List Dot), keepInside pts ds = .ok r →
    ∀ d ∈ r, polygonInside pts (sample d).1 (sample d).2 = .ok true := by
  intro ds
  induction ds with
  | nil =>
    intro r h d hd
    simp only [keepInside, Except.ok.injEq] at h
    subst h
    simp at hd
  | cons d0 ds ih =>
    intro r h d hd
    unfold keepInside at h
    cases hp : polygonInside pts (sample d0).1 (sample d0).2 with
    | error e => simp [hp] at h
    | ok inside =>
      cases hk : keepInside pts ds with
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

/-- A dot set by the fill has its sample point inside the bounding box of the vertices. -/
theorem fill_raster_inside (pts : List Point) (dots : List Dot) (h : fill pts = .ok dots)
    (d : Dot) (hd : d ∈ dots) : InBBox pts (sample d).1 (sample d).2 := by
  unfold fill at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    simp at hd
  · exact polygonInside_between (keepInside_mem pts _ dots h d hd)

end Elegant.Text.Braille

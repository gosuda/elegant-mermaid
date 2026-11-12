import ElegantGeometry.Basic

set_option autoImplicit false

/-! Cell canvas of the text back end (`spec/render-cells.md`, requirements
render-cells-02 to render-cells-11 and render-cells-85 to render-cells-87).

A canvas holds `W` columns and `H` rows of cells. Every write goes through `Canvas.put`,
which applies its function only to an on-canvas cell. -/

namespace Elegant.Text

/-- Arm bit north. -/
def bitN : Nat := 1

/-- Arm bit east. -/
def bitE : Nat := 2

/-- Arm bit south. -/
def bitS : Nat := 4

/-- Arm bit west. -/
def bitW : Nat := 8

/-- Line style code `none`. -/
def styleNone : Nat := 0

/-- Line style code `dotted`. -/
def styleDotted : Nat := 1

/-- Line style code `rounded`. -/
def styleRounded : Nat := 2

/-- Line style code `light`. -/
def styleLight : Nat := 3

/-- Line style code `heavy`. -/
def styleHeavy : Nat := 4

/-- Line style code `double`. -/
def styleDouble : Nat := 5

/-- The cell width of a written grapheme cluster. -/
inductive ClusterWidth where
  | one
  | two
  deriving DecidableEq, Repr

/-- The width in cells. -/
def ClusterWidth.toNat : ClusterWidth → Nat
  | .one => 1
  | .two => 2

/-- The text of a cell: nothing, the first cell of a written cluster with its cell width,
or the continuation marker of the second cell of a width-2 cluster. -/
inductive Label where
  | empty
  | cluster (text : String) (width : ClusterWidth)
  | cont
  deriving DecidableEq, Repr

/-- One canvas cell. `mask` holds four arm bits, `style` a line style code from 0 to 5,
`dots` eight braille bits, and `symbol` is 0 or one code point. -/
structure Cell where
  mask : Nat := 0
  style : Nat := 0
  dots : Nat := 0
  label : Label := .empty
  symbol : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The blank cell. -/
def Cell.empty : Cell := {}

/-- OR the masks, take the larger style, OR the dots, take the larger symbol, and keep the
label of the first cell. -/
def mergeCell (a b : Cell) : Cell :=
  { a with
    mask := a.mask ||| b.mask
    style := max a.style b.style
    dots := a.dots ||| b.dots
    symbol := max a.symbol b.symbol }

/-- Merge every cell of a list into the blank cell. -/
def mergeAll (l : List Cell) : Cell :=
  l.foldl mergeCell Cell.empty

theorem mergeCell_right_comm (z x y : Cell) :
    mergeCell (mergeCell z x) y = mergeCell (mergeCell z y) x := by
  simp only [mergeCell, Cell.mk.injEq]
  refine ⟨?_, ?_, ?_, trivial, ?_⟩
  · rw [Nat.or_assoc, Nat.or_assoc, Nat.or_comm x.mask y.mask]
  · omega
  · rw [Nat.or_assoc, Nat.or_assoc, Nat.or_comm x.dots y.dots]
  · omega

/-- Merging a list of cells into the blank cell does not depend on the order. -/
theorem canvas_merge_order_independent {l₁ l₂ : List Cell} (h : l₁.Perm l₂) :
    mergeAll l₁ = mergeAll l₂ :=
  h.foldl_eq' (fun _ _ _ _ z => mergeCell_right_comm z _ _) Cell.empty

/-- A canvas of `W` columns and `H` rows, stored row by row. -/
structure Canvas where
  W : Nat
  H : Nat
  cells : Array Cell
  size_eq : cells.size = W * H

/-- A blank canvas. -/
def Canvas.new (w h : Nat) : Canvas :=
  { W := w, H := h, cells := Array.replicate (w * h) Cell.empty, size_eq := by simp }

/-- The position `(c, r)` lies on the canvas. -/
def Canvas.Inside (g : Canvas) (c r : Int) : Prop :=
  0 ≤ c ∧ c < g.W ∧ 0 ≤ r ∧ r < g.H

instance (g : Canvas) (c r : Int) : Decidable (g.Inside c r) := by
  unfold Canvas.Inside
  infer_instance

/-- The position of cell `(c, r)` in the row-major array. -/
def Canvas.index (g : Canvas) (c r : Int) : Nat :=
  r.toNat * g.W + c.toNat

/-- The cell at `(c, r)`, or the blank cell off the canvas. The specification writes this
as `at`, which is a Lean keyword. -/
def Canvas.cellAt (g : Canvas) (c r : Int) : Cell :=
  if g.Inside c r then (g.cells[g.index c r]?).getD Cell.empty else Cell.empty

/-- Apply `f` to the cell at `(c, r)` when it is on the canvas, and change nothing otherwise. -/
def Canvas.put (g : Canvas) (c r : Int) (f : Cell → Cell) : Canvas :=
  if g.Inside c r then
    { g with
      cells := g.cells.modify (g.index c r) f
      size_eq := by rw [Array.size_modify]; exact g.size_eq }
  else g

/-- Set the symbol to the larger of the current symbol and `s`. -/
def Canvas.putSymbol (g : Canvas) (c r : Int) (s : Nat) : Canvas :=
  g.put c r fun cell => { cell with symbol := max cell.symbol s }

/-- OR arm bits `mask` into the cell and take the larger of the cell style and `style`. -/
def Canvas.attach (g : Canvas) (c r : Int) (mask style : Nat) : Canvas :=
  g.put c r fun cell => { cell with mask := cell.mask ||| mask, style := max cell.style style }

/-- Bit E on cells `x0..x1-1` and bit W on cells `x0+1..x1`; nothing unless `x0 < x1`. -/
def Canvas.hSegment (g : Canvas) (x0 x1 y : Int) (style : Nat) : Canvas :=
  (List.range (x1 - x0).toNat).foldl
    (fun g (i : Nat) => (g.attach (x0 + i) y bitE style).attach (x0 + i + 1) y bitW style) g

/-- Bit S on cells `y0..y1-1` and bit N on cells `y0+1..y1`; nothing unless `y0 < y1`. -/
def Canvas.vSegment (g : Canvas) (x y0 y1 : Int) (style : Nat) : Canvas :=
  (List.range (y1 - y0).toNat).foldl
    (fun g (i : Nat) => (g.attach x (y0 + i) bitS style).attach x (y0 + i + 1) bitN style) g

/-- An axis-aligned segment between two cells; a diagonal segment writes nothing. -/
def Canvas.segment (g : Canvas) (a b : Int × Int) (style : Nat) : Canvas :=
  if a.2 = b.2 then g.hSegment (min a.1 b.1) (max a.1 b.1) a.2 style
  else if a.1 = b.1 then g.vSegment a.1 (min a.2 b.2) (max a.2 b.2) style
  else g

/-- The consecutive pairs of a list. -/
def consecutivePairs {α : Type} : List α → List (α × α)
  | a :: b :: t => (a, b) :: consecutivePairs (b :: t)
  | _ => []

/-- A polyline as a list of segments. -/
def Canvas.polyline (g : Canvas) (pts : List (Int × Int)) (style : Nat) : Canvas :=
  (consecutivePairs pts).foldl (fun g e => g.segment e.1 e.2 style) g

theorem index_inj {r r' c c' w : Nat} (hc : c < w) (hc' : c' < w)
    (h : r * w + c = r' * w + c') : r = r' ∧ c = c' := by
  rcases Nat.lt_trichotomy r r' with hr | hr | hr
  · have : (r + 1) * w ≤ r' * w := Nat.mul_le_mul_right w hr
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · subst hr
    omega
  · have : (r' + 1) * w ≤ r * w := Nat.mul_le_mul_right w hr
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

theorem index_lt (g : Canvas) {c r : Int} (h : g.Inside c r) : g.index c r < g.W * g.H := by
  unfold Canvas.Inside at h
  unfold Canvas.index
  have h1 : (r.toNat + 1) * g.W ≤ g.H * g.W := Nat.mul_le_mul_right g.W (by omega)
  rw [Nat.add_mul, Nat.one_mul] at h1
  rw [Nat.mul_comm g.W g.H]
  omega

theorem index_eq_iff (g : Canvas) {c r c' r' : Int} (h : g.Inside c r) (h' : g.Inside c' r') :
    g.index c r = g.index c' r' ↔ c = c' ∧ r = r' := by
  unfold Canvas.Inside at h h'
  unfold Canvas.index
  constructor
  · intro e
    have := index_inj (r := r.toNat) (r' := r'.toNat) (c := c.toNat) (c' := c'.toNat)
      (w := g.W) (by omega) (by omega) e
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

theorem put_W (g : Canvas) (c r : Int) (f : Cell → Cell) : (g.put c r f).W = g.W := by
  unfold Canvas.put
  split <;> rfl

theorem put_H (g : Canvas) (c r : Int) (f : Cell → Cell) : (g.put c r f).H = g.H := by
  unfold Canvas.put
  split <;> rfl

theorem put_inside_iff (g : Canvas) (c r : Int) (f : Cell → Cell) (c' r' : Int) :
    (g.put c r f).Inside c' r' ↔ g.Inside c' r' := by
  unfold Canvas.Inside
  rw [put_W, put_H]

theorem put_index (g : Canvas) (c r : Int) (f : Cell → Cell) (c' r' : Int) :
    (g.put c r f).index c' r' = g.index c' r' := by
  unfold Canvas.index
  rw [put_W]

theorem put_cells (g : Canvas) {c r : Int} (f : Cell → Cell) (h : g.Inside c r) :
    (g.put c r f).cells = g.cells.modify (g.index c r) f := by
  unfold Canvas.put
  simp [h]

theorem cellAt_put (g : Canvas) (c r : Int) (f : Cell → Cell) (c' r' : Int) :
    (g.put c r f).cellAt c' r' =
      if g.Inside c r ∧ c' = c ∧ r' = r then f (g.cellAt c r) else g.cellAt c' r' := by
  by_cases h : g.Inside c r
  · by_cases h' : g.Inside c' r'
    · unfold Canvas.cellAt
      simp only [(put_inside_iff g c r f c' r').mpr h', h', ↓reduceIte, put_index, put_cells g f h]
      rw [Array.getElem?_modify]
      by_cases e : c' = c ∧ r' = r
      · obtain ⟨rfl, rfl⟩ := e
        have hlt : g.index c' r' < g.cells.size := by rw [g.size_eq]; exact index_lt g h
        simp [hlt, h]
      · have hne : g.index c r ≠ g.index c' r' := fun hh =>
          e ((index_eq_iff g h h').mp hh |>.imp Eq.symm Eq.symm)
        simp [hne, e, h]
    · have hne : ¬ (c' = c ∧ r' = r) := by
        rintro ⟨rfl, rfl⟩
        exact h' h
      have h'' : ¬ (g.put c r f).Inside c' r' := fun hh => h' ((put_inside_iff g c r f c' r').mp hh)
      unfold Canvas.cellAt
      simp [h'', h', hne]
  · have : g.put c r f = g := by
      unfold Canvas.put
      simp [h]
    rw [this]
    simp [h]

/-- A write changes only on-canvas cells. -/
theorem cells_inside_canvas (g : Canvas) (c r : Int) (f : Cell → Cell) (c' r' : Int)
    (h : (g.put c r f).cellAt c' r' ≠ g.cellAt c' r') :
    0 ≤ c' ∧ c' < g.W ∧ 0 ≤ r' ∧ r' < g.H := by
  rw [cellAt_put] at h
  by_cases e : g.Inside c r ∧ c' = c ∧ r' = r
  · obtain ⟨hi, rfl, rfl⟩ := e
    exact hi
  · simp only [e, ↓reduceIte] at h
    exact absurd rfl h

/-- `putSymbol` changes the symbol of one on-canvas cell and nothing else. -/
theorem putSymbol_changes_symbol_only (g : Canvas) (c r : Int) (s : Nat)
    (hc : 0 ≤ c ∧ c < g.W) (hr : 0 ≤ r ∧ r < g.H) (c' r' : Int)
    (_hc' : 0 ≤ c' ∧ c' < g.W) (_hr' : 0 ≤ r' ∧ r' < g.H) :
    ((c', r') ≠ (c, r) → (g.putSymbol c r s).cellAt c' r' = g.cellAt c' r') ∧
    ((g.putSymbol c r s).cellAt c r).mask = (g.cellAt c r).mask ∧
    ((g.putSymbol c r s).cellAt c r).style = (g.cellAt c r).style ∧
    ((g.putSymbol c r s).cellAt c r).dots = (g.cellAt c r).dots ∧
    ((g.putSymbol c r s).cellAt c r).label = (g.cellAt c r).label := by
  have hin : g.Inside c r := ⟨hc.1, hc.2, hr.1, hr.2⟩
  refine ⟨fun hne => ?_, ?_, ?_, ?_, ?_⟩ <;> unfold Canvas.putSymbol <;> rw [cellAt_put]
  · have : ¬ (g.Inside c r ∧ c' = c ∧ r' = r) := by
      rintro ⟨_, rfl, rfl⟩
      exact hne rfl
    simp only [this, ↓reduceIte]
  all_goals simp [hin]

/-- Every cell that differs between `g` and `g'` lies on the canvas of `g`, and the size is
kept. -/
def Canvas.Confined (g g' : Canvas) : Prop :=
  g'.W = g.W ∧ g'.H = g.H ∧ ∀ c r, g'.cellAt c r ≠ g.cellAt c r → g.Inside c r

theorem confined_refl (g : Canvas) : g.Confined g :=
  ⟨rfl, rfl, fun _ _ h => absurd rfl h⟩

theorem confined_trans {g g' g'' : Canvas} (h : g.Confined g') (h' : g'.Confined g'') :
    g.Confined g'' := by
  obtain ⟨hw, hh, hc⟩ := h
  obtain ⟨hw', hh', hc'⟩ := h'
  refine ⟨by omega, by omega, fun c r hne => ?_⟩
  by_cases e : g''.cellAt c r = g'.cellAt c r
  · rw [e] at hne
    exact hc c r hne
  · have hi := hc' c r e
    unfold Canvas.Inside at hi ⊢
    omega

theorem put_confined (g : Canvas) (c r : Int) (f : Cell → Cell) : g.Confined (g.put c r f) :=
  ⟨put_W g c r f, put_H g c r f, fun c' r' h => cells_inside_canvas g c r f c' r' h⟩

theorem foldl_confined {α : Type} (step : Canvas → α → Canvas)
    (hstep : ∀ (g : Canvas) (a : α), g.Confined (step g a)) :
    ∀ (l : List α) (g : Canvas), g.Confined (l.foldl step g) := by
  intro l
  induction l with
  | nil => intro g; exact confined_refl g
  | cons a l ih => intro g; exact confined_trans (hstep g a) (ih (step g a))

theorem attach_confined (g : Canvas) (c r : Int) (mask style : Nat) :
    g.Confined (g.attach c r mask style) :=
  put_confined g c r _

theorem hSegment_confined (g : Canvas) (x0 x1 y : Int) (style : Nat) :
    g.Confined (g.hSegment x0 x1 y style) :=
  foldl_confined _ (fun g _ => confined_trans (attach_confined g _ _ _ _)
    (attach_confined _ _ _ _ _)) _ g

theorem vSegment_confined (g : Canvas) (x y0 y1 : Int) (style : Nat) :
    g.Confined (g.vSegment x y0 y1 style) :=
  foldl_confined _ (fun g _ => confined_trans (attach_confined g _ _ _ _)
    (attach_confined _ _ _ _ _)) _ g

theorem segment_confined (g : Canvas) (a b : Int × Int) (style : Nat) :
    g.Confined (g.segment a b style) := by
  unfold Canvas.segment
  split
  · exact hSegment_confined g _ _ _ _
  · split
    · exact vSegment_confined g _ _ _ _
    · exact confined_refl g

theorem polyline_confined (g : Canvas) (pts : List (Int × Int)) (style : Nat) :
    g.Confined (g.polyline pts style) :=
  foldl_confined (fun (g : Canvas) (e : (Int × Int) × (Int × Int)) => g.segment e.1 e.2 style)
    (fun g e => segment_confined g e.1 e.2 style) _ g

/-- A segment writes only on-canvas cells. -/
theorem segment_cells_inside_canvas (g : Canvas) (a b : Int × Int) (style : Nat) (c' r' : Int)
    (h : (g.segment a b style).cellAt c' r' ≠ g.cellAt c' r') :
    0 ≤ c' ∧ c' < g.W ∧ 0 ≤ r' ∧ r' < g.H :=
  (segment_confined g a b style).2.2 c' r' h

/-- A polyline writes only on-canvas cells. -/
theorem polyline_cells_inside_canvas (g : Canvas) (pts : List (Int × Int)) (style : Nat)
    (c' r' : Int) (h : (g.polyline pts style).cellAt c' r' ≠ g.cellAt c' r') :
    0 ≤ c' ∧ c' < g.W ∧ 0 ≤ r' ∧ r' < g.H :=
  (polyline_confined g pts style).2.2 c' r' h

end Elegant.Text

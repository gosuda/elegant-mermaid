import Elegant.Chart.XY

set_option autoImplicit false

/-! Theorems of the xychart family (`spec/layout/charts.md`, charts-109): every plot box lies inside
the plot rectangle, every line point lies inside it, and the plot lies inside the canvas. The
statements are over the Lean functions that `geomcheck` runs. -/

namespace Elegant
namespace Chart
namespace XY

/-! ### Positions along an axis -/

theorem clampPosition_between (a : Axis) (v edge : Int) (h : a.r0 ≤ a.r1 - edge) :
    a.r0 ≤ a.clampPosition v edge ∧ a.clampPosition v edge ≤ a.r1 - edge := by
  unfold Axis.clampPosition
  have := clamp_between v a.r0 (a.r1 - edge)
  omega

theorem bandPos_between (a : Axis) (slot edge : Int) (h : a.r0 ≤ a.r1 - edge) :
    a.r0 ≤ a.bandPos slot edge ∧ a.bandPos slot edge ≤ a.r1 - edge := by
  unfold Axis.bandPos
  split <;> exact clampPosition_between a _ edge h

theorem valuePos_between (a : Axis) (v edge : Int) (h : a.r0 ≤ a.r1 - edge) :
    a.r0 ≤ a.valuePos v edge ∧ a.valuePos v edge ≤ a.r1 - edge :=
  clampPosition_between a _ edge h

theorem pointPos_between (a : Axis) (p : XPoint) (edge : Int) (h : a.r0 ≤ a.r1 - edge) :
    a.r0 ≤ a.pointPos p edge ∧ a.pointPos p edge ≤ a.r1 - edge := by
  unfold Axis.pointPos
  split
  · exact bandPos_between a _ edge h
  · split
    · exact clampPosition_between a _ edge h
    · exact valuePos_between a _ edge h

theorem tickPos_between (a : Axis) (k : Nat) (edge : Int) (h : a.r0 ≤ a.r1 - edge) :
    a.r0 ≤ a.tickPos k edge ∧ a.tickPos k edge ≤ a.r1 - edge := by
  unfold Axis.tickPos
  split
  · exact bandPos_between a _ edge h
  · exact valuePos_between a _ edge h

/-- A clamped position stays inside an inner range that lies inside the clamp range. -/
theorem clampPosition_inner (a : Axis) {v lo hi : Int} (edge : Int) (h1 : lo ≤ v) (h2 : v ≤ hi)
    (h3 : a.r0 ≤ lo) (h4 : lo ≤ a.r1 - edge) :
    lo ≤ a.clampPosition v edge ∧ a.clampPosition v edge ≤ hi := by
  unfold Axis.clampPosition
  have := clamp_between v a.r0 (a.r1 - edge)
  unfold clamp
  omega

/-- The distinct indices of an axis are below its distinct count. -/
def Axis.Distinct (a : Axis) : Prop := ∀ i ∈ a.distinct, i < a.n

/-- With room for the outer padding, a point lies inside the inner range of its axis. -/
theorem pointPos_inner (a : Axis) (p : XPoint) (edge : Int) (hd : a.Distinct) (ho : 0 ≤ a.outer)
    (h2 : 2 * a.outer ≤ a.r1 - a.r0) (hR : edge ≤ a.r1 - a.r0) (he : edge ≤ 1) :
    a.r0 + a.outer ≤ a.pointPos p edge ∧ a.pointPos p edge ≤ a.r1 - a.outer := by
  have hlo : a.r0 + a.outer ≤ a.r1 - edge := by omega
  have hin : a.r0 + a.outer ≤ a.r1 - a.outer := by omega
  have key : ∀ v, a.innerLo ≤ v → v ≤ a.innerHi →
      a.r0 + a.outer ≤ a.clampPosition v edge ∧ a.clampPosition v edge ≤ a.r1 - a.outer := by
    intro v hv1 hv2
    unfold Axis.innerLo at hv1
    unfold Axis.innerHi at hv2
    exact clampPosition_inner a edge hv1 hv2 (by omega) hlo
  unfold Axis.pointPos
  split
  · unfold Axis.bandPos
    split
    · rename_i index hidx
      unfold Axis.bandIndex at hidx
      split at hidx
      · cases hidx
      · have hmem : index ∈ a.distinct := List.mem_of_getElem? hidx
        have := band_in_range (hd index hmem) (show a.innerLo ≤ a.innerHi by
          unfold Axis.innerLo Axis.innerHi; omega)
        exact key _ this.1 this.2
    · exact key _ (Int.le_refl _) (by unfold Axis.innerLo Axis.innerHi; omega)
  · split
    · exact clampPosition_inner a edge (Int.le_refl _) (by omega) (by omega) hlo
    · unfold Axis.valuePos
      have hcl := clamp_between p.x a.lo a.hi
      have hcl2 := clamp_between p.x a.lo a.hi
      have hm := linear_into_plot a.linear (clamp p.x a.lo a.hi) (by
        unfold Axis.linear; split <;> simp only [] <;> omega) (by
        unfold Axis.linear; split <;> simp only [] <;> omega)
      have hl : a.linear.r0 = a.innerLo ∧ a.linear.r1 = a.innerHi := by
        unfold Axis.linear; split <;> exact ⟨rfl, rfl⟩
      have hmin : min a.linear.r0 a.linear.r1 = a.innerLo := by
        rw [hl.1, hl.2]; unfold Axis.innerLo Axis.innerHi; omega
      have hmax : max a.linear.r0 a.linear.r1 = a.innerHi := by
        rw [hl.1, hl.2]; unfold Axis.innerLo Axis.innerHi; omega
      rw [hmin, hmax] at hm
      exact key _ hm.1 hm.2
/-! ### Points and bars inside the plot -/

/-- The axes sit on the plot rectangle: the category axis along the plot side that the
orientation names, the value axis along the other, and the plot is at least one edge wide. -/
def Aligned (a : Arranged) (horizontal : Bool) (edge : Int) : Prop :=
  (horizontal = true → a.x.r0 = a.plot.y ∧ a.x.r1 = a.plot.y + a.plot.h ∧
    a.y.r0 = a.plot.x ∧ a.y.r1 = a.plot.x + a.plot.w) ∧
  (horizontal = false → a.x.r0 = a.plot.x ∧ a.x.r1 = a.plot.x + a.plot.w ∧
    a.y.r0 = a.plot.y ∧ a.y.r1 = a.plot.y + a.plot.h) ∧
  edge ≤ a.plot.w ∧ edge ≤ a.plot.h

theorem pointXY_inside {a : Arranged} {horizontal : Bool} (c : XYConsts)
    (h : Aligned a horizontal c.edge) (pt : XPoint) :
    a.plot.x ≤ (a.pointXY c horizontal pt).1 ∧
      (a.pointXY c horizontal pt).1 + c.edge ≤ a.plot.x + a.plot.w ∧
      a.plot.y ≤ (a.pointXY c horizontal pt).2 ∧
      (a.pointXY c horizontal pt).2 + c.edge ≤ a.plot.y + a.plot.h := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold Arranged.pointXY
  cases horizontal
  · obtain ⟨hx0, hx1, hy0, hy1⟩ := h2 rfl
    have hc := pointPos_between a.x pt c.edge (by omega)
    have hv := valuePos_between a.y pt.value c.edge (by omega)
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  · obtain ⟨hx0, hx1, hy0, hy1⟩ := h1 rfl
    have hc := pointPos_between a.x pt c.edge (by omega)
    have hv := valuePos_between a.y pt.value c.edge (by omega)
    simp only [↓reduceIte]
    omega

private theorem foldl_min_ge {l : List (Int × Int)} (f : Int × Int → Int) {init b : Int}
    (h0 : b ≤ init) (h : ∀ p ∈ l, b ≤ f p) :
    b ≤ l.foldl (fun m p => min m (f p)) init := by
  induction l generalizing init with
  | nil => simpa using h0
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (by have := h x (List.Mem.head _); omega) (fun p hp => h p (List.Mem.tail _ hp))

private theorem foldl_max_le {l : List (Int × Int)} (f : Int × Int → Int) {init b : Int}
    (h0 : init ≤ b) (h : ∀ p ∈ l, f p ≤ b) :
    l.foldl (fun m p => max m (f p)) init ≤ b := by
  induction l generalizing init with
  | nil => simpa using h0
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (by have := h x (List.Mem.head _); omega) (fun p hp => h p (List.Mem.tail _ hp))

private theorem foldl_min_le {l : List (Int × Int)} (f : Int × Int → Int) {init : Int} :
    l.foldl (fun m p => min m (f p)) init ≤ init := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have := ih (init := min init (f x))
    omega

private theorem foldl_max_ge {l : List (Int × Int)} (f : Int × Int → Int) {init : Int} :
    init ≤ l.foldl (fun m p => max m (f p)) init := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have := ih (init := max init (f x))
    omega

/-- Every line point lies inside the plot rectangle, so the bounds of a line do. -/
theorem xychart_points_inside_plot {a : Arranged} {horizontal : Bool} (c : XYConsts)
    (h : Aligned a horizontal c.edge) (hw : 0 ≤ a.plot.w) (hh : 0 ≤ a.plot.h) (pl : XPlot) :
    a.plot.Contained (lineBounds a c horizontal pl) := by
  unfold lineBounds
  cases hpts : (pl.points.filter (·.present)).map (a.pointXY c horizontal) with
  | nil => unfold Rect.Contained; simp only []; omega
  | cons first rest =>
    have hall : ∀ p ∈ first :: rest, a.plot.x ≤ p.1 ∧ p.1 + c.edge ≤ a.plot.x + a.plot.w ∧
        a.plot.y ≤ p.2 ∧ p.2 + c.edge ≤ a.plot.y + a.plot.h := by
      intro p hp
      rw [← hpts] at hp
      obtain ⟨pt, _, hpt⟩ := List.mem_map.mp hp
      rw [← hpt]
      exact pointXY_inside c h pt
    have hf := hall first (List.Mem.head _)
    have hr : ∀ p ∈ rest, a.plot.x ≤ p.1 ∧ p.1 + c.edge ≤ a.plot.x + a.plot.w ∧
        a.plot.y ≤ p.2 ∧ p.2 + c.edge ≤ a.plot.y + a.plot.h :=
      fun p hp => hall p (List.Mem.tail _ hp)
    have e1 := foldl_min_ge (l := rest) Prod.fst (init := first.1) (b := a.plot.x) hf.1
      (fun p hp => (hr p hp).1)
    have e2 := foldl_min_ge (l := rest) Prod.snd (init := first.2) (b := a.plot.y) hf.2.2.1
      (fun p hp => (hr p hp).2.2.1)
    have e3 := foldl_max_le (l := rest) Prod.fst (init := first.1) (b := a.plot.x + a.plot.w - c.edge)
      (by omega) (fun p hp => by have := (hr p hp).2.1; omega)
    have e4 := foldl_max_le (l := rest) Prod.snd (init := first.2) (b := a.plot.y + a.plot.h - c.edge)
      (by omega) (fun p hp => by have := (hr p hp).2.2.2; omega)
    have e5 := foldl_min_le (l := rest) Prod.fst (init := first.1)
    have e6 := foldl_min_le (l := rest) Prod.snd (init := first.2)
    have e7 := foldl_max_ge (l := rest) Prod.fst (init := first.1)
    have e8 := foldl_max_ge (l := rest) Prod.snd (init := first.2)
    unfold Rect.Contained
    simp only []
    omega

/-- The outer padding of the category axis leaves room for the bars: it is not negative, and it is
at most half the axis plus half a unit. -/
def BarFrame (a : Arranged) : Prop := 0 ≤ a.x.outer ∧ 2 * a.x.outer ≤ a.x.r1 - a.x.r0 + 1

theorem tickDistance_nonneg (a : Axis) : 0 ≤ a.tickDistance := by
  unfold Axis.tickDistance
  split
  · omega
  · exact Int.fdiv_nonneg (by omega) (by omega)
private theorem w0_spec (o dist : Int) (ho : 0 ≤ o) (hd : 0 ≤ dist) :
    0 ≤ min (2 * o) dist * (1000 - 50) / 1000 ∧
      min (2 * o) dist * (1000 - 50) / 1000 ≤ min (2 * o) dist ∧
      (min (2 * o) dist ≤ 1 → min (2 * o) dist * (1000 - 50) / 1000 = 0) := by
  have h950 : (1000 : Int) - 50 = 950 := by decide
  rw [h950]
  generalize hm : min (2 * o) dist = m
  have h1 : 0 ≤ m := by omega
  refine ⟨by omega, by omega, fun h => by omega⟩


/-- A bar is at most as wide as twice the outer padding, or one edge; with no room it is one edge. -/
theorem barWidth_spec {c : XYConsts} (hc : c.Pos) {cell : Bool}
    (hcell : (cell = true ∧ c.edge = 1) ∨ (cell = false ∧ c.edge = 0)) (a : Arranged)
    (hb : BarFrame a) :
    0 ≤ barWidth a c cell ∧ barWidth a c cell ≤ max (2 * a.x.outer) c.edge ∧
      (a.x.r1 - a.x.r0 < 2 * a.x.outer → barWidth a c cell = c.edge) := by
  obtain ⟨ho, h2⟩ := hb
  have hd := tickDistance_nonneg a.x
  have hw0 := w0_spec a.x.outer a.x.tickDistance ho hd
  have hpad := hc.barPad
  have hsmall : a.x.r1 - a.x.r0 < 2 * a.x.outer → a.x.tickDistance ≤ 1 := by
    intro hlt
    unfold Axis.tickDistance
    unfold Axis.innerHi Axis.innerLo
    split
    · omega
    · have h1 : max (a.x.r1 - a.x.outer - (a.x.r0 + a.x.outer))
          (a.x.r0 + a.x.outer - (a.x.r1 - a.x.outer)) = 1 := by omega
      rw [h1]
      exact Int.fdiv_le_self _ (by omega)
  unfold barWidth
  rw [hpad, Measure.fdiv_of_nonneg (by decide : (0 : Int) ≤ 1000)]
  generalize hw : min (2 * a.x.outer) a.x.tickDistance * (1000 - 50) / 1000 = w0 at *
  refine ⟨?_, ?_, ?_⟩
  · rcases hcell with ⟨h1, _⟩ | ⟨h1, _⟩ <;> subst h1 <;> simp <;> omega
  · rcases hcell with ⟨h1, h3⟩ | ⟨h1, h3⟩ <;> subst h1 <;> simp <;> omega
  · intro hlt
    have h1 := hsmall hlt
    have h4 := hw0.2.2 (by omega)
    rcases hcell with ⟨h5, h3⟩ | ⟨h5, h3⟩ <;> subst h5 <;> simp <;> omega

/-- Across the category axis, a bar stays inside the axis. -/
theorem bar_cross_span {c : XYConsts} (hc : c.Pos) {cell : Bool}
    (hcell : (cell = true ∧ c.edge = 1) ∨ (cell = false ∧ c.edge = 0)) (a : Arranged)
    (hd : a.x.Distinct) (hb : BarFrame a) (hR : c.edge ≤ a.x.r1 - a.x.r0) (pt : XPoint) :
    a.x.r0 ≤ a.x.pointPos pt c.edge - Int.fdiv (barWidth a c cell) 2 ∧
      a.x.pointPos pt c.edge - Int.fdiv (barWidth a c cell) 2 + barWidth a c cell ≤ a.x.r1 := by
  have hspec := barWidth_spec hc hcell a hb
  obtain ⟨ho, h2⟩ := hb
  have hedge : c.edge ≤ 1 := hc.edge.2
  have hedge0 : 0 ≤ c.edge := hc.edge.1
  have hw := hspec.1
  have hf := Measure.fdiv_of_nonneg (a := barWidth a c cell) (b := 2) (by decide)
  have hbetween := pointPos_between a.x pt c.edge (by omega)
  by_cases hcase : 2 * a.x.outer ≤ a.x.r1 - a.x.r0
  · have hin := pointPos_inner a.x pt c.edge hd ho hcase hR hedge
    have hle := hspec.2.1
    rw [hf]
    omega
  · have hw2 := hspec.2.2 (by omega)
    rw [hf]
    omega

/-- Every bar lies inside the plot rectangle. -/
theorem xychart_bar_inside_plot {c : XYConsts} (hc : c.Pos) {cell horizontal : Bool}
    (hcell : (cell = true ∧ c.edge = 1) ∨ (cell = false ∧ c.edge = 0)) {a : Arranged}
    (hal : Aligned a horizontal c.edge) (hd : a.x.Distinct) (hb : BarFrame a) (pt : XPoint) :
    a.plot.Contained (barRect a c cell horizontal pt) := by
  obtain ⟨h1, h2, h3, h4⟩ := hal
  unfold barRect
  cases horizontal
  · obtain ⟨hx0, hx1, hy0, hy1⟩ := h2 rfl
    have hspan := bar_cross_span hc hcell a hd hb (by omega) pt
    have hv := valuePos_between a.y pt.value c.edge (by omega)
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold Rect.Contained
    simp only []
    omega
  · obtain ⟨hx0, hx1, hy0, hy1⟩ := h1 rfl
    have hspan := bar_cross_span hc hcell a hd hb (by omega) pt
    have hv := valuePos_between a.y pt.value c.edge (by omega)
    simp only [↓reduceIte]
    unfold Rect.Contained
    simp only []
    omega


end XY
end Chart
end Elegant

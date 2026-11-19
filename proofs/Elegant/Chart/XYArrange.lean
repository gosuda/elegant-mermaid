import Elegant.Chart.XYFacts

set_option autoImplicit false

/-! The arrangement of the xychart family: the plot rectangle lies inside the canvas, the axes sit on
the plot rectangle, and the outer padding of the category axis leaves room for the bars. These are
the facts that `XYFacts` assumes of an arrangement. -/

namespace Elegant
namespace Chart
namespace XY

/-- The constants after the config keys have been applied: the plot reserve is a percentage in the
range that the model accepts. -/
structure ConstsOk (c : XYConsts) : Prop where
  pos : c.Pos
  reservedLo : 30 ≤ c.reserved
  reservedHi : c.reserved ≤ 100

/-- Every measured box has a non-negative size. -/
def ItemsOk (items : List Item) : Prop := ∀ it ∈ items, 0 ≤ it.box.w ∧ 0 ≤ it.box.h

theorem findKind_mem {items : List Item} {k : Kind} {i : Nat} {it : Item}
    (h : findKind items k = some (i, it)) : it ∈ items := by
  unfold findKind at h
  cases hf : items.zipIdx.find? (fun (it, _) => it.spec.kind == k) with
  | none => simp [hf] at h
  | some p =>
    simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    have hp := List.mem_of_find?_eq_some hf
    have hq : p.1 ∈ items :=
      List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp (show (p.1, p.2) ∈ items.zipIdx from hp))
    rw [← h.2]
    exact hq

theorem titleNeed_spec {c : XYConsts} (hc : 0 ≤ c.axisTitlePad) {items : List Item}
    (hi : ItemsOk items) (k : Kind) (room : Int) :
    0 ≤ titleNeed c items k room ∧ (0 ≤ room → titleNeed c items k room ≤ room) := by
  unfold titleNeed
  split
  · rename_i i it hfind
    have := hi it (findKind_mem hfind)
    split <;> omega
  · omega

theorem tickExtent_nonneg (items : List Item) (k : Kind) :
    0 ≤ (tickExtent items k).1 ∧ 0 ≤ (tickExtent items k).2 := by
  unfold tickExtent
  have key : ∀ (l : List Item) (e : Int × Int), 0 ≤ e.1 → 0 ≤ e.2 →
      0 ≤ (l.foldl (fun (e : Int × Int) it =>
        if it.spec.kind == k then (max e.1 it.box.w, max e.2 it.box.h) else e) e).1 ∧
      0 ≤ (l.foldl (fun (e : Int × Int) it =>
        if it.spec.kind == k then (max e.1 it.box.w, max e.2 it.box.h) else e) e).2 := by
    intro l
    induction l with
    | nil => intro e h1 h2; exact ⟨h1, h2⟩
    | cons x xs ih =>
      intro e h1 h2
      simp only [List.foldl_cons]
      exact ih _ (by split <;> (try dsimp only) <;> omega) (by split <;> (try dsimp only) <;> omega)
  exact key items (0, 0) (by decide) (by decide)

private theorem carve (b : Bool) (n r : Int) (hn : 0 ≤ n) (hr : 0 ≤ r) :
    0 ≤ (if (b && decide (n ≤ r)) = true then r - n else r) ∧
      (if (b && decide (n ≤ r)) = true then r - n else r) ≤ r := by
  cases b
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]; omega
  · simp only [Bool.true_and, decide_eq_true_eq]
    split <;> omega

theorem spaceCore_spec {c : XYConsts} (hc : c.Pos) (a : Axis) {room extHalf extNeed pad availOuter : Int}
    (hp : 0 ≤ pad) (hr : 0 ≤ room) (he : 0 ≤ extHalf) (hn : 0 ≤ extNeed) (ha : a.outer = 0)
    (hao : 0 ≤ availOuter) :
    0 ≤ (spaceCore c a room extHalf extNeed pad availOuter).rest ∧
      (spaceCore c a room extHalf extNeed pad availOuter).rest ≤ room ∧
      0 ≤ (spaceCore c a room extHalf extNeed pad availOuter).outer ∧
      (spaceCore c a room extHalf extNeed pad availOuter).outer ≤ Int.fdiv (200 * availOuter) 1000 := by
  have hfd : 0 ≤ Int.fdiv (200 * availOuter) 1000 := Int.fdiv_nonneg (by omega) (by omega)
  have hfd2 : 0 ≤ Int.fdiv extHalf 2 := Int.fdiv_nonneg he (by omega)
  have hom := hc.outerMax
  have hl := hc.axisLine
  have htl := hc.tickLen
  unfold spaceCore
  dsimp only
  rw [hom]
  have hline : 0 ≤ (if room > c.axisLine then c.axisLine else 0) ∧
      (if room > c.axisLine then c.axisLine else 0) ≤ room := by split <;> omega
  have hk := carve a.showLabels (extNeed + 2 * pad) (room - (if room > c.axisLine then c.axisLine else 0))
    (by omega) (by omega)
  generalize (if (a.showLabels && decide (extNeed + 2 * pad ≤
      room - (if room > c.axisLine then c.axisLine else 0))) = true then
      room - (if room > c.axisLine then c.axisLine else 0) - (extNeed + 2 * pad)
    else room - (if room > c.axisLine then c.axisLine else 0)) = r2 at hk ⊢
  generalize (if room > c.axisLine then c.axisLine else 0) = line at hk hline ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · split <;> omega
  · split <;> omega
  · split <;> omega
  · split <;> omega

theorem horizontalSpace_spec {c : XYConsts} (hc : c.Pos) {items : List Item} (hi : ItemsOk items)
    (a : Axis) {availW availH : Int} (ha : a.outer = 0) (hH : 0 ≤ availH) (hW : 0 ≤ availW) :
    (horizontalSpace c items a availW availH).space.w = availW ∧
      0 ≤ (horizontalSpace c items a availW availH).space.h ∧
      (horizontalSpace c items a availW availH).space.h ≤ availH ∧
      0 ≤ (horizontalSpace c items a availW availH).outer ∧
      (horizontalSpace c items a availW availH).outer ≤ Int.fdiv (200 * availW) 1000 := by
  have hext := tickExtent_nonneg items (tickKind a)
  have hcore := spaceCore_spec hc a (room := availH) (extHalf := (tickExtent items (tickKind a)).1)
    (extNeed := (tickExtent items (tickKind a)).2) hc.padY hH hext.1 hext.2 ha hW
  have htn := titleNeed_spec hc.axisTitlePad hi (titleKind a)
    (spaceCore c a availH (tickExtent items (tickKind a)).1 (tickExtent items (tickKind a)).2 c.padY
      availW).rest
  unfold horizontalSpace
  dsimp only
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> omega

theorem verticalSpace_spec {c : XYConsts} (hc : c.Pos) {items : List Item}
    (a : Axis) {availW availH : Int} (ha : a.outer = 0) (hH : 0 ≤ availH) (hW : 0 ≤ availW) :
    (verticalSpace c items a availW availH).space.h = availH ∧
      0 ≤ (verticalSpace c items a availW availH).space.w ∧
      (verticalSpace c items a availW availH).space.w ≤ availW ∧
      0 ≤ (verticalSpace c items a availW availH).outer ∧
      (verticalSpace c items a availW availH).outer ≤ Int.fdiv (200 * availH) 1000 := by
  have hext := tickExtent_nonneg items (tickKind a)
  have hcore := spaceCore_spec hc a (room := availW) (extHalf := (tickExtent items (tickKind a)).2)
    (extNeed := (tickExtent items (tickKind a)).1) hc.padX hW hext.2 hext.1 ha hH
  unfold verticalSpace
  dsimp only
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> omega

theorem horizontalSpace_keep (c : XYConsts) (items : List Item) (a : Axis) (w h : Int) :
    (horizontalSpace c items a w h).distinct = a.distinct ∧ (horizontalSpace c items a w h).n = a.n := by
  unfold horizontalSpace
  exact ⟨rfl, rfl⟩

theorem verticalSpace_keep (c : XYConsts) (items : List Item) (a : Axis) (w h : Int) :
    (verticalSpace c items a w h).distinct = a.distinct ∧ (verticalSpace c items a w h).n = a.n := by
  unfold verticalSpace
  exact ⟨rfl, rfl⟩

theorem titleSpace_spec {c : XYConsts} (hc : 0 ≤ c.titlePad) {items : List Item}
    (hi : ItemsOk items) {availH : Int} (hH : 0 ≤ availH) :
    0 ≤ (titleSpace c items availH).1 ∧ (titleSpace c items availH).1 ≤ availH := by
  unfold titleSpace
  split
  · dsimp only; omega
  · rename_i i it hfind
    have := hi it (findKind_mem hfind)
    dsimp only
    split <;> dsimp only <;> omega

theorem sideTitleSpace_spec {c : XYConsts} (hc : 0 ≤ c.axisTitlePad) {items : List Item}
    (hi : ItemsOk items) (horizontal : Bool) {availH : Int} (hH : 0 ≤ availH) :
    0 ≤ (sideTitleSpace c items horizontal availH).1 ∧
      (sideTitleSpace c items horizontal availH).1 ≤ availH := by
  unfold sideTitleSpace
  split
  · dsimp only; omega
  · rename_i i it hfind
    have := hi it (findKind_mem hfind)
    dsimp only
    split <;> dsimp only <;> omega

theorem foldl_max_nonneg {α : Type} (f : α → Int) (l : List α) (init : Int) (h0 : 0 ≤ init) :
    0 ≤ l.foldl (fun m x => max m (f x)) init := by
  induction l generalizing init with
  | nil => exact h0
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih _ (by omega)

theorem legendInfo_spec {c : XYConsts} (hc : c.Pos) (items : List Item) (availW availH : Int) :
    0 ≤ (legendInfo c items availW availH).w ∧ 0 ≤ (legendInfo c items availW availH).h ∧
      ((legendInfo c items availW availH).beside = true →
        (legendInfo c items availW availH).w ≤ availW ∧
          (legendInfo c items availW availH).h ≤ availH) := by
  unfold legendInfo
  dsimp only
  generalize items.filter (fun it => it.spec.kind == Kind.legend) = legends
  have hw : 0 ≤ legends.foldl (fun m it => max m it.box.w) 0 :=
    foldl_max_nonneg (fun it : Item => it.box.w) legends 0 (Int.le_refl 0)
  have hh : 0 ≤ legends.foldl (fun m it => max m it.box.h) 0 :=
    foldl_max_nonneg (fun it : Item => it.box.h) legends 0 (Int.le_refl 0)
  generalize legends.foldl (fun m it => max m it.box.w) 0 = widest at hw ⊢
  generalize legends.foldl (fun m it => max m it.box.h) 0 = lh at hh ⊢
  split
  · dsimp only
    exact ⟨Int.le_refl _, Int.le_refl _, fun h => by simp at h⟩
  · rename_i hne
    have h1 := Int.mul_nonneg (show 0 ≤ (legends.length : Int) by omega) hh
    have h2 := Int.mul_nonneg (show 0 ≤ (legends.length : Int) - 1 by omega) hc.itemGap
    have h3 := hc.legendPad
    have h4 := hc.legendMarker
    have h5 := hc.markerGap
    dsimp only
    refine ⟨by omega, by omega, fun h => ?_⟩
    simpa using h

/-! ### The stage -/

/-- What the stage of an arrangement guarantees about the room it leaves. -/
structure StageOk (inp : Input) (st : Stage) (x0 y0 : Axis) (availW0 availH2 top : Int) : Prop where
  availW : 0 ≤ st.availW ∧ st.availW ≤ availW0
  availH : 0 ≤ st.availH ∧ st.availH ≤ availH2
  plotX : 0 ≤ st.plotX ∧ st.plotX + st.availW = availW0
  plotY : top ≤ st.plotY ∧ st.plotY + st.availH ≤ top + availH2
  outer : 0 ≤ st.x.outer ∧
    st.x.outer ≤ Int.fdiv (200 * (if inp.horizontal then availH2 else availW0)) 1000
  keepX : st.x.distinct = x0.distinct ∧ st.x.n = x0.n
  keepY : st.y.distinct = y0.distinct ∧ st.y.n = y0.n

theorem stageOf_spec {c : XYConsts} (hc : c.Pos) {items : List Item} (hi : ItemsOk items)
    (inp : Input) {x0 y0 : Axis} (hx : x0.outer = 0) (hy : y0.outer = 0)
    {availW0 availH2 top : Int} (hW : 0 ≤ availW0) (hH : 0 ≤ availH2) :
    StageOk inp (stageOf c inp items x0 y0 availW0 availH2 top) x0 y0 availW0 availH2 top := by
  unfold stageOf
  split
  · rename_i hh
    have hxs := verticalSpace_spec hc (items := items) x0 (availW := availW0) (availH := availH2)
      hx hH hW
    have hys := horizontalSpace_spec hc hi y0
      (availW := availW0 - (verticalSpace c items x0 availW0 availH2).space.w) (availH := availH2)
      hy hH (by omega)
    have kx := verticalSpace_keep c items x0 availW0 availH2
    have ky := horizontalSpace_keep c items y0
      (availW0 - (verticalSpace c items x0 availW0 availH2).space.w) availH2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · omega
    · omega
    · omega
    · omega
    · simp only [hh, ↓reduceIte]
      omega
    · exact kx
    · exact ky
  · rename_i hh
    have hxs := horizontalSpace_spec hc hi x0 (availW := availW0) (availH := availH2) hx hH hW
    have hys := verticalSpace_spec hc (items := items) y0 (availW := availW0)
      (availH := availH2 - (horizontalSpace c items x0 availW0 availH2).space.h) hy (by omega) hW
    have kx := horizontalSpace_keep c items x0 availW0 availH2
    have ky := verticalSpace_keep c items y0 availW0
      (availH2 - (horizontalSpace c items x0 availW0 availH2).space.h)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · omega
    · omega
    · omega
    · omega
    · simp only [hh, Bool.false_eq_true, ↓reduceIte]
      omega
    · exact kx
    · exact ky

/-! ### The outer padding of the bars -/

theorem raiseOuter_frame (a : Axis) {ratio : Int} (h0 : 0 ≤ ratio) (h1 : ratio ≤ 1000)
    (ho : 0 ≤ a.outer) (hb : 2 * a.outer ≤ a.r1 - a.r0 + 1) (hR : 0 ≤ a.r1 - a.r0) :
    0 ≤ (a.raiseOuter ratio).outer ∧ 2 * (a.raiseOuter ratio).outer ≤ a.r1 - a.r0 + 1 ∧
      (a.raiseOuter ratio).r0 = a.r0 ∧ (a.raiseOuter ratio).r1 = a.r1 ∧
      (a.raiseOuter ratio).distinct = a.distinct ∧ (a.raiseOuter ratio).n = a.n := by
  unfold Axis.raiseOuter
  dsimp only
  split
  · have hd := tickDistance_nonneg a
    have hdle : a.tickDistance ≤ a.r1 - a.r0 + 1 := by
      unfold Axis.tickDistance
      split
      · omega
      · have hM : max (a.innerHi - a.innerLo) (a.innerLo - a.innerHi) ≤ a.r1 - a.r0 + 1 := by
          unfold Axis.innerHi Axis.innerLo; omega
        have hMn : 0 ≤ max (a.innerHi - a.innerLo) (a.innerLo - a.innerHi) := by omega
        exact Int.le_trans (Int.fdiv_le_self _ hMn) hM
    have hq := Int.mul_nonneg h0 hd
    have hq2 : ratio * a.tickDistance ≤ 1000 * a.tickDistance :=
      Int.mul_le_mul_of_nonneg_right h1 hd
    rw [Measure.fdiv_of_nonneg (by decide : (0 : Int) ≤ 2000)]
    exact ⟨by dsimp only; omega, by dsimp only; omega, rfl, rfl, rfl, rfl⟩
  · exact ⟨ho, hb, rfl, rfl, rfl, rfl⟩

theorem setAreas_vertical {c : XYConsts} {inp : Input} (h : inp.horizontal = false) (plot : Rect)
    (top : Int) (x y : Axis) :
    setAreas c inp plot top x y =
      (if hasBars inp = true then
        ({ x with area := ⟨plot.x, plot.y + plot.h, plot.w, x.space.h⟩, r0 := plot.x,
                  r1 := plot.x + plot.w } : Axis).raiseOuter c.barRatio
       else { x with area := ⟨plot.x, plot.y + plot.h, plot.w, x.space.h⟩, r0 := plot.x,
                     r1 := plot.x + plot.w },
       { y with area := ⟨0, plot.y, y.space.w, plot.h⟩, r0 := plot.y, r1 := plot.y + plot.h }) := by
  unfold setAreas
  rw [h]
  try rfl

theorem setAreas_horizontal {c : XYConsts} {inp : Input} (h : inp.horizontal = true) (plot : Rect)
    (top : Int) (x y : Axis) :
    setAreas c inp plot top x y =
      (if hasBars inp = true then
        ({ x with area := ⟨0, plot.y, x.space.w, plot.h⟩, r0 := plot.y,
                  r1 := plot.y + plot.h } : Axis).raiseOuter c.barRatio
       else { x with area := ⟨0, plot.y, x.space.w, plot.h⟩, r0 := plot.y, r1 := plot.y + plot.h },
       { y with area := ⟨plot.x, top, plot.w, y.space.h⟩, r0 := plot.x,
                r1 := plot.x + plot.w }) := by
  unfold setAreas
  rw [h]
  try rfl

theorem setAreas_spec {c : XYConsts} (hc : c.Pos) (inp : Input) (plot : Rect) (top : Int)
    (x y : Axis) (hw : 0 ≤ plot.w) (hh : 0 ≤ plot.h) (ho : 0 ≤ x.outer)
    (hb : 2 * x.outer ≤ (if inp.horizontal then plot.h else plot.w) + 1) :
    (inp.horizontal = true →
      (setAreas c inp plot top x y).1.r0 = plot.y ∧
        (setAreas c inp plot top x y).1.r1 = plot.y + plot.h ∧
        (setAreas c inp plot top x y).2.r0 = plot.x ∧
        (setAreas c inp plot top x y).2.r1 = plot.x + plot.w) ∧
    (inp.horizontal = false →
      (setAreas c inp plot top x y).1.r0 = plot.x ∧
        (setAreas c inp plot top x y).1.r1 = plot.x + plot.w ∧
        (setAreas c inp plot top x y).2.r0 = plot.y ∧
        (setAreas c inp plot top x y).2.r1 = plot.y + plot.h) ∧
    0 ≤ (setAreas c inp plot top x y).1.outer ∧
    2 * (setAreas c inp plot top x y).1.outer ≤ (if inp.horizontal then plot.h else plot.w) + 1 ∧
    (setAreas c inp plot top x y).1.distinct = x.distinct ∧
    (setAreas c inp plot top x y).1.n = x.n := by
  have hr0 : (0 : Int) ≤ c.barRatio := by rw [hc.barRatio]; decide
  have hr1 : c.barRatio ≤ 1000 := by rw [hc.barRatio]; decide
  cases hH : inp.horizontal
  · have hext : (if (false : Bool) = true then plot.h else plot.w) = plot.w := rfl
    rw [hH, hext] at hb
    rw [hext, setAreas_vertical hH]
    by_cases hbar : hasBars inp = true
    · rw [ite_t hbar]
      obtain ⟨k1, k2, k3, k4, k5, k6⟩ := raiseOuter_frame
        { x with area := ⟨plot.x, plot.y + plot.h, plot.w, x.space.h⟩, r0 := plot.x,
                 r1 := plot.x + plot.w } hr0 hr1 ho (by dsimp only; omega) (by dsimp only; omega)
      exact ⟨fun h => absurd h (by decide), fun _ => ⟨k3, k4, rfl, rfl⟩, k1,
        by dsimp only at k2 ⊢; omega, k5, k6⟩
    · rw [ite_f hbar]
      exact ⟨fun h => absurd h (by decide), fun _ => ⟨rfl, rfl, rfl, rfl⟩, ho, hb, rfl, rfl⟩
  · have hext : (if (true : Bool) = true then plot.h else plot.w) = plot.h := rfl
    rw [hH, hext] at hb
    rw [hext, setAreas_horizontal hH]
    by_cases hbar : hasBars inp = true
    · rw [ite_t hbar]
      obtain ⟨k1, k2, k3, k4, k5, k6⟩ := raiseOuter_frame
        { x with area := ⟨0, plot.y, x.space.w, plot.h⟩, r0 := plot.y, r1 := plot.y + plot.h }
        hr0 hr1 ho (by dsimp only; omega) (by dsimp only; omega)
      exact ⟨fun _ => ⟨k3, k4, rfl, rfl⟩, fun h => absurd h (by decide), k1,
        by dsimp only at k2 ⊢; omega, k5, k6⟩
    · rw [ite_f hbar]
      exact ⟨fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun h => absurd h (by decide), ho, hb, rfl, rfl⟩

/-! ### The arrangement -/

/-- With the plot reserve a percentage in `[30, 100]`, the outer padding that an axis may take
(a fifth of the room beside the reserve) is at most half the reserve and half a unit. -/
theorem outer_bound (D res : Int) (hD : 0 ≤ D) (h1 : 30 ≤ res) (h2 : res ≤ 100) :
    0 ≤ Int.fdiv (D * res) 100 ∧ Int.fdiv (D * res) 100 ≤ D ∧
      2 * Int.fdiv (200 * (D - Int.fdiv (D * res) 100)) 1000 ≤ Int.fdiv (D * res) 100 + 1 := by
  have hP1 : D * 30 ≤ D * res := Int.mul_le_mul_of_nonneg_left h1 hD
  have hP2 : D * res ≤ D * 100 := Int.mul_le_mul_of_nonneg_left h2 hD
  have hP0 : 0 ≤ D * res := by omega
  rw [Measure.fdiv_of_nonneg (by decide : (0 : Int) ≤ 100)]
  have hq : 0 ≤ 200 * (D - D * res / 100) := by omega
  rw [Measure.fdiv_of_nonneg (by decide : (0 : Int) ≤ 1000)]
  omega

/-- What an arrangement guarantees: the plot lies inside the canvas, the axes sit on the plot,
and the category axis leaves room for the bars. -/
structure ArrangeOk (inp : Input) (a : Arranged) (x0 : Axis) (edge : Int) : Prop where
  size : 0 < a.width ∧ 0 < a.height
  canvas : 0 ≤ a.plot.x ∧ a.plot.x + a.plot.w ≤ a.width ∧ 0 ≤ a.plot.y ∧
    a.plot.y + a.plot.h ≤ a.height
  aligned : Aligned a inp.horizontal edge
  barFrame : BarFrame a
  keep : a.x.distinct = x0.distinct ∧ a.x.n = x0.n

theorem arrangeWith_spec {c : XYConsts} (hc : c.Pos) (inp : Input) {x0 y0 : Axis}
    {width height chartW0 chartH0 : Int} {titled : Int × Bool} {side : Int × Option Nat × Bool}
    {st : Stage} {leg : LegendInfo} (hw : 0 < width) (hh : 0 < height)
    (hW0 : 0 ≤ chartW0) (hH0 : 0 ≤ chartH0) (hW1 : chartW0 ≤ width) (hH1 : chartH0 ≤ height)
    (hbW : 2 * Int.fdiv (200 * (width - chartW0)) 1000 ≤ chartW0 + 1)
    (hbH : 2 * Int.fdiv (200 * (height - chartH0)) 1000 ≤ chartH0 + 1)
    (ht : 0 ≤ titled.1 ∧ titled.1 ≤ height - chartH0)
    (hs : 0 ≤ side.1 ∧ side.1 ≤ height - chartH0 - titled.1)
    (hst : StageOk inp st x0 y0 (width - chartW0) (height - chartH0 - titled.1 - side.1)
      (titled.1 + side.1))
    (hl : 0 ≤ leg.w ∧ (leg.beside = true → leg.w ≤ st.availW)) :
    ArrangeOk inp (arrangeWith c inp width height chartW0 chartH0 titled side st leg) x0 c.edge := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨p1, p2⟩, ⟨q1, q2⟩, ⟨o1, o2⟩, k, _⟩ := hst
  have hedge := hc.edge
  unfold arrangeWith
  dsimp only
  have haw2 : 0 ≤ (if leg.beside = true then st.availW - leg.w else st.availW) ∧
      (if leg.beside = true then st.availW - leg.w else st.availW) ≤ st.availW := by
    split
    · rename_i hb
      have := hl.2 hb
      omega
    · omega
  generalize (if leg.beside = true then st.availW - leg.w else st.availW) = aw2 at haw2 ⊢
  have hcW : c.edge ≤ max (chartW0 + max aw2 0) c.edge ∧ chartW0 ≤ max (chartW0 + max aw2 0) c.edge ∧
      max (chartW0 + max aw2 0) c.edge ≤ width := by omega
  have hcH : c.edge ≤ max (chartH0 + max st.availH 0) c.edge ∧
      chartH0 ≤ max (chartH0 + max st.availH 0) c.edge ∧
      max (chartH0 + max st.availH 0) c.edge ≤ height := by omega
  generalize max (chartW0 + max aw2 0) c.edge = chartW at hcW ⊢
  generalize max (chartH0 + max st.availH 0) c.edge = chartH at hcH ⊢
  have hplot : (⟨max (min st.plotX (width - chartW)) 0, max (min st.plotY (height - chartH)) 0,
      chartW, chartH⟩ : Rect).x = max (min st.plotX (width - chartW)) 0 := rfl
  have hplot2 : (⟨max (min st.plotX (width - chartW)) 0, max (min st.plotY (height - chartH)) 0,
      chartW, chartH⟩ : Rect).y = max (min st.plotY (height - chartH)) 0 := rfl
  have hpw : (⟨max (min st.plotX (width - chartW)) 0, max (min st.plotY (height - chartH)) 0,
      chartW, chartH⟩ : Rect).w = chartW := rfl
  have hph : (⟨max (min st.plotX (width - chartW)) 0, max (min st.plotY (height - chartH)) 0,
      chartW, chartH⟩ : Rect).h = chartH := rfl
  generalize (⟨max (min st.plotX (width - chartW)) 0, max (min st.plotY (height - chartH)) 0,
      chartW, chartH⟩ : Rect) = plot at hplot hplot2 hpw hph ⊢
  have hbound : 2 * st.x.outer ≤ (if inp.horizontal then plot.h else plot.w) + 1 := by
    cases hH : inp.horizontal
    · have hext : (if (false : Bool) = true then plot.h else plot.w) = plot.w := rfl
      rw [hext]
      rw [hH] at o2
      have hext2 : (if (false : Bool) = true then height - chartH0 - titled.1 - side.1
          else width - chartW0) = width - chartW0 := rfl
      rw [hext2] at o2
      omega
    · have hext : (if (true : Bool) = true then plot.h else plot.w) = plot.h := rfl
      rw [hext]
      rw [hH] at o2
      have hext2 : (if (true : Bool) = true then height - chartH0 - titled.1 - side.1
          else width - chartW0) = height - chartH0 - titled.1 - side.1 := rfl
      rw [hext2] at o2
      have hmono := fdiv_mono (D := 1000) (by decide)
        (show 200 * (height - chartH0 - titled.1 - side.1) ≤ 200 * (height - chartH0) by omega)
      omega
  obtain ⟨sa1, sa2, sa3, sa4, sa5, sa6⟩ := setAreas_spec hc inp plot (titled.1 + side.1) st.x st.y
    (by omega) (by omega) o1 hbound
  refine ⟨⟨hw, hh⟩, ?_, ⟨sa1, sa2, ?_, ?_⟩, ⟨sa3, ?_⟩, ⟨?_, ?_⟩⟩
  · dsimp only
    omega
  · dsimp only
    omega
  · dsimp only
    omega
  · cases hH : inp.horizontal
    · have := sa2 hH
      have hext : (if (false : Bool) = true then plot.h else plot.w) = plot.w := rfl
      rw [hH, hext] at sa4
      dsimp only
      omega
    · have := sa1 hH
      have hext : (if (true : Bool) = true then plot.h else plot.w) = plot.h := rfl
      rw [hH, hext] at sa4
      dsimp only
      omega
  · exact sa5.trans k.1
  · exact sa6.trans k.2

theorem arrange_spec {c : XYConsts} (hc : ConstsOk c) {items : List Item} (hi : ItemsOk items)
    (inp : Input) {x0 y0 : Axis} (hx : x0.outer = 0) (hy : y0.outer = 0) :
    ArrangeOk inp (arrange c inp items x0 y0) x0 c.edge := by
  have hp := hc.pos
  have ob := outer_bound c.width c.reserved (Int.le_of_lt hp.width) hc.reservedLo hc.reservedHi
  have ob' := outer_bound c.height c.reserved (Int.le_of_lt hp.height) hc.reservedLo hc.reservedHi
  have ht := titleSpace_spec hp.titlePad hi
    (availH := c.height - Int.fdiv (c.height * c.reserved) 100) (by omega)
  have hs := sideTitleSpace_spec hp.axisTitlePad hi inp.horizontal
    (availH := c.height - Int.fdiv (c.height * c.reserved) 100 -
      (titleSpace c items (c.height - Int.fdiv (c.height * c.reserved) 100)).1) (by omega)
  have hst := stageOf_spec hp hi inp hx hy
    (availW0 := c.width - Int.fdiv (c.width * c.reserved) 100)
    (availH2 := c.height - Int.fdiv (c.height * c.reserved) 100 -
      (titleSpace c items (c.height - Int.fdiv (c.height * c.reserved) 100)).1 -
      (sideTitleSpace c items inp.horizontal (c.height - Int.fdiv (c.height * c.reserved) 100 -
        (titleSpace c items (c.height - Int.fdiv (c.height * c.reserved) 100)).1)).1)
    (top := (titleSpace c items (c.height - Int.fdiv (c.height * c.reserved) 100)).1 +
      (sideTitleSpace c items inp.horizontal (c.height - Int.fdiv (c.height * c.reserved) 100 -
        (titleSpace c items (c.height - Int.fdiv (c.height * c.reserved) 100)).1)).1)
    (by omega) (by omega)
  unfold arrange
  dsimp only
  have hl := legendInfo_spec hp items
    (stageOf c inp items x0 y0 (c.width - Int.fdiv (c.width * c.reserved) 100)
      (c.height - Int.fdiv (c.height * c.reserved) 100 -
        (titleSpace c items (c.height - Int.fdiv (c.height * c.reserved) 100)).1 -
        (sideTitleSpace c items inp.horizontal (c.height - Int.fdiv (c.height * c.reserved) 100 -
          (titleSpace c items (c.height - Int.fdiv (c.height * c.reserved) 100)).1)).1)
      ((titleSpace c items (c.height - Int.fdiv (c.height * c.reserved) 100)).1 +
        (sideTitleSpace c items inp.horizontal (c.height - Int.fdiv (c.height * c.reserved) 100 -
          (titleSpace c items (c.height - Int.fdiv (c.height * c.reserved) 100)).1)).1)).availW
    (Int.fdiv (c.height * c.reserved) 100)
  exact arrangeWith_spec hp inp hp.width hp.height ob.1 ob'.1 ob.2.1 ob'.2.1 ob.2.2 ob'.2.2 ht hs hst
    ⟨hl.1, fun hb => (hl.2.2 hb).1⟩

end XY
end Chart
end Elegant

import Elegant.Chart.XYArrange

set_option autoImplicit false

/-! The validity of the xychart family (`spec/layout/charts.md`, charts-109): for every chart that the
family lays out, the plot rectangle lies inside the canvas and every other box lies inside the plot
rectangle. The statements are over the Lean functions that `geomcheck` runs. -/

namespace Elegant
namespace Chart
namespace XY

/-- The options of the input that the family reads are in the ranges that the model accepts. -/
structure InputOk (inp : Input) : Prop where
  width : ∀ n, inp.width = some n → 1 ≤ n
  height : ∀ n, inp.height = some n → 1 ≤ n
  reserved : ∀ n, inp.reserved = some n → 30 ≤ n ∧ n ≤ 100
  fontSize : ∀ n, inp.fontSize = some n → 0 ≤ n

theorem bind_ok {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem mapM_ok_mem {α β : Type} (f : α → Except LayoutError β) (P : β → Prop)
    (hf : ∀ a b, f a = .ok b → P b) :
    ∀ (l : List α) (bs : List β), l.mapM f = .ok bs → ∀ b ∈ bs, P b := by
  intro l
  induction l with
  | nil =>
    intro bs h b hb
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp at hb
  | cons a as ih =>
    intro bs h b hb
    rw [List.mapM_cons] at h
    obtain ⟨b1, hfa, h⟩ := bind_ok h
    obtain ⟨bs1, hrest, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact hf a _ hfa
    · exact ih bs1 hrest b hb'

/-! ### The constants and the measured labels -/

theorem adjustedConsts_ok {profile : Profile} {inp : Input} {c0 : XYConsts} (hin : InputOk inp)
    (h0 : c0.Pos) (hr : 30 ≤ c0.reserved ∧ c0.reserved ≤ 100) :
    ConstsOk (adjustedConsts profile inp c0) := by
  unfold adjustedConsts
  refine ⟨⟨?_, ?_, h0.barPad, h0.barRatio, h0.outerMax, h0.axisLine, h0.axisTitlePad, h0.padX,
    h0.padY, h0.tickLen, h0.titlePad, h0.legendPad, h0.legendMarker, h0.markerGap, h0.itemGap,
    h0.pointSize, h0.edge⟩, ?_, ?_⟩
  · cases hn : inp.width with
    | none => exact h0.width
    | some n =>
      have := hin.width n hn
      dsimp only
      split
      · rw [Measure.ceilDiv_eq (by decide)]
        omega
      · omega
  · cases hn : inp.height with
    | none => exact h0.height
    | some n =>
      have := hin.height n hn
      dsimp only
      split
      · rw [Measure.ceilDiv_eq (by decide)]
        omega
      · omega
  · cases hn : inp.reserved with
    | none => exact hr.1
    | some n => exact (hin.reserved n hn).1
  · cases hn : inp.reserved with
    | none => exact hr.2
    | some n => exact (hin.reserved n hn).2

theorem lineHeight_nonneg (cell : Bool) (role : Measure.Role) {size : Int} (hs : 0 ≤ size) :
    0 ≤ lineHeight cell role size := by
  unfold lineHeight roundHalfUp
  split
  · decide
  · cases role <;>
      (apply Int.fdiv_nonneg <;> simp only [Measure.Role.sizePx, Measure.Role.lineHeightPx] <;> omega)

theorem measureText_ok {cell : Bool} {text : String} {role : Measure.Role} {size : Int}
    {tb : TextBox} (h : measureText cell text role size = .ok tb) (hs : 0 ≤ size) :
    0 ≤ tb.w ∧ 0 ≤ tb.h := by
  unfold measureText at h
  obtain ⟨m, _, h⟩ := bind_ok h
  split at h
  · cases h
  · rename_i lines _
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨foldl_max_nonneg (fun l => l.width) lines 0 (Int.le_refl 0),
      Int.mul_nonneg (by omega) (lineHeight_nonneg cell role hs)⟩

theorem styleOf_nonneg {c : XYConsts} (hc : 0 ≤ c.pointSize) {x : Axis} (hx : 0 ≤ x.fontSize)
    (s : Spec) : 0 ≤ (styleOf c x s).2 := by
  unfold styleOf
  split
  · dsimp only; decide
  · dsimp only; exact hx
  · dsimp only; exact Int.fdiv_nonneg hc (by omega)
  · dsimp only; decide

theorem measureAll_ok {c : XYConsts} (hc : 0 ≤ c.pointSize) {cell : Bool} {x : Axis}
    (hx : 0 ≤ x.fontSize) {specs : List Spec} {items : List Item}
    (h : measureAll c cell x specs = .ok items) : ItemsOk items := by
  unfold measureAll at h
  refine mapM_ok_mem _ (fun it => 0 ≤ it.box.w ∧ 0 ≤ it.box.h) ?_ specs items h
  intro s it hit
  have hsz := styleOf_nonneg hc hx s
  rcases hp : styleOf c x s with ⟨role, size⟩
  rw [hp] at hsz
  simp only [hp] at hit
  obtain ⟨box, hbox, hit⟩ := bind_ok hit
  simp only [pure, Except.pure, Except.ok.injEq] at hit
  subst hit
  exact measureText_ok hbox hsz

/-! ### The axes -/

theorem distinctStep_inv (acc : List String × List Nat) (name : String)
    (h : ∀ i ∈ acc.2, i < acc.1.length) :
    ∀ i ∈ (distinctStep acc name).2, i < (distinctStep acc name).1.length := by
  unfold distinctStep
  split
  · rename_i at_ hfind
    have hlt := (List.findIdx?_eq_some_iff_findIdx_eq.mp hfind).1
    intro i hi
    dsimp only at hi ⊢
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact h i hi
    · exact hlt
  · intro i hi
    dsimp only at hi ⊢
    simp only [List.mem_append, List.mem_singleton, List.length_append, List.length_singleton] at hi ⊢
    rcases hi with hi | rfl
    · have := h i hi
      omega
    · omega

theorem distinctIndex_lt (cats : List String) :
    ∀ i ∈ (distinctIndex cats).1, i < (distinctIndex cats).2 := by
  unfold distinctIndex
  have key : ∀ (l : List String) (acc : List String × List Nat),
      (∀ i ∈ acc.2, i < acc.1.length) →
      ∀ i ∈ (l.foldl distinctStep acc).2, i < (l.foldl distinctStep acc).1.length := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons x xs ih => intro acc h; exact ih _ (distinctStep_inv acc x h)
  exact key cats ([], []) (by simp)

theorem linearAxis_spec {isX : Bool} {lo hi : Int} {a : Axis} {cap : Bool}
    (h : linearAxis isX lo hi = .ok (a, cap)) : a.outer = 0 ∧ a.distinct = [] := by
  unfold linearAxis at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨ticks, capped⟩, _, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _⟩ := h
  exact ⟨rfl, rfl⟩

theorem newAxes_spec {inp : Input} {x y : Axis} {cap : Bool}
    (h : newAxes inp = .ok (x, y, cap)) : x.outer = 0 ∧ y.outer = 0 ∧ x.Distinct := by
  unfold newAxes at h
  obtain ⟨⟨y1, capped⟩, hy, h⟩ := bind_ok h
  have hys := linearAxis_spec hy
  by_cases hb : inp.band = true
  · simp only [hb, ↓reduceIte] at h
    rcases hd : distinctIndex inp.categories with ⟨distinct, n⟩
    simp only [hd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, _⟩ := h
    have hlt := distinctIndex_lt inp.categories
    rw [hd] at hlt
    exact ⟨rfl, hys.1, hlt⟩
  · simp only [hb] at h
    obtain ⟨⟨x1, xCapped⟩, hx, h⟩ := bind_ok h
    have hxs := linearAxis_spec hx
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, _⟩ := h
    exact ⟨hxs.1, hys.1, fun i hi => by rw [hxs.2] at hi; simp at hi⟩

/-! ### The preparation -/

/-- What the preparation guarantees about its constants, measured labels and axes. -/
structure PrepOk (profile : Profile) (p : Prep) : Prop where
  consts : ConstsOk p.c
  items : ItemsOk p.items
  xOuter : p.x0.outer = 0
  yOuter : p.y0.outer = 0
  distinct : p.x0.Distinct
  edge : ((profile == .cell) = true ∧ p.c.edge = 1) ∨ ((profile == .cell) = false ∧ p.c.edge = 0)

theorem prepare_spec {profile : Profile} {inp : Input} {p : Prep} (hin : InputOk inp)
    (h : prepare profile inp = .ok p) : PrepOk profile p := by
  unfold prepare at h
  obtain ⟨c0, hl, h⟩ := bind_ok h
  obtain ⟨⟨x1, y1, cap⟩, hn, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨items, hm, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hcs := adjustedConsts_ok (profile := profile) hin (load_pos hl) (load_reserved hl)
  have hax := newAxes_spec hn
  have hfs : 0 ≤ (categoryAxis inp x1).fontSize := by
    unfold categoryAxis
    cases hf : inp.fontSize with
    | none => exact (by decide : (0 : Int) ≤ (none : Option Int).getD 14)
    | some n => exact hin.fontSize n hf
  refine ⟨hcs, measureAll_ok hcs.pos.pointSize hfs hm, hax.1, hax.2.1, hax.2.2, ?_⟩
  rcases load_edge hl with ⟨hp, he⟩ | ⟨hp, he⟩
  · subst hp
    exact Or.inl ⟨by decide, he⟩
  · subst hp
    exact Or.inr ⟨by decide, he⟩

/-! ### The frame -/

theorem seriesBoxes_notPlot (inp : Input) : ∀ b ∈ seriesBoxes inp, b.isPlot = false := by
  intro b hb
  unfold seriesBoxes at hb
  obtain ⟨⟨pl, i⟩, _, hb⟩ := List.mem_flatMap.mp hb
  dsimp only at hb
  split at hb
  · simp only [List.mem_singleton] at hb
    subst hb
    rfl
  · obtain ⟨⟨pt, j⟩, _, hb⟩ := List.mem_filterMap.mp hb
    dsimp only at hb
    split at hb
    · simp only [Option.some.injEq] at hb
      subst hb
      rfl
    · cases hb

theorem boxRect_plot (a : Arranged) (c : XYConsts) (cell : Bool) (inp : Input) :
    boxRect a c cell inp plotBox = a.plot := rfl

/-- The frame of a laid-out chart: the plot box comes first and lies inside the canvas, and every
other box lies inside the plot box. -/
theorem layout_frame {profile : Profile} {inp : Input} {r : Result} (hin : InputOk inp)
    (h : layout profile inp = .ok r) :
    ∃ (rest : List BoxSpec) (plot : Rect) (restRects : List Rect),
      r.boxes = plotBox :: rest ∧ (∀ b ∈ rest, b.isPlot = false) ∧
      r.boxRects = plot :: restRects ∧
      0 ≤ plot.x ∧ plot.x + plot.w ≤ r.canvas.w ∧ 0 ≤ plot.y ∧ plot.y + plot.h ≤ r.canvas.h ∧
      (∀ q ∈ restRects, plot.Contained q) := by
  unfold layout at h
  obtain ⟨p, hp, hf⟩ := bind_ok h
  have hpo := prepare_spec hin hp
  unfold finish at hf
  dsimp only at hf
  obtain ⟨placed, _, hf⟩ := bind_ok hf
  obtain ⟨_, _, hf⟩ := bind_ok hf
  obtain ⟨_, _, hf⟩ := bind_ok hf
  obtain ⟨groups, _, hf⟩ := bind_ok hf
  simp only [Except.ok.injEq] at hf
  subst hf
  have ha := arrange_spec hpo.consts hpo.items inp hpo.xOuter hpo.yOuter
  have hd : (arrange p.c inp p.items p.x0 p.y0).x.Distinct := by
    unfold Axis.Distinct
    rw [ha.keep.1, ha.keep.2]
    exact hpo.distinct
  have hc := hpo.consts.pos
  have hal := ha.aligned
  have hwpos : 0 ≤ (arrange p.c inp p.items p.x0 p.y0).plot.w := by
    have := hal.2.2.1
    have := hc.edge.1
    omega
  have hhpos : 0 ≤ (arrange p.c inp p.items p.x0 p.y0).plot.h := by
    have := hal.2.2.2
    have := hc.edge.1
    omega
  refine ⟨seriesBoxes inp, (arrange p.c inp p.items p.x0 p.y0).plot,
    (seriesBoxes inp).map (boxRect (arrange p.c inp p.items p.x0 p.y0) p.c (profile == .cell) inp),
    rfl, seriesBoxes_notPlot inp, rfl, ha.canvas.1, ha.canvas.2.1, ha.canvas.2.2.1,
    ha.canvas.2.2.2, ?_⟩
  intro q hq
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
  have hnp := seriesBoxes_notPlot inp b hb
  unfold boxRect
  simp only [hnp, Bool.false_eq_true, ↓reduceIte]
  split
  · exact xychart_points_inside_plot p.c hal hwpos hhpos _
  · exact xychart_bar_inside_plot hc hpo.edge hal hd ha.barFrame _

end XY
end Chart
end Elegant

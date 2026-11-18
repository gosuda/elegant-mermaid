import Elegant.Chart.Quadrant

set_option autoImplicit false

namespace Elegant.Chart.Quadrant

theorem quadrant_point_in_plot (plot : Rect) (edge : Int) (p : InputPoint)
    (he : 0 ≤ edge) (hw : edge ≤ plot.w) (hh : edge ≤ plot.h)
    (hx : 0 ≤ p.x ∧ p.x ≤ 1000) (hy : 0 ≤ p.y ∧ p.y ≤ 1000) :
    plot.x ≤ (centre plot edge p).x ∧ (centre plot edge p).x ≤ plot.x + plot.w ∧
    plot.y ≤ (centre plot edge p).y ∧ (centre plot edge p).y ≤ plot.y + plot.h := by
  have bx := fdiv_scaled_between p.x 1000 (max (plot.w - 3 * edge) 0) (by omega) hx.1 hx.2
  have by_ := fdiv_scaled_between p.y 1000 (max (plot.h - 3 * edge) 0) (by omega) hy.1 hy.2
  simp only [centre]
  have wx : 0 ≤ max (plot.w - 3 * edge) 0 := Int.le_max_right _ _
  have wy : 0 ≤ max (plot.h - 3 * edge) 0 := Int.le_max_right _ _
  rw [Int.min_eq_left wx, Int.max_eq_right wx] at bx
  rw [Int.min_eq_left wy, Int.max_eq_right wy] at by_
  omega

theorem quadrant_x_monotone (plot : Rect) (edge : Int) (a b : InputPoint)
    (h : a.x ≤ b.x) : (centre plot edge a).x ≤ (centre plot edge b).x := by
  have hm := Int.mul_le_mul_of_nonneg_right h (Int.le_max_right (plot.w - 3 * edge) 0)
  have hf := fdiv_mono (D := 1000) (by omega) hm
  simp only [centre]
  omega

theorem quadrant_split_monotone (plot : Rect) (edge : Int) (p : InputPoint)
    (hx : 500 ≤ p.x) :
    plot.x + edge + Int.fdiv (500 * max (plot.w - 3 * edge) 0) 1000 ≤
      (centre plot edge p).x := by
  exact quadrant_x_monotone plot edge ⟨500, p.y, p.radius⟩ p hx

theorem quadrant_split_counterexample :
    let plot : Rect := ⟨1, 1, 60, 30⟩
    let p : InputPoint := ⟨500, 500, -1⟩
    500 ≤ p.x ∧ (centre plot 1 p).x < plot.x + Int.fdiv plot.w 2 := by
  decide

theorem within_contained (r outer : Rect)
    (hx : r.x ≤ outer.x + outer.w) (hy : r.y ≤ outer.y + outer.h)
    (hw : 0 ≤ outer.w) (hh : 0 ≤ outer.h) :
    Rect.Contained outer (within r outer) := by
  simp only [within, Rect.Contained]
  omega

theorem tile_contained (plot : Rect) (i : Nat)
    (hw : 0 ≤ plot.w) (hh : 0 ≤ plot.h) :
    Rect.Contained plot (tile plot i) := by
  have bw := fdiv_between plot.w 2 0 plot.w (by omega) (by omega) (by omega)
  have bh := fdiv_between plot.h 2 0 plot.h (by omega) (by omega) (by omega)
  simp only [tile, Rect.Contained]
  split <;> split <;> omega

theorem plot_contained (canvas : Size) (plot : Rect)
    (hx : 0 ≤ plot.x) (hy : 0 ≤ plot.y)
    (hw : plot.x + plot.w ≤ canvas.w) (hh : plot.y + plot.h ≤ canvas.h) :
    Rect.Contained ⟨0, 0, canvas.w, canvas.h⟩ plot := by
  simp only [Rect.Contained, Int.zero_add]
  exact ⟨hx, hw, hy, hh⟩

theorem sceneOf_routes_empty (m : Model) (c : Constants) (g : Geometry)
    (ps : List Placement) : (sceneOf m c g ps).routes = [] := by
  rfl

theorem sceneOf_route_constraints (m : Model) (c : Constants) (g : Geometry)
    (ps : List Placement) :
    Validator.C4 (sceneOf m c g ps).layoutDump ∧
    Validator.C5 (sceneOf m c g ps).layoutDump ∧
    Validator.C6 (sceneOf m c g ps).layoutDump := by
  simp [Validator.C4, Validator.C5, Validator.C6, Scene.layoutDump,
    sceneOf_routes_empty]

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x.bind f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem successful_scene_assembly (m : Model) (s : Scene)
    (h : layout m = .ok s) :
    ∃ g ps, arrange m (constants m) (pointInputs m) = .ok g ∧
      place m (constants m) g = .ok ps ∧ s = sceneOf m (constants m) g ps := by
  unfold layout at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨g, hg, h⟩ := bind_ok h
    obtain ⟨ps, hps, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨g, ps, hg, hps, h.symm⟩

theorem successful_route_constraints (m : Model) (s : Scene)
    (h : layout m = .ok s) :
    Validator.C4 s.layoutDump ∧ Validator.C5 s.layoutDump ∧
      Validator.C6 s.layoutDump := by
  obtain ⟨g, ps, _, _, hs⟩ := successful_scene_assembly m s h
  rw [hs]
  exact sceneOf_route_constraints m (constants m) g ps

theorem successful_point_coordinates (m : Model) (s : Scene)
    (h : layout m = .ok s) (p : InputPoint) (hp : p ∈ pointInputs m) :
    0 ≤ p.x ∧ p.x ≤ 1000 ∧ 0 ≤ p.y ∧ p.y ≤ 1000 := by
  unfold layout at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hg
    have hall :
        ((pointInputs m).all fun q =>
          decide (0 ≤ q.x ∧ q.x ≤ 1000 ∧ 0 ≤ q.y ∧ q.y ≤ 1000 ∧ -1 ≤ q.radius)) = true := by
      cases he : ((pointInputs m).all fun q =>
          decide (0 ≤ q.x ∧ q.x ≤ 1000 ∧ 0 ≤ q.y ∧ q.y ≤ 1000 ∧ -1 ≤ q.radius)) with
      | false =>
        exact False.elim (hg (by simp only [he, Bool.not_false]))
      | true => rfl
    have hmem := List.all_eq_true.mp hall p hp
    have bound : 0 ≤ p.x ∧ p.x ≤ 1000 ∧ 0 ≤ p.y ∧ p.y ≤ 1000 ∧ -1 ≤ p.radius :=
      of_decide_eq_true hmem
    exact ⟨bound.1, bound.2.1, bound.2.2.1, bound.2.2.2.1⟩

theorem successful_point_radii (m : Model) (s : Scene)
    (h : layout m = .ok s) (p : InputPoint) (hp : p ∈ pointInputs m) :
    -1 ≤ p.radius := by
  unfold layout at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hg
    have hall :
        ((pointInputs m).all fun q =>
          decide (0 ≤ q.x ∧ q.x ≤ 1000 ∧ 0 ≤ q.y ∧ q.y ≤ 1000 ∧ -1 ≤ q.radius)) = true := by
      cases he : ((pointInputs m).all fun q =>
          decide (0 ≤ q.x ∧ q.x ≤ 1000 ∧ 0 ≤ q.y ∧ q.y ≤ 1000 ∧ -1 ≤ q.radius)) with
      | false =>
        exact False.elim (hg (by simp only [he, Bool.not_false]))
      | true => rfl
    have hmem := List.all_eq_true.mp hall p hp
    have bound : 0 ≤ p.x ∧ p.x ≤ 1000 ∧ 0 ≤ p.y ∧ p.y ≤ 1000 ∧ -1 ≤ p.radius :=
      of_decide_eq_true hmem
    exact bound.2.2.2.2

theorem successful_arrange_dimensions (m : Model) (c : Constants)
    (points : List InputPoint) (g : Geometry)
    (h : arrange m c points = .ok g) :
    2 ≤ g.plot.w ∧ 2 ≤ g.plot.h ∧
      g.tiles = (List.range 4).map (tile g.plot) ∧
      g.centres = points.map (centre g.plot c.edge) ∧
      g.radii.length = points.length ∧
      g.pointBoxes.length = points.length ∧
      g.canvas.w = g.plot.x + g.plot.w + c.padX := by
  unfold arrange at h
  dsimp only at h
  obtain ⟨a, _, h⟩ := bind_ok h
  rcases a with ⟨aw, ah, atitle⟩
  dsimp only at h
  obtain ⟨b, _, h⟩ := bind_ok h
  rcases b with ⟨bw, bh, bleft⟩
  dsimp only at h
  obtain ⟨d, _, h⟩ := bind_ok h
  rcases d with ⟨dw, dh, dbottom⟩
  simp only [pure, Except.pure, Except.ok.injEq] at h
  cases h
  dsimp only
  refine ⟨Int.le_max_right _ _, Int.le_max_right _ _, rfl, rfl, ?_, ?_, ?_⟩
  · simp
  · simp
  · omega

theorem successful_arrange_empty (m : Model) (c : Constants) (g : Geometry)
    (hl : m.labels = []) (h : arrange m c [] = .ok g) :
    g =
      let plot : Rect :=
        ⟨c.padX, c.padY, max (c.width - 2 * c.padX) 2,
          max (c.height - 2 * c.padY) 2⟩
      let tiles := (List.range 4).map (tile plot)
      { canvas := ⟨2 * c.padX + plot.w, 2 * c.padY + plot.h⟩,
        plot, tiles,
        inner := tiles.zipIdx.map (fun (r, i) => innerTile c r i),
        centres := [], radii := [], pointBoxes := [] } := by
  simpa [arrange, measureKinds, hl, Pure.pure, Except.pure, Bind.bind, Except.bind] using h.symm

theorem successful_arrange_empty_plot_contained (m : Model) (c : Constants)
    (g : Geometry) (hl : m.labels = []) (h : arrange m c [] = .ok g)
    (hx : 0 ≤ c.padX) (hy : 0 ≤ c.padY) :
    Rect.Contained ⟨0, 0, g.canvas.w, g.canvas.h⟩ g.plot := by
  have he := successful_arrange_empty m c g hl h
  rw [he]
  apply plot_contained
  · exact hx
  · exact hy
  · dsimp only
    omega
  · dsimp only
    omega

theorem successful_arrange_plot_right_margin (m : Model) (c : Constants)
    (points : List InputPoint) (g : Geometry)
    (h : arrange m c points = .ok g) (hx : 0 ≤ c.padX) :
    g.plot.x + g.plot.w ≤ g.canvas.w := by
  have he := (successful_arrange_dimensions m c points g h).2.2.2.2.2.2
  omega

theorem successful_arrange_reservation_bounds (m : Model) (c : Constants)
    (points : List InputPoint) (g : Geometry)
    (h : arrange m c points = .ok g) :
    ∃ title left bottom : Int,
      g.plot.x = c.padX + left ∧
      g.plot.y = c.padY + title ∧
      g.canvas.w = g.plot.x + g.plot.w + c.padX ∧
      g.canvas.h = g.plot.y + g.plot.h + c.padY + bottom := by
  unfold arrange at h
  dsimp only at h
  obtain ⟨a, _, h⟩ := bind_ok h
  rcases a with ⟨aw, ah, atitle⟩
  dsimp only at h
  obtain ⟨b, _, h⟩ := bind_ok h
  rcases b with ⟨bw, bh, bleft⟩
  dsimp only at h
  obtain ⟨d, _, h⟩ := bind_ok h
  rcases d with ⟨dw, dh, dbottom⟩
  simp only [pure, Except.pure, Except.ok.injEq] at h
  cases h
  dsimp only
  refine ⟨(if atitle then
      max (c.titleBand + ah - XY.lineHeight (m.profile == .cell) .title c.titleFont)
        (c.titlePad + ah) else 0),
    (if bleft then max c.yBand (bw + 2 * c.yPad) else 0),
    (if dbottom then
      max (c.xBand + dh - XY.lineHeight (m.profile == .cell) .label c.xFont)
        (c.xPad + dh) else 0), rfl, rfl, ?_, ?_⟩ <;> omega


private theorem foldl_max_nonneg {α : Type} (f : α → Int) (xs : List α)
    (initial : Int) (hi : 0 ≤ initial) :
    0 ≤ xs.foldl (fun n a => max n (f a)) initial := by
  induction xs generalizing initial with
  | nil => exact hi
  | cons a xs ih =>
    exact ih (max initial (f a)) (Int.le_trans hi (Int.le_max_left _ _))

theorem successful_measureKinds_nonneg (m : Model) (c : Constants)
    (target : Int) (kinds : List Nat) (w h : Int) (present : Bool)
    (hm : measureKinds m c target kinds = .ok (w, h, present)) :
    0 ≤ w ∧ 0 ≤ h := by
  unfold measureKinds at hm
  obtain ⟨ts, _, hm⟩ := bind_ok hm
  simp only [pure, Except.pure, Except.ok.injEq] at hm
  cases hm
  exact ⟨foldl_max_nonneg (fun t : XY.TextBox => t.w) ts 0 (by omega),
    foldl_max_nonneg (fun t : XY.TextBox => t.h) ts 0 (by omega)⟩

theorem successful_arrange_nonnegative_reservations (m : Model) (c : Constants)
    (points : List InputPoint) (g : Geometry)
    (h : arrange m c points = .ok g)
    (ht : 0 ≤ c.titlePad) (hx : 0 ≤ c.xPad) (hy : 0 ≤ c.yPad) :
    c.padX ≤ g.plot.x ∧ c.padY ≤ g.plot.y ∧
      g.plot.y + g.plot.h + c.padY ≤ g.canvas.h := by
  unfold arrange at h
  dsimp only at h
  obtain ⟨a, ha, h⟩ := bind_ok h
  rcases a with ⟨aw, ah, atitle⟩
  have hat := (successful_measureKinds_nonneg m c _ _ aw ah atitle ha).2
  dsimp only at h
  obtain ⟨b, hb, h⟩ := bind_ok h
  rcases b with ⟨bw, bh, bleft⟩
  have hbw := (successful_measureKinds_nonneg m c _ _ bw bh bleft hb).1
  dsimp only at h
  obtain ⟨d, hd, h⟩ := bind_ok h
  rcases d with ⟨dw, dh, dbottom⟩
  have hdh := (successful_measureKinds_nonneg m c _ _ dw dh dbottom hd).2
  simp only [pure, Except.pure, Except.ok.injEq] at h
  cases h
  dsimp only
  have htitle :
      0 ≤ (if atitle then
        max (c.titleBand + ah - XY.lineHeight (m.profile == .cell) .title c.titleFont)
          (c.titlePad + ah) else 0) := by
    cases atitle with
    | false => exact Int.le_refl 0
    | true => exact Int.le_trans (by omega) (Int.le_max_right _ _)
  have hleft : 0 ≤ (if bleft then max c.yBand (bw + 2 * c.yPad) else 0) := by
    cases bleft with
    | false => exact Int.le_refl 0
    | true => exact Int.le_trans (by omega) (Int.le_max_right _ _)
  have hbottom :
      0 ≤ (if dbottom then
        max (c.xBand + dh - XY.lineHeight (m.profile == .cell) .label c.xFont)
          (c.xPad + dh) else 0) := by
    cases dbottom with
    | false => exact Int.le_refl 0
    | true => exact Int.le_trans (by omega) (Int.le_max_right _ _)
  exact ⟨by omega, by omega, by omega⟩

theorem successful_arrange_tiles_contained (m : Model) (c : Constants)
    (points : List InputPoint) (g : Geometry)
    (h : arrange m c points = .ok g) (r : Rect) (hr : r ∈ g.tiles) :
    Rect.Contained g.plot r := by
  obtain ⟨hw, hh, ht, _⟩ := successful_arrange_dimensions m c points g h
  rw [ht] at hr
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  exact tile_contained g.plot i (by omega) (by omega)

private theorem getD_contained (outer fallback : Rect) (rects : List Rect)
    (i : Nat) (hf : Rect.Contained outer fallback)
    (hr : ∀ r ∈ rects, Rect.Contained outer r) :
    Rect.Contained outer (rects.getD i fallback) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : rects[i]? with
  | none => exact hf
  | some r => exact hr r (List.mem_of_getElem? hi)

theorem successful_arrange_boxRectFor_contained (m : Model) (c : Constants)
    (points : List InputPoint) (g : Geometry)
    (h : arrange m c points = .ok g)
    (hp : ∀ r ∈ g.pointBoxes, Rect.Contained g.plot r) (id : String) :
    Rect.Contained g.plot (boxRectFor g id) := by
  have hrefl : Rect.Contained g.plot g.plot := Rect.Contained.refl _
  have htiles := successful_arrange_tiles_contained m c points g h
  unfold boxRectFor
  by_cases hplot : id = "plot"
  · simp only [hplot]
    exact hrefl
  · simp only [hplot]
    cases htile : tileIndexOf id with
    | some i => exact getD_contained g.plot g.plot g.tiles i hrefl htiles
    | none =>
      cases hpt : pointIndexOf id with
      | some i => exact getD_contained g.plot g.plot g.pointBoxes i hrefl hp
      | none => exact hrefl

theorem successful_arrange_pointBoxes (m : Model) (c : Constants)
    (points : List InputPoint) (g : Geometry)
    (h : arrange m c points = .ok g) :
    g.pointBoxes = (g.centres.zip g.radii).map (fun (p, r) =>
      if m.profile == .cell && r.x ≤ 1 && r.y ≤ 1 then (⟨p.x, p.y, 1, 1⟩ : Rect)
      else within ⟨p.x - r.x, p.y - r.y, 2 * r.x + c.edge, 2 * r.y + c.edge⟩ g.plot) := by
  unfold arrange at h
  dsimp only at h
  obtain ⟨a, _, h⟩ := bind_ok h
  rcases a with ⟨aw, ah, atitle⟩
  dsimp only at h
  obtain ⟨b, _, h⟩ := bind_ok h
  rcases b with ⟨bw, bh, bleft⟩
  dsimp only at h
  obtain ⟨d, _, h⟩ := bind_ok h
  rcases d with ⟨dw, dh, dbottom⟩
  simp only [pure, Except.pure, Except.ok.injEq] at h
  cases h
  rfl

theorem successful_arrange_radii_nonneg (m : Model) (c : Constants)
    (points : List InputPoint) (g : Geometry)
    (h : arrange m c points = .ok g)
    (hcx : 0 ≤ c.radiusX) (hcy : 0 ≤ c.radiusY)
    (hp : ∀ p ∈ points, -1 ≤ p.radius) :
    ∀ r ∈ g.radii, 0 ≤ r.x ∧ 0 ≤ r.y := by
  unfold arrange at h
  dsimp only at h
  obtain ⟨a, _, h⟩ := bind_ok h
  rcases a with ⟨aw, ah, atitle⟩
  dsimp only at h
  obtain ⟨b, _, h⟩ := bind_ok h
  rcases b with ⟨bw, bh, bleft⟩
  dsimp only at h
  obtain ⟨d, _, h⟩ := bind_ok h
  rcases d with ⟨dw, dh, dbottom⟩
  simp only [pure, Except.pure, Except.ok.injEq] at h
  cases h
  intro r hr
  obtain ⟨p, hpm, rfl⟩ := List.mem_map.mp hr
  have hpr := hp p hpm
  split
  · exact ⟨hcx, hcy⟩
  · rename_i hn
    have hpn : 0 ≤ p.radius := by
      have hne : p.radius ≠ -1 := by
        intro he
        exact hn (by simpa only [beq_iff_eq] using he)
      omega
    constructor
    · change 0 ≤ unitsX m.profile p.radius
      unfold unitsX
      split
      · rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
        omega
      · omega
    · change 0 ≤ unitsY m.profile p.radius
      unfold unitsY
      split
      · rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
        omega
      · omega

theorem successful_arrange_pointBoxes_contained (m : Model) (g : Geometry)
    (h : arrange m (constants m) (pointInputs m) = .ok g)
    (hpoints : ∀ p ∈ pointInputs m,
      0 ≤ p.x ∧ p.x ≤ 1000 ∧ 0 ≤ p.y ∧ p.y ≤ 1000)
    (hradii : ∀ r ∈ g.radii, 0 ≤ r.x ∧ 0 ≤ r.y) :
    ∀ r ∈ g.pointBoxes, Rect.Contained g.plot r := by
  obtain ⟨hw, hh, _, hcentres, _⟩ :=
    successful_arrange_dimensions m (constants m) (pointInputs m) g h
  intro rect hrect
  rw [successful_arrange_pointBoxes m (constants m) (pointInputs m) g h] at hrect
  obtain ⟨⟨p, radius⟩, hpair, rfl⟩ := List.mem_map.mp hrect
  have hpm := (List.of_mem_zip hpair).1
  rw [hcentres] at hpm
  obtain ⟨input, hin, rfl⟩ := List.mem_map.mp hpm
  obtain ⟨hx, hxx, hy, hyy⟩ := hpoints input hin
  obtain ⟨hrx, hry⟩ := hradii radius (List.of_mem_zip hpair).2
  have hedge : (constants m).edge = if m.profile == .cell then 1 else 0 := by
    rfl
  have he : 0 ≤ (constants m).edge := by
    rw [hedge]
    split <;> omega
  have hew : (constants m).edge ≤ g.plot.w := by
    rw [hedge]
    split <;> omega
  have heh : (constants m).edge ≤ g.plot.h := by
    rw [hedge]
    split <;> omega
  split
  rename_i hpairEq
  simp only [Prod.mk.injEq] at hpairEq
  obtain ⟨rfl, rfl⟩ := hpairEq
  split
  · rename_i hsmall
    have hcell : (m.profile == .cell) = true := by
      simp only [Bool.and_eq_true] at hsmall
      exact hsmall.1.1
    have heone : (constants m).edge = 1 := by rw [hedge, hcell]; rfl
    have bx := fdiv_scaled_between input.x 1000 (max (g.plot.w - 3) 0)
      (by omega) hx hxx
    have by_ := fdiv_scaled_between input.y 1000 (max (g.plot.h - 3) 0)
      (by omega) hy hyy
    have wx : 0 ≤ max (g.plot.w - 3) 0 := Int.le_max_right _ _
    have wy : 0 ≤ max (g.plot.h - 3) 0 := Int.le_max_right _ _
    rw [Int.min_eq_left wx, Int.max_eq_right wx] at bx
    rw [Int.min_eq_left wy, Int.max_eq_right wy] at by_
    simp only [Rect.Contained, centre, heone, Int.mul_one]
    omega
  · obtain ⟨_, bx, _, by_⟩ :=
      quadrant_point_in_plot g.plot (constants m).edge input he hew heh
        ⟨hx, hxx⟩ ⟨hy, hyy⟩
    apply within_contained <;> (try dsimp only) <;> omega

theorem sceneOf_canvas (m : Model) (c : Constants) (g : Geometry)
    (ps : List Placement) : (sceneOf m c g ps).canvas = g.canvas := by
  rfl

theorem sceneOf_box_metadata (m : Model) (c : Constants) (g : Geometry)
    (ps : List Placement) :
    (sceneOf m c g ps).boxes =
      m.boxes.map (fun b =>
        ⟨b.id, b.role.id, boxRectFor g b.id, b.parent, b.exclusive⟩) := by
  rfl

theorem sceneOf_label_metadata (m : Model) (c : Constants) (g : Geometry)
    (ps : List Placement) :
    (sceneOf m c g ps).labels.map (fun l => (l.id, l.owner, l.text, l.rect)) =
      ps.map (fun p => (p.label.id, p.label.owner, p.label.text, p.rect)) := by
  simp [sceneOf, List.map_map]

theorem successful_geometry_checkpoint (m : Model) (s : Scene)
    (h : layout m = .ok s) :
    ∃ g ps, arrange m (constants m) (pointInputs m) = .ok g ∧
      place m (constants m) g = .ok ps ∧
      s = sceneOf m (constants m) g ps ∧
      2 ≤ g.plot.w ∧ 2 ≤ g.plot.h ∧
      g.tiles.length = 4 ∧ g.centres.length = (pointInputs m).length ∧
      g.radii.length = (pointInputs m).length ∧
      g.pointBoxes.length = (pointInputs m).length ∧
      (∀ r ∈ g.tiles, Rect.Contained g.plot r) := by
  obtain ⟨g, ps, hg, hp, hs⟩ := successful_scene_assembly m s h
  obtain ⟨hw, hh, ht, hc, hr, hb, _⟩ :=
    successful_arrange_dimensions m (constants m) (pointInputs m) g hg
  refine ⟨g, ps, hg, hp, hs, hw, hh, ?_, ?_, hr, hb, ?_⟩
  · simp [ht]
  · simp [hc]
  · exact fun r hm => successful_arrange_tiles_contained m (constants m)
      (pointInputs m) g hg r hm

theorem successful_arrange_clipped_point_contained (m : Model) (c : Constants)
    (points : List InputPoint) (g : Geometry)
    (h : arrange m c points = .ok g) (p : InputPoint)
    (hx : 0 ≤ p.x ∧ p.x ≤ 1000) (hy : 0 ≤ p.y ∧ p.y ≤ 1000)
    (he : 0 ≤ c.edge) (hew : c.edge ≤ g.plot.w)
    (heh : c.edge ≤ g.plot.h) (radius : Point)
    (hrx : 0 ≤ radius.x) (hry : 0 ≤ radius.y) :
    Rect.Contained g.plot
      (within
        ⟨(centre g.plot c.edge p).x - radius.x,
          (centre g.plot c.edge p).y - radius.y,
          2 * radius.x + c.edge, 2 * radius.y + c.edge⟩ g.plot) := by
  obtain ⟨hw, hh, _⟩ := successful_arrange_dimensions m c points g h
  obtain ⟨_, bx, _, by_⟩ :=
    quadrant_point_in_plot g.plot c.edge p he hew heh hx hy
  apply within_contained
  · dsimp only
    omega
  · dsimp only
    omega
  · omega
  · omega

theorem sceneOf_boxes_nonexclusive (m : Model) (c : Constants) (g : Geometry)
    (ps : List Placement) (hn : ∀ b ∈ m.boxes, b.exclusive = false) :
    ∀ b ∈ (sceneOf m c g ps).layoutDump.boxes, b.exclusive = false := by
  intro b hb
  change b ∈ m.boxes.map (fun a =>
    (⟨a.id, a.role.id, boxRectFor g a.id, a.parent, a.exclusive⟩ : Box)) at hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  exact hn a ha


theorem sceneOf_c1_of_plot_containment (m : Model) (c : Constants)
    (g : Geometry) (ps : List Placement)
    (hp : Rect.Contained ⟨0, 0, g.canvas.w, g.canvas.h⟩ g.plot)
    (hb : ∀ b ∈ m.boxes, Rect.Contained g.plot (boxRectFor g b.id)) :
    Validator.C1 (sceneOf m c g ps).layoutDump := by
  intro b hm
  change b ∈ m.boxes.map (fun a =>
    (⟨a.id, a.role.id, boxRectFor g a.id, a.parent, a.exclusive⟩ : Box)) at hm
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
  have hi := hb a ha
  change Rect.Contained ⟨0, 0, g.canvas.w, g.canvas.h⟩ (boxRectFor g a.id)
  simp only [Rect.Contained] at hp hi ⊢
  omega

theorem sceneOf_c3_of_semantic_parents (m : Model) (c : Constants)
    (g : Geometry) (ps : List Placement)
    (hparents : ∀ a ∈ m.boxes, a.parent = "" ∨ a.parent = "plot")
    (hchildren : ∀ a ∈ m.boxes, a.parent = "plot" →
      Rect.Contained g.plot (boxRectFor g a.id)) :
    Validator.C3 (sceneOf m c g ps).layoutDump := by
  intro b hb hn p hp
  have hpm := List.mem_of_find?_eq_some hp
  have hpid : p.id = b.parent := by
    simpa only [beq_iff_eq] using List.find?_some hp
  change b ∈ m.boxes.map (fun a =>
    (⟨a.id, a.role.id, boxRectFor g a.id, a.parent, a.exclusive⟩ : Box)) at hb
  change p ∈ m.boxes.map (fun a =>
    (⟨a.id, a.role.id, boxRectFor g a.id, a.parent, a.exclusive⟩ : Box)) at hpm
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpm
  have hap : a.parent = "plot" :=
    (hparents a ha).resolve_left hn
  have hqp : q.id = "plot" := hpid.trans hap
  change Rect.Contained (boxRectFor g q.id) (boxRectFor g a.id)
  rw [hqp, boxRectFor_plot]
  exact hchildren a ha hap
theorem successful_boxes_nonexclusive (m : Model) (s : Scene)
    (h : layout m = .ok s) (hn : ∀ b ∈ m.boxes, b.exclusive = false) :
    ∀ b ∈ s.layoutDump.boxes, b.exclusive = false := by
  obtain ⟨g, ps, _, _, rfl⟩ := successful_scene_assembly m s h
  exact sceneOf_boxes_nonexclusive m (constants m) g ps hn

theorem successful_label_clearance (m : Model) (s : Scene)
    (h : layout m = .ok s) (hn : ∀ b ∈ m.boxes, b.exclusive = false) :
    Validator.C7 s.layoutDump := by
  intro l _ b hb he _
  have hf := successful_boxes_nonexclusive m s h hn b hb
  rw [hf] at he
  contradiction

theorem successful_no_group_frames (m : Model) (s : Scene)
    (h : layout m = .ok s) (hn : ∀ b ∈ m.boxes, b.role.id ≠ "group") :
    Validator.C8 s.layoutDump := by
  obtain ⟨g, ps, _, _, rfl⟩ := successful_scene_assembly m s h
  have hroles : ∀ b ∈ (sceneOf m (constants m) g ps).layoutDump.boxes,
      b.role ≠ "group" := by
    intro b hb
    change b ∈ m.boxes.map (fun a =>
      (⟨a.id, a.role.id, boxRectFor g a.id, a.parent, a.exclusive⟩ : Box)) at hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact hn a ha
  constructor
  · intro b hb hg
    exact False.elim (hroles b hb hg)
  · intro b hb hg
    exact False.elim (hroles b hb hg)

end Elegant.Chart.Quadrant

import Elegant.Chart.TreemapAdapter
import Elegant.Kinds.Treemap

namespace Elegant.Treemap

def zeroValueParent : Tile := ⟨0, 0, 10, 10⟩

theorem zero_value_row_geometry :
    (placeRow [0] zeroValueParent 0 0).1 = [⟨0, 0, 10, 0⟩] := by
  decide

theorem zero_value_area_counterexample :
    ((placeRow [0] zeroValueParent 0 0).1.map area).sum ≠ area zeroValueParent := by
  decide

theorem zero_value_squarify_counterexample :
    squarify [0] zeroValueParent 1737350766 2000 =
      .ok ([⟨0, 0, 10, 0⟩], false) := by
  rfl

theorem padded_positive_area_counterexample :
    let parent : Tile := ⟨0, 0, 100, 100⟩
    let inner := childArea parent 10 10 25 10 10
    let cells := (placeRow [1] inner 1 1).1
    (cells.map (fun cell => area (insetCell cell 10 10))).sum ≠ area parent := by
  decide

theorem collapsed_parent_containment_repaired :
    let parent : Tile := ⟨0, 0, 0, 0⟩
    let inner := childArea parent 10 10 25 10 10
    let child := insetCell ((placeRow [1] inner 1 1).1.headD parent) 10 10
    child = parent := by
  decide

theorem childKeyLe_trans (nodes : List Node) (a b c : Nat)
    (hab : childKeyLe nodes a b = true) (hbc : childKeyLe nodes b c = true) :
    childKeyLe nodes a c = true := by
  simp only [childKeyLe, decide_eq_true_eq] at *
  omega

theorem childKeyLe_total (nodes : List Node) (a b : Nat) :
    (childKeyLe nodes a b || childKeyLe nodes b a) = true := by
  simp only [childKeyLe, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem treemap_children_sorted (nodes : List Node) (id : String) :
    (sortedChildren nodes id).Pairwise (fun a b => childKeyLe nodes a b = true) ∧
    sortedChildren nodes id = (children nodes id).mergeSort (childKeyLe nodes) := by
  exact ⟨List.pairwise_mergeSort (childKeyLe_trans nodes) (childKeyLe_total nodes)
    (children nodes id), rfl⟩

theorem sortedChildren_perm (nodes : List Node) (id : String) :
    (sortedChildren nodes id).Perm (children nodes id) :=
  List.mergeSort_perm _ _

theorem roundDiv_mono (a b d : Int) (hd : 0 < d) (hab : a ≤ b) :
    roundDiv a d ≤ roundDiv b d := by
  unfold roundDiv
  exact Chart.fdiv_mono (by omega) (by omega)

theorem roundDiv_zero (d : Int) (hd : 0 < d) : roundDiv 0 d = 0 := by
  unfold roundDiv
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
  exact Int.ediv_eq_zero_of_lt (by omega) (by omega)

theorem roundDiv_whole (d k : Int) (hd : 0 < d) :
    roundDiv (d * k) d = k := by
  unfold roundDiv
  have hlo := Int.fmod_nonneg_of_pos (2 * (d * k) + d) (by omega : 0 < 2 * d)
  have hfactor : 2 * (d * k) + d = (2 * d) * k + d := by
    simp [Int.mul_assoc]
  have hlower : k ≤ Int.fdiv (2 * (d * k) + d) (2 * d) := by
    apply Chart.le_fdiv_of_mul_le (by omega)
    rw [hfactor]
    omega
  have hupper : Int.fdiv (2 * (d * k) + d) (2 * d) < k + 1 := by
    have ht : 2 * (d * k) + d < (2 * d) * (k + 1) := by
      rw [hfactor, Int.mul_add, Int.mul_one]
      omega
    have hbase := Int.mul_fdiv_add_fmod (2 * (d * k) + d) (2 * d)
    by_cases hh : Int.fdiv (2 * (d * k) + d) (2 * d) < k + 1
    · exact hh
    · have hm := Int.mul_le_mul_of_nonneg_left (show k + 1 ≤
          Int.fdiv (2 * (d * k) + d) (2 * d) by omega) (by omega : 0 ≤ 2 * d)
      omega
  omega

theorem containedSpan_bounds (lo hi parentLo parentHi : Int) (h : parentLo ≤ parentHi) :
    parentLo ≤ (containedSpan lo hi parentLo parentHi).1 ∧
    (containedSpan lo hi parentLo parentHi).2 ≤ parentHi := by
  unfold containedSpan
  exact ⟨Int.le_max_left _ _, Int.max_le.mpr ⟨h, Int.min_le_left _ _⟩⟩

theorem childArea_inside (r : Tile) (padX padY header innerX innerY : Int)
    (hx : r.x0 ≤ r.x1) (hy : r.y0 ≤ r.y1) :
    r.x0 ≤ (childArea r padX padY header innerX innerY).x0 ∧
    (childArea r padX padY header innerX innerY).x1 ≤ r.x1 ∧
    r.y0 ≤ (childArea r padX padY header innerX innerY).y0 ∧
    (childArea r padX padY header innerX innerY).y1 ≤ r.y1 := by
  have hxb := containedSpan_bounds (r.x0 + padX - Int.fdiv innerX 2)
    (r.x1 - (padX - Int.fdiv innerX 2)) r.x0 r.x1 hx
  have hyb := containedSpan_bounds (r.y0 + header + padY - Int.fdiv innerY 2)
    (r.y1 - (padY - Int.fdiv innerY 2)) r.y0 r.y1 hy
  exact ⟨hxb.1, hxb.2, hyb.1, hyb.2⟩

theorem insetCell_inside (r : Tile) (innerX innerY : Int)
    (hx : r.x0 ≤ r.x1) (hy : r.y0 ≤ r.y1) :
    r.x0 ≤ (insetCell r innerX innerY).x0 ∧
    (insetCell r innerX innerY).x1 ≤ r.x1 ∧
    r.y0 ≤ (insetCell r innerX innerY).y0 ∧
    (insetCell r innerX innerY).y1 ≤ r.y1 := by
  have hxb := containedSpan_bounds (r.x0 + Int.fdiv innerX 2)
    (r.x1 - Int.fdiv innerX 2) r.x0 r.x1 hx
  have hyb := containedSpan_bounds (r.y0 + Int.fdiv innerY 2)
    (r.y1 - Int.fdiv innerY 2) r.y0 r.y1 hy
  exact ⟨hxb.1, hxb.2, hyb.1, hyb.2⟩

theorem containedSpan_ordered (lo hi parentLo parentHi : Int) :
    (containedSpan lo hi parentLo parentHi).1 ≤
      (containedSpan lo hi parentLo parentHi).2 := by
  unfold containedSpan collapseSpan
  split <;> dsimp <;> omega

theorem childArea_ordered (r : Tile) (padX padY header innerX innerY : Int) :
    (childArea r padX padY header innerX innerY).x0 ≤
      (childArea r padX padY header innerX innerY).x1 ∧
    (childArea r padX padY header innerX innerY).y0 ≤
      (childArea r padX padY header innerX innerY).y1 :=
  ⟨containedSpan_ordered _ _ _ _, containedSpan_ordered _ _ _ _⟩

theorem insetCell_ordered (r : Tile) (innerX innerY : Int) :
    (insetCell r innerX innerY).x0 ≤ (insetCell r innerX innerY).x1 ∧
    (insetCell r innerX innerY).y0 ≤ (insetCell r innerX innerY).y1 :=
  ⟨containedSpan_ordered _ _ _ _, containedSpan_ordered _ _ _ _⟩

def Tile.Inside (inner outer : Tile) : Prop :=
  outer.x0 ≤ inner.x0 ∧ inner.x1 ≤ outer.x1 ∧
    outer.y0 ≤ inner.y0 ∧ inner.y1 ≤ outer.y1

def Tile.Ordered (t : Tile) : Prop := t.x0 ≤ t.x1 ∧ t.y0 ≤ t.y1

theorem tile_inside_trans (a b c : Tile) (hab : a.Inside b) (hbc : b.Inside c) :
    a.Inside c := by
  rcases hab with ⟨h1, h2, h3, h4⟩
  rcases hbc with ⟨h5, h6, h7, h8⟩
  exact ⟨Int.le_trans h5 h1, Int.le_trans h2 h6, Int.le_trans h7 h3, Int.le_trans h4 h8⟩

theorem tile_inside_rect (a b : Tile) (h : a.Inside b) :
    Rect.Contained (tileRect b) (tileRect a) := by
  rcases h with ⟨h1, h2, h3, h4⟩
  simp only [Rect.Contained, tileRect]
  omega

theorem drawn_cell_inside_parent (parent cell : Tile)
    (padX padY header innerX innerY : Int)
    (hp : parent.Ordered) (hc : cell.Ordered)
    (ht : cell.Inside (childArea parent padX padY header innerX innerY)) :
    (insetCell cell innerX innerY).Inside parent := by
  have hi := insetCell_inside cell innerX innerY hc.1 hc.2
  have ha := childArea_inside parent padX padY header innerX innerY hp.1 hp.2
  exact tile_inside_trans _ _ _ hi (tile_inside_trans _ _ _ ht ha)

theorem insetCell_preserves_horizontal_separation (a b : Tile) (innerX innerY : Int)
    (ha : a.Ordered) (hb : b.Ordered) (h : a.x1 ≤ b.x0) :
    (insetCell a innerX innerY).x1 ≤ (insetCell b innerX innerY).x0 := by
  have hia := insetCell_inside a innerX innerY ha.1 ha.2
  have hib := insetCell_inside b innerX innerY hb.1 hb.2
  exact Int.le_trans hia.2.1 (Int.le_trans h hib.1)

theorem insetCell_preserves_vertical_separation (a b : Tile) (innerX innerY : Int)
    (ha : a.Ordered) (hb : b.Ordered) (h : a.y1 ≤ b.y0) :
    (insetCell a innerX innerY).y1 ≤ (insetCell b innerX innerY).y0 := by
  have hia := insetCell_inside a innerX innerY ha.1 ha.2
  have hib := insetCell_inside b innerX innerY hb.1 hb.2
  exact Int.le_trans hia.2.2.2 (Int.le_trans h hib.2.2.1)

def finalBoundary (along total cumulative previous : Int) (values : List Int) : Int :=
  if values.isEmpty then previous
  else if total > 0 then roundDiv (along * (cumulative + values.sum)) total else 0

theorem placeCells_area (r : Tile) (dice : Bool)
    (along thickness total cumulative previous : Int) (values : List Int) :
    ((placeCells r dice along thickness total cumulative previous values).map area).sum =
      thickness * (finalBoundary along total cumulative previous values - previous) := by
  induction values generalizing cumulative previous with
  | nil => simp [placeCells, finalBoundary]
  | cons v vs ih =>
    simp only [placeCells, List.map_cons, List.sum_cons]
    rw [ih]
    cases dice <;> cases vs
    all_goals
      unfold area finalBoundary
      simp
    all_goals
      simp only [Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul, Int.add_assoc]
      simp only [Int.mul_comm]
      omega

theorem placeRow_area (values : List Int) (r : Tile) (total remaining : Int)
    (hv : values ≠ []) (ht : 0 < total) (hs : values.sum = total) :
    let dx := r.x1 - r.x0
    let dy := r.y1 - r.y0
    let across := if dx < dy then dy else dx
    let along := if dx < dy then dx else dy
    let thickness := if remaining > 0 then roundDiv (across * total) remaining else across
    ((placeRow values r total remaining).1.map area).sum = thickness * along := by
  have hempty : values.isEmpty = false := by cases values <;> simp_all
  unfold placeRow
  rw [placeCells_area]
  simp only [finalBoundary, hempty, Bool.false_eq_true, ite_false, ht, ite_true,
    Int.zero_add, hs, Int.sub_zero, decide_eq_true_eq]
  have hround (a : Int) : roundDiv (a * total) total = a := by
    rw [Int.mul_comm]
    exact roundDiv_whole total a ht
  simp only [hround]
  by_cases hr : remaining > 0 <;> simp_all

theorem placeRow_area_conservation (values : List Int) (r : Tile) (total remaining : Int)
    (hv : values ≠ []) (ht : 0 < total) (hs : values.sum = total) :
    ((placeRow values r total remaining).1.map area).sum +
      area (placeRow values r total remaining).2 = area r := by
  rw [placeRow_area values r total remaining hv ht hs]
  unfold placeRow area
  dsimp only
  by_cases hd : r.x1 - r.x0 < r.y1 - r.y0 <;>
    by_cases hr : remaining > 0
  all_goals
    simp only [hd, hr, ht, decide_true, decide_false, Bool.true_and,
      Bool.false_eq_true, ite_true, ite_false]
    simp only [Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul]
    simp only [Int.mul_comm]
    omega

theorem placeCells_zero_area (r : Tile) (dice : Bool)
    (along thickness cumulative : Int) (values : List Int) :
    ∀ cell ∈ placeCells r dice along thickness 0 cumulative 0 values,
      area cell = 0 := by
  induction values generalizing cumulative with
  | nil => simp [placeCells]
  | cons v vs ih =>
    intro cell hcell
    simp only [placeCells, Int.lt_irrefl, ite_false, List.mem_cons] at hcell
    rcases hcell with hcell | hcell
    · subst cell
      cases dice <;> simp [area]
    · exact ih (cumulative + v) cell hcell

theorem placeRow_zero_area (values : List Int) (r : Tile) :
    ∀ cell ∈ (placeRow values r 0 0).1, area cell = 0 := by
  unfold placeRow
  exact placeCells_zero_area _ _ _ _ _ _

theorem nonnegative_sum (values : List Int)
    (hn : ∀ v ∈ values, 0 ≤ v) : 0 ≤ values.sum := by
  induction values with
  | nil => simp
  | cons v vs ih =>
    have hv := hn v (by simp)
    have hvs := ih (fun w hw => hn w (by simp [hw]))
    simp only [List.sum_cons]
    omega

theorem zero_sum_values (values : List Int)
    (hn : ∀ v ∈ values, 0 ≤ v) (hs : values.sum = 0) :
    ∀ v ∈ values, v = 0 := by
  induction values with
  | nil => simp
  | cons v vs ih =>
    have hv := hn v (by simp)
    have hvs : ∀ w ∈ vs, 0 ≤ w := fun w hw => hn w (by simp [hw])
    have hsnonneg := nonnegative_sum vs hvs
    have hsum : vs.sum = 0 := by simp only [List.sum_cons] at hs; omega
    have hvzero : v = 0 := by simp only [List.sum_cons] at hs; omega
    intro w hw
    rcases List.mem_cons.mp hw with h | h
    · exact h.trans hvzero
    · exact ih hvs hsum w h

theorem tileRows_zero_area (steps fuel : Nat) (values : List Int)
    (r : Tile) (rho : Int)
    (hn : ∀ v ∈ values, 0 ≤ v) (hs : values.sum = 0) :
    ∀ cell ∈ (tileRows steps fuel values r 0 rho).1, area cell = 0 := by
  rw [tileRows_zero steps fuel values r rho (zero_sum_values values hn hs)]
  exact placeRow_zero_area values r

def Tile.Separated (a b : Tile) : Prop :=
  a.x1 ≤ b.x0 ∨ b.x1 ≤ a.x0 ∨ a.y1 ≤ b.y0 ∨ b.y1 ≤ a.y0

theorem insetCell_preserves_separation (a b : Tile) (innerX innerY : Int)
    (ha : a.Ordered) (hb : b.Ordered) (h : a.Separated b) :
    (insetCell a innerX innerY).Separated (insetCell b innerX innerY) := by
  rcases h with h | h | h | h
  · exact Or.inl (insetCell_preserves_horizontal_separation a b innerX innerY ha hb h)
  · exact Or.inr (Or.inl
      (insetCell_preserves_horizontal_separation b a innerX innerY hb ha h))
  · exact Or.inr (Or.inr (Or.inl
      (insetCell_preserves_vertical_separation a b innerX innerY ha hb h)))
  · exact Or.inr (Or.inr (Or.inr
      (insetCell_preserves_vertical_separation b a innerX innerY hb ha h)))

theorem drawn_cells_inside_parent (parent : Tile) (cells : List Tile)
    (padX padY header innerX innerY : Int) (hp : parent.Ordered)
    (hc : ∀ cell ∈ cells, cell.Ordered)
    (ht : ∀ cell ∈ cells,
      cell.Inside (childArea parent padX padY header innerX innerY)) :
    ∀ drawn ∈ cells.map (fun cell => insetCell cell innerX innerY),
      drawn.Inside parent := by
  intro drawn hd
  rcases List.mem_map.mp hd with ⟨cell, hcell, rfl⟩
  exact drawn_cell_inside_parent parent cell padX padY header innerX innerY
    hp (hc cell hcell) (ht cell hcell)

theorem roundDiv_fraction_bounds (across total remaining : Int)
    (ha : 0 ≤ across) (ht : 0 ≤ total) (hr : 0 < remaining)
    (hle : total ≤ remaining) :
    0 ≤ roundDiv (across * total) remaining ∧
      roundDiv (across * total) remaining ≤ across := by
  have hn := Int.mul_nonneg ha ht
  have hm := Int.mul_le_mul_of_nonneg_left hle ha
  have hlo := roundDiv_mono 0 (across * total) remaining hr hn
  have hhi := roundDiv_mono (across * total) (across * remaining) remaining hr hm
  rw [roundDiv_zero remaining hr] at hlo
  have hw : roundDiv (across * remaining) remaining = across := by
    rw [Int.mul_comm]
    exact roundDiv_whole remaining across hr
  rw [hw] at hhi
  exact ⟨hlo, hhi⟩

theorem placeRow_free_inside (values : List Int) (r : Tile) (total remaining : Int)
    (ho : r.Ordered) (ht : 0 ≤ total) (hr : 0 < remaining)
    (hle : total ≤ remaining) :
    (placeRow values r total remaining).2.Ordered ∧
      (placeRow values r total remaining).2.Inside r := by
  have hdx : 0 ≤ r.x1 - r.x0 := by have := ho.1; omega
  have hdy : 0 ≤ r.y1 - r.y0 := by have := ho.2; omega
  have hx := roundDiv_fraction_bounds (r.x1 - r.x0) total remaining hdx ht hr hle
  have hy := roundDiv_fraction_bounds (r.y1 - r.y0) total remaining hdy ht hr hle
  unfold placeRow Tile.Ordered Tile.Inside
  by_cases hd : r.x1 - r.x0 < r.y1 - r.y0 <;>
    by_cases hp : 0 < total
  all_goals
    simp only [hd, hp, hr, decide_true, decide_false, Bool.true_and,
      Bool.false_and, ite_true, ite_false, Bool.false_eq_true]
    try dsimp only
    rcases ho with ⟨hox, hoy⟩
    omega

theorem placeCells_bounds (r : Tile) (dice : Bool)
    (along thickness total cumulative previous : Int) (values : List Int)
    (ha : 0 ≤ along) (hh : 0 ≤ thickness) (ht : 0 < total)
    (hc : 0 ≤ cumulative) (hv : ∀ v ∈ values, 0 ≤ v)
    (hs : cumulative + values.sum ≤ total)
    (hp : previous = roundDiv (along * cumulative) total) :
    ∀ cell ∈ placeCells r dice along thickness total cumulative previous values,
      cell.Ordered ∧ cell.Inside
        (if dice then ⟨r.x0 + previous, r.y0, r.x0 + along, r.y0 + thickness⟩
          else ⟨r.x0, r.y0 + previous, r.x0 + thickness, r.y0 + along⟩) := by
  induction values generalizing cumulative previous with
  | nil => simp [placeCells]
  | cons v vs ih =>
    have hv0 := hv v (by simp)
    have hvs : ∀ w ∈ vs, 0 ≤ w := fun w hw => hv w (by simp [hw])
    have hsum := nonnegative_sum vs hvs
    have hnext : cumulative + v ≤ total := by
      simp only [List.sum_cons] at hs
      omega
    have hcum : 0 ≤ cumulative + v := by omega
    have hboundary := roundDiv_fraction_bounds along (cumulative + v) total
      ha hcum ht hnext
    have hmono := roundDiv_mono (along * cumulative) (along * (cumulative + v))
      total ht (Int.mul_le_mul_of_nonneg_left (by omega) ha)
    have hprevious : previous ≤ roundDiv (along * (cumulative + v)) total := by
      simpa only [hp] using hmono
    have hrest : cumulative + v + vs.sum ≤ total := by
      simp only [List.sum_cons] at hs
      omega
    have tail := ih (cumulative + v) (roundDiv (along * (cumulative + v)) total)
      hcum hvs hrest rfl
    intro cell hcell
    simp only [placeCells, ht, ite_true, List.mem_cons] at hcell
    rcases hcell with hcell | hcell
    · subst cell
      cases dice <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        Tile.Ordered, Tile.Inside] <;> omega
    · obtain ⟨hordered, hinside⟩ := tail cell hcell
      refine ⟨hordered, ?_⟩
      cases dice <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        Tile.Inside] at hinside ⊢ <;> omega

theorem placeCells_separated (r : Tile) (dice : Bool)
    (along thickness total cumulative previous : Int) (values : List Int)
    (ha : 0 ≤ along) (hh : 0 ≤ thickness) (ht : 0 < total)
    (hc : 0 ≤ cumulative) (hv : ∀ v ∈ values, 0 ≤ v)
    (hs : cumulative + values.sum ≤ total)
    (hp : previous = roundDiv (along * cumulative) total) :
    (placeCells r dice along thickness total cumulative previous values).Pairwise
      Tile.Separated := by
  induction values generalizing cumulative previous with
  | nil => simp [placeCells]
  | cons v vs ih =>
    have hv0 := hv v (by simp)
    have hvs : ∀ w ∈ vs, 0 ≤ w := fun w hw => hv w (by simp [hw])
    have hcum : 0 ≤ cumulative + v := by omega
    have hrest : cumulative + v + vs.sum ≤ total := by
      simp only [List.sum_cons] at hs
      omega
    have htail := ih (cumulative + v) (roundDiv (along * (cumulative + v)) total)
      hcum hvs hrest rfl
    have hb := placeCells_bounds r dice along thickness total (cumulative + v)
      (roundDiv (along * (cumulative + v)) total) vs ha hh ht hcum hvs hrest rfl
    simp only [placeCells, ht, ite_true, List.pairwise_cons]
    refine ⟨?_, htail⟩
    intro cell hcell
    have hi := (hb cell hcell).2
    cases dice
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      exact hi.2.2.1
    · exact Or.inl hi.1

theorem placeCells_inside (r : Tile) (dice : Bool)
    (along thickness total : Int) (values : List Int)
    (ha : 0 ≤ along) (hh : 0 ≤ thickness) (ht : 0 < total)
    (halong : along ≤ if dice then r.x1 - r.x0 else r.y1 - r.y0)
    (hthick : thickness ≤ if dice then r.y1 - r.y0 else r.x1 - r.x0)
    (hv : ∀ v ∈ values, 0 ≤ v) (hs : values.sum ≤ total) :
    ∀ cell ∈ placeCells r dice along thickness total 0 0 values,
      cell.Ordered ∧ cell.Inside r := by
  have hb := placeCells_bounds r dice along thickness total 0 0 values
    ha hh ht (by omega) hv (by simpa using hs)
    (by rw [Int.mul_zero, roundDiv_zero total ht])
  intro cell hcell
  obtain ⟨ho, hi⟩ := hb cell hcell
  refine ⟨ho, ?_⟩
  cases dice <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    Tile.Inside] at hi halong hthick ⊢ <;> omega

theorem placeRow_cells_inside (values : List Int) (r : Tile) (total remaining : Int)
    (ho : r.Ordered) (hv : ∀ v ∈ values, 0 ≤ v)
    (ht : 0 < total) (hr : 0 < remaining)
    (hs : values.sum = total) (hle : total ≤ remaining) :
    ∀ cell ∈ (placeRow values r total remaining).1,
      cell.Ordered ∧ cell.Inside r := by
  have hdx : 0 ≤ r.x1 - r.x0 := by have := ho.1; omega
  have hdy : 0 ≤ r.y1 - r.y0 := by have := ho.2; omega
  have hx := roundDiv_fraction_bounds (r.x1 - r.x0) total remaining hdx
    (by omega) hr hle
  have hy := roundDiv_fraction_bounds (r.y1 - r.y0) total remaining hdy
    (by omega) hr hle
  by_cases hd : r.x1 - r.x0 < r.y1 - r.y0
  · simpa only [placeRow, hd, ht, hr, decide_true, Bool.true_and, ite_true] using
      placeCells_inside r true (r.x1 - r.x0)
        (roundDiv ((r.y1 - r.y0) * total) remaining) total values
        hdx hy.1 ht (by simp) (by simpa using hy.2) hv (by omega)
  · simpa only [placeRow, hd, ht, hr, decide_false, Bool.true_and,
        decide_true, Bool.false_eq_true, ite_true, ite_false] using
      placeCells_inside r false (r.y1 - r.y0)
        (roundDiv ((r.x1 - r.x0) * total) remaining) total values
        hdy hx.1 ht (by simp) (by simpa using hx.2) hv (by omega)

theorem placeRow_cells_separated (values : List Int) (r : Tile) (total remaining : Int)
    (ho : r.Ordered) (hv : ∀ v ∈ values, 0 ≤ v)
    (ht : 0 < total) (hr : 0 < remaining)
    (hs : values.sum = total) (hle : total ≤ remaining) :
    (placeRow values r total remaining).1.Pairwise Tile.Separated := by
  have hdx : 0 ≤ r.x1 - r.x0 := by have := ho.1; omega
  have hdy : 0 ≤ r.y1 - r.y0 := by have := ho.2; omega
  have hx := roundDiv_fraction_bounds (r.x1 - r.x0) total remaining hdx
    (by omega) hr hle
  have hy := roundDiv_fraction_bounds (r.y1 - r.y0) total remaining hdy
    (by omega) hr hle
  by_cases hd : r.x1 - r.x0 < r.y1 - r.y0
  · simpa only [placeRow, hd, ht, hr, decide_true, Bool.true_and, ite_true] using
      placeCells_separated r true (r.x1 - r.x0)
        (roundDiv ((r.y1 - r.y0) * total) remaining) total 0 0 values
        hdx hy.1 ht (by omega) hv (by omega)
        (by rw [Int.mul_zero, roundDiv_zero total ht])
  · simpa only [placeRow, hd, ht, hr, decide_false, Bool.true_and,
        decide_true, Bool.false_eq_true, ite_true, ite_false] using
      placeCells_separated r false (r.y1 - r.y0)
        (roundDiv ((r.x1 - r.x0) * total) remaining) total 0 0 values
        hdy hx.1 ht (by omega) hv (by omega)
        (by rw [Int.mul_zero, roundDiv_zero total ht])

theorem foldl_add_sum (values : List Int) (initial : Int) :
    values.foldl (· + ·) initial = initial + values.sum := by
  induction values generalizing initial with
  | nil => simp
  | cons v vs ih =>
    simp [List.foldl, ih, Int.add_assoc]

theorem squarify_zero_area (values : List Int) (r : Tile) (rho : Int) (fuel : Nat)
    (out : List Tile) (capped : Bool)
    (hn : ∀ v ∈ values, 0 ≤ v) (hs : values.sum = 0)
    (h : squarify values r rho fuel = .ok (out, capped)) :
    ∀ cell ∈ out, area cell = 0 := by
  unfold squarify at h
  rw [foldl_add_sum] at h
  simp only [Int.zero_add, hs] at h
  split at h
  · contradiction
  · have he := Except.ok.inj h
    have hout := congrArg (fun p : List Tile × Bool => p.1) he
    change (tileRows values.length fuel values r 0 rho).1 = out at hout
    rw [← hout]
    exact tileRows_zero_area values.length fuel values r rho hn hs

theorem drawn_cells_separated (cells : List Tile) (innerX innerY : Int)
    (ho : ∀ cell ∈ cells, cell.Ordered)
    (hs : cells.Pairwise Tile.Separated) :
    (cells.map (fun cell => insetCell cell innerX innerY)).Pairwise Tile.Separated := by
  induction cells with
  | nil => simp
  | cons cell cells ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    simp only [List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih (fun c hc => ho c (by simp [hc])) htail⟩
    intro drawn hd
    rcases List.mem_map.mp hd with ⟨other, hother, rfl⟩
    exact insetCell_preserves_separation cell other innerX innerY
      (ho cell (by simp)) (ho other (by simp [hother])) (hhead other hother)

theorem placeRow_consumes_remaining (values : List Int) (r : Tile) (total : Int)
    (ht : 0 < total) :
    area (placeRow values r total total).2 = 0 := by
  have hx : roundDiv ((r.x1 - r.x0) * total) total = r.x1 - r.x0 := by
    rw [Int.mul_comm]
    exact roundDiv_whole total _ ht
  have hy : roundDiv ((r.y1 - r.y0) * total) total = r.y1 - r.y0 := by
    rw [Int.mul_comm]
    exact roundDiv_whole total _ ht
  unfold placeRow
  by_cases hd : r.x1 - r.x0 < r.y1 - r.y0
  all_goals
    simp only [hd, ht, decide_true, decide_false, Bool.true_and,
      Bool.false_eq_true, ite_true, ite_false, hx, hy, area]
    have hcancel (a b : Int) : b - (a + (b - a)) = 0 := by omega
    simp only [hcancel, Int.mul_zero, Int.zero_mul]

theorem placeCells_zero_inside (r : Tile) (dice : Bool)
    (along thickness cumulative : Int) (values : List Int)
    (ho : r.Ordered) (ht : 0 ≤ thickness)
    (hle : thickness ≤ if dice then r.y1 - r.y0 else r.x1 - r.x0) :
    ∀ cell ∈ placeCells r dice along thickness 0 cumulative 0 values,
      cell.Ordered ∧ cell.Inside r := by
  induction values generalizing cumulative with
  | nil => simp [placeCells]
  | cons v vs ih =>
    intro cell hcell
    simp only [placeCells, Int.lt_irrefl, ite_false, List.mem_cons] at hcell
    rcases hcell with hcell | hcell
    · subst cell
      rcases ho with ⟨hox, hoy⟩
      cases dice <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        Tile.Ordered, Tile.Inside] at hle ⊢ <;> omega
    · exact ih (cumulative + v) cell hcell

theorem placeRow_zero_inside (values : List Int) (r : Tile) (ho : r.Ordered) :
    ∀ cell ∈ (placeRow values r 0 0).1, cell.Ordered ∧ cell.Inside r := by
  have hdx : 0 ≤ r.x1 - r.x0 := by have := ho.1; omega
  have hdy : 0 ≤ r.y1 - r.y0 := by have := ho.2; omega
  by_cases hd : r.x1 - r.x0 < r.y1 - r.y0
  · simpa only [placeRow, hd, decide_true, Bool.false_and,
        Int.lt_irrefl, decide_false, Bool.false_eq_true, ite_false, ite_true] using
      placeCells_zero_inside r true (r.x1 - r.x0) (r.y1 - r.y0) 0 values
        ho hdy (by simp)
  · simpa only [placeRow, hd, decide_false, Bool.false_and, Bool.false_eq_true,
        Int.lt_irrefl, ite_false] using
      placeCells_zero_inside r false (r.y1 - r.y0) (r.x1 - r.x0) 0 values
        ho hdx (by simp)

theorem placeCells_zero_shape (r : Tile) (dice : Bool)
    (along thickness cumulative : Int) (values : List Int) :
    ∀ cell ∈ placeCells r dice along thickness 0 cumulative 0 values,
      cell = if dice then ⟨r.x0, r.y0, r.x0, r.y0 + thickness⟩
        else ⟨r.x0, r.y0, r.x0 + thickness, r.y0⟩ := by
  induction values generalizing cumulative with
  | nil => simp [placeCells]
  | cons v vs ih =>
    intro cell hc
    simp only [placeCells, Int.lt_irrefl, ite_false, List.mem_cons] at hc
    rcases hc with hc | hc
    · subst cell
      cases dice <;> simp only [Int.add_zero]
    · exact ih (cumulative + v) cell hc

theorem placeCells_zero_separated (r : Tile) (dice : Bool)
    (along thickness cumulative : Int) (values : List Int) :
    (placeCells r dice along thickness 0 cumulative 0 values).Pairwise
      Tile.Separated := by
  induction values generalizing cumulative with
  | nil => simp [placeCells]
  | cons v vs ih =>
    simp only [placeCells, Int.lt_irrefl, ite_false, List.pairwise_cons]
    refine ⟨?_, ih (cumulative + v)⟩
    intro cell hc
    have he := placeCells_zero_shape r dice along thickness (cumulative + v) vs cell hc
    rw [he]
    cases dice <;> simp [Tile.Separated]

theorem placeRow_zero_separated (values : List Int) (r : Tile) :
    (placeRow values r 0 0).1.Pairwise Tile.Separated := by
  unfold placeRow
  exact placeCells_zero_separated _ _ _ _ _ _

theorem tileRows_zero_inside (steps fuel : Nat) (values : List Int)
    (r : Tile) (rho : Int) (ho : r.Ordered)
    (hn : ∀ v ∈ values, 0 ≤ v) (hs : values.sum = 0) :
    ∀ cell ∈ (tileRows steps fuel values r 0 rho).1,
      cell.Ordered ∧ cell.Inside r := by
  rw [tileRows_zero steps fuel values r rho (zero_sum_values values hn hs)]
  exact placeRow_zero_inside values r ho

theorem tileRows_zero_separated (steps fuel : Nat) (values : List Int)
    (r : Tile) (rho : Int)
    (hn : ∀ v ∈ values, 0 ≤ v) (hs : values.sum = 0) :
    (tileRows steps fuel values r 0 rho).1.Pairwise Tile.Separated := by
  rw [tileRows_zero steps fuel values r rho (zero_sum_values values hn hs)]
  exact placeRow_zero_separated values r

theorem zero_area_sum (cells : List Tile)
    (hz : ∀ cell ∈ cells, area cell = 0) : (cells.map area).sum = 0 := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hz cell (by simp), ih (fun c hc => hz c (by simp [hc]))]
    rfl

theorem tileRows_area_exact (steps fuel : Nat) (values : List Int)
    (r : Tile) (remaining rho : Int)
    (hn : ∀ v ∈ values, 0 ≤ v) (hsum : values.sum = remaining)
    (hr : 0 < remaining) (hs : values.length ≤ steps) (hf : values.length ≤ fuel) :
    ((tileRows steps fuel values r remaining rho).1.map area).sum = area r := by
  induction steps generalizing fuel values r remaining with
  | zero =>
    have hempty : values = [] := by cases values <;> simp_all
    simp [hempty] at hsum
    omega
  | succ steps ih =>
    cases values with
    | nil => simp at hsum; omega
    | cons v vs =>
      cases fuel with
      | zero => simp only [List.length_cons] at hf; omega
      | succ fuel =>
        let next := nextRow (v :: vs) r remaining rho
        let row := next.1
        let rest := next.2.1
        let total := next.2.2
        let free := (placeRow row r total remaining).2
        have hp : row ++ rest = v :: vs := nextRow_partition _ _ _ _
        have hrow : ∀ w ∈ row, 0 ≤ w := by
          intro w hw
          apply hn w
          rw [← hp]
          exact List.mem_append.mpr (Or.inl hw)
        have hrest : ∀ w ∈ rest, 0 ≤ w := by
          intro w hw
          apply hn w
          rw [← hp]
          exact List.mem_append.mpr (Or.inr hw)
        have hrowSum : row.sum = total := nextRow_sum _ _ _ _ hsum
        have hrestSum : rest.sum = remaining - total :=
          nextRow_remaining_sum _ _ _ _ hsum
        have ht : 0 < total := nextRow_positive _ _ _ _ hn hsum hr
        have hnonempty : row ≠ [] := nextRow_nonempty _ _ _ _ _
        have hshort : rest.length < (v :: vs).length :=
          nextRow_rest_shorter _ _ _ _ _
        have hsteps : rest.length ≤ steps := by
          simp only [List.length_cons] at hs hshort
          omega
        have hfuel : rest.length ≤ fuel := by
          simp only [List.length_cons] at hf hshort
          omega
        have hconserve := placeRow_area_conservation row r total remaining
          hnonempty ht hrowSum
        change (((placeRow row r total remaining).1 ++
          (tileRows steps fuel rest free (remaining - total) rho).1).map area).sum =
          area r
        rw [List.map_append, List.sum_append]
        have hnrest := nonnegative_sum rest hrest
        by_cases hpositive : 0 < remaining - total
        · rw [ih fuel rest free (remaining - total) hrest hrestSum
            hpositive hsteps hfuel]
          exact hconserve
        · have hzero : remaining - total = 0 := by omega
          have hremaining : remaining = total := by omega
          have hzeroValues : rest.sum = 0 := by omega
          have htail := tileRows_zero_area steps fuel rest free rho hrest hzeroValues
          rw [hzero, zero_area_sum _ htail]
          have hfree : area free = 0 := by
            dsimp only [free]
            rw [hremaining]
            exact placeRow_consumes_remaining row r total ht
          change ((placeRow row r total remaining).1.map area).sum + area free = area r
            at hconserve
          rw [hfree] at hconserve
          exact hconserve

theorem treemap_area_exact (values : List Int) (r : Tile) (rho : Int) (fuel : Nat)
    (out : List Tile) (capped : Bool)
    (hn : ∀ v ∈ values, 0 ≤ v) (hf : values.length ≤ fuel)
    (h : squarify values r rho fuel = .ok (out, capped)) :
    (0 < values.sum → (out.map area).sum = area r) ∧
      (values.sum = 0 → ∀ cell ∈ out, area cell = 0) := by
  refine ⟨?_, fun hz => squarify_zero_area values r rho fuel out capped hn hz h⟩
  intro ht
  unfold squarify at h
  rw [foldl_add_sum] at h
  simp only [Int.zero_add] at h
  split at h
  · contradiction
  · have he := Except.ok.inj h
    have hout := congrArg (fun p : List Tile × Bool => p.1) he
    change (tileRows values.length fuel values r values.sum rho).1 = out at hout
    rw [← hout]
    exact tileRows_area_exact values.length fuel values r values.sum rho
      hn rfl ht (Nat.le_refl _) hf

theorem placeCells_cross_end (r : Tile) (dice : Bool)
    (along thickness total cumulative previous : Int) (values : List Int) :
    ∀ cell ∈ placeCells r dice along thickness total cumulative previous values,
      if dice then cell.y1 = r.y0 + thickness else cell.x1 = r.x0 + thickness := by
  induction values generalizing cumulative previous with
  | nil => simp [placeCells]
  | cons v vs ih =>
    intro cell hcell
    simp only [placeCells, List.mem_cons] at hcell
    rcases hcell with hcell | hcell
    · subst cell
      cases dice <;> rfl
    · exact ih _ _ cell hcell

theorem placeRow_before_free (values : List Int) (r : Tile) (total remaining : Int)
    (cell later : Tile) (hc : cell ∈ (placeRow values r total remaining).1)
    (hl : later.Inside (placeRow values r total remaining).2) :
    cell.Separated later := by
  let dx := r.x1 - r.x0
  let dy := r.y1 - r.y0
  let dice := decide (dx < dy)
  let along := if dice then dx else dy
  let across := if dice then dy else dx
  let thickness := if total > 0 && remaining > 0 then
    roundDiv (across * total) remaining else across
  have he := placeCells_cross_end r dice along thickness total 0 0 values cell hc
  by_cases hd : dx < dy
  · have hcell : cell.y1 = r.y0 + thickness := by simpa [dice, hd] using he
    have hfree : (placeRow values r total remaining).2.y0 = r.y0 + thickness := by
      change (if dice then { r with y0 := r.y0 + thickness }
        else { r with x0 := r.x0 + thickness }).y0 = _
      rw [show dice = true by simp [dice, hd]]
      rfl
    have hlower : r.y0 + thickness ≤ later.y0 := hfree ▸ hl.2.2.1
    exact Or.inr (Or.inr (Or.inl (by omega)))
  · have hcell : cell.x1 = r.x0 + thickness := by simpa [dice, hd] using he
    have hfree : (placeRow values r total remaining).2.x0 = r.x0 + thickness := by
      change (if dice then { r with y0 := r.y0 + thickness }
        else { r with x0 := r.x0 + thickness }).x0 = _
      rw [show dice = false by simp [dice, hd]]
      rfl
    have hlower : r.x0 + thickness ≤ later.x0 := hfree ▸ hl.1
    exact Or.inl (by omega)

theorem tileRows_geometry (steps fuel : Nat) (values : List Int)
    (r : Tile) (remaining rho : Int)
    (hn : ∀ v ∈ values, 0 ≤ v) (hsum : values.sum = remaining)
    (ho : r.Ordered) (hs : values.length ≤ steps) :
    (∀ cell ∈ (tileRows steps fuel values r remaining rho).1,
      cell.Ordered ∧ cell.Inside r) ∧
      (tileRows steps fuel values r remaining rho).1.Pairwise Tile.Separated := by
  induction steps generalizing fuel values r remaining with
  | zero =>
    have hempty : values = [] := by cases values <;> simp_all
    subst values
    simp [tileRows, placeRow, placeCells]
  | succ steps ih =>
    by_cases hr : 0 < remaining
    · cases values with
      | nil => simp at hsum; omega
      | cons v vs =>
        cases fuel with
        | zero =>
          have hc := placeRow_cells_inside (v :: vs) r remaining remaining
            ho hn hr hr hsum (Int.le_refl _)
          have hp := placeRow_cells_separated (v :: vs) r remaining remaining
            ho hn hr hr hsum (Int.le_refl _)
          simpa [tileRows, tileRows_nil] using And.intro hc hp
        | succ fuel =>
          let next := nextRow (v :: vs) r remaining rho
          let row := next.1
          let rest := next.2.1
          let total := next.2.2
          let free := (placeRow row r total remaining).2
          have hp : row ++ rest = v :: vs := nextRow_partition _ _ _ _
          have hrow : ∀ w ∈ row, 0 ≤ w := by
            intro w hw
            apply hn w
            rw [← hp]
            exact List.mem_append.mpr (Or.inl hw)
          have hrest : ∀ w ∈ rest, 0 ≤ w := by
            intro w hw
            apply hn w
            rw [← hp]
            exact List.mem_append.mpr (Or.inr hw)
          have hrowSum : row.sum = total := nextRow_sum _ _ _ _ hsum
          have hrestSum : rest.sum = remaining - total :=
            nextRow_remaining_sum _ _ _ _ hsum
          have ht : 0 < total := nextRow_positive _ _ _ _ hn hsum hr
          have hnrest := nonnegative_sum rest hrest
          have hle : total ≤ remaining := by omega
          have hshort : rest.length < (v :: vs).length :=
            nextRow_rest_shorter _ _ _ _ _
          have hsteps : rest.length ≤ steps := by
            simp only [List.length_cons] at hs hshort
            omega
          have hfree := placeRow_free_inside row r total remaining ho (by omega) hr hle
          have htail := ih fuel rest free (remaining - total)
            hrest hrestSum hfree.1 hsteps
          have hcells := placeRow_cells_inside row r total remaining
            ho hrow ht hr hrowSum hle
          have hpairs := placeRow_cells_separated row r total remaining
            ho hrow ht hr hrowSum hle
          change (∀ cell ∈ (placeRow row r total remaining).1 ++
            (tileRows steps fuel rest free (remaining - total) rho).1,
              cell.Ordered ∧ cell.Inside r) ∧
            ((placeRow row r total remaining).1 ++
              (tileRows steps fuel rest free (remaining - total) rho).1).Pairwise
                Tile.Separated
          refine ⟨?_, List.pairwise_append.mpr ⟨hpairs, htail.2, ?_⟩⟩
          · intro cell hc
            rcases List.mem_append.mp hc with hc | hc
            · exact hcells cell hc
            · have hc' := htail.1 cell hc
              exact ⟨hc'.1, tile_inside_trans cell free r hc'.2 hfree.2⟩
          · intro cell hc later hl
            exact placeRow_before_free row r total remaining cell later hc
              (htail.1 later hl).2
    · have hnremaining : 0 ≤ remaining := by
        rw [← hsum]
        exact nonnegative_sum values hn
      have hz : remaining = 0 := by omega
      have hsumzero : values.sum = 0 := hsum.trans hz
      rw [hz]
      exact ⟨tileRows_zero_inside _ _ _ _ _ ho hn hsumzero,
        tileRows_zero_separated _ _ _ _ _ hn hsumzero⟩

theorem parentDepth_stable (nodes : List Node) (fuel : Nat) (id : String)
    (h : parentDepth nodes fuel id < fuel) :
    parentDepth nodes (fuel + 1) id = parentDepth nodes fuel id := by
  induction fuel generalizing id with
  | zero => omega
  | succ fuel ih =>
    by_cases hid : id = ""
    · subst id
      simp only [parentDepth]
    · cases hn : nodes.find? (fun n => n.source.id == id) with
      | none => simp [parentDepth, hn]
      | some n =>
        have htail : parentDepth nodes fuel n.source.parent < fuel := by
          have hstep : 1 + parentDepth nodes fuel n.source.parent < fuel + 1 := by
            simpa [parentDepth, hid, hn] using h
          omega
        simpa [parentDepth, hid, hn] using
          congrArg Nat.succ (ih n.source.parent htail)

theorem dependencyRanks_sorted (nodes : List Node) :
    ((dependencyRanks nodes).mergeSort (fun a b => decide (a.2 ≤ b.2))).Pairwise
      (fun a b => decide (a.2 ≤ b.2) = true) := by
  apply List.pairwise_mergeSort
  · intro a b c hab hbc
    simp only [decide_eq_true_eq] at *
    omega
  · intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega

theorem dependencyRanks_perm (nodes : List Node) :
    ((dependencyRanks nodes).mergeSort (fun a b => decide (a.2 ≤ b.2))).Perm
      (dependencyRanks nodes) :=
  List.mergeSort_perm _ _

theorem squarify_geometry (values : List Int) (r : Tile) (rho : Int) (fuel : Nat)
    (out : List Tile) (capped : Bool)
    (hn : ∀ v ∈ values, 0 ≤ v) (ho : r.Ordered)
    (h : squarify values r rho fuel = .ok (out, capped)) :
    (∀ cell ∈ out, cell.Ordered ∧ cell.Inside r) ∧
      out.Pairwise Tile.Separated := by
  unfold squarify at h
  rw [foldl_add_sum] at h
  simp only [Int.zero_add] at h
  split at h
  · contradiction
  · have he := Except.ok.inj h
    have hout := congrArg (fun p : List Tile × Bool => p.1) he
    change (tileRows values.length fuel values r values.sum rho).1 = out at hout
    rw [← hout]
    exact tileRows_geometry values.length fuel values r values.sum rho
      hn rfl ho (Nat.le_refl _)

theorem squarify_drawn_geometry (values : List Int) (parent : Tile)
    (padX padY header innerX innerY rho : Int) (fuel : Nat)
    (out : List Tile) (capped : Bool)
    (hn : ∀ v ∈ values, 0 ≤ v) (hp : parent.Ordered)
    (h : squarify values (childArea parent padX padY header innerX innerY)
      rho fuel = .ok (out, capped)) :
    (∀ drawn ∈ out.map (fun cell => insetCell cell innerX innerY),
      drawn.Ordered ∧ drawn.Inside parent) ∧
      (out.map (fun cell => insetCell cell innerX innerY)).Pairwise
        Tile.Separated := by
  have hg := squarify_geometry values
    (childArea parent padX padY header innerX innerY) rho fuel out capped hn
    (childArea_ordered parent padX padY header innerX innerY) h
  refine ⟨?_, drawn_cells_separated out innerX innerY
    (fun cell hc => (hg.1 cell hc).1) hg.2⟩
  intro drawn hd
  rcases List.mem_map.mp hd with ⟨cell, hc, rfl⟩
  exact ⟨insetCell_ordered cell innerX innerY,
    drawn_cell_inside_parent parent cell padX padY header innerX innerY hp
      (hg.1 cell hc).1 (hg.1 cell hc).2⟩

theorem tile_separated_rect (a b : Tile) (h : a.Separated b) :
    Disjoint (tileRect a) (tileRect b) := by
  unfold Disjoint Rect.meetsInterior tileRect
  rcases h with h | h | h | h <;> dsimp only <;> omega

theorem treemap_children_disjoint (values : List Int) (parent : Tile)
    (padX padY header innerX innerY rho : Int) (fuel : Nat)
    (out : List Tile) (capped : Bool)
    (hn : ∀ v ∈ values, 0 ≤ v) (hp : parent.Ordered)
    (h : squarify values (childArea parent padX padY header innerX innerY)
      rho fuel = .ok (out, capped)) :
    (out.map (fun cell => tileRect (insetCell cell innerX innerY))).Pairwise Disjoint := by
  have hg := squarify_drawn_geometry values parent padX padY header innerX innerY
    rho fuel out capped hn hp h
  have hd := hg.2.map tileRect (fun a b hab => tile_separated_rect a b hab)
  simpa only [List.map_map, Function.comp_def] using hd

theorem treemap_children_inside_parent (values : List Int) (parent : Tile)
    (padX padY header innerX innerY rho : Int) (fuel : Nat)
    (out : List Tile) (capped : Bool)
    (hn : ∀ v ∈ values, 0 ≤ v) (hp : parent.Ordered)
    (h : squarify values (childArea parent padX padY header innerX innerY)
      rho fuel = .ok (out, capped)) :
    ∀ child ∈ out.map (fun cell => tileRect (insetCell cell innerX innerY)),
      Rect.Contained (tileRect parent) child := by
  have hg := squarify_drawn_geometry values parent padX padY header innerX innerY
    rho fuel out capped hn hp h
  intro child hc
  obtain ⟨cell, hcell, rfl⟩ := List.mem_map.mp hc
  have hi := (hg.1 (insetCell cell innerX innerY) (List.mem_map.mpr ⟨cell, hcell, rfl⟩)).2
  exact tile_inside_rect _ _ hi

theorem layout_box_from_tiled_node (m : Model) (scene : Scene)
    (h : layout m = .ok scene) (box : Box) (hb : box ∈ scene.boxes) :
    ∃ node : Node,
      box.id = node.source.id ∧
      box.parent = node.source.parent ∧
      box.rect = tileRect node.rect := by
  obtain ⟨nodes, _, hboxes, _, _⟩ := layout_execution m scene h
  rw [hboxes] at hb
  obtain ⟨node, _, rfl⟩ := List.mem_map.mp hb
  exact ⟨node, rfl, rfl, rfl⟩

theorem successful_canvas_eq (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) :
    result.scene.canvas = ⟨(constants m).width,
      (if (labelText m "title").isEmpty then 0 else (constants m).titleBand) +
        (constants m).height⟩ := by
  obtain ⟨_, _, _, hcanvas, _⟩ := layout_execution m result.scene
    (Kinds.Treemap.layout_adapter_success m result h)
  exact hcanvas

theorem successful_canvas_width_nonnegative (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) :
    0 ≤ result.scene.canvas.w := by
  rw [successful_canvas_eq m result h]
  exact Kinds.Treemap.layout_width_nonnegative m result h

theorem successful_canvas_height_nonnegative (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) :
    0 ≤ result.scene.canvas.h := by
  have hh := Kinds.Treemap.layout_height_nonnegative m result h
  have hb : 0 ≤ (constants m).titleBand := by
    change 0 ≤ LayoutConst.treemap_title_band.get m.profile
    cases m.profile <;> decide
  rw [successful_canvas_eq m result h]
  dsimp only
  split <;> omega

theorem successful_root_ordered (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) (band : Int) :
    (⟨0, band, (constants m).width, band + (constants m).height⟩ : Tile).Ordered := by
  have hw := Kinds.Treemap.layout_width_nonnegative m result h
  have hh := Kinds.Treemap.layout_height_nonnegative m result h
  exact ⟨hw, by dsimp only; omega⟩

theorem treemap_children_geometry (values : List Int) (parent : Tile)
    (padX padY header innerX innerY rho : Int) (fuel : Nat)
    (out : List Tile) (capped : Bool)
    (hn : ∀ v ∈ values, 0 ≤ v) (hp : parent.Ordered)
    (h : squarify values (childArea parent padX padY header innerX innerY)
      rho fuel = .ok (out, capped)) :
    (out.map (fun cell => tileRect (insetCell cell innerX innerY))).Pairwise Disjoint ∧
    ∀ child ∈ out.map (fun cell => tileRect (insetCell cell innerX innerY)),
      Rect.Contained (tileRect parent) child :=
  ⟨treemap_children_disjoint values parent padX padY header innerX innerY rho
      fuel out capped hn hp h,
    treemap_children_inside_parent values parent padX padY header innerX innerY rho
      fuel out capped hn hp h⟩

theorem squarify_values_nonnegative (values : List Int) (r : Tile) (rho : Int)
    (fuel : Nat) (out : List Tile) (capped : Bool)
    (h : squarify values r rho fuel = .ok (out, capped)) :
    ∀ v ∈ values, 0 ≤ v := by
  intro v hv
  apply Classical.byContradiction
  intro hn
  have hvneg : v < 0 := by omega
  have hbad : values.any (· < 0) = true :=
    List.any_eq_true.mpr ⟨v, hv, by simpa only [decide_eq_true_eq] using hvneg⟩
  unfold squarify at h
  simp only [hbad, Bool.true_or, ite_true] at h
  cases h

theorem treemap_children_geometry_of_success (values : List Int) (parent : Tile)
    (padX padY header innerX innerY rho : Int) (fuel : Nat)
    (out : List Tile) (capped : Bool) (hp : parent.Ordered)
    (h : squarify values (childArea parent padX padY header innerX innerY)
      rho fuel = .ok (out, capped)) :
    (out.map (fun cell => tileRect (insetCell cell innerX innerY))).Pairwise Disjoint ∧
    ∀ child ∈ out.map (fun cell => tileRect (insetCell cell innerX innerY)),
      Rect.Contained (tileRect parent) child := by
  exact treemap_children_geometry values parent padX padY header innerX innerY rho
    fuel out capped
    (squarify_values_nonnegative values
      (childArea parent padX padY header innerX innerY) rho fuel out capped h) hp h

theorem modify_preserves_ordered (nodes : List Node) (i : Nat) (f : Node → Node)
    (hn : ∀ n ∈ nodes, n.rect.Ordered)
    (hf : ∀ n, n.rect.Ordered → (f n).rect.Ordered) :
    ∀ n ∈ nodes.modify i f, n.rect.Ordered := by
  induction nodes generalizing i with
  | nil =>
    intro n h
    simp at h
  | cons first rest ih =>
    have hfirst := hn first (List.mem_cons_self)
    have hrest : ∀ n ∈ rest, n.rect.Ordered :=
      fun n h => hn n (List.mem_cons_of_mem first h)
    cases i with
    | zero =>
      change ∀ n ∈ f first :: rest, n.rect.Ordered
      intro n h
      rcases List.mem_cons.mp h with h | h
      · subst n
        exact hf first hfirst
      · exact hrest n h
    | succ i =>
      change ∀ n ∈ first :: rest.modify i f, n.rect.Ordered
      intro n h
      rcases List.mem_cons.mp h with h | h
      · subst n
        exact hfirst
      · exact ih i hrest n h

theorem assigned_cells_ordered (nodes : List Node) (assignments : List (Nat × Tile))
    (innerX innerY : Int) (hn : ∀ n ∈ nodes, n.rect.Ordered) :
    ∀ n ∈ assignments.foldl (fun out (j, cell) =>
      out.modify j (fun old => { old with rect := insetCell cell innerX innerY })) nodes,
      n.rect.Ordered := by
  induction assignments generalizing nodes with
  | nil => exact hn
  | cons assignment rest ih =>
    apply ih
    exact modify_preserves_ordered nodes assignment.1
      (fun old => { old with rect := insetCell assignment.2 innerX innerY }) hn
      (fun _ _ => insetCell_ordered assignment.2 innerX innerY)

def declarationOrderWitness : Model := {
  kind := "treemap"
  profile := .cell
  boxes := [
    { id := "root", role := .group, exclusive := false },
    { id := "h", role := .group, parent := "g", exclusive := false },
    { id := "g", role := .group, parent := "root", exclusive := false },
    { id := "leaf", parent := "h" }]
  regionSets := [{ parent := 0, regions := [0, 0, 1] }]
}

theorem declarationOrderWitness_wellFormed : WellFormed declarationOrderWitness := by
  decide

theorem declarationOrderWitness_withinLimits : WithinLimits declarationOrderWitness := by
  decide

namespace DeclarationOrderExecution

private def witness : Model := declarationOrderWitness

private def initial : List Treemap.Node := [
  { source := { id := "root", role := .group, exclusive := false } },
  { source := { id := "h", role := .group, parent := "g", exclusive := false } },
  { source := { id := "g", role := .group, parent := "root", exclusive := false } },
  { source := { id := "leaf", parent := "h" }, value := 1 }]

private def aggregated : List Treemap.Node := [
  { source := { id := "root", role := .group, exclusive := false }, value := 1 },
  { source := { id := "h", role := .group, parent := "g", exclusive := false }, value := 1 },
  { source := { id := "g", role := .group, parent := "root", exclusive := false }, value := 1 },
  { source := { id := "leaf", parent := "h" }, value := 1 }]

theorem initial_eq : Treemap.initialNodes witness = initial := by
  rfl

theorem dependency_order_eq :
    Treemap.dependencyOrder (Treemap.initialNodes witness) = [0, 2, 1, 3] := by
  change ((([(0, 0), (1, 2), (2, 1), (3, 3)] : List (Nat × Nat)).mergeSort
    (fun a b => decide (a.2 ≤ b.2))).map (·.1)) = [0, 2, 1, 3]
  simp [List.mergeSort, List.MergeSort.Internal.splitInTwo]

theorem aggregate_eq : Treemap.aggregate (Treemap.initialNodes witness) = aggregated := by
  unfold Treemap.aggregate
  rw [dependency_order_eq]
  rfl

theorem aggregated_order_eq :
    Treemap.dependencyOrder aggregated = [0, 2, 1, 3] := by
  change ((([(0, 0), (1, 2), (2, 1), (3, 3)] : List (Nat × Nat)).mergeSort
    (fun a b => decide (a.2 ≤ b.2))).map (·.1)) = [0, 2, 1, 3]
  simp [List.mergeSort, List.MergeSort.Internal.splitInTwo]

theorem series_eq : Treemap.assignSeries aggregated = aggregated := by
  unfold Treemap.assignSeries
  rw [aggregated_order_eq]
  rfl

private def seeded : List Treemap.Node :=
  aggregated.map fun n => if n.source.id == "root" then
    { n with rect := ⟨0, 0, 120, 32⟩ } else n


theorem seeded_order_eq :
    Treemap.dependencyOrder seeded = [0, 2, 1, 3] := by
  change ((([(0, 0), (1, 2), (2, 1), (3, 3)] : List (Nat × Nat)).mergeSort
    (fun a b => decide (a.2 ≤ b.2))).map (·.1)) = [0, 2, 1, 3]
  simp [List.mergeSort, List.MergeSort.Internal.splitInTwo]

theorem constants_eq : Treemap.constants witness =
    { width := 120, height := 32, titleBand := 2, header := 2,
      padX := 2, padY := 1, innerX := 2, innerY := 1,
      rho := 1737350766, fuel := 2000 : Treemap.Consts } := by
  rfl

theorem root_children_eq : Treemap.sortedChildren seeded "root" = [2] := by
  change ([2] : List Nat).mergeSort (Treemap.childKeyLe seeded) = [2]
  exact List.mergeSort_singleton _

theorem root_child_area_eq :
    Treemap.childArea ⟨0, 0, 120, 32⟩
      (Treemap.constants witness).padX (Treemap.constants witness).padY
      (Treemap.constants witness).header (Treemap.constants witness).innerX
      (Treemap.constants witness).innerY = ⟨1, 3, 119, 31⟩ := by
  rw [constants_eq]
  rfl

theorem root_squarify_eq :
    Treemap.squarify [1]
      (Treemap.childArea ⟨0, 0, 120, 32⟩
        (Treemap.constants witness).padX (Treemap.constants witness).padY
        (Treemap.constants witness).header (Treemap.constants witness).innerX
        (Treemap.constants witness).innerY)
      (Treemap.constants witness).rho (Treemap.constants witness).fuel =
        .ok ([⟨1, 3, 119, 31⟩], false) := by
  rw [root_child_area_eq, constants_eq]
  rfl

theorem root_placement_eq :
    (do
      let (cells, _) ← Treemap.squarify [1]
        (Treemap.childArea ⟨0, 0, 120, 32⟩
          (Treemap.constants witness).padX (Treemap.constants witness).padY
          (Treemap.constants witness).header (Treemap.constants witness).innerX
          (Treemap.constants witness).innerY)
        (Treemap.constants witness).rho (Treemap.constants witness).fuel
      pure (([2].zip cells).foldl (fun (out : List Treemap.Node) (j, cell) =>
        out.modify j (fun old => { old with rect := (Treemap.insetCell cell
          (Treemap.constants witness).innerX (Treemap.constants witness).innerY) }))
        seeded)) =
      .ok (seeded.modify 2 (fun old => { old with rect := ⟨2, 3, 118, 31⟩ })) := by
  rw [root_squarify_eq, constants_eq]
  rfl

private def afterRoot : List Treemap.Node :=
  seeded.modify 2 (fun old => { old with rect := ⟨2, 3, 118, 31⟩ })

private def afterG : List Treemap.Node :=
  afterRoot.modify 1 (fun old => { old with rect := ⟨4, 6, 116, 30⟩ })

private def tiled : List Treemap.Node :=
  afterG.modify 3 (fun old => { old with rect := ⟨6, 9, 114, 29⟩ })

theorem g_children_eq : Treemap.sortedChildren afterRoot "g" = [1] := by
  change ([1] : List Nat).mergeSort (Treemap.childKeyLe afterRoot) = [1]
  exact List.mergeSort_singleton _

theorem g_squarify_eq :
    Treemap.squarify [1]
      (Treemap.childArea ⟨2, 3, 118, 31⟩
        (Treemap.constants witness).padX (Treemap.constants witness).padY
        (Treemap.constants witness).header (Treemap.constants witness).innerX
        (Treemap.constants witness).innerY)
      (Treemap.constants witness).rho (Treemap.constants witness).fuel =
        .ok ([⟨3, 6, 117, 30⟩], false) := by
  rw [constants_eq]
  rfl

theorem g_placement_eq :
    (do
      let (cells, _) ← Treemap.squarify [1]
        (Treemap.childArea ⟨2, 3, 118, 31⟩
          (Treemap.constants witness).padX (Treemap.constants witness).padY
          (Treemap.constants witness).header (Treemap.constants witness).innerX
          (Treemap.constants witness).innerY)
        (Treemap.constants witness).rho (Treemap.constants witness).fuel
      pure (([1].zip cells).foldl (fun (out : List Treemap.Node) (j, cell) =>
        out.modify j (fun old => { old with rect := (Treemap.insetCell cell
          (Treemap.constants witness).innerX (Treemap.constants witness).innerY) }))
        afterRoot)) = .ok afterG := by
  rw [g_squarify_eq, constants_eq]
  rfl

theorem h_children_eq : Treemap.sortedChildren afterG "h" = [3] := by
  change ([3] : List Nat).mergeSort (Treemap.childKeyLe afterG) = [3]
  exact List.mergeSort_singleton _

theorem h_squarify_eq :
    Treemap.squarify [1]
      (Treemap.childArea ⟨4, 6, 116, 30⟩
        (Treemap.constants witness).padX (Treemap.constants witness).padY
        (Treemap.constants witness).header (Treemap.constants witness).innerX
        (Treemap.constants witness).innerY)
      (Treemap.constants witness).rho (Treemap.constants witness).fuel =
        .ok ([⟨5, 9, 115, 29⟩], false) := by
  rw [constants_eq]
  rfl

theorem h_placement_eq :
    (do
      let (cells, _) ← Treemap.squarify [1]
        (Treemap.childArea ⟨4, 6, 116, 30⟩
          (Treemap.constants witness).padX (Treemap.constants witness).padY
          (Treemap.constants witness).header (Treemap.constants witness).innerX
          (Treemap.constants witness).innerY)
        (Treemap.constants witness).rho (Treemap.constants witness).fuel
      pure (([3].zip cells).foldl (fun (out : List Treemap.Node) (j, cell) =>
        out.modify j (fun old => { old with rect := (Treemap.insetCell cell
          (Treemap.constants witness).innerX (Treemap.constants witness).innerY) }))
        afterG)) = .ok tiled := by
  rw [h_squarify_eq, constants_eq]
  rfl

theorem leaf_children_eq : Treemap.sortedChildren tiled "leaf" = [] := by
  change ([] : List Nat).mergeSort (Treemap.childKeyLe tiled) = []
  exact List.mergeSort_nil

theorem seeded_eq :
    (aggregated.map fun n => if n.source.id == "root" then
      { n with rect := ⟨0,
        (if (Treemap.labelText witness "title").isEmpty then 0
          else (Treemap.constants witness).titleBand),
        (Treemap.constants witness).width,
        (if (Treemap.labelText witness "title").isEmpty then 0
          else (Treemap.constants witness).titleBand) +
            (Treemap.constants witness).height⟩ } else n) = seeded := by
  rfl

private theorem seeded_val2 :
    (Option.map Treemap.Node.value seeded[2]?).getD 0 = 1 := rfl

private theorem seeded_rect0 : seeded[0]? = some
    ({ source := { id := "root", role := .group, exclusive := false },
       value := 1, rect := ⟨0, 0, 120, 32⟩ } : Treemap.Node) := rfl

private theorem afterRoot_val1 :
    (Option.map Treemap.Node.value afterRoot[1]?).getD 0 = 1 := rfl

private theorem afterRoot_rect2 : afterRoot[2]? = some
    ({ source := { id := "g", role := .group, parent := "root", exclusive := false },
       value := 1, rect := ⟨2, 3, 118, 31⟩ } : Treemap.Node) := rfl

private theorem afterG_val3 :
    (Option.map Treemap.Node.value afterG[3]?).getD 0 = 1 := rfl

private theorem afterG_rect1 : afterG[1]? = some
    ({ source := { id := "h", role := .group, parent := "g", exclusive := false },
       value := 1, rect := ⟨4, 6, 116, 30⟩ } : Treemap.Node) := rfl

set_option backward.dsimp.instances true in
theorem tiling_eq : Treemap.tileNodes (Treemap.constants witness) seeded = .ok tiled := by
  let step : List Treemap.Node → Nat → Except LayoutError (List Treemap.Node) :=
    fun (acc : List Treemap.Node) (i : Nat) => do
      match acc[i]? with
      | none => pure acc
      | some n =>
        let order := Treemap.sortedChildren acc n.source.id
        if order.isEmpty then pure acc else do
          let values := order.map (fun j => (acc[j]?).map Treemap.Node.value |>.getD 0)
          let c := Treemap.constants witness
          let free := Treemap.childArea n.rect c.padX c.padY c.header c.innerX c.innerY
          let (cells, _) ← Treemap.squarify values free c.rho c.fuel
          pure ((order.zip cells).foldl (fun out (j, cell) =>
            out.modify j (fun old => { old with rect := Treemap.insetCell cell c.innerX c.innerY })) acc)
  have hroot : step seeded 0 = .ok afterRoot := by
    dsimp only [step]
    rw [seeded_rect0]
    dsimp only
    rw [root_children_eq]
    simp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte, List.map, seeded_val2]
    exact root_placement_eq
  have hg : step afterRoot 2 = .ok afterG := by
    dsimp only [step]
    rw [afterRoot_rect2]
    dsimp only
    rw [g_children_eq]
    simp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte, List.map, afterRoot_val1]
    exact g_placement_eq
  have hh : step afterG 1 = .ok tiled := by
    dsimp only [step]
    rw [afterG_rect1]
    dsimp only
    rw [h_children_eq]
    simp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte, List.map, afterG_val3]
    exact h_placement_eq
  have hleaf : step tiled 3 = .ok tiled := by
    dsimp only [step]
    change (if (Treemap.sortedChildren tiled "leaf").isEmpty then
      pure tiled else _) = Except.ok tiled
    rw [leaf_children_eq]
    rfl
  change List.foldlM step seeded (Treemap.dependencyOrder seeded) = .ok tiled
  rw [seeded_order_eq]
  simp only [List.foldlM_cons, hroot, hg, hh, hleaf, List.foldlM_nil,
    bind, Except.bind, pure, Except.pure]

theorem public_success : ∃ result, Kinds.Treemap.layout witness = .ok result := by
  have hs : ∃ scene, Treemap.layout witness = .ok scene := by
    unfold Treemap.layout
    dsimp only
    rw [aggregate_eq, series_eq]
    rw [seeded_eq, tiling_eq]
    exact ⟨_, rfl⟩
  obtain ⟨scene, hs⟩ := hs
  refine ⟨{ scene, budgetExhausted := false }, ?_⟩
  unfold Kinds.Treemap.layout
  rw [hs]
  rfl


private def output : Scene := {
  kind := witness.kind
  profile := witness.profile
  options := { witness.options with direction := .TB }
  canvas := ⟨120, 32⟩
  boxes := tiled.map fun n =>
    { id := n.source.id, role := n.source.role.id, rect := tileRect n.rect,
      parent := n.source.parent, exclusive := n.source.exclusive }
  items := [BoxRole.group, BoxRole.node] |>.flatMap fun role =>
    (tiled.filter (fun n => n.source.role == role)).map fun n =>
      let r := tileRect n.rect
      let style := if role == .group then "group" else "series"
      let paint : Paint := { style, series := ⟨n.series % 12, Nat.mod_lt _ (by decide)⟩ }
      { role := if role == .group then GroupRole.group else .node
        owner := n.source.id
        items := if n.source.id == "root" || r.w ≤ 0 || r.h ≤ 0 then []
          else [Primitive.rect r paint] }
}

theorem layout_eq : Treemap.layout witness = .ok output := by
  unfold Treemap.layout
  dsimp only
  rw [aggregate_eq, series_eq, seeded_eq, tiling_eq]
  rfl

theorem public_layout_eq : Kinds.Treemap.layout witness =
    .ok { scene := output, budgetExhausted := false } := by
  unfold Kinds.Treemap.layout
  rw [layout_eq]
  rfl

theorem output_valid : HardConstraints output.layoutDump := by
  apply (Validator.check_iff _).mp
  decide

end DeclarationOrderExecution
theorem declarationOrderWitness_layout_valid :
    match Kinds.Treemap.layout declarationOrderWitness with
    | .error _ => False
    | .ok result => HardConstraints result.scene.layoutDump := by
  have hw : declarationOrderWitness = DeclarationOrderExecution.witness := rfl
  rw [hw, DeclarationOrderExecution.public_layout_eq]
  exact DeclarationOrderExecution.output_valid

def declarationOrderControl : Model :=
  { declarationOrderWitness with boxes := [
      { id := "root", role := .group, exclusive := false },
      { id := "g", role := .group, parent := "root", exclusive := false },
      { id := "h", role := .group, parent := "g", exclusive := false },
      { id := "leaf", parent := "h" }] }

namespace DeclarationOrderControlExecution

private def witness : Model := declarationOrderControl

private def initial : List Treemap.Node := [
  { source := { id := "root", role := .group, exclusive := false } },
  { source := { id := "g", role := .group, parent := "root", exclusive := false } },
  { source := { id := "h", role := .group, parent := "g", exclusive := false } },
  { source := { id := "leaf", parent := "h" }, value := 1 }]

private def aggregated : List Treemap.Node := [
  { source := { id := "root", role := .group, exclusive := false }, value := 1 },
  { source := { id := "g", role := .group, parent := "root", exclusive := false }, value := 1 },
  { source := { id := "h", role := .group, parent := "g", exclusive := false }, value := 1 },
  { source := { id := "leaf", parent := "h" }, value := 1 }]

theorem initial_eq : Treemap.initialNodes witness = initial := by
  rfl

theorem dependency_order_eq :
    Treemap.dependencyOrder (Treemap.initialNodes witness) = [0, 1, 2, 3] := by
  change ((([(0, 0), (1, 1), (2, 2), (3, 3)] : List (Nat × Nat)).mergeSort
    (fun a b => decide (a.2 ≤ b.2))).map (·.1)) = [0, 1, 2, 3]
  simp [List.mergeSort, List.MergeSort.Internal.splitInTwo]

theorem aggregate_eq : Treemap.aggregate (Treemap.initialNodes witness) = aggregated := by
  unfold Treemap.aggregate
  rw [dependency_order_eq]
  rfl

theorem aggregated_order_eq :
    Treemap.dependencyOrder aggregated = [0, 1, 2, 3] := by
  change ((([(0, 0), (1, 1), (2, 2), (3, 3)] : List (Nat × Nat)).mergeSort
    (fun a b => decide (a.2 ≤ b.2))).map (·.1)) = [0, 1, 2, 3]
  simp [List.mergeSort, List.MergeSort.Internal.splitInTwo]

theorem series_eq : Treemap.assignSeries aggregated = aggregated := by
  unfold Treemap.assignSeries
  rw [aggregated_order_eq]
  rfl

private def seeded : List Treemap.Node :=
  aggregated.map fun n => if n.source.id == "root" then
    { n with rect := ⟨0, 0, 120, 32⟩ } else n


theorem seeded_order_eq :
    Treemap.dependencyOrder seeded = [0, 1, 2, 3] := by
  change ((([(0, 0), (1, 1), (2, 2), (3, 3)] : List (Nat × Nat)).mergeSort
    (fun a b => decide (a.2 ≤ b.2))).map (·.1)) = [0, 1, 2, 3]
  simp [List.mergeSort, List.MergeSort.Internal.splitInTwo]

theorem constants_eq : Treemap.constants witness =
    { width := 120, height := 32, titleBand := 2, header := 2,
      padX := 2, padY := 1, innerX := 2, innerY := 1,
      rho := 1737350766, fuel := 2000 : Treemap.Consts } := by
  rfl

theorem root_children_eq : Treemap.sortedChildren seeded "root" = [1] := by
  change ([1] : List Nat).mergeSort (Treemap.childKeyLe seeded) = [1]
  exact List.mergeSort_singleton _

theorem root_child_area_eq :
    Treemap.childArea ⟨0, 0, 120, 32⟩
      (Treemap.constants witness).padX (Treemap.constants witness).padY
      (Treemap.constants witness).header (Treemap.constants witness).innerX
      (Treemap.constants witness).innerY = ⟨1, 3, 119, 31⟩ := by
  rw [constants_eq]
  rfl

theorem root_squarify_eq :
    Treemap.squarify [1]
      (Treemap.childArea ⟨0, 0, 120, 32⟩
        (Treemap.constants witness).padX (Treemap.constants witness).padY
        (Treemap.constants witness).header (Treemap.constants witness).innerX
        (Treemap.constants witness).innerY)
      (Treemap.constants witness).rho (Treemap.constants witness).fuel =
        .ok ([⟨1, 3, 119, 31⟩], false) := by
  rw [root_child_area_eq, constants_eq]
  rfl

theorem root_placement_eq :
    (do
      let (cells, _) ← Treemap.squarify [1]
        (Treemap.childArea ⟨0, 0, 120, 32⟩
          (Treemap.constants witness).padX (Treemap.constants witness).padY
          (Treemap.constants witness).header (Treemap.constants witness).innerX
          (Treemap.constants witness).innerY)
        (Treemap.constants witness).rho (Treemap.constants witness).fuel
      pure (([1].zip cells).foldl (fun (out : List Treemap.Node) (j, cell) =>
        out.modify j (fun old => { old with rect := (Treemap.insetCell cell
          (Treemap.constants witness).innerX (Treemap.constants witness).innerY) }))
        seeded)) =
      .ok (seeded.modify 1 (fun old => { old with rect := ⟨2, 3, 118, 31⟩ })) := by
  rw [root_squarify_eq, constants_eq]
  rfl

private def afterRoot : List Treemap.Node :=
  seeded.modify 1 (fun old => { old with rect := ⟨2, 3, 118, 31⟩ })

private def afterG : List Treemap.Node :=
  afterRoot.modify 2 (fun old => { old with rect := ⟨4, 6, 116, 30⟩ })

private def tiled : List Treemap.Node :=
  afterG.modify 3 (fun old => { old with rect := ⟨6, 9, 114, 29⟩ })

theorem g_children_eq : Treemap.sortedChildren afterRoot "g" = [2] := by
  change ([2] : List Nat).mergeSort (Treemap.childKeyLe afterRoot) = [2]
  exact List.mergeSort_singleton _

theorem g_squarify_eq :
    Treemap.squarify [1]
      (Treemap.childArea ⟨2, 3, 118, 31⟩
        (Treemap.constants witness).padX (Treemap.constants witness).padY
        (Treemap.constants witness).header (Treemap.constants witness).innerX
        (Treemap.constants witness).innerY)
      (Treemap.constants witness).rho (Treemap.constants witness).fuel =
        .ok ([⟨3, 6, 117, 30⟩], false) := by
  rw [constants_eq]
  rfl

theorem g_placement_eq :
    (do
      let (cells, _) ← Treemap.squarify [1]
        (Treemap.childArea ⟨2, 3, 118, 31⟩
          (Treemap.constants witness).padX (Treemap.constants witness).padY
          (Treemap.constants witness).header (Treemap.constants witness).innerX
          (Treemap.constants witness).innerY)
        (Treemap.constants witness).rho (Treemap.constants witness).fuel
      pure (([2].zip cells).foldl (fun (out : List Treemap.Node) (j, cell) =>
        out.modify j (fun old => { old with rect := (Treemap.insetCell cell
          (Treemap.constants witness).innerX (Treemap.constants witness).innerY) }))
        afterRoot)) = .ok afterG := by
  rw [g_squarify_eq, constants_eq]
  rfl

theorem h_children_eq : Treemap.sortedChildren afterG "h" = [3] := by
  change ([3] : List Nat).mergeSort (Treemap.childKeyLe afterG) = [3]
  exact List.mergeSort_singleton _

theorem h_squarify_eq :
    Treemap.squarify [1]
      (Treemap.childArea ⟨4, 6, 116, 30⟩
        (Treemap.constants witness).padX (Treemap.constants witness).padY
        (Treemap.constants witness).header (Treemap.constants witness).innerX
        (Treemap.constants witness).innerY)
      (Treemap.constants witness).rho (Treemap.constants witness).fuel =
        .ok ([⟨5, 9, 115, 29⟩], false) := by
  rw [constants_eq]
  rfl

theorem h_placement_eq :
    (do
      let (cells, _) ← Treemap.squarify [1]
        (Treemap.childArea ⟨4, 6, 116, 30⟩
          (Treemap.constants witness).padX (Treemap.constants witness).padY
          (Treemap.constants witness).header (Treemap.constants witness).innerX
          (Treemap.constants witness).innerY)
        (Treemap.constants witness).rho (Treemap.constants witness).fuel
      pure (([3].zip cells).foldl (fun (out : List Treemap.Node) (j, cell) =>
        out.modify j (fun old => { old with rect := (Treemap.insetCell cell
          (Treemap.constants witness).innerX (Treemap.constants witness).innerY) }))
        afterG)) = .ok tiled := by
  rw [h_squarify_eq, constants_eq]
  rfl

theorem leaf_children_eq : Treemap.sortedChildren tiled "leaf" = [] := by
  change ([] : List Nat).mergeSort (Treemap.childKeyLe tiled) = []
  exact List.mergeSort_nil

theorem seeded_eq :
    (aggregated.map fun n => if n.source.id == "root" then
      { n with rect := ⟨0,
        (if (Treemap.labelText witness "title").isEmpty then 0
          else (Treemap.constants witness).titleBand),
        (Treemap.constants witness).width,
        (if (Treemap.labelText witness "title").isEmpty then 0
          else (Treemap.constants witness).titleBand) +
            (Treemap.constants witness).height⟩ } else n) = seeded := by
  rfl

private theorem seeded_val1 :
    (Option.map Treemap.Node.value seeded[1]?).getD 0 = 1 := rfl

private theorem seeded_rect0 : seeded[0]? = some
    ({ source := { id := "root", role := .group, exclusive := false },
       value := 1, rect := ⟨0, 0, 120, 32⟩ } : Treemap.Node) := rfl

private theorem afterRoot_val2 :
    (Option.map Treemap.Node.value afterRoot[2]?).getD 0 = 1 := rfl

private theorem afterRoot_rect1 : afterRoot[1]? = some
    ({ source := { id := "g", role := .group, parent := "root", exclusive := false },
       value := 1, rect := ⟨2, 3, 118, 31⟩ } : Treemap.Node) := rfl

private theorem afterG_val3 :
    (Option.map Treemap.Node.value afterG[3]?).getD 0 = 1 := rfl

private theorem afterG_rect2 : afterG[2]? = some
    ({ source := { id := "h", role := .group, parent := "g", exclusive := false },
       value := 1, rect := ⟨4, 6, 116, 30⟩ } : Treemap.Node) := rfl

set_option backward.dsimp.instances true in
theorem tiling_eq : Treemap.tileNodes (Treemap.constants witness) seeded = .ok tiled := by
  let step : List Treemap.Node → Nat → Except LayoutError (List Treemap.Node) :=
    fun (acc : List Treemap.Node) (i : Nat) => do
      match acc[i]? with
      | none => pure acc
      | some n =>
        let order := Treemap.sortedChildren acc n.source.id
        if order.isEmpty then pure acc else do
          let values := order.map (fun j => (acc[j]?).map Treemap.Node.value |>.getD 0)
          let c := Treemap.constants witness
          let free := Treemap.childArea n.rect c.padX c.padY c.header c.innerX c.innerY
          let (cells, _) ← Treemap.squarify values free c.rho c.fuel
          pure ((order.zip cells).foldl (fun out (j, cell) =>
            out.modify j (fun old => { old with rect := Treemap.insetCell cell c.innerX c.innerY })) acc)
  have hroot : step seeded 0 = .ok afterRoot := by
    dsimp only [step]
    rw [seeded_rect0]
    dsimp only
    rw [root_children_eq]
    simp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte, List.map, seeded_val1]
    exact root_placement_eq
  have hg : step afterRoot 1 = .ok afterG := by
    dsimp only [step]
    rw [afterRoot_rect1]
    dsimp only
    rw [g_children_eq]
    simp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte, List.map, afterRoot_val2]
    exact g_placement_eq
  have hh : step afterG 2 = .ok tiled := by
    dsimp only [step]
    rw [afterG_rect2]
    dsimp only
    rw [h_children_eq]
    simp only [List.isEmpty, Bool.false_eq_true, ↓reduceIte, List.map, afterG_val3]
    exact h_placement_eq
  have hleaf : step tiled 3 = .ok tiled := by
    dsimp only [step]
    change (if (Treemap.sortedChildren tiled "leaf").isEmpty then
      pure tiled else _) = Except.ok tiled
    rw [leaf_children_eq]
    rfl
  change List.foldlM step seeded (Treemap.dependencyOrder seeded) = .ok tiled
  rw [seeded_order_eq]
  simp only [List.foldlM_cons, hroot, hg, hh, hleaf, List.foldlM_nil,
    bind, Except.bind, pure, Except.pure]

theorem public_success : ∃ result, Kinds.Treemap.layout witness = .ok result := by
  have hs : ∃ scene, Treemap.layout witness = .ok scene := by
    unfold Treemap.layout
    dsimp only
    rw [aggregate_eq, series_eq]
    rw [seeded_eq, tiling_eq]
    exact ⟨_, rfl⟩
  obtain ⟨scene, hs⟩ := hs
  refine ⟨{ scene, budgetExhausted := false }, ?_⟩
  unfold Kinds.Treemap.layout
  rw [hs]
  rfl


private def output : Scene := {
  kind := witness.kind
  profile := witness.profile
  options := { witness.options with direction := .TB }
  canvas := ⟨120, 32⟩
  boxes := tiled.map fun n =>
    { id := n.source.id, role := n.source.role.id, rect := tileRect n.rect,
      parent := n.source.parent, exclusive := n.source.exclusive }
  items := [BoxRole.group, BoxRole.node] |>.flatMap fun role =>
    (tiled.filter (fun n => n.source.role == role)).map fun n =>
      let r := tileRect n.rect
      let style := if role == .group then "group" else "series"
      let paint : Paint := { style, series := ⟨n.series % 12, Nat.mod_lt _ (by decide)⟩ }
      { role := if role == .group then GroupRole.group else .node
        owner := n.source.id
        items := if n.source.id == "root" || r.w ≤ 0 || r.h ≤ 0 then []
          else [Primitive.rect r paint] }
}

theorem layout_eq : Treemap.layout witness = .ok output := by
  unfold Treemap.layout
  dsimp only
  rw [aggregate_eq, series_eq, seeded_eq, tiling_eq]
  rfl

theorem public_layout_eq : Kinds.Treemap.layout witness =
    .ok { scene := output, budgetExhausted := false } := by
  unfold Kinds.Treemap.layout
  rw [layout_eq]
  rfl

theorem output_valid : HardConstraints output.layoutDump := by
  apply (Validator.check_iff _).mp
  decide

end DeclarationOrderControlExecution
theorem declarationOrderControl_layout_valid :
    match Kinds.Treemap.layout declarationOrderControl with
    | .error _ => False
    | .ok result => HardConstraints result.scene.layoutDump := by
  have hw : declarationOrderControl = DeclarationOrderControlExecution.witness := rfl
  rw [hw, DeclarationOrderControlExecution.public_layout_eq]
  exact DeclarationOrderControlExecution.output_valid

def negativeWidthWitness : Model := {
  kind := "treemap"
  profile := .cell
  options := { config := [("nodeWidth", .integer (-1))] }
  boxes := [{ id := "a" }]
}

theorem negativeWidthWitness_wellFormed : WellFormed negativeWidthWitness := by
  decide

theorem negativeWidthWitness_withinLimits : WithinLimits negativeWidthWitness := by
  decide

private def negativeWidthScene : Scene := {
  kind := "treemap"
  profile := .cell
  options := negativeWidthWitness.options
  canvas := ⟨-1, 32⟩
  boxes := [{ id := "a", role := "node", rect := ⟨0, 0, 0, 0⟩, parent := "", exclusive := true }]
  items := [{ role := .node, owner := "a", items := [] }]
}

theorem negativeWidthWitness_layout_eq :
    Treemap.layout negativeWidthWitness = .ok negativeWidthScene := by
  have horder : dependencyOrder (initialNodes negativeWidthWitness) = [0] := by
    change ((([(0, 0)] : List (Nat × Nat)).mergeSort
      (fun a b => decide (a.2 ≤ b.2))).map (·.1)) = [0]
    simp only [List.mergeSort_singleton, List.map]
  have ha : aggregate (initialNodes negativeWidthWitness) =
      initialNodes negativeWidthWitness := by
    unfold aggregate
    rw [horder]
    rfl
  have hs : assignSeries (initialNodes negativeWidthWitness) =
      initialNodes negativeWidthWitness := by
    unfold assignSeries
    rw [horder]
    rfl
  have ht : tileNodes (constants negativeWidthWitness)
      (initialNodes negativeWidthWitness) = .ok (initialNodes negativeWidthWitness) := by
    unfold tileNodes
    rw [horder]
    simp [initialNodes, negativeWidthWitness, sortedChildren, children,
      List.foldlM_cons, List.foldlM_nil, List.mergeSort_nil] <;> rfl
  have hseed (c : Consts) (band : Int) :
      ((initialNodes negativeWidthWitness).map fun n =>
        if n.source.id == "root" then
          { n with rect := ⟨0, band, c.width, band + c.height⟩ } else n) =
        initialNodes negativeWidthWitness := by
    rfl
  have htitle : placeTitle negativeWidthWitness (constants negativeWidthWitness)
      (initialLabels negativeWidthWitness) = .ok [] := by
    rfl
  have hlabels (lc : LeafConsts) :
      (initialNodes negativeWidthWitness).foldlM (fun ls n =>
        if n.source.id == "root" then Except.ok ls
        else if (children (initialNodes negativeWidthWitness) n.source.id).isEmpty then
          placeLeaf negativeWidthWitness lc n ls
        else placeHeader negativeWidthWitness (constants negativeWidthWitness) n ls)
        [] = .ok [] := by
    rfl
  show layout negativeWidthWitness = .ok negativeWidthScene
  unfold layout
  dsimp only
  rw [ha, hs, hseed, ht]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [htitle]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rw [hlabels]
  dsimp only [bind, Except.bind, pure, Except.pure]
  rfl

theorem negativeWidthWitness_rejected :
    Kinds.Treemap.layout negativeWidthWitness = .error (.geometry .domain) := by
  rfl

def negativeHeightWitness : Model := {
  kind := "treemap"
  profile := .cell
  options := { config := [("nodeHeight", .integer (-2))] }
}

theorem negativeHeightWitness_wellFormed : WellFormed negativeHeightWitness := by
  decide

theorem negativeHeightWitness_withinLimits : WithinLimits negativeHeightWitness := by
  decide

theorem negativeHeightWitness_height :
    (constants negativeHeightWitness).height = -1 := by
  rfl

theorem negativeHeightWitness_rejected :
    Kinds.Treemap.layout negativeHeightWitness = .error (.geometry .domain) := by
  rfl

namespace C7Counterexample

/-- Own-label regression for the exempt-owner-and-ancestors C7 contract:
    `x.name` is placed strictly inside its owner `x`; revised scope
    `["x", "root"]` exempts the own box, so `c7Dump` now satisfies C7. -/
def c7Witness : Model := {
  kind := "treemap",
  profile := .cell,
  boxes := [{ id := "root", role := .group, exclusive := false },
            { id := "x", parent := "root" }],
  labels := [{ id := "x.name", owner := "x", text := "x" }],
  regionSets := [{ parent := 0, regions := [1] }] }

theorem c7Witness_wellFormed : WellFormed c7Witness := by
  decide

theorem c7Witness_withinLimits : WithinLimits c7Witness := by
  decide

/-- The independently defined dump for the own-label regression. The
    executable input above is preserved for parent probing; no definitional
    layout-equality claim is made here. -/
def c7Dump : LayoutDump :=
  { canvas := ⟨120, 32⟩,
    boxes := [{ id := "root", role := "group", rect := ⟨0, 0, 120, 32⟩,
                parent := "", exclusive := false },
              { id := "x", role := "node", rect := ⟨2, 3, 116, 28⟩,
                parent := "root", exclusive := true }],
    routes := [],
    labels := [{ id := "x.name", owner := "x", rect := ⟨59, 16, 1, 1⟩,
                 lines := ["x"] }] }

theorem c7Dump_satisfies_c7 : Validator.C7 c7Dump :=
  (Validator.c7_iff c7Dump).mp (by decide)

/-- Runnable C7 counterexample surviving the exempt-owner-and-ancestors
    contract: identical geometry to `c7Witness`, but the placed label
    `x.name` is owned by `"root"` instead of `"x"`. Model WF only requires
    the owner to name any box (`Model.lean:129`); placement looks the label
    up by id (`TreemapAdapter.lean:196,211`) and copies `source.owner`
    verbatim (`:319`), so the label still renders at `⟨59, 16, 1, 1⟩`
    strictly inside exclusive `x`. Revised scope is `["root"]`, `x` stays
    outside scope, and C7 is false on otherwise unchanged successful output.
    The public adapter `Kinds.Treemap.layout` rejects a label whose id is not its
    owner id followed by `.name` or `.value`; this chart-level witness records why. -/
def c7RootOwnerWitness : Model := {
  kind := "treemap",
  profile := .cell,
  boxes := [{ id := "root", role := .group, exclusive := false },
            { id := "x", parent := "root" }],
  labels := [{ id := "x.name", owner := "root", text := "x" }],
  regionSets := [{ parent := 0, regions := [1] }] }

theorem c7RootOwnerWitness_wellFormed : WellFormed c7RootOwnerWitness := by
  decide

theorem c7RootOwnerWitness_withinLimits : WithinLimits c7RootOwnerWitness := by
  decide

def c7RootOwnerDump : LayoutDump :=
  { canvas := ⟨120, 32⟩,
    boxes := [{ id := "root", role := "group", rect := ⟨0, 0, 120, 32⟩,
                parent := "", exclusive := false },
              { id := "x", role := "node", rect := ⟨2, 3, 116, 28⟩,
                parent := "root", exclusive := true }],
    routes := [],
    labels := [{ id := "x.name", owner := "root", rect := ⟨59, 16, 1, 1⟩,
                 lines := ["x"] }] }

/-- Layout-equality claim omitted: executable input and independently
    defined dump above are preserved for parent probing of the actual
    public adapter. -/

theorem c7RootOwnerDump_violates_c7 : ¬ Validator.C7 c7RootOwnerDump := by
  intro h
  have ht : Validator.c7 c7RootOwnerDump = true := (Validator.c7_iff c7RootOwnerDump).mpr h
  have hf : Validator.c7 c7RootOwnerDump = false := by decide
  rw [hf] at ht
  cases ht

theorem c7RootOwnerDump_not_hard : ¬ HardConstraints c7RootOwnerDump := by
  intro h
  exact c7RootOwnerDump_violates_c7 h.2.2.2.2.2.2.1

end C7Counterexample

namespace EmptyIdCounterexample

/-- Second admission gap, independent of the C7 owner mismatch:
    `modelWellFormed` admits a box with `id := ""` (`Model.lean:123-130`
    checks uniqueness and parent termination only). `Treemap.children`
    (`TreemapAdapter.lean:55-56`) then treats every `parent = ""` box,
    including `"root"` and the empty-id box itself, as children of the
    empty-id node. Because `dependencyOrder` sorts depth-0 nodes by
    declaration order, a `""`-id box declared after `"root"` rewrites
    `root`'s preset canvas tile to the zero tile *after* `root`'s own
    step has already placed its children inside the preset. The children
    keep their nonzero rects while `root`'s final rect is `⟨0,0,0,0⟩`,
    so C3 (`p.rect.Contained b.rect`) fails on otherwise successful
    output. The public adapter `Kinds.Treemap.layout` rejects any box whose id is
    the empty string; this chart-level witness records why. -/
def emptyIdWitness : Model := {
  kind := "treemap",
  profile := .cell,
  boxes := [{ id := "root", role := .group, exclusive := false },
            { id := "x", parent := "root" },
            { id := "", parent := "" }],
  regionSets := [{ parent := 0, regions := [0, 0] }] }

theorem emptyIdWitness_wellFormed : WellFormed emptyIdWitness := by
  decide

theorem emptyIdWitness_withinLimits : WithinLimits emptyIdWitness := by
  decide

/-- Actual public-adapter geometry recorded by the parent execution. -/
def emptyIdDump : LayoutDump :=
  { canvas := ⟨120, 32⟩,
    boxes := [{ id := "root", role := "group", rect := ⟨0, 0, 0, 0⟩,
                parent := "", exclusive := false },
              { id := "x", role := "node", rect := ⟨2, 3, 116, 0⟩,
                parent := "root", exclusive := true },
              { id := "", role := "node", rect := ⟨0, 0, 0, 0⟩,
                parent := "", exclusive := true }],
    routes := [],
    labels := [] }

theorem emptyIdDump_violates_c3 : ¬ Validator.C3 emptyIdDump := by
  intro h
  have hx : (show Box from
      { id := "x", role := "node", rect := ⟨2, 3, 116, 0⟩,
        parent := "root", exclusive := true }) ∈ emptyIdDump.boxes := by
    decide
  have hroot : emptyIdDump.box? "root" = some
      { id := "root", role := "group", rect := ⟨0, 0, 0, 0⟩,
        parent := "", exclusive := false } := by
    decide
  have hcont := h _ hx (by decide) _ hroot
  have hnot : ¬ (⟨0, 0, 0, 0⟩ : Rect).Contained ⟨2, 3, 116, 0⟩ := by
    decide
  exact hnot hcont

theorem emptyIdDump_not_hard : ¬ HardConstraints emptyIdDump := by
  intro h
  exact emptyIdDump_violates_c3 h.2.2.1

theorem emptyIdDump_satisfies_c1 : Validator.C1 emptyIdDump :=
  (Validator.c1_iff emptyIdDump).mp (by decide)

theorem emptyIdDump_satisfies_c2 : Validator.C2 emptyIdDump :=
  (Validator.c2_iff emptyIdDump).mp (by decide)

theorem emptyIdDump_satisfies_c8 : Validator.C8 emptyIdDump :=
  (Validator.c8_iff emptyIdDump).mp (by decide)

end EmptyIdCounterexample

namespace TileForest

/-- Proper ancestors of `id` through model-box `parent` links, fuel-bounded
    exactly like `LayoutDump.ancestors`. -/
def boxAncestors (boxes : List ModelBox) : Nat → String → List String
  | 0, _ => []
  | n + 1, s =>
    match boxes.find? (fun b => b.id == s) with
    | none => []
    | some b => if b.parent = "" then [] else b.parent :: boxAncestors boxes n b.parent

/-- `a` and `b` are the same box or one is a proper ancestor of the other. -/
def forestRelated (boxes : List ModelBox) (a b : ModelBox) : Prop :=
  a.id = b.id ∨ b.id ∈ boxAncestors boxes boxes.length a.id ∨
    a.id ∈ boxAncestors boxes boxes.length b.id

theorem forestRelated_comm (boxes : List ModelBox) (a b : ModelBox) :
    forestRelated boxes a b ↔ forestRelated boxes b a := by
  unfold forestRelated
  constructor
  · intro h
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · intro h
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

theorem nodup_boxes_id_inj {boxes : List ModelBox}
    (hn : (boxes.map (·.id)).Nodup) {a b : ModelBox}
    (ha : a ∈ boxes) (hb : b ∈ boxes) (h : a.id = b.id) : a = b := by
  revert hn a b
  induction boxes with
  | nil => intro hn a b ha hb h; simp at ha
  | cons x xs ih =>
    intro hn a b ha hb h
    simp only [List.map] at hn
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · have hb2 : b.id ∈ xs.map (·.id) := List.mem_map.mpr ⟨b, hb, rfl⟩
      rw [← h] at hb2
      exact absurd hb2 hx
    · have ha2 : a.id ∈ xs.map (·.id) := List.mem_map.mpr ⟨a, ha, rfl⟩
      rw [h] at ha2
      exact absurd ha2 hx
    · exact @ih hxs a b ha hb h

theorem findBox_eq (boxes : List ModelBox) (hn : (boxes.map (·.id)).Nodup)
    {b : ModelBox} (hb : b ∈ boxes) :
    boxes.find? (fun x => x.id == b.id) = some b := by
  cases h : boxes.find? (fun x => x.id == b.id) with
  | none =>
    rw [List.find?_eq_none] at h
    have := h b hb
    simp at this
  | some a =>
    have ha : a ∈ boxes := List.mem_of_find?_eq_some h
    have hpa := List.find?_some h
    have haid : a.id = b.id := by simpa using hpa
    have hab : a = b := nodup_boxes_id_inj hn ha hb haid
    exact congrArg some hab


end TileForest

namespace ConstructionTransport

/-- C1 fragment at tile level: the root tile sits inside the canvas rect.
    Global C1 additionally needs every descendant tile inside the root tile;
    per-parent containment below gives one tiling step of that chain. -/
theorem rootTile_contained_in_canvas (width height band : Int)
    (_hw : 0 ≤ width) (_hh : 0 ≤ height) (hb : 0 ≤ band) :
    Rect.Contained ⟨0, 0, width, band + height⟩ ⟨0, band, width, height⟩ := by
  unfold Rect.Contained
  dsimp only
  omega

/-- C2/C3/C8a fragment at tile level for one tiled parent: siblings are
    pairwise disjoint (C2, and C8a for sibling subtrees) and each child is
    contained in the parent tile (C3). Global clauses need this lifted along
    the ancestor chain via `tile_inside_trans`; no global claim is made here. -/
theorem parent_children_validator_c2c3 (values : List Int) (parent : Tile)
    (padX padY header innerX innerY rho : Int) (fuel : Nat)
    (out : List Tile) (capped : Bool) (hp : parent.Ordered)
    (h : squarify values (childArea parent padX padY header innerX innerY)
      rho fuel = .ok (out, capped)) :
    (out.map (fun cell => tileRect (insetCell cell innerX innerY))).Pairwise Disjoint ∧
    ∀ child ∈ out.map (fun cell => tileRect (insetCell cell innerX innerY)),
      Rect.Contained (tileRect parent) child :=
  treemap_children_geometry_of_success values parent padX padY header innerX innerY
    rho fuel out capped hp h

/-- C7 transport for the revised exempt-owner-and-ancestors contract: when no
    route carries the label's owner id, the owner is in scope, so a label in
    its own box is exempt from clearance against that box. The surviving
    root-owner counterexample shows the hypothesis matters: with owner
    `"root"` the scope is `["root"]` and exclusive `x` stays in scope. -/
theorem owner_mem_labelOwnerAnc_of_no_route (d : LayoutDump) (l : Label)
    (hroute : d.routes.find? (fun r => r.id == l.owner) = none) :
    l.owner ∈ d.labelOwnerAnc l := by
  unfold LayoutDump.labelOwnerAnc
  rw [hroute]
  exact List.mem_cons_self

end ConstructionTransport

namespace CanvasC1

/-- Canvas tile whose `tileRect` is the scene canvas rectangle. -/
def canvasTile (c : Consts) (band : Int) : Tile :=
  ⟨0, 0, c.width, band + c.height⟩

/-- The band the adapter reserves for the title, matching `layout`. -/
def bandOf (m : Model) : Int :=
  if (labelText m "title").isEmpty then 0 else (constants m).titleBand

theorem tileRect_canvasTile (c : Consts) (band : Int) :
    tileRect (canvasTile c band) = ⟨0, 0, c.width, band + c.height⟩ := by
  simp [tileRect, canvasTile]

theorem bandOf_nonneg (m : Model) : 0 ≤ bandOf m := by
  unfold bandOf
  split
  · omega
  · unfold constants
    cases m.profile <;>
      simp [LayoutConst.treemap_title_band, LayoutConst.Pair.get]

theorem except_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem map_source_modify {l : List Node} (i : Nat) (f : Node → Node)
    (hf : ∀ n, (f n).source = n.source) :
    (l.modify i f).map Node.source = l.map Node.source := by
  induction l generalizing i with
  | nil => cases i <;> simp [List.modify]
  | cons x xs ih =>
    cases i with
    | zero => simp [List.modify, List.map, hf x]
    | succ i =>
      change x.source :: (xs.modify i f).map Node.source = x.source :: xs.map Node.source
      rw [ih i]

theorem map_rect_modify {l : List Node} (i : Nat) (f : Node → Node)
    (hf : ∀ n, (f n).rect = n.rect) :
    (l.modify i f).map Node.rect = l.map Node.rect := by
  induction l generalizing i with
  | nil => cases i <;> simp [List.modify]
  | cons x xs ih =>
    cases i with
    | zero => simp [List.modify, List.map, hf x]
    | succ i =>
      change x.rect :: (xs.modify i f).map Node.rect = x.rect :: xs.map Node.rect
      rw [ih i]

theorem foldl_map_source {α : Type} (f : List Node → α → List Node)
    (l : List α) (init : List Node)
    (hf : ∀ acc i, (f acc i).map Node.source = acc.map Node.source) :
    (l.foldl f init).map Node.source = init.map Node.source := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, ih (f init a), hf init a]

theorem foldl_map_rect {α : Type} (f : List Node → α → List Node)
    (l : List α) (init : List Node)
    (hf : ∀ acc i, (f acc i).map Node.rect = acc.map Node.rect) :
    (l.foldl f init).map Node.rect = init.map Node.rect := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, ih (f init a), hf init a]

theorem assignSeries_rect (nodes : List Node) :
    (assignSeries nodes).map Node.rect = nodes.map Node.rect := by
  unfold assignSeries
  apply foldl_map_rect
  intro acc i
  by_cases hi : acc[i]? = none
  · simp [hi]
  · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp hi
    simp only [hn]
    apply map_rect_modify
    intro old
    rfl

theorem aggregate_rect (nodes : List Node) :
    (aggregate nodes).map Node.rect = nodes.map Node.rect := by
  unfold aggregate
  apply foldl_map_rect
  intro acc i
  by_cases hi : acc[i]? = none
  · simp [hi]
  · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp hi
    simp only [hn]
    by_cases hj : acc.findIdx? (fun parent => parent.source.id == n.source.parent) = none
    · simp [hj]
    · obtain ⟨j, hj'⟩ := Option.ne_none_iff_exists'.mp hj
      simp only [hj']
      apply map_rect_modify
      intro old
      rfl

theorem initialNodes_rect (m : Model) :
    ∀ n ∈ initialNodes m, n.rect = ⟨0, 0, 0, 0⟩ := by
  intro n hn
  unfold initialNodes at hn
  obtain ⟨⟨b, i⟩, _, hnode⟩ := List.mem_map.mp hn
  exact (congrArg Node.rect hnode).symm

theorem aggregate_initial_rect (m : Model) :
    ∀ n ∈ aggregate (initialNodes m), n.rect = ⟨0, 0, 0, 0⟩ := by
  intro n hn
  have hmem : n.rect ∈ (aggregate (initialNodes m)).map Node.rect :=
    List.mem_map.mpr ⟨n, hn, rfl⟩
  rw [aggregate_rect] at hmem
  obtain ⟨w, hw, hwr⟩ := List.mem_map.mp hmem
  rw [← hwr]
  exact initialNodes_rect m w hw

theorem assignSeries_aggregate_initial_rect (m : Model) :
    ∀ n ∈ assignSeries (aggregate (initialNodes m)), n.rect = ⟨0, 0, 0, 0⟩ := by
  intro n hn
  have hmem : n.rect ∈ (assignSeries (aggregate (initialNodes m))).map Node.rect :=
    List.mem_map.mpr ⟨n, hn, rfl⟩
  rw [assignSeries_rect] at hmem
  obtain ⟨w, hw, hwr⟩ := List.mem_map.mp hmem
  rw [← hwr]
  exact aggregate_initial_rect m w hw

/-- The seeding map of `layout`: the root keeps the canvas tile, others keep
    their initial (zero) rectangle. -/
def presetNode (m : Model) (band : Int) (n : Node) : Node :=
  if n.source.id == "root" then
    { n with rect := ⟨0, band, (constants m).width, band + (constants m).height⟩ }
  else n

theorem seeded_rect_cases (m : Model) (n : Node)
    (hn : n ∈ (assignSeries (aggregate (initialNodes m))).map
      (presetNode m (bandOf m))) :
    n.rect = ⟨0, 0, 0, 0⟩ ∨
      n.rect = ⟨0, bandOf m, (constants m).width,
        bandOf m + (constants m).height⟩ := by
  obtain ⟨w, hw, hpreset⟩ := List.mem_map.mp hn
  rw [← hpreset]
  unfold presetNode
  split
  · exact Or.inr rfl
  · exact Or.inl (assignSeries_aggregate_initial_rect m w hw)

theorem seeded_invariant (m : Model) (hw : 0 ≤ (constants m).width)
    (hh : 0 ≤ (constants m).height) (hb : 0 ≤ bandOf m) :
    ∀ n ∈ (assignSeries (aggregate (initialNodes m))).map (presetNode m (bandOf m)),
      n.rect.Ordered ∧
        Rect.Contained (tileRect (canvasTile (constants m) (bandOf m)))
          (tileRect n.rect) := by
  intro n hn
  rcases seeded_rect_cases m n hn with h | h
  · rw [h]
    constructor
    · exact ⟨Int.le_refl 0, Int.le_refl 0⟩
    · apply tile_inside_rect
      change 0 ≤ 0 ∧ 0 ≤ (constants m).width ∧
        0 ≤ 0 ∧ 0 ≤ bandOf m + (constants m).height
      exact ⟨Int.le_refl 0, hw, Int.le_refl 0, Int.add_nonneg hb hh⟩
  · rw [h]
    constructor
    · exact ⟨hw, by change bandOf m ≤ bandOf m + (constants m).height; omega⟩
    · apply tile_inside_rect
      change 0 ≤ 0 ∧ (constants m).width ≤ (constants m).width ∧
        0 ≤ bandOf m ∧
        bandOf m + (constants m).height ≤ bandOf m + (constants m).height
      exact ⟨Int.le_refl 0, Int.le_refl _, hb, Int.le_refl _⟩

/-- The step `tileNodes` performs for one index, factored out so the fold
    invariant can be stated. -/
def tileStep (c : Consts) (acc : List Node) (i : Nat) :
    Except LayoutError (List Node) := do
  match acc[i]? with
  | none => pure acc
  | some n =>
    let order := sortedChildren acc n.source.id
    if order.isEmpty then pure acc else do
      let values := order.map (fun j => (acc[j]?).map (·.value) |>.getD 0)
      let free := childArea n.rect c.padX c.padY c.header c.innerX c.innerY
      let (cells, _) ← squarify values free c.rho c.fuel
      pure ((order.zip cells).foldl (fun out (j, cell) =>
        out.modify j (fun old => { old with rect := insetCell cell c.innerX c.innerY })) acc)

theorem tileNodes_eq_foldlM (c : Consts) (nodes : List Node) :
    tileNodes c nodes = (dependencyOrder nodes).foldlM (tileStep c) nodes := by
  rfl

theorem modify_preserves {l : List Node} (j : Nat) (f : Node → Node)
    (P : Node → Prop) (hn : ∀ n ∈ l, P n) (hf : ∀ old, P old → P (f old)) :
    ∀ n ∈ l.modify j f, P n := by
  induction l generalizing j with
  | nil => intro n h; simp at h
  | cons x xs ih =>
    cases j with
    | zero =>
      intro n h
      change n ∈ f x :: xs at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hf x (hn x (List.mem_cons_self))
      · exact hn n (List.mem_cons_of_mem x h)
    | succ j =>
      intro n h
      change n ∈ x :: xs.modify j f at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hn n (List.mem_cons_self)
      · exact ih j (fun m hm => hn m (List.mem_cons_of_mem x hm)) n h

theorem batch_preserves (nodes : List Node) (assignments : List (Nat × Tile))
    (P : Node → Prop) (innerX innerY : Int)
    (hn : ∀ n ∈ nodes, P n)
    (hassign : ∀ p ∈ assignments, ∀ old, P old →
      P { old with rect := insetCell p.2 innerX innerY }) :
    ∀ n ∈ assignments.foldl (fun out (j, cell) =>
      out.modify j (fun old => { old with rect := insetCell cell innerX innerY })) nodes,
      P n := by
  induction assignments generalizing nodes with
  | nil => exact hn
  | cons a rest ih =>
    rw [List.foldl_cons]
    apply ih
    · exact modify_preserves a.1 _ P hn (hassign a (List.mem_cons_self))
    · intro p hp old ho
      exact hassign p (List.mem_cons_of_mem a hp) old ho

set_option maxHeartbeats 1600000 in
theorem tileStep_invariant (c : Consts) (band : Int) (acc : List Node) (i : Nat)
    (acc' : List Node)
    (hinv : ∀ n ∈ acc, n.rect.Ordered ∧
      Rect.Contained (tileRect (canvasTile c band)) (tileRect n.rect))
    (h : tileStep c acc i = .ok acc') :
    ∀ n ∈ acc', n.rect.Ordered ∧
      Rect.Contained (tileRect (canvasTile c band)) (tileRect n.rect) := by
  unfold tileStep at h
  by_cases hi : acc[i]? = none
  · rw [hi] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hinv
  · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp hi
    simp only [hn] at h
    by_cases ho : (sortedChildren acc n.source.id).isEmpty = true
    · rw [ho] at h
      simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact hinv
    · have ho' : (sortedChildren acc n.source.id).isEmpty = false := by
        cases hv : (sortedChildren acc n.source.id).isEmpty <;> simp_all
      rw [ho'] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨cells, capped⟩, hsq, hrest⟩ := except_bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at hrest
      rw [← hrest]
      have hnmem : n ∈ acc := List.mem_of_getElem? hn
      have hnP := hinv n hnmem
      have hfree : (childArea n.rect c.padX c.padY c.header c.innerX c.innerY).Ordered :=
        childArea_ordered n.rect c.padX c.padY c.header c.innerX c.innerY
      have hnonneg :
          ∀ v ∈ (sortedChildren acc n.source.id).map
            (fun j => (acc[j]?).map (·.value) |>.getD 0), 0 ≤ v :=
        squarify_values_nonnegative
          ((sortedChildren acc n.source.id).map
            (fun j => (acc[j]?).map (·.value) |>.getD 0))
          (childArea n.rect c.padX c.padY c.header c.innerX c.innerY)
          c.rho c.fuel cells capped hsq
      have hgeo := squarify_geometry
        ((sortedChildren acc n.source.id).map
          (fun j => (acc[j]?).map (·.value) |>.getD 0))
        (childArea n.rect c.padX c.padY c.header c.innerX c.innerY) c.rho c.fuel
        cells capped hnonneg hfree hsq
      apply batch_preserves acc (sortedChildren acc n.source.id |>.zip cells)
        (fun m => m.rect.Ordered ∧
          Rect.Contained (tileRect (canvasTile c band)) (tileRect m.rect))
        c.innerX c.innerY hinv
      intro p hp old hold
      obtain ⟨_, hcellmem⟩ := List.of_mem_zip hp
      have hcell := hgeo.1 p.2 hcellmem
      have hdrawn : (insetCell p.2 c.innerX c.innerY).Inside n.rect :=
        drawn_cell_inside_parent n.rect p.2 c.padX c.padY c.header c.innerX c.innerY
          hnP.1 hcell.1 hcell.2
      refine ⟨insetCell_ordered p.2 c.innerX c.innerY, ?_⟩
      exact Rect.Contained.trans hnP.2 (tile_inside_rect _ _ hdrawn)

theorem foldlM_tile_invariant (c : Consts) (band : Int) :
    ∀ (l : List Nat) (acc out : List Node),
      (∀ n ∈ acc, n.rect.Ordered ∧
        Rect.Contained (tileRect (canvasTile c band)) (tileRect n.rect)) →
      l.foldlM (tileStep c) acc = .ok out →
      ∀ n ∈ out, n.rect.Ordered ∧
        Rect.Contained (tileRect (canvasTile c band)) (tileRect n.rect) := by
  intro l
  induction l with
  | nil =>
    intro acc out hinv h
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hinv
  | cons i is ih =>
    intro acc out hinv h
    simp only [List.foldlM] at h
    obtain ⟨mid, hmid, hrest⟩ := except_bind_ok h
    exact ih mid out (tileStep_invariant c band acc i mid hinv hmid) hrest

theorem tileNodes_invariant (c : Consts) (band : Int) (nodes0 out : List Node)
    (hinv : ∀ n ∈ nodes0, n.rect.Ordered ∧
      Rect.Contained (tileRect (canvasTile c band)) (tileRect n.rect))
    (h : tileNodes c nodes0 = .ok out) :
    ∀ n ∈ out, n.rect.Ordered ∧
      Rect.Contained (tileRect (canvasTile c band)) (tileRect n.rect) := by
  rw [tileNodes_eq_foldlM] at h
  exact foldlM_tile_invariant c band (dependencyOrder nodes0) nodes0 out hinv h

/-- Clause 1 on the actual successful adapter: every dump box lies inside the
    canvas. The tiling fold preserves canvas containment at every step because
    each assigned cell sits inside `childArea` of its parent tile, which the
    invariant already contains in the canvas. -/
theorem treemap_c1 (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) :
    Validator.C1 result.scene.layoutDump := by
  obtain ⟨nodes, hnodes, hboxes, hcanvas, _⟩ :=
    layout_execution m result.scene (Kinds.Treemap.layout_adapter_success m result h)
  have hw := Kinds.Treemap.layout_width_nonnegative m result h
  have hh := Kinds.Treemap.layout_height_nonnegative m result h
  have hb := bandOf_nonneg m
  have hinv := seeded_invariant m hw hh hb
  have hout := tileNodes_invariant (constants m) (bandOf m) _ nodes hinv hnodes
  intro b hb'
  have hb'' : b ∈ result.scene.boxes := hb'
  rw [hboxes] at hb''
  obtain ⟨node, hnode, rfl⟩ := List.mem_map.mp hb''
  show Rect.Contained (Validator.canvasRect result.scene.layoutDump)
    (tileRect node.rect)
  have hcont := hout node hnode
  have hc : result.scene.layoutDump.canvas =
      ⟨(constants m).width, bandOf m + (constants m).height⟩ := hcanvas
  change Rect.Contained
    ⟨0, 0, result.scene.layoutDump.canvas.w, result.scene.layoutDump.canvas.h⟩
    (tileRect node.rect)
  rw [hc]
  simpa only [tileRect_canvasTile] using hcont.2

theorem zero_extent_disjoint (r s : Rect)
    (h : r.w = 0 ∨ r.h = 0) : Disjoint r s := by
  unfold Disjoint Rect.meetsInterior
  rcases h with h | h <;> omega

theorem modify_getElem? (nodes : List Node) (i j : Nat) (f : Node → Node) :
    (nodes.modify i f)[j]? =
      if i = j then (nodes[j]?).map f else nodes[j]? := by
  by_cases hij : i = j
  · subst j
    simpa only [ite_eq_left, Option.map_eq_map] using List.getElem?_modify_eq f i nodes
  · simpa only [ite_eq_right hij] using List.getElem?_modify_ne f nodes hij

theorem batch_getElem?_outside (nodes : List Node)
    (assignments : List (Nat × Tile)) (innerX innerY : Int) (j : Nat)
    (houtside : ∀ p ∈ assignments, p.1 ≠ j) :
    (assignments.foldl (fun out (k, cell) =>
      out.modify k (fun old => { old with rect := insetCell cell innerX innerY }))
        nodes)[j]? = nodes[j]? := by
  induction assignments generalizing nodes with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldl_cons]
    rw [ih _ (fun q hq => houtside q (List.mem_cons_of_mem p hq))]
    rw [modify_getElem?]
    simp only [houtside p List.mem_cons_self, ↓reduceIte]

theorem batch_getElem?_assigned (nodes : List Node)
    (assignments : List (Nat × Tile)) (innerX innerY : Int)
    (hnodup : (assignments.map Prod.fst).Nodup)
    (p : Nat × Tile) (hp : p ∈ assignments)
    (old : Node) (hold : nodes[p.1]? = some old) :
    ((assignments.foldl (fun out (k, cell) =>
      out.modify k (fun n => { n with rect := insetCell cell innerX innerY }))
        nodes)[p.1]?).map Node.rect = some (insetCell p.2 innerX innerY) := by
  induction assignments generalizing nodes old with
  | nil => simp at hp
  | cons q qs ih =>
    obtain ⟨hq, hqs⟩ := List.nodup_cons.mp hnodup
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with heq | hp
    · subst p
      rw [batch_getElem?_outside _ qs innerX innerY q.1]
      · rw [modify_getElem?, ite_eq_left rfl, hold]
        rfl
      · intro p hp heq
        apply hq
        exact List.mem_map.mpr ⟨p, hp, heq⟩
    · have hne : q.1 ≠ p.1 := by
        intro heq
        apply hq
        exact List.mem_map.mpr ⟨p, hp, heq.symm⟩
      apply ih _ hqs hp old
      rw [modify_getElem?, ite_eq_right hne]
      exact hold

theorem zip_rects_pairwise (indices : List Nat) (cells : List Tile)
    (innerX innerY : Int)
    (h : (cells.map (fun cell =>
      tileRect (insetCell cell innerX innerY))).Pairwise Disjoint) :
    ((indices.zip cells).map (fun p =>
      tileRect (insetCell p.2 innerX innerY))).Pairwise Disjoint := by
  induction indices generalizing cells with
  | nil => simp
  | cons i indices ih =>
    cases cells with
    | nil => simp
    | cons cell cells =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih cells htail⟩
      intro r hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      exact hhead _ (List.mem_map.mpr ⟨p.2, (List.of_mem_zip hp).2, rfl⟩)

theorem batch_source (nodes : List Node) (assignments : List (Nat × Tile))
    (innerX innerY : Int) :
    (assignments.foldl (fun out (j, cell) =>
      out.modify j (fun old => { old with rect := insetCell cell innerX innerY }))
        nodes).map Node.source = nodes.map Node.source := by
  apply foldl_map_source
  intro acc p
  apply map_source_modify
  intro n
  rfl

theorem tileStep_source (c : Consts) (acc out : List Node) (i : Nat)
    (h : tileStep c acc i = .ok out) :
    out.map Node.source = acc.map Node.source := by
  unfold tileStep at h
  cases hi : acc[i]? with
  | none =>
    simp only [hi, pure, Except.pure, Except.ok.injEq] at h
    subst out
    rfl
  | some n =>
    simp only [hi] at h
    by_cases ho : (sortedChildren acc n.source.id).isEmpty = true
    · rw [ho] at h
      simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst out
      rfl
    · have ho' : (sortedChildren acc n.source.id).isEmpty = false := by
        cases hv : (sortedChildren acc n.source.id).isEmpty <;> simp_all
      rw [ho'] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨cells, capped⟩, _, hrest⟩ := except_bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at hrest
      rw [← hrest]
      exact batch_source acc _ c.innerX c.innerY

theorem foldlM_tile_source (c : Consts) (order : List Nat)
    (acc out : List Node) (h : order.foldlM (tileStep c) acc = .ok out) :
    out.map Node.source = acc.map Node.source := by
  induction order generalizing acc with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst out
    rfl
  | cons i is ih =>
    simp only [List.foldlM] at h
    obtain ⟨mid, hmid, hrest⟩ := except_bind_ok h
    exact (ih mid hrest).trans (tileStep_source c acc mid i hmid)

theorem tileNodes_source (c : Consts) (acc out : List Node)
    (h : tileNodes c acc = .ok out) :
    out.map Node.source = acc.map Node.source := by
  rw [tileNodes_eq_foldlM] at h
  exact foldlM_tile_source c (dependencyOrder acc) acc out h

theorem tileStep_children_execution (c : Consts) (acc out : List Node)
    (i : Nat) (parent : Node) (hi : acc[i]? = some parent)
    (hchildren : (sortedChildren acc parent.source.id).isEmpty = false)
    (hparent : parent.rect.Ordered)
    (h : tileStep c acc i = .ok out) :
    ∃ cells capped,
      squarify
        ((sortedChildren acc parent.source.id).map
          (fun j => (acc[j]?).map (·.value) |>.getD 0))
        (childArea parent.rect c.padX c.padY c.header c.innerX c.innerY)
        c.rho c.fuel = .ok (cells, capped) ∧
      out = ((sortedChildren acc parent.source.id).zip cells).foldl
        (fun nodes (j, cell) =>
          nodes.modify j (fun old =>
            { old with rect := insetCell cell c.innerX c.innerY })) acc ∧
      (cells.map (fun cell =>
        tileRect (insetCell cell c.innerX c.innerY))).Pairwise Disjoint := by
  unfold tileStep at h
  simp only [hi, hchildren, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨⟨cells, capped⟩, hsq, hrest⟩ := except_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at hrest
  refine ⟨cells, capped, hsq, hrest.symm, ?_⟩
  exact (treemap_children_geometry_of_success _ parent.rect c.padX c.padY
    c.header c.innerX c.innerY c.rho c.fuel cells capped hparent hsq).1

theorem tileStep_assigned_output_c2 (c : Consts) (acc out : List Node)
    (i : Nat) (parent : Node) (hi : acc[i]? = some parent)
    (hchildren : (sortedChildren acc parent.source.id).isEmpty = false)
    (hparent : parent.rect.Ordered)
    (h : tileStep c acc i = .ok out) :
    ∃ assignments : List (Nat × Tile),
      out = assignments.foldl (fun nodes (j, cell) =>
        nodes.modify j (fun old =>
          { old with rect := insetCell cell c.innerX c.innerY })) acc ∧
      (assignments.map (fun p =>
        tileRect (insetCell p.2 c.innerX c.innerY))).Pairwise Disjoint ∧
      ∀ p ∈ assignments,
        (assignments.map Prod.fst).Nodup →
        ∀ old, acc[p.1]? = some old →
          (out[p.1]?).map (fun n => tileRect n.rect) =
            some (tileRect (insetCell p.2 c.innerX c.innerY)) := by
  obtain ⟨cells, capped, _, hout, hgeometry⟩ :=
    tileStep_children_execution c acc out i parent hi hchildren hparent h
  refine ⟨(sortedChildren acc parent.source.id).zip cells, hout,
    zip_rects_pairwise _ cells c.innerX c.innerY hgeometry, ?_⟩
  intro p hp hnodup old hold
  rw [hout]
  have hrect := batch_getElem?_assigned acc
    ((sortedChildren acc parent.source.id).zip cells)
    c.innerX c.innerY hnodup p hp old hold
  have hmapped := congrArg (Option.map tileRect) hrect
  simpa only [Option.map_map, Function.comp_def, Option.map_some] using hmapped

theorem children_index_nodup (nodes : List Node) (id : String) :
    (children nodes id).Nodup := by
  have hall : (nodes.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  exact hall.sublist (List.filter_sublist.map Prod.snd)

theorem sortedChildren_index_nodup (nodes : List Node) (id : String) :
    (sortedChildren nodes id).Nodup :=
  (sortedChildren_perm nodes id).nodup_iff.mpr (children_index_nodup nodes id)

theorem sortedChildren_index_source (nodes : List Node) (id : String) (j : Nat)
    (hj : j ∈ sortedChildren nodes id) :
    ∃ n, nodes[j]? = some n ∧ n.source.parent = id := by
  have hchild := (sortedChildren_perm nodes id).mem_iff.mp hj
  obtain ⟨⟨n, k⟩, hnk, hkj⟩ := List.mem_map.mp hchild
  have hk : k = j := hkj
  subst k
  obtain ⟨hlookup, hparent⟩ := List.mem_filter.mp hnk
  exact ⟨n, List.mk_mem_zipIdx_iff_getElem?.mp hlookup,
    by simpa only [beq_iff_eq] using hparent⟩

theorem zip_indices_nodup (indices : List Nat) (cells : List Tile)
    (hindices : indices.Nodup) :
    ((indices.zip cells).map Prod.fst).Nodup := by
  induction indices generalizing cells with
  | nil => simp
  | cons i indices ih =>
    cases cells with
    | nil => simp
    | cons cell cells =>
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hindices
      simp only [List.zip_cons_cons, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih cells htail⟩
      intro hmem
      obtain ⟨p, hp, hpi⟩ := List.mem_map.mp hmem
      exact hnot (hpi ▸ (List.of_mem_zip hp).1)

theorem tileStep_assigned_output (c : Consts) (acc out : List Node)
    (i : Nat) (parent : Node) (hi : acc[i]? = some parent)
    (hchildren : (sortedChildren acc parent.source.id).isEmpty = false)
    (hparent : parent.rect.Ordered)
    (h : tileStep c acc i = .ok out) :
    ∃ assignments : List (Nat × Tile),
      out = assignments.foldl (fun nodes (j, cell) =>
        nodes.modify j (fun old =>
          { old with rect := insetCell cell c.innerX c.innerY })) acc ∧
      (assignments.map Prod.fst).Nodup ∧
      (assignments.map (fun p =>
        tileRect (insetCell p.2 c.innerX c.innerY))).Pairwise Disjoint ∧
      ∀ p ∈ assignments,
        ∃ old, acc[p.1]? = some old ∧ old.source.parent = parent.source.id ∧
          (out[p.1]?).map (fun n => tileRect n.rect) =
            some (tileRect (insetCell p.2 c.innerX c.innerY)) := by
  obtain ⟨cells, capped, _, hout, hgeometry⟩ :=
    tileStep_children_execution c acc out i parent hi hchildren hparent h
  have hnodup := zip_indices_nodup (sortedChildren acc parent.source.id) cells
    (sortedChildren_index_nodup acc parent.source.id)
  refine ⟨(sortedChildren acc parent.source.id).zip cells, hout, hnodup,
    zip_rects_pairwise _ cells c.innerX c.innerY hgeometry, ?_⟩
  intro p hp
  obtain ⟨old, hold, hsource⟩ :=
    sortedChildren_index_source acc parent.source.id p.1 (List.of_mem_zip hp).1
  refine ⟨old, hold, hsource, ?_⟩
  rw [hout]
  have hrect := batch_getElem?_assigned acc
    ((sortedChildren acc parent.source.id).zip cells)
    c.innerX c.innerY hnodup p hp old hold
  have hmapped := congrArg (Option.map tileRect) hrect
  simpa only [Option.map_map, Function.comp_def, Option.map_some] using hmapped

theorem tileNodes_source_lookup (c : Consts) (acc out : List Node)
    (h : tileNodes c acc = .ok out) (j : Nat) :
    (out[j]?).map Node.source = (acc[j]?).map Node.source := by
  have hs := congrArg (fun sources : List ModelBox => sources[j]?)
    (tileNodes_source c acc out h)
  simpa only [List.getElem?_map] using hs

theorem parentDepth_le_fuel (nodes : List Node) (fuel : Nat) (id : String) :
    parentDepth nodes fuel id ≤ fuel := by
  induction fuel generalizing id with
  | zero => simp [parentDepth]
  | succ fuel ih =>
    by_cases hid : id = ""
    · subst id
      simp [parentDepth]
    · cases hf : nodes.find? (fun n => n.source.id == id) with
      | none => simp [parentDepth, hf]
      | some n =>
        have hstep : 1 + parentDepth nodes fuel n.source.parent ≤ fuel + 1 := by
          have htail := ih n.source.parent
          omega
        simpa [parentDepth, hid, hf] using hstep

theorem parentDepth_mono_step (nodes : List Node) (fuel : Nat) (id : String) :
    parentDepth nodes fuel id ≤ parentDepth nodes (fuel + 1) id := by
  induction fuel generalizing id with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    by_cases hid : id = ""
    · subst id
      simp [parentDepth]
    · cases hf : nodes.find? (fun n => n.source.id == id) with
      | none => simp [parentDepth, hf]
      | some n =>
        simpa [parentDepth, hid, hf] using Nat.succ_le_succ (ih n.source.parent)

theorem parentDepth_strict_of_lookup (nodes : List Node) (fuel : Nat)
    (id : String) (parent : Node) (hid : id ≠ "")
    (hlookup : nodes.find? (fun n => n.source.id == id) = some parent)
    (hdepth : parentDepth nodes fuel parent.source.parent < fuel) :
    parentDepth nodes fuel parent.source.parent <
      parentDepth nodes fuel id := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    have hstable : parentDepth nodes (fuel + 1) parent.source.parent =
        parentDepth nodes fuel parent.source.parent := by
      have hbound := parentDepth_le_fuel nodes fuel parent.source.parent
      by_cases hlt : parentDepth nodes fuel parent.source.parent < fuel
      · exact parentDepth_stable nodes fuel parent.source.parent hlt
      · have heq : parentDepth nodes fuel parent.source.parent = fuel := by omega
        have hmono := parentDepth_mono_step nodes fuel parent.source.parent
        omega
    rw [hstable]
    have hexec : parentDepth nodes (fuel + 1) id =
        1 + parentDepth nodes fuel parent.source.parent := by
      simp [parentDepth, hlookup]
    rw [hexec]
    omega

theorem dependencyOrder_perm_indices (nodes : List Node) :
    (dependencyOrder nodes).Perm (nodes.zipIdx.map Prod.snd) := by
  have hp := (List.mergeSort_perm (dependencyRanks nodes)
    (fun a b => decide (a.2 ≤ b.2))).map Prod.fst
  simpa only [dependencyOrder, dependencyRanks, List.map_map, Function.comp_def] using hp

theorem dependencyOrder_index_nodup (nodes : List Node) :
    (dependencyOrder nodes).Nodup := by
  apply (dependencyOrder_perm_indices nodes).nodup_iff.mpr
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' _

theorem dependencyRanks_index_source (nodes : List Node) (p : Nat × Nat)
    (hp : p ∈ dependencyRanks nodes) :
    ∃ n, nodes[p.1]? = some n ∧
      p.2 = parentDepth nodes nodes.length n.source.parent := by
  obtain ⟨⟨n, j⟩, hnode, hpair⟩ := List.mem_map.mp hp
  rcases hpair with rfl
  exact ⟨n, List.mk_mem_zipIdx_iff_getElem?.mp hnode, rfl⟩

theorem dependencyOrder_index_source (nodes : List Node) (j : Nat)
    (hj : j ∈ dependencyOrder nodes) :
    ∃ n, nodes[j]? = some n := by
  have hindex := (dependencyOrder_perm_indices nodes).mem_iff.mp hj
  obtain ⟨⟨n, k⟩, hnode, hkj⟩ := List.mem_map.mp hindex
  have hk : k = j := hkj
  subst k
  exact ⟨n, List.mk_mem_zipIdx_iff_getElem?.mp hnode⟩

theorem dependencyRanks_strict_position (nodes : List Node)
    (a b : Nat) (p q : Nat × Nat)
    (ha : ((dependencyRanks nodes).mergeSort
      (fun x y => decide (x.2 ≤ y.2)))[a]? = some p)
    (hb : ((dependencyRanks nodes).mergeSort
      (fun x y => decide (x.2 ≤ y.2)))[b]? = some q)
    (hstrict : p.2 < q.2) : a < b := by
  obtain ⟨habound, hpa⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hbbound, hqb⟩ := List.getElem?_eq_some_iff.mp hb
  have hsorted := Elegant.Treemap.dependencyRanks_sorted nodes
  by_cases hlt : b < a
  · have hle := hsorted.rel_getElem_of_lt hbbound habound hlt
    rw [hqb, hpa] at hle
    have hle' : q.2 ≤ p.2 := by
      simpa only [decide_eq_true_eq] using hle
    omega
  · by_cases heq : a = b
    · subst b
      have hpq : p = q := Option.some.inj (ha.symm.trans hb)
      rw [← hpq] at hstrict
      exact (Nat.lt_irrefl p.2 hstrict).elim
    · omega

theorem assignSeries_source (nodes : List Node) :
    (assignSeries nodes).map Node.source = nodes.map Node.source := by
  unfold assignSeries
  apply foldl_map_source
  intro acc i
  by_cases hi : acc[i]? = none
  · simp [hi]
  · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp hi
    simp only [hn]
    apply map_source_modify
    intro old
    rfl

theorem aggregate_source (nodes : List Node) :
    (aggregate nodes).map Node.source = nodes.map Node.source := by
  unfold aggregate
  apply foldl_map_source
  intro acc i
  by_cases hi : acc[i]? = none
  · simp [hi]
  · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp hi
    simp only [hn]
    by_cases hj : acc.findIdx? (fun parent => parent.source.id == n.source.parent) = none
    · simp [hj]
    · obtain ⟨j, hj'⟩ := Option.ne_none_iff_exists'.mp hj
      simp only [hj']
      apply map_source_modify
      intro old
      rfl

theorem initialNodes_source (m : Model) :
    (initialNodes m).map Node.source = m.boxes := by
  simp only [initialNodes, List.map_map]
  exact List.zipIdx_map_fst 0 m.boxes

theorem seeded_source (m : Model) :
    ((assignSeries (aggregate (initialNodes m))).map
      (presetNode m (bandOf m))).map Node.source = m.boxes := by
  have hpreset : ∀ n : Node, (presetNode m (bandOf m) n).source = n.source := by
    intro n
    unfold presetNode
    split <;> rfl
  calc
    _ = (assignSeries (aggregate (initialNodes m))).map Node.source := by
      simp only [List.map_map, Function.comp_def, hpreset]
    _ = m.boxes := by
      rw [assignSeries_source, aggregate_source, initialNodes_source]

theorem parentDepth_source_eq (left right : List Node)
    (hsources : left.map Node.source = right.map Node.source)
    (fuel : Nat) (id : String) :
    parentDepth left fuel id = parentDepth right fuel id := by
  induction fuel generalizing id with
  | zero => rfl
  | succ fuel ih =>
    by_cases hid : id = ""
    · subst id
      rfl
    · have hfind :
          (left.find? (fun n => n.source.id == id)).map Node.source =
          (right.find? (fun n => n.source.id == id)).map Node.source := by
        have hs := congrArg
          (fun sources : List ModelBox => sources.find? (fun b => b.id == id)) hsources
        simpa only [List.find?_map, Function.comp_def] using hs
      cases hl : left.find? (fun n => n.source.id == id) with
      | none =>
        cases hr : right.find? (fun n => n.source.id == id) with
        | none => simp [parentDepth, hl, hr]
        | some n => simp [hl, hr] at hfind
      | some n =>
        cases hr : right.find? (fun n => n.source.id == id) with
        | none => simp [hl, hr] at hfind
        | some other =>
          have hsource : n.source = other.source := by
            simpa only [hl, hr, Option.map_some, Option.some.injEq] using hfind
          have hparent := congrArg ModelBox.parent hsource
          simpa [parentDepth, hid, hl, hr, hparent] using
            ih other.source.parent

theorem dependencyOrder_rank_at (nodes : List Node) (a i : Nat)
    (ha : (dependencyOrder nodes)[a]? = some i) :
    ∃ n, nodes[i]? = some n ∧
      ((dependencyRanks nodes).mergeSort
        (fun x y => decide (x.2 ≤ y.2)))[a]? =
          some (i, parentDepth nodes nodes.length n.source.parent) := by
  simp only [dependencyOrder, List.getElem?_map] at ha
  obtain ⟨p, hpa, hpi⟩ := Option.map_eq_some_iff.mp ha
  have hmember : p ∈ dependencyRanks nodes :=
    List.mem_mergeSort.mp (List.mem_of_getElem? hpa)
  obtain ⟨n, hn, hdepth⟩ := dependencyRanks_index_source nodes p hmember
  have hp : p = (i, parentDepth nodes nodes.length n.source.parent) :=
    Prod.ext hpi hdepth
  refine ⟨n, ?_, ?_⟩
  · simpa only [hpi] using hn
  · rw [← hp]
    exact hpa

theorem dependencyOrder_strict_position (nodes : List Node)
    (a b i j : Nat) (parent child : Node)
    (ha : (dependencyOrder nodes)[a]? = some i)
    (hb : (dependencyOrder nodes)[b]? = some j)
    (hi : nodes[i]? = some parent) (hj : nodes[j]? = some child)
    (hstrict : parentDepth nodes nodes.length parent.source.parent <
      parentDepth nodes nodes.length child.source.parent) : a < b := by
  obtain ⟨pnode, hpnode, hpa⟩ := dependencyOrder_rank_at nodes a i ha
  obtain ⟨qnode, hqnode, hqb⟩ := dependencyOrder_rank_at nodes b j hb
  have hp : pnode = parent := Option.some.inj (hpnode.symm.trans hi)
  have hq : qnode = child := Option.some.inj (hqnode.symm.trans hj)
  subst pnode
  subst qnode
  exact dependencyRanks_strict_position nodes a b _ _ hpa hqb hstrict

theorem find_source_id_of_mem (nodes : List Node)
    (hnodup : (nodes.map (fun n => n.source.id)).Nodup)
    (n : Node) (hn : n ∈ nodes) :
    nodes.find? (fun other => other.source.id == n.source.id) = some n := by
  induction nodes with
  | nil => simp at hn
  | cons first rest ih =>
    obtain ⟨hfirst, hrest⟩ := List.nodup_cons.mp hnodup
    rcases List.mem_cons.mp hn with heq | hmem
    · subst n
      simp
    · have hne : first.source.id ≠ n.source.id := by
        intro heq
        apply hfirst
        exact List.mem_map.mpr ⟨n, hmem, heq.symm⟩
      simpa [List.find?_cons, hne] using ih hrest hmem

def DepthProfile (nodes : List Node) (id : String) (depth : Nat) : Prop :=
  ∀ fuel, parentDepth nodes fuel id = min fuel depth

theorem depthProfile_unique (nodes : List Node) (id : String) (a b : Nat)
    (ha : DepthProfile nodes id a) (hb : DepthProfile nodes id b) : a = b := by
  have h := (ha (a + b + 1)).symm.trans (hb (a + b + 1))
  omega

theorem depthProfile_step (nodes : List Node) (n : Node)
    (hid : n.source.id ≠ "")
    (hlookup : nodes.find? (fun other => other.source.id == n.source.id) = some n)
    (depth : Nat) (hparent : DepthProfile nodes n.source.parent depth) :
    DepthProfile nodes n.source.id (depth + 1) := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ fuel =>
    calc
      parentDepth nodes (fuel + 1) n.source.id =
          1 + parentDepth nodes fuel n.source.parent := by
        simp [parentDepth, hlookup]
      _ = min (fuel + 1) (depth + 1) := by
        rw [hparent fuel]
        omega

theorem source_ids_nodup (m : Model) (hwf : WellFormed m)
    (nodes : List Node) (hsources : nodes.map Node.source = m.boxes) :
    (nodes.map (fun n => n.source.id)).Nodup := by
  have hids := congrArg (List.map ModelBox.id) hsources
  have hmodel := Model.boxIds_nodup hwf
  rw [← hids] at hmodel
  simpa only [List.map_map, Function.comp_def] using hmodel

theorem source_parent_depthProfile (m : Model) (hwf : WellFormed m)
    (nodes : List Node) (hsources : nodes.map Node.source = m.boxes)
    (b : ModelBox) (hb : b ∈ m.boxes) :
    ∃ depth, DepthProfile nodes b.parent depth := by
  have hnodup := source_ids_nodup m hwf nodes hsources
  apply Elegant.parent_induction m hwf
    (fun id => ∃ depth, DepthProfile nodes id depth) ?_ ?_ b hb
  · refine ⟨0, ?_⟩
    intro fuel
    cases fuel <;> simp [parentDepth]
  · intro source hsource hparent
    by_cases hid : source.id = ""
    · refine ⟨0, ?_⟩
      intro fuel
      cases fuel <;> simp [parentDepth, hid]
    · have hmem : source ∈ nodes.map Node.source := by
        rw [hsources]
        exact hsource
      obtain ⟨n, hn, hns⟩ := List.mem_map.mp hmem
      obtain ⟨depth, hdepth⟩ := hparent
      refine ⟨depth + 1, ?_⟩
      have hlookup := find_source_id_of_mem nodes hnodup n hn
      have hnid : n.source.id ≠ "" := by simpa only [hns] using hid
      have hp : DepthProfile nodes n.source.parent depth := by
        simpa only [hns] using hdepth
      simpa only [hns] using depthProfile_step nodes n hnid hlookup depth hp

theorem depthProfile_trace (nodes : List Node) (depth : Nat) (id : String)
    (hprofile : DepthProfile nodes id depth) :
    ∃ ids : List String,
      ids.length = depth ∧ ids.Nodup ∧
      ∀ name ∈ ids, name ∈ nodes.map (fun n => n.source.id) ∧
        ∃ rank, DepthProfile nodes name rank ∧ 0 < rank ∧ rank ≤ depth := by
  induction depth generalizing id with
  | zero =>
    refine ⟨[], rfl, by simp, ?_⟩
    simp
  | succ depth ih =>
    have hid : id ≠ "" := by
      intro hid
      have hone := hprofile 1
      simp [parentDepth, hid] at hone
    obtain ⟨n, hlookup⟩ :
        ∃ n, nodes.find? (fun n => n.source.id == id) = some n := by
      cases hf : nodes.find? (fun n => n.source.id == id) with
      | none =>
        have hone := hprofile 1
        simp [parentDepth, hf] at hone
      | some n => exact ⟨n, rfl⟩
    have hparent : DepthProfile nodes n.source.parent depth := by
      intro fuel
      have hs := hprofile (fuel + 1)
      have hstep : parentDepth nodes (fuel + 1) id =
          1 + parentDepth nodes fuel n.source.parent := by
        simp [parentDepth, hlookup]
      rw [hstep] at hs
      omega
    obtain ⟨ids, hlength, hnodup, hmembers⟩ := ih n.source.parent hparent
    have hnot : id ∉ ids := by
      intro hmem
      obtain ⟨_, rank, hrank, _, hrankle⟩ := hmembers id hmem
      have heq := depthProfile_unique nodes id (depth + 1) rank hprofile hrank
      omega
    have hnid : n.source.id = id := by
      simpa only [beq_iff_eq] using List.find?_some hlookup
    refine ⟨id :: ids, by simp [hlength], List.nodup_cons.mpr ⟨hnot, hnodup⟩, ?_⟩
    intro name hname
    rcases List.mem_cons.mp hname with hname | hname
    · subst name
      refine ⟨List.mem_map.mpr ⟨n, List.mem_of_find?_eq_some hlookup, hnid⟩,
        depth + 1, hprofile, by omega, by omega⟩
    · obtain ⟨hmem, rank, hrank, hpos, hle⟩ := hmembers name hname
      exact ⟨hmem, rank, hrank, hpos, by omega⟩

theorem source_parent_depth_lt_length (m : Model) (hwf : WellFormed m)
    (nodes : List Node) (hsources : nodes.map Node.source = m.boxes)
    (b : ModelBox) (hb : b ∈ m.boxes) :
    parentDepth nodes nodes.length b.parent < nodes.length := by
  obtain ⟨depth, hprofile⟩ := source_parent_depthProfile m hwf nodes hsources b hb
  obtain ⟨ids, hlength, hnodup, hmembers⟩ := depthProfile_trace nodes depth b.parent hprofile
  have hmem : b ∈ nodes.map Node.source := by
    rw [hsources]
    exact hb
  obtain ⟨n, hn, hns⟩ := List.mem_map.mp hmem
  have hids := source_ids_nodup m hwf nodes hsources
  have hnot : b.id ∉ ids := by
    intro hbin
    obtain ⟨_, rank, hrank, hpositive, hbound⟩ := hmembers b.id hbin
    by_cases hid : b.id = ""
    · have hzero : DepthProfile nodes b.id 0 := by
        intro fuel
        cases fuel <;> simp [parentDepth, hid]
      have heq := depthProfile_unique nodes b.id 0 rank hzero hrank
      omega
    · have hnid : n.source.id ≠ "" := by simpa only [hns] using hid
      have hp : DepthProfile nodes n.source.parent depth := by
        simpa only [hns] using hprofile
      have hnode := depthProfile_step nodes n hnid
        (find_source_id_of_mem nodes hids n hn) depth hp
      have hbox : DepthProfile nodes b.id (depth + 1) := by
        simpa only [hns] using hnode
      have heq := depthProfile_unique nodes b.id (depth + 1) rank hbox hrank
      omega
  have hsubset : b.id :: ids ⊆ nodes.map (fun n => n.source.id) := by
    intro name hname
    rcases List.mem_cons.mp hname with hname | hname
    · subst name
      exact List.mem_map.mpr ⟨n, hn, congrArg ModelBox.id hns⟩
    · exact (hmembers name hname).1
  have hbound := (List.nodup_cons.mpr ⟨hnot, hnodup⟩).length_le_of_subset hsubset
  simp only [List.length_cons, List.length_map, hlength] at hbound
  rw [hprofile nodes.length]
  omega

theorem dependencyOrder_parent_before_child (m : Model) (hwf : WellFormed m)
    (nodes : List Node) (hsources : nodes.map Node.source = m.boxes)
    (a b i j : Nat) (parent child : Node)
    (ha : (dependencyOrder nodes)[a]? = some i)
    (hb : (dependencyOrder nodes)[b]? = some j)
    (hi : nodes[i]? = some parent) (hj : nodes[j]? = some child)
    (hlink : child.source.parent = parent.source.id)
    (hid : parent.source.id ≠ "") : a < b := by
  have hmem : parent ∈ nodes := List.mem_of_getElem? hi
  have hsource : parent.source ∈ m.boxes := by
    rw [← hsources]
    exact List.mem_map.mpr ⟨parent, hmem, rfl⟩
  have hbound := source_parent_depth_lt_length m hwf nodes hsources
    parent.source hsource
  have hlookup := find_source_id_of_mem nodes
    (source_ids_nodup m hwf nodes hsources) parent hmem
  have hstrict := parentDepth_strict_of_lookup nodes nodes.length
    parent.source.id parent hid hlookup hbound
  apply dependencyOrder_strict_position nodes a b i j parent child ha hb hi hj
  simpa only [hlink] using hstrict

theorem tile_disjoint_symm (r s : Rect) (h : Disjoint r s) : Disjoint s r := by
  unfold Disjoint Rect.meetsInterior at *
  omega

theorem pairwise_symmetric_distinct {α : Type} (R : α → α → Prop)
    (hsymm : ∀ a b, R a b → R b a) (items : List α)
    (hpair : items.Pairwise R) (a b : α)
    (ha : a ∈ items) (hb : b ∈ items) (hne : a ≠ b) : R a b := by
  induction items generalizing a b with
  | nil => simp at ha
  | cons first rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
    rcases List.mem_cons.mp ha with haeq | ha
    · rcases List.mem_cons.mp hb with hbeq | hb
      · exact (hne (haeq.trans hbeq.symm)).elim
      · rw [haeq]
        exact hhead b hb
    · rcases List.mem_cons.mp hb with hbeq | hb
      · rw [hbeq]
        exact hsymm first a (hhead a ha)
      · exact ih htail a b ha hb hne

theorem source_lookup_of_map_eq (before after : List Node)
    (hsources : after.map Node.source = before.map Node.source)
    (j : Nat) (n : Node) (hn : after[j]? = some n) :
    ∃ old, before[j]? = some old ∧ old.source = n.source := by
  have hs := congrArg (fun sources : List ModelBox => sources[j]?) hsources
  simp only [List.getElem?_map, hn, Option.map_some] at hs
  exact Option.map_eq_some_iff.mp hs.symm

theorem sortedChildren_mem_of_lookup (nodes : List Node) (id : String)
    (j : Nat) (n : Node) (hj : nodes[j]? = some n) (hparent : n.source.parent = id) :
    j ∈ sortedChildren nodes id := by
  apply (sortedChildren_perm nodes id).mem_iff.mpr
  apply List.mem_map.mpr
  refine ⟨(n, j), List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
  · exact List.mk_mem_zipIdx_iff_getElem?.mpr hj
  · simpa only [beq_iff_eq] using hparent

def SiblingDisjoint (nodes : List Node) : Prop :=
  ∀ a ∈ nodes, ∀ b ∈ nodes, a.source.id ≠ b.source.id →
    a.source.parent = b.source.parent → Disjoint (tileRect a.rect) (tileRect b.rect)

theorem seeded_sibling_disjoint (m : Model) :
    SiblingDisjoint ((assignSeries (aggregate (initialNodes m))).map
      (presetNode m (bandOf m))) := by
  intro a ha b hb hne _
  obtain ⟨oldA, holdA, rfl⟩ := List.mem_map.mp ha
  obtain ⟨oldB, holdB, rfl⟩ := List.mem_map.mp hb
  by_cases hrootA : oldA.source.id = "root"
  · have hrootB : oldB.source.id ≠ "root" := by
      intro hrootB
      apply hne
      simp [presetNode, hrootA, hrootB]
    have hzero := assignSeries_aggregate_initial_rect m oldB holdB
    have hdis := zero_extent_disjoint (tileRect ⟨0, 0, 0, 0⟩)
      (tileRect (presetNode m (bandOf m) oldA).rect) (Or.inl rfl)
    have hsymm := tile_disjoint_symm _ _ hdis
    simpa [presetNode, hrootB, hzero] using hsymm
  · have hzero := assignSeries_aggregate_initial_rect m oldA holdA
    have hdis := zero_extent_disjoint (tileRect ⟨0, 0, 0, 0⟩)
      (tileRect (presetNode m (bandOf m) oldB).rect) (Or.inl rfl)
    simpa [presetNode, hrootA, hzero] using hdis

theorem batch_sibling_disjoint (nodes : List Node) (assignments : List (Nat × Tile))
    (innerX innerY : Int) (parentId : String)
    (hinv : SiblingDisjoint nodes)
    (hnodup : (assignments.map Prod.fst).Nodup)
    (hpair : (assignments.map (fun p =>
      tileRect (insetCell p.2 innerX innerY))).Pairwise Disjoint)
    (hsource : ∀ p ∈ assignments, ∃ old,
      nodes[p.1]? = some old ∧ old.source.parent = parentId)
    (hcomplete : ∀ j old, nodes[j]? = some old → old.source.parent = parentId →
      ∃ p ∈ assignments, p.1 = j) :
    SiblingDisjoint (assignments.foldl (fun out (j, cell) =>
      out.modify j (fun old =>
        { old with rect := insetCell cell innerX innerY })) nodes) := by
  let out := assignments.foldl (fun out (j, cell) =>
    out.modify j (fun old => { old with rect := insetCell cell innerX innerY })) nodes
  intro a ha b hb hne hparent
  obtain ⟨i, hia⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨j, hjb⟩ := List.mem_iff_getElem?.mp hb
  have hsources : out.map Node.source = nodes.map Node.source :=
    batch_source nodes assignments innerX innerY
  obtain ⟨oldA, hiold, hsourceA⟩ := source_lookup_of_map_eq nodes out hsources i a hia
  obtain ⟨oldB, hjold, hsourceB⟩ := source_lookup_of_map_eq nodes out hsources j b hjb
  by_cases htarget : a.source.parent = parentId
  · obtain ⟨p, hp, hpi⟩ := hcomplete i oldA hiold
      (by simpa only [hsourceA] using htarget)
    obtain ⟨q, hq, hqj⟩ := hcomplete j oldB hjold
      (by simpa only [hsourceB, ← hparent] using htarget)
    have hij : i ≠ j := by
      intro hij
      rw [← hij] at hjb
      have hab := Option.some.inj (hia.symm.trans hjb)
      exact hne (congrArg (fun n : Node => n.source.id) hab)
    have hpq : p ≠ q := by
      intro hpq
      have hindices := congrArg Prod.fst hpq
      exact hij (hpi.symm.trans (hindices.trans hqj))
    have hrel := List.pairwise_map.mp hpair
    have hsep := pairwise_symmetric_distinct
      (fun p q : Nat × Tile => Disjoint
        (tileRect (insetCell p.2 innerX innerY))
        (tileRect (insetCell q.2 innerX innerY)))
      (fun _ _ h => tile_disjoint_symm _ _ h) assignments hrel p q hp hq hpq
    have har := batch_getElem?_assigned nodes assignments innerX innerY hnodup p hp
      oldA (by simpa only [hpi] using hiold)
    have hbr := batch_getElem?_assigned nodes assignments innerX innerY hnodup q hq
      oldB (by simpa only [hqj] using hjold)
    have hareq : a.rect = insetCell p.2 innerX innerY := by
      simpa only [hpi, hia, Option.map_some, Option.some.injEq] using har
    have hbreq : b.rect = insetCell q.2 innerX innerY := by
      simpa only [hqj, hjb, Option.map_some, Option.some.injEq] using hbr
    simpa only [hareq, hbreq] using hsep
  · have houtsideA : ∀ p ∈ assignments, p.1 ≠ i := by
      intro p hp hpi
      obtain ⟨old, hold, htargetOld⟩ := hsource p hp
      rw [hpi] at hold
      have holdA : old = oldA := Option.some.inj (hold.symm.trans hiold)
      apply htarget
      simpa only [holdA, hsourceA] using htargetOld
    have houtsideB : ∀ p ∈ assignments, p.1 ≠ j := by
      intro p hp hpj
      obtain ⟨old, hold, htargetOld⟩ := hsource p hp
      rw [hpj] at hold
      have holdB : old = oldB := Option.some.inj (hold.symm.trans hjold)
      apply htarget
      simpa only [holdB, hsourceB, ← hparent] using htargetOld
    have hia' : nodes[i]? = some a :=
      (batch_getElem?_outside nodes assignments innerX innerY i houtsideA).symm.trans hia
    have hjb' : nodes[j]? = some b :=
      (batch_getElem?_outside nodes assignments innerX innerY j houtsideB).symm.trans hjb
    exact hinv a (List.mem_of_getElem? hia') b (List.mem_of_getElem? hjb') hne hparent

theorem tileStep_sibling_disjoint (c : Consts) (acc out : List Node) (i : Nat)
    (hordered : ∀ n ∈ acc, n.rect.Ordered)
    (hinv : SiblingDisjoint acc) (h : tileStep c acc i = .ok out) :
    SiblingDisjoint out := by
  cases hi : acc[i]? with
  | none =>
    simp [tileStep, hi] at h
    have heq : acc = out := Except.ok.inj h
    subst out
    exact hinv
  | some parent =>
    by_cases hempty : (sortedChildren acc parent.source.id).isEmpty = true
    · simp [tileStep, hi, hempty] at h
      have heq : acc = out := Except.ok.inj h
      subst out
      exact hinv
    · have hchildren : (sortedChildren acc parent.source.id).isEmpty = false :=
        Bool.eq_false_iff.mpr hempty
      obtain ⟨cells, capped, hsq, hout, hgeometry⟩ :=
        tileStep_children_execution c acc out i parent hi hchildren
          (hordered parent (List.mem_of_getElem? hi)) h
      have hlength : cells.length = (sortedChildren acc parent.source.id).length := by
        simpa only [List.length_map] using squarify_length _ _ _ _ cells capped hsq
      rw [hout]
      apply batch_sibling_disjoint acc
        ((sortedChildren acc parent.source.id).zip cells)
        c.innerX c.innerY parent.source.id hinv
        (zip_indices_nodup _ _ (sortedChildren_index_nodup acc parent.source.id))
        (zip_rects_pairwise _ cells c.innerX c.innerY hgeometry)
      · intro p hp
        exact sortedChildren_index_source acc parent.source.id p.1 (List.of_mem_zip hp).1
      · intro j old hj hparent
        have hmember := sortedChildren_mem_of_lookup acc parent.source.id j old hj hparent
        have hmap : ((sortedChildren acc parent.source.id).zip cells).map Prod.fst =
            sortedChildren acc parent.source.id :=
          List.map_fst_zip (by omega)
        rw [← hmap] at hmember
        exact List.mem_map.mp hmember

theorem foldlM_tile_sibling_disjoint (c : Consts) (band : Int) (order : List Nat) :
    ∀ acc out : List Node,
      (∀ n ∈ acc, n.rect.Ordered ∧
        Rect.Contained (tileRect (canvasTile c band)) (tileRect n.rect)) →
      SiblingDisjoint acc →
      order.foldlM (tileStep c) acc = .ok out →
      SiblingDisjoint out := by
  induction order with
  | nil =>
    intro acc out _ hsibling h
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst out
    exact hsibling
  | cons i rest ih =>
    intro acc out hcanvas hsibling h
    simp only [List.foldlM] at h
    obtain ⟨mid, hmid, hrest⟩ := except_bind_ok h
    apply ih mid out (tileStep_invariant c band acc i mid hcanvas hmid)
      (tileStep_sibling_disjoint c acc mid i (fun n hn => (hcanvas n hn).1)
        hsibling hmid) hrest

theorem treemap_c2 (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Treemap.layout m = .ok result) :
    Validator.C2 result.scene.layoutDump := by
  obtain ⟨nodes, hnodes, hboxes, _, _⟩ :=
    layout_execution m result.scene (Kinds.Treemap.layout_adapter_success m result h)
  have hcanvas := seeded_invariant m
    (Kinds.Treemap.layout_width_nonnegative m result h)
    (Kinds.Treemap.layout_height_nonnegative m result h) (bandOf_nonneg m)
  rw [tileNodes_eq_foldlM] at hnodes
  have hsibling := foldlM_tile_sibling_disjoint (constants m) (bandOf m)
    _ _ nodes hcanvas (seeded_sibling_disjoint m) hnodes
  intro a ha b hb hne _ _ hparent
  have ha' : a ∈ result.scene.boxes := ha
  have hb' : b ∈ result.scene.boxes := hb
  rw [hboxes] at ha' hb'
  obtain ⟨nodeA, hnodeA, rfl⟩ := List.mem_map.mp ha'
  obtain ⟨nodeB, hnodeB, rfl⟩ := List.mem_map.mp hb'
  exact hsibling nodeA hnodeA nodeB hnodeB hne hparent

def emptyGroupFrameWitness : Model := {
  kind := "treemap"
  profile := .cell
  boxes := [
    { id := "root", role := .group, exclusive := false },
    { id := "", role := .group, parent := "root", exclusive := false },
    { id := "foreign", parent := "" }]
  regionSets := [{ parent := 0, regions := [1, 1] }]
}

theorem emptyGroupFrameWitness_wellFormed : WellFormed emptyGroupFrameWitness := by
  decide

theorem emptyGroupFrameWitness_withinLimits : WithinLimits emptyGroupFrameWitness := by
  decide

end CanvasC1
end Elegant.Treemap

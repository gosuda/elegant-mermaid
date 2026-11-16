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

end Elegant.Treemap

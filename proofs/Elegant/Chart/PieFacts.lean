import Elegant.Chart.Pie
import Elegant.Chart.RadarFacts

set_option autoImplicit false

namespace Elegant.Chart.Pie

theorem pie_endpoints_in_square {radius : Int} (hr : 0 ≤ radius) (cx cy angle : Int) :
    -radius ≤ (vertex cx cy radius angle).x - cx ∧
    (vertex cx cy radius angle).x - cx ≤ radius ∧
    -radius ≤ (vertex cx cy radius angle).y - cy ∧
    (vertex cx cy radius angle).y - cy ≤ radius := by
  have hc := Radar.cosine_bounded angle
  have hs := Radar.sine_bounded angle
  have h2r : 0 ≤ 2 * radius := by omega
  have cx0 := Int.mul_le_mul_of_nonneg_left hc.1 h2r
  have cx1 := Int.mul_le_mul_of_nonneg_left hc.2 h2r
  have sy0 := Int.mul_le_mul_of_nonneg_left hs.1 h2r
  have sy1 := Int.mul_le_mul_of_nonneg_left hs.2 h2r
  have hx := Int.mul_fdiv_add_fmod (2 * radius * cosQ15 angle + 32768) 65536
  have hy := Int.mul_fdiv_add_fmod (2 * radius * sinQ15 angle + 32768) 65536
  have hx0 := Int.fmod_nonneg_of_pos (2 * radius * cosQ15 angle + 32768) (by decide : (0 : Int) < 65536)
  have hx1 := Int.fmod_lt_of_pos (2 * radius * cosQ15 angle + 32768) (by decide : (0 : Int) < 65536)
  have hy0 := Int.fmod_nonneg_of_pos (2 * radius * sinQ15 angle + 32768) (by decide : (0 : Int) < 65536)
  have hy1 := Int.fmod_lt_of_pos (2 * radius * sinQ15 angle + 32768) (by decide : (0 : Int) < 65536)
  simp only [vertex]
  omega

def baseSum (total : Int) (vs : List Int) : Int :=
  (vs.map (fun v => Int.fdiv (65536 * v) total)).sum

def fracSum (total : Int) (vs : List Int) : Int :=
  (vs.map (fun v => Int.fmod (65536 * v) total)).sum

theorem allocation_identity (total : Int) (vs : List Int) :
    total * baseSum total vs + fracSum total vs = 65536 * vs.sum := by
  induction vs with
  | nil => simp [baseSum, fracSum]
  | cons v vs ih =>
    have hv := Int.mul_fdiv_add_fmod (65536 * v) total
    simp only [baseSum, fracSum, List.map_cons, List.sum_cons] at ih ⊢
    simp only [Int.mul_add] at *
    omega

theorem fractions_nonnegative (total : Int) (ht : 0 < total) (vs : List Int) :
    0 ≤ fracSum total vs := by
  induction vs with
  | nil => simp [fracSum]
  | cons v vs ih =>
    have hv := Int.fmod_nonneg_of_pos (65536 * v) ht
    simpa only [fracSum, List.map_cons, List.sum_cons] using Int.add_nonneg hv ih

theorem fractions_strict_upper (total : Int) (ht : 0 < total) (vs : List Int)
    (hne : vs ≠ []) :
    fracSum total vs < (vs.length : Int) * total := by
  induction vs with
  | nil => contradiction
  | cons v vs ih =>
    have hv := Int.fmod_lt_of_pos (65536 * v) ht
    cases vs with
    | nil => simpa [fracSum] using hv
    | cons w ws =>
      have hs := ih (by simp)
      simp only [fracSum, List.map_cons, List.sum_cons, List.length_cons, Int.natCast_add,
        Int.natCast_one, Int.add_mul, Int.one_mul] at hs ⊢
      omega

theorem pie_remainder_lt_count (vs : List Int) (ht : 0 < vs.sum) :
    let r := 65536 - baseSum vs.sum vs
    0 ≤ r ∧ r < (vs.length : Int) := by
  have hne : vs ≠ [] := by intro h; simp [h] at ht
  have hid := allocation_identity vs.sum vs
  have hn := fractions_nonnegative vs.sum ht vs
  have hu := fractions_strict_upper vs.sum ht vs hne
  have he : vs.sum * (65536 - baseSum vs.sum vs) = fracSum vs.sum vs := by
    simp only [Int.mul_sub, Int.mul_comm vs.sum 65536]
    omega
  dsimp only
  constructor
  · by_cases h : 0 ≤ 65536 - baseSum vs.sum vs
    · exact h
    · have neg := Int.mul_neg_of_pos_of_neg ht (show 65536 - baseSum vs.sum vs < 0 by omega)
      omega
  · by_cases h : 65536 - baseSum vs.sum vs < (vs.length : Int)
    · exact h
    · have hm := Int.mul_le_mul_of_nonneg_left
        (show (vs.length : Int) ≤ 65536 - baseSum vs.sum vs by omega) (by omega : 0 ≤ vs.sum)
      rw [he] at hm
      rw [Int.mul_comm vs.sum (vs.length : Int)] at hm
      omega

theorem indicator_sum (xs selected : List Nat) (hx : xs.Nodup) (hs : selected.Nodup)
    (hsub : ∀ i ∈ selected, i ∈ xs) :
    (xs.map (fun i => if selected.contains i then (1 : Int) else 0)).sum =
      (selected.length : Int) := by
  have count : ∀ ys : List Nat,
      (ys.map (fun i => if selected.contains i then (1 : Int) else 0)).sum =
        ((ys.filter selected.contains).length : Int) := by
    intro ys
    induction ys with
    | nil => simp
    | cons y ys ih =>
      by_cases h : selected.contains y = true
      · simp only [List.map_cons, List.sum_cons, h, ite_true, List.filter_cons, ih,
          List.length_cons, Int.natCast_add, Int.natCast_one]
        omega
      · have hf : selected.contains y = false := Bool.eq_false_iff.mpr h
        simp only [List.map_cons, List.sum_cons, hf, Bool.false_eq_true, ite_false,
          List.filter_cons, ih, Int.zero_add]
  rw [count]
  have hp : (xs.filter selected.contains).Perm selected :=
    (List.perm_ext_iff_of_nodup (hx.filter _) hs).mpr (by
      intro i
      simp only [List.mem_filter, List.contains_iff_mem]
      exact ⟨fun h => h.2, fun h => ⟨hsub i h, h⟩⟩)
  rw [hp.length_eq]

theorem remainderOrder_perm (vs : List Int) :
    (remainderOrder vs).Perm (List.range vs.length) := by
  have hp := (List.mergeSort_perm vs.zipIdx (remainderLE vs.sum)).map Prod.snd
  simpa only [remainderOrder, remainderPairs, List.zipIdx_map_snd, List.range_eq_range'] using hp

theorem extras_nodup (vs : List Int) : (extras vs).Nodup :=
  ((remainderOrder_perm vs).symm.nodup (List.nodup_range)).take

theorem extras_in_range (vs : List Int) (i : Nat) (hi : i ∈ extras vs) :
    i ∈ List.range vs.length :=
  (remainderOrder_perm vs).mem_iff.mp (List.mem_of_mem_take hi)

theorem extras_length (vs : List Int) (ht : 0 < vs.sum) :
    ((extras vs).length : Int) = 65536 - baseSum vs.sum vs := by
  have hr := pie_remainder_lt_count vs ht
  have hp := (remainderOrder_perm vs).length_eq
  simp only [List.length_range] at hp
  simp only [extras, List.length_take, hp]
  have hb : (bases vs).sum = baseSum vs.sum vs := rfl
  rw [hb]
  omega

theorem sum_map_add_int {α : Type} (xs : List α) (f g : α → Int) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem pie_angles_sum_turn (vs : List Int) (ht : 0 < vs.sum) :
    (sweeps vs).sum = 65536 := by
  have hzero : vs.sum ≠ 0 := by omega
  simp only [sweeps, hzero, ite_false]
  rw [sum_map_add_int]
  have hf : ((bases vs).zipIdx.map Prod.fst) = bases vs := List.zipIdx_map_fst 0 _
  have hi : ((bases vs).zipIdx.map (fun p => if (extras vs).contains p.2 then (1 : Int) else 0)).sum =
      ((List.range vs.length).map (fun i => if (extras vs).contains i then (1 : Int) else 0)).sum := by
    have he := List.map_map (f := Prod.snd)
      (g := fun i : Nat => if (extras vs).contains i then (1 : Int) else 0)
      (l := (bases vs).zipIdx)
    exact (congrArg List.sum he).symm.trans (by
      simp [List.zipIdx_map_snd, bases, List.range_eq_range'])
  rw [hf, hi, indicator_sum _ _ List.nodup_range (extras_nodup vs) (extras_in_range vs),
    extras_length vs ht]
  change baseSum vs.sum vs + (65536 - baseSum vs.sum vs) = 65536
  omega

theorem sweeps_nonnegative (vs : List Int) (ht : 0 < vs.sum)
    (hn : ∀ v ∈ vs, 0 ≤ v) :
    ∀ a ∈ sweeps vs, 0 ≤ a := by
  intro a ha
  have hz : vs.sum ≠ 0 := by omega
  simp only [sweeps, hz, ite_false, List.mem_map] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  have hb : p.1 ∈ bases vs :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
  obtain ⟨v, hv, he⟩ := List.mem_map.mp hb
  have hnv := hn v hv
  have hf := fdiv_mono (D := vs.sum) ht (show 0 ≤ 65536 * v by omega)
  simp only [Int.zero_fdiv] at hf
  change Int.fdiv (65536 * v) vs.sum = p.1 at he
  rw [he] at hf
  split <;> omega

def Contiguous (start finish : Int) : List Slice → Prop
  | [] => start = finish
  | sl :: rest => sl.start = start ∧ Contiguous (sl.start + sl.sweep) finish rest

theorem scan_contiguous (angles : List Int) (hn : ∀ a ∈ angles, 0 ≤ a)
    (start : Int) (index : Nat) :
    Contiguous start (start + angles.sum) (scanSlices start index angles) := by
  induction angles generalizing start index with
  | nil => simp [scanSlices, Contiguous]
  | cons a rest ih =>
    have ha := hn a (by simp)
    have hr : ∀ b ∈ rest, 0 ≤ b := fun b hb => hn b (by simp [hb])
    by_cases hp : a > 0
    · simp only [scanSlices, hp, ite_true, List.singleton_append, Contiguous]
      constructor
      · trivial
      · simpa [List.sum_cons, Int.add_assoc] using ih hr (start + a) (index + 1)
    · have hz : a = 0 := by omega
      subst a
      simpa [scanSlices, Contiguous] using ih hr start (index + 1)

theorem scan_index_lower_bound (angles : List Int) (start : Int) (index : Nat) :
    ∀ sl ∈ scanSlices start index angles, index ≤ sl.index := by
  induction angles generalizing start index with
  | nil => simp [scanSlices]
  | cons a rest ih =>
    intro sl hsl
    by_cases hp : a > 0
    · simp only [scanSlices, hp, ite_true, List.singleton_append, List.mem_cons] at hsl
      rcases hsl with rfl | hsl
      · exact Nat.le_refl _
      · have h := ih (start + a) (index + 1) sl hsl
        omega
    · simp only [scanSlices, hp, ite_false, List.nil_append] at hsl
      have h := ih (start + a) (index + 1) sl hsl
      omega

theorem scan_indices_ordered (angles : List Int) (start : Int) (index : Nat) :
    (scanSlices start index angles).Pairwise (fun a b => a.index < b.index) := by
  induction angles generalizing start index with
  | nil => exact .nil
  | cons a rest ih =>
    by_cases hp : a > 0
    · simp only [scanSlices, hp, ite_true, List.singleton_append]
      apply List.Pairwise.cons
      · intro sl hsl
        have h := scan_index_lower_bound rest (start + a) (index + 1) sl hsl
        change index < sl.index
        omega
      · exact ih (start + a) (index + 1)
    · simpa only [scanSlices, hp, ite_false, List.nil_append] using ih (start + a) (index + 1)

theorem pie_declaration_order (vs : List Int) :
    (slices vs).Pairwise (fun a b => a.index < b.index) :=
  scan_indices_ordered (sweeps vs) 0 0

theorem pie_slices_contiguous (vs : List Int) (ht : 0 < vs.sum)
    (hn : ∀ v ∈ vs, 0 ≤ v) :
    Contiguous 0 65536 (slices vs) := by
  have h := scan_contiguous (sweeps vs) (sweeps_nonnegative vs ht hn) 0 0
  simpa [slices, pie_angles_sum_turn vs ht] using h

theorem sum_strict_upper {α : Type} (xs : List α) (f : α → Int) (total : Int)
    (hlt : ∀ x ∈ xs, f x < total) (hne : xs ≠ []) :
    (xs.map f).sum < (xs.length : Int) * total := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    have hx := hlt x (by simp)
    cases xs with
    | nil => simpa using hx
    | cons y ys =>
      have hy := ih (fun z hz => hlt z (by simp [hz])) (by simp)
      simp only [List.map_cons, List.sum_cons, List.length_cons, Int.natCast_add,
        Int.natCast_one, Int.add_mul, Int.one_mul] at hy ⊢
      omega

theorem zero_not_in_prefix {α : Type} (xs : List α) (f : α → Int) (count : Nat) (total : Int)
    (hn : ∀ x ∈ xs, 0 ≤ f x) (hlt : ∀ x ∈ xs, f x < total)
    (hs : xs.Pairwise (fun a b => f b ≤ f a))
    (hc : count ≤ xs.length)
    (balance : (xs.map f).sum = (count : Int) * total) :
    ∀ x ∈ xs.take count, f x ≠ 0 := by
  intro x hx hz
  have suffix : ((xs.drop count).map f).sum = 0 := by
    have he : (xs.drop count).map f = (xs.drop count).map (fun _ => (0 : Int)) := by
      apply List.map_congr_left
      intro y hy
      have hxy := hs.rel_of_mem_take_of_mem_drop hx hy
      have hy0 := hn y (List.mem_of_mem_drop hy)
      omega
    rw [he]
    induction xs.drop count with
    | nil => rfl
    | cons y ys ih => simp [ih]
  have hp := sum_strict_upper (xs.take count) f total
    (fun y hy => hlt y (List.mem_of_mem_take hy))
    (by intro he; rw [he] at hx; contradiction)
  have decomposition : (xs.map f).sum =
      ((xs.take count).map f).sum + ((xs.drop count).map f).sum := by
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  rw [suffix] at decomposition
  simp only [List.length_take, Nat.min_eq_left hc] at hp
  omega

theorem remainderPairs_sorted (vs : List Int) :
    (remainderPairs vs).Pairwise (fun a b =>
      Int.fmod (65536 * b.1) vs.sum ≤ Int.fmod (65536 * a.1) vs.sum) := by
  have h := List.pairwise_mergeSort (le := remainderLE vs.sum)
    (by intro a b c hab hbc; simp only [remainderLE, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hab hbc ⊢; omega)
    (by intro a b; simp only [remainderLE, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq]; omega) vs.zipIdx
  apply h.imp
  intro a b hab
  simp only [remainderLE, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hab
  omega

theorem sum_perm_int {xs ys : List Int} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.sum_cons, ih]
  | swap x y rest => simp only [List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem pie_extra_only_positive_frac (vs : List Int) (ht : 0 < vs.sum)
    (i : Nat) (hi : i ∈ extras vs) :
    0 < Int.fmod (65536 * vs.getD i 0) vs.sum := by
  let count := (65536 - baseSum vs.sum vs).toNat
  let f := fun p : Int × Nat => Int.fmod (65536 * p.1) vs.sum
  have hr := pie_remainder_lt_count vs ht
  have hc : (count : Int) = 65536 - baseSum vs.sum vs := by dsimp [count]; omega
  have perm := List.mergeSort_perm vs.zipIdx (remainderLE vs.sum)
  have hs : ((remainderPairs vs).map f).sum = fracSum vs.sum vs := by
    have hp := sum_perm_int (perm.map f)
    have he : (vs.zipIdx.map f) = vs.map (fun v => Int.fmod (65536 * v) vs.sum) := by
      change (vs.zipIdx.map ((fun v => Int.fmod (65536 * v) vs.sum) ∘ Prod.fst)) = _
      rw [← List.map_map]
      simp
    simpa only [remainderPairs, he, fracSum] using hp
  have balance : ((remainderPairs vs).map f).sum = (count : Int) * vs.sum := by
    rw [hs, hc]
    have hid := allocation_identity vs.sum vs
    simp only [Int.sub_mul, Int.mul_comm vs.sum] at *
    omega
  have selected := zero_not_in_prefix (remainderPairs vs) f count vs.sum
    (fun p _ => Int.fmod_nonneg_of_pos _ ht)
    (fun p _ => Int.fmod_lt_of_pos _ ht)
    (remainderPairs_sorted vs)
    (by have hl : (remainderPairs vs).length = vs.length := by
          simpa only [remainderPairs, List.length_zipIdx] using perm.length_eq
        rw [hl]
        omega)
    balance
  have him : i ∈ ((remainderPairs vs).take count).map Prod.snd := by
    simpa [extras, remainderOrder, count, bases, baseSum, List.map_take] using hi
  obtain ⟨p, hp, hpi⟩ := List.mem_map.mp him
  have hnz := selected p hp
  have hmem := perm.mem_iff.mp (List.mem_of_mem_take hp)
  have hget := List.mem_zipIdx_iff_getElem?.mp hmem
  have hval : vs.getD i 0 = p.1 := by
    rw [← hpi]
    simp [List.getD_eq_getElem?_getD, hget]
  rw [hval]
  have hn := Int.fmod_nonneg_of_pos (65536 * p.1) ht
  change Int.fmod (65536 * p.1) vs.sum ≠ 0 at hnz
  omega

theorem extrema_in_rect (ps : List Point) (a : Int × Int × Int × Int) (r : Rect)
    (ha : r.x ≤ a.1 ∧ r.y ≤ a.2.1 ∧ a.2.2.1 ≤ r.x + r.w ∧ a.2.2.2 ≤ r.y + r.h)
    (hp : ∀ p ∈ ps, r.x ≤ p.x ∧ r.y ≤ p.y ∧ p.x ≤ r.x + r.w ∧ p.y ≤ r.y + r.h) :
    let b := ps.foldl Radar.extendExtrema a
    r.x ≤ b.1 ∧ r.y ≤ b.2.1 ∧ b.2.2.1 ≤ r.x + r.w ∧ b.2.2.2 ≤ r.y + r.h := by
  induction ps generalizing a with
  | nil => exact ha
  | cons p ps ih =>
    have h := hp p (by simp)
    simp only [List.foldl_cons]
    apply ih (Radar.extendExtrema a p)
    · dsimp only [Radar.extendExtrema]
      omega
    · intro q hq
      exact hp q (by simp [hq])

theorem bounds_in_rect (ps : List Point) (hne : ps ≠ []) (r : Rect)
    (hp : ∀ p ∈ ps, r.x ≤ p.x ∧ r.y ≤ p.y ∧ p.x ≤ r.x + r.w ∧ p.y ≤ r.y + r.h) :
    r.Contained (Radar.bounds ps) := by
  have hfirst := hp (ps.headD ⟨0, 0⟩) (by cases ps with
    | nil => contradiction
    | cons p ps => simp)
  have h := extrema_in_rect ps
    ((ps.headD ⟨0, 0⟩).x, (ps.headD ⟨0, 0⟩).y,
     (ps.headD ⟨0, 0⟩).x, (ps.headD ⟨0, 0⟩).y) r hfirst hp
  change r.x ≤ (ps.foldl Radar.extendExtrema _).1 ∧
    (ps.foldl Radar.extendExtrema _).1 +
      ((ps.foldl Radar.extendExtrema _).2.2.1 - (ps.foldl Radar.extendExtrema _).1) ≤ r.x + r.w ∧
    r.y ≤ (ps.foldl Radar.extendExtrema _).2.1 ∧
    (ps.foldl Radar.extendExtrema _).2.1 +
      ((ps.foldl Radar.extendExtrema _).2.2.2 - (ps.foldl Radar.extendExtrema _).2.1) ≤ r.y + r.h
  omega

theorem arc_points_in_square (cx cy radius start sweep : Int) (hr : 0 ≤ radius) :
    ∀ p ∈ arcPoints cx cy radius start sweep,
      cx - radius ≤ p.x ∧ cy - radius ≤ p.y ∧ p.x ≤ cx + radius ∧ p.y ≤ cy + radius := by
  intro p hp
  simp only [arcPoints, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hp
  rcases hp with (rfl | rfl) | ⟨i, _, rfl⟩
  · have h := pie_endpoints_in_square hr cx cy start
    omega
  · have h := pie_endpoints_in_square hr cx cy (start + sweep)
    omega
  · have h := pie_endpoints_in_square hr cx cy
      (Int.fdiv (min start (start + sweep) + 16383) 16384 * 16384 + (i : Int) * 16384)
    omega

theorem slice_rect_in_square (cx cy radius inner : Int) (sl : Slice)
    (hr : 0 ≤ radius) (hi : 0 ≤ inner) (hir : inner ≤ radius) :
    (⟨cx - radius, cy - radius, 2 * radius, 2 * radius⟩ : Rect).Contained
      (sliceRect cx cy radius inner sl) := by
  unfold sliceRect
  apply bounds_in_rect
  · simp [arcPoints]
  · intro p hp
    simp only [List.mem_append] at hp
    rcases hp with hp | hp
    · have h := arc_points_in_square cx cy radius
        (Int.fmod (sl.start - 16384) 65536) sl.sweep hr p hp
      dsimp only
      omega
    · split at hp
      · simp only [List.mem_singleton] at hp
        subst p
        dsimp only
        omega
      · have h := arc_points_in_square cx cy inner
          (Int.fmod (sl.start - 16384) 65536) sl.sweep hi p hp
        dsimp only
        omega

theorem pie_plot_in_canvas (height : Int) (extra : List Point) :
    let extent := Radar.bounds (Radar.corners ⟨0, 0, height, height⟩ ++ extra)
    (⟨0, 0, extent.w, extent.h⟩ : Rect).Contained
      (Radar.shiftRect (-extent.x) (-extent.y) ⟨0, 0, height, height⟩) := by
  let points := Radar.corners (⟨0, 0, height, height⟩ : Rect) ++ extra
  have hc : (Radar.bounds points).Contained (⟨0, 0, height, height⟩ : Rect) := by
    apply Radar.bounds_contains_rect
    intro p hp
    exact List.mem_append_left _ hp
  have hs := Radar.shift_containment hc (-(Radar.bounds points).x) (-(Radar.bounds points).y)
  simpa [Radar.shiftRect, points, Int.add_right_neg] using hs

theorem pie_slice_inside_plot (height margin inner dx dy : Int) (sl : Slice)
    (hm : 0 ≤ margin)
    (hr : 0 ≤ Int.fdiv height 2 - margin)
    (hi : 0 ≤ inner) (hir : inner ≤ Int.fdiv height 2 - margin) :
    (Radar.shiftRect dx dy ⟨0, 0, height, height⟩).Contained
      (sliceRect (Int.fdiv height 2 + dx) (Int.fdiv height 2 + dy)
        (Int.fdiv height 2 - margin) inner sl) := by
  have hs := slice_rect_in_square (Int.fdiv height 2 + dx) (Int.fdiv height 2 + dy)
    (Int.fdiv height 2 - margin) inner sl hr hi hir
  have hq := Int.mul_fdiv_add_fmod height 2
  have hn := Int.fmod_nonneg_of_pos height (by decide : (0 : Int) < 2)
  have hl := Int.fmod_lt_of_pos height (by decide : (0 : Int) < 2)
  dsimp only [Rect.Contained, Radar.shiftRect] at hs ⊢
  omega

theorem pie_inner_radius_bounded (radius donut : Int) (hr : 0 ≤ radius) :
    let inner := if 0 < donut ∧ donut ≤ 900 then Int.fdiv (radius * donut) 1000 else 0
    0 ≤ inner ∧ inner ≤ radius := by
  dsimp only
  split
  · rename_i hd
    have h0 := Int.mul_nonneg hr (by omega : 0 ≤ donut)
    have h1 := Int.mul_le_mul_of_nonneg_left (show donut ≤ 1000 by omega) hr
    exact fdiv_between (radius * donut) 1000 0 radius (by decide)
      (by omega) (by simpa [Int.mul_comm] using h1)
  · exact ⟨by omega, hr⟩

theorem scan_zero (vs : List Int) (start : Int) (index : Nat) :
    scanSlices start index (vs.map (fun _ => 0)) = [] := by
  induction vs generalizing index with
  | nil => rfl
  | cons v vs ih => simpa [scanSlices] using ih (index + 1)

theorem pie_zero_total_no_slices (vs : List Int) (ht : vs.sum = 0) :
    slices vs = [] := by
  simp only [slices, sweeps, ht, ite_true]
  exact scan_zero vs 0 0

theorem model_relations_flags {m : Model} (hm : modelRelations m = true) :
    ∀ b ∈ m.boxes, b.exclusive = false ∧ b.role = .node := by
  cases hb : m.boxes with
  | nil => simp [modelRelations, hb] at hm
  | cons root rest =>
    simp only [modelRelations, hb, Bool.and_eq_true, beq_iff_eq,
      List.all_eq_true] at hm
    intro b hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · constructor
      · cases he : b.exclusive <;> simp_all
      · exact hm.1.1.1.1.2
    · have h := hm.1.2 b hmem
      constructor
      · cases he : b.exclusive <;> simp_all
      · exact h.1.1

theorem assemble_valid {m : Model} (hm : modelRelations m = true)
    (captions : List Caption) (inner : Int) (hi : 0 ≤ inner) (hir : inner ≤ 11840) :
    HardConstraints (assemble m inner captions).layoutDump := by
  let vs := values m
  let swatches := (List.range vs.length).map fun (i : Nat) =>
    (⟨28224, 14400 - Int.fdiv (1408 * (vs.length : Int)) 2 + (i : Int) * 1408, 1152, 1152⟩ : Rect)
  let longest := (captions.filter (fun t => t.kind == 2)).foldl (fun n t => max n t.rect.w) 0
  let extra := captions.flatMap (fun t => Radar.corners t.rect) ++
    swatches.flatMap Radar.corners ++ if vs.isEmpty then [] else [⟨28800 + 2560 + 1408 + longest, 28800⟩]
  let extent := Radar.bounds (Radar.corners ⟨0, 0, 28800, 28800⟩ ++ extra)
  let dx := -extent.x
  let dy := -extent.y
  let plot := Radar.shiftRect dx dy ⟨0, 0, 28800, 28800⟩
  let place := fun b : ModelBox =>
    let rect := if b.id == "plot" then plot else
      match (slices vs).find? (fun s => b.id == "s" ++ toString s.index) with
      | none => plot
      | some sl => sliceRect (14400 + dx) (14400 + dy) 11840 inner sl
    ({ id := b.id, role := b.role.id, parent := b.parent, exclusive := b.exclusive, rect } : Box)
  have hboxes : (assemble m inner captions).boxes = m.boxes.map place := by
    simp only [assemble, constant, LayoutConst.pie_height, LayoutConst.pie_margin,
      LayoutConst.pie_legend_row, LayoutConst.pie_legend_size, LayoutConst.pie_legend_offset,
      place, plot, dx, dy, extent, extra, swatches, vs, longest, List.append_assoc]
    rfl
  cases hb : m.boxes with
  | nil => simp [modelRelations, hb] at hm
  | cons root rest =>
    have hfields := hm
    simp only [modelRelations, hb, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hfields
    have hid : root.id = "plot" := hfields.1.1.1.1.1
    have hp : root.parent = "" := hfields.1.1.1.2
    have hr : root.role = .node := hfields.1.1.1.1.2
    have hroot : place root = ⟨"plot", "node", plot, "", false⟩ := by
      have he := (model_relations_flags hm root (by rw [hb]; simp)).1
      simp [place, hid, hp, hr, he, BoxRole.id]
    apply Radar.radar_hard_of_frame
      (b0 := ⟨"plot", "node", plot, "", false⟩) (tail := rest.map place)
    · change (assemble m inner captions).boxes = _
      rw [hboxes, hb, List.map_cons, hroot]
    · rfl
    · rfl
    · intro b hb'
      change b ∈ (assemble m inner captions).boxes at hb'
      rw [hboxes] at hb'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb'
      have hqf := model_relations_flags hm q hq
      exact ⟨hqf.1, by simp [place, hqf.2, BoxRole.id]⟩
    · intro b hb'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb'
      have hqp : q.parent = "plot" := (hfields.1.2 q hq).1.2
      constructor
      · exact hqp
      · change plot.Contained (place q).rect
        dsimp only [place]
        split
        · exact ⟨by omega, by omega, by omega, by omega⟩
        · split
          · exact ⟨by omega, by omega, by omega, by omega⟩
          · exact pie_slice_inside_plot 28800 2560 inner dx dy _ (by decide) (by decide) hi hir
    · rfl
    · have half : Int.fdiv (28800 : Int) 2 = 14400 := by decide
      simpa [assemble, Scene.layoutDump, Validator.canvasRect, constant,
        LayoutConst.pie_height, LayoutConst.pie_margin, LayoutConst.pie_legend_row,
        LayoutConst.pie_legend_size, LayoutConst.pie_legend_offset,
        plot, dx, dy, extent, extra, swatches, vs, longest, List.append_assoc, half]
        using pie_plot_in_canvas 28800 extra

theorem pie_valid {m : Model} {scene : Scene}
    (_hw : Elegant.WellFormed m) (_hl : WithinLimits m)
    (h : layout m = .ok scene) : HardConstraints scene.layoutDump := by
  unfold layout at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hguard
    have hm : modelRelations m = true := by
      cases he : modelRelations m <;> simp_all
    obtain ⟨_, _, h⟩ := Radar.radar_bind_ok h
    obtain ⟨captions, _, h⟩ := Radar.radar_bind_ok h
    obtain ⟨_, _, h⟩ := Radar.radar_bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst scene
    have hi := pie_inner_radius_bounded 11840 (Radar.config m.options "donutHole" 0) (by decide)
    apply assemble_valid hm captions _ hi.1 hi.2

end Elegant.Chart.Pie

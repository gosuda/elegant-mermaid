import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SizingFacts
import Elegant.Layered.CgShape
import Elegant.Layered.Coords
import Elegant.Layered.Route
import Elegant.Layered.Loops
import Elegant.Layered.Pipeline
import Elegant.Layered.PolylineBoxMiss
import Elegant.Layered.Rank

set_option autoImplicit false

namespace Elegant.Layered

section Helpers

private theorem foldl_add_zero (a : Int) :
    ∀ l : List Int, l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  intro l
  induction l generalizing a with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    simp only [List.foldl_cons, Int.zero_add]
    rw [ih (a + x), ih x]
    omega

private theorem loop_width_sum_ge (slot : Int) (hs : 0 ≤ slot) (labels : List LoopLabel)
    (hw : ∀ l ∈ labels, 0 ≤ l.width) (start : Nat) :
    2 * slot * (labels.length : Int) ≤
      ((labels.zipIdx start).map
        (fun q => slot * ((q.2 : Int) + 2) + q.1.width)).foldl (· + ·) 0 := by
  induction labels generalizing start with
  | nil => simp [List.map_nil, List.foldl_nil]
  | cons l ls ih =>
    have hls := ih (fun a ha => hw a (by simp [ha]))
    have hl := hw l (by simp)
    have hstart : 0 ≤ (start : Int) := by omega
    have hterm : 2 * slot ≤ slot * ((start : Int) + 2) + l.width := by
      have hmul := Int.mul_nonneg hs hstart
      rw [Int.mul_add]
      omega
    rw [Int.mul_add] at hterm
    rw [List.zipIdx_cons, List.map_cons, List.foldl_cons, Int.zero_add]
    simp only [Int.natCast_add, Int.natCast_one, Int.mul_add, Int.mul_one,
      List.length_cons]
    rw [foldl_add_zero]
    have htail := hls (start + 1)
    simp only [Int.mul_add] at htail
    omega
private theorem extent_ge_two_mul (slot : Int) (hs : 0 ≤ slot)
    (labels : List LoopLabel) (hw : ∀ l ∈ labels, 0 ≤ l.width) :
    2 * slot * (labels.length : Int) ≤ Loops.extent slot labels := by
  have heq : Loops.extent slot labels =
      ((labels.zipIdx 0).map
        (fun q => slot * ((q.2 : Int) + 2) + q.1.width)).foldl (· + ·) 0 := rfl
  rw [heq]
  exact loop_width_sum_ge slot hs labels hw 0

private theorem band_ge_two_slot (slot : Int) (labels : List LoopLabel) :
    2 * slot ≤ Loops.band slot labels := by
  have key : ∀ (l : List LoopLabel) (init : Int),
      init ≤ l.foldl (fun h l => max h l.height) init := by
    intro l
    induction l with
    | nil => intro init; exact Int.le_refl init
    | cons a rest ih =>
      intro init
      rw [List.foldl_cons]
      exact Int.le_trans (Int.le_max_left init a.height) (ih (max init a.height))
  exact key labels (2 * slot)

private theorem fdiv_w_add_extent (w : Int) (_hw : 0 ≤ w) (le : Nat) :
    Int.fdiv (w + 2 * (le : Int)) 2 = Int.fdiv w 2 + (le : Int) := by
  have e1 : Int.fdiv (w + 2 * (le : Int)) 2 = (w + 2 * (le : Int)) / 2 :=
    Int.fdiv_eq_ediv_of_nonneg _ (by decide)
  have e2 : Int.fdiv w 2 = w / 2 := Int.fdiv_eq_ediv_of_nonneg _ (by decide)
  rw [e1, e2]
  omega

end Helpers

section LoopFacts

/-- Slot and label-size bounds that follow from a successful loop placement. -/
private structure LoopFacts (slot : Int) (sizes : List LoopLabel) where
  slotNonneg : 0 ≤ slot
  widths : ∀ l ∈ sizes, 0 ≤ l.width
  heights : ∀ l ∈ sizes, 0 ≤ l.height

private theorem loopFacts_of_loops {node : Rect} {slot : Int} {sizes : List LoopLabel}
    {out : List LoopPlacement}
    (ok : Loops.loops node slot sizes = .ok out) : LoopFacts slot sizes := by
  unfold Loops.loops at ok
  dsimp only at ok
  split at ok
  · contradiction
  · split at ok
    · contradiction
    · rename_i hslot
      split at ok
      · contradiction
      · split at ok
        · have hslot0 : ¬ (slot < 0) := fun h => hslot (Or.inl h)
          have hfalse : sizes.any
              (fun l => decide (l.width < 0) || decide (l.height < 0)) = false := by
            cases hb : sizes.any
                (fun l => decide (l.width < 0) || decide (l.height < 0)) with
            | false => rfl
            | true => exact absurd hb (hslot ∘ Or.inr)
          have hall := List.any_eq_false.mp hfalse
          refine ⟨by omega, ?_, ?_⟩
          · intro l hl
            have h := hall l hl
            simp at h
            omega
          · intro l hl
            have h := hall l hl
            simp at h
            omega
        · contradiction

private theorem loopFacts_of_exact {node : Rect} {slot : Int} {sizes : List LoopLabel}
    {out : List LoopPlacement}
    (ok : Loops.exactLoops node slot sizes = .ok out) : LoopFacts slot sizes := by
  unfold Loops.exactLoops at ok
  dsimp only at ok
  split at ok
  · contradiction
  · split at ok
    · contradiction
    · rename_i hslot
      split at ok
      · contradiction
      · split at ok
        · have hslot0 : ¬ (slot < 0) := fun h => hslot (Or.inl h)
          have hfalse : sizes.any
              (fun l => decide (l.width < 0) || decide (l.height < 0)) = false := by
            cases hb : sizes.any
                (fun l => decide (l.width < 0) || decide (l.height < 0)) with
            | false => rfl
            | true => exact absurd hb (hslot ∘ Or.inr)
          have hall := List.any_eq_false.mp hfalse
          refine ⟨by omega, ?_, ?_⟩
          · intro l hl
            have h := hall l hl
            simp at h
            omega
          · intro l hl
            have h := hall l hl
            simp at h
            omega
        · contradiction

end LoopFacts

section Misses

open PipelineImpl

private theorem foldl_max_ge_init :
    ∀ (l : List LoopLabel) (b : Int), b ≤ l.foldl (fun w l => max w l.width) b := by
  intro l
  induction l with
  | nil => intro b; exact Int.le_refl b
  | cons a rest ih =>
    intro b
    rw [List.foldl_cons]
    exact Int.le_trans (Int.le_max_left b a.width) (ih (max b a.width))

theorem exactExtent_pos (slot : Int) (sizes : List LoopLabel)
    (hs : 0 < slot) (hne : sizes ≠ []) : 0 < Loops.exactExtent slot sizes := by
  have hni : sizes.isEmpty = false := by
    cases hb : sizes.isEmpty with
    | false => rfl
    | true => rw [List.isEmpty_iff] at hb; exact absurd hb hne
  have hW : 0 ≤ sizes.foldl (fun w l => max w l.width) 0 := foldl_max_ge_init _ _
  have hEE : Loops.exactExtent slot sizes =
      slot * (2 * (sizes.length : Int) + 1)
        + sizes.foldl (fun w l => max w l.width) 0 := by
    unfold Loops.exactExtent
    dsimp only
    rw [hni]
    rfl
  rw [hEE]
  have hm := Int.mul_pos hs (by omega : (0 : Int) < 2 * (sizes.length : Int) + 1)
  omega

private theorem exact_frac_bounds (height : Int) (count index : Nat)
    (offset : Int) (hh : 0 ≤ height) (hi : index < count)
    (ho : 1 ≤ offset ∧ offset ≤ 2) :
    0 ≤ Int.fdiv ((2 * (index : Int) + offset) * height) (2 * (count : Int) + 1) ∧
      Int.fdiv ((2 * (index : Int) + offset) * height) (2 * (count : Int) + 1) ≤ height := by
  have hd : 0 < 2 * (count : Int) + 1 := by omega
  have hn : 0 ≤ 2 * (index : Int) + offset := by omega
  have hu : 2 * (index : Int) + offset ≤ 2 * (count : Int) + 1 := by omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
  constructor
  · exact Int.ediv_nonneg (Int.mul_nonneg hn hh) (by omega)
  · have hm := Int.mul_le_mul_of_nonneg_right hu hh
    have he := Int.ediv_le_ediv (c := 2 * (count : Int) + 1) hd hm
    simpa only [Int.mul_comm (2 * (count : Int) + 1) height,
      Int.mul_ediv_cancel _ (show (2 * (count : Int) + 1 : Int) ≠ 0 by omega)] using he

private theorem half_band_le (band slot : Int) (_h0 : 0 ≤ band) (hb : 2 * slot ≤ band) :
    Int.fdiv band 2 + slot ≤ band := by
  rw [Int.fdiv_eq_ediv_of_nonneg band (by decide)]
  omega

private theorem loops_ok_map {node : Rect} {slot : Int} {sizes : List LoopLabel}
    {placements : List LoopPlacement}
    (h : Loops.loops node slot sizes = .ok placements) :
    placements = (sizes.zipIdx.map fun q =>
      Loops.placement node slot (Loops.band slot sizes) sizes.length q.2 q.1) := by
  unfold Loops.loops at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · cases h; rfl
        · contradiction

private theorem exactLoops_ok_map {node : Rect} {slot : Int} {sizes : List LoopLabel}
    {placements : List LoopPlacement}
    (h : Loops.exactLoops node slot sizes = .ok placements) :
    placements = (sizes.zipIdx.map fun q =>
      Loops.exactPlacement node slot (Loops.band slot sizes) sizes.length q.2 q.1) := by
  unfold Loops.exactLoops at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · cases h; rfl
        · contradiction

/-- The rectangle reserved to the right of node `v` for its self-loop routes. -/
def loopFootprint (cg : Graph) (run : Run) (labels : List MeasuredLabel)
    (v : Nat) : Rect :=
  let f := frameRect default cg run v
  ⟨f.x + f.w, f.y,
    (if run.exact.contains v then Loops.exactExtent else Loops.extent)
      cg.slot (loopSizes cg.edges labels v cg.slot), f.h⟩

private theorem loopSizes_width_nonneg {cg : Graph} {labels : List MeasuredLabel} {v : Nat}
    {slot : Int} {label : LoopLabel} (hm : label ∈ loopSizes cg.edges labels v slot) :
    0 ≤ label.width := by
  obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hm
  rw [stackSize_width_eq]
  exact Labels.stackWidth_nonneg _

private theorem extent_nonneg {slot : Int} {sizes : List LoopLabel} (hs : 0 ≤ slot)
    (hw : ∀ l ∈ sizes, 0 ≤ l.width) : 0 ≤ Loops.extent slot sizes := by
  have h1 := extent_ge_two_mul slot hs sizes hw
  have h2 : 0 ≤ 2 * slot * (sizes.length : Int) :=
    Int.mul_nonneg (by omega) (Int.natCast_nonneg _)
  omega

private theorem extent_ge_lane {slot : Int} {sizes : List LoopLabel} (hs : 0 ≤ slot)
    (hw : ∀ l ∈ sizes, 0 ≤ l.width) {index : Nat} (hi : index < sizes.length) :
    slot * ((index : Int) + 1) ≤ Loops.extent slot sizes := by
  have h1 := extent_ge_two_mul slot hs sizes hw
  have hlen : (index : Int) + 1 ≤ (sizes.length : Int) := by omega
  have h2 : 2 * slot * ((index : Int) + 1) ≤ 2 * slot * (sizes.length : Int) :=
    Int.mul_le_mul_of_nonneg_left hlen (by omega)
  have h3 : slot * ((index : Int) + 1) ≤ 2 * slot * ((index : Int) + 1) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  omega


private theorem placement_points_contained {node : Rect} {slot loopBand : Int}
    {count index : Nat} {label : LoopLabel} (hs : 0 ≤ slot) (hband : 2 * slot ≤ loopBand)
    (hi : index < count) (hn : count * loopBand ≤ node.h)
    {xMax : Int} (hx : slot * (count : Int) ≤ xMax)
    (p : Point) (hp : p ∈ (Loops.placement node slot loopBand count index label).points) :
    PointIn ⟨node.x + node.w, node.y, xMax, node.h⟩ p := by
  have hband0 : 0 ≤ loopBand := by omega
  have hlane0 : 0 ≤ slot * ((index : Int) + 1) := Int.mul_nonneg hs (by omega)
  have hlane : slot * ((index : Int) + 1) ≤ slot * (count : Int) :=
    Int.mul_le_mul_of_nonneg_left (by omega) hs
  have hsc : 0 ≤ slot * (count : Int) := Int.mul_nonneg hs (Int.natCast_nonneg _)
  have hx0 : 0 ≤ xMax := by omega
  have hidxband : 0 ≤ (index : Int) * loopBand := Int.mul_nonneg (by omega) hband0
  have hhalf : loopBand / 2 + slot ≤ loopBand := by omega
  have hnext : ((index : Int) + 1) * loopBand ≤ (count : Int) * loopBand :=
    Int.mul_le_mul_of_nonneg_right (by omega) hband0
  have hrew : ((index : Int) + 1) * loopBand = (index : Int) * loopBand + loopBand := by
    rw [Int.add_mul, Int.one_mul]
  have hidxband_le : (index : Int) * loopBand + loopBand ≤ (count : Int) * loopBand := by
    rw [← hrew]
    exact hnext
  unfold Loops.placement at hp
  dsimp only at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    · rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega : (0:Int) ≤ 2)] <;>
      simp only [PointIn] <;> omega

private theorem exactPlacement_points_contained {node : Rect} {slot loopBand : Int}
    {count index : Nat} {label : LoopLabel} (hs : 0 ≤ slot) (hh : 0 ≤ node.h)
    (hband : 2 * slot ≤ loopBand) (hi : index < count) (hn : count * loopBand ≤ node.h)
    {xMax : Int} (hx : 2 * slot * (count : Int) ≤ xMax)
    (p : Point) (hp : p ∈ (Loops.exactPlacement node slot loopBand count index label).points) :
    PointIn ⟨node.x + node.w, node.y, xMax, node.h⟩ p := by
  have hband0 : 0 ≤ loopBand := by omega
  have hsc : 0 ≤ 2 * slot * (count : Int) :=
    Int.mul_nonneg (by omega) (Int.natCast_nonneg _)
  have hx0 : 0 ≤ xMax := by omega
  have hlaneA0 : 0 ≤ slot * (2 * (index : Int) + 1) := Int.mul_nonneg hs (by omega)
  have hlaneB0 : 0 ≤ slot * (2 * (index : Int) + 2) := Int.mul_nonneg hs (by omega)
  have hlaneAB : slot * (2 * (index : Int) + 1) ≤ slot * (2 * (index : Int) + 2) :=
    Int.mul_le_mul_of_nonneg_left (by omega) hs
  have hlaneB : slot * (2 * (index : Int) + 2) ≤ 2 * slot * (count : Int) := by
    have h1 : slot * (2 * (index : Int) + 2) ≤ slot * (2 * (count : Int)) :=
      Int.mul_le_mul_of_nonneg_left (by omega) hs
    have h2 : slot * (2 * (count : Int)) = 2 * slot * (count : Int) := by
      rw [← Int.mul_assoc, Int.mul_comm slot 2]
    omega
  have hidxband : 0 ≤ (index : Int) * loopBand := Int.mul_nonneg (by omega) hband0
  have hhalf : loopBand / 2 + slot ≤ loopBand := by omega
  have hnext : ((index : Int) + 1) * loopBand ≤ (count : Int) * loopBand :=
    Int.mul_le_mul_of_nonneg_right (by omega) hband0
  have hrew : ((index : Int) + 1) * loopBand = (index : Int) * loopBand + loopBand := by
    rw [Int.add_mul, Int.one_mul]
  have hidxband_le : (index : Int) * loopBand + loopBand ≤ (count : Int) * loopBand := by
    rw [← hrew]
    exact hnext
  have hbA := exact_frac_bounds node.h count index 1 hh hi ⟨by omega, by omega⟩
  have hbB := exact_frac_bounds node.h count index 2 hh hi ⟨by omega, by omega⟩
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)] at hbA hbB
  unfold Loops.exactPlacement at hp
  dsimp only at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega : (0:Int) ≤ 2)]) <;>
    (try rw [Int.fdiv_eq_ediv_of_nonneg _
      (by omega : (0:Int) ≤ 2 * (count : Int) + 1)]) <;>
    simp only [PointIn] <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

private theorem loops_result_contained {node : Rect} {slot : Int} {sizes : List LoopLabel}
    {placements : List LoopPlacement}
    (h : Loops.loops node slot sizes = .ok placements) (hs : 0 ≤ slot)
    (hn : (sizes.length : Int) * Loops.band slot sizes ≤ node.h)
    {xMax : Int} (hx : slot * (sizes.length : Int) ≤ xMax)
    {p : LoopPlacement} (hmem : p ∈ placements) :
    ∀ q ∈ p.points, PointIn ⟨node.x + node.w, node.y, xMax, node.h⟩ q := by
  have hmap := loops_ok_map h
  rw [hmap] at hmem
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
  have hidxlt : q.2 < sizes.length := by
    have hlt := (List.mem_zipIdx hq).2.1
    omega
  exact fun r hr => placement_points_contained hs (band_ge_two_slot slot sizes)
    hidxlt hn hx r hr

private theorem exactLoops_result_contained {node : Rect} {slot : Int} {sizes : List LoopLabel}
    {placements : List LoopPlacement}
    (h : Loops.exactLoops node slot sizes = .ok placements) (hs : 0 ≤ slot)
    (hn : (sizes.length : Int) * Loops.band slot sizes ≤ node.h)
    {xMax : Int} (hx : 2 * slot * (sizes.length : Int) ≤ xMax)
    {p : LoopPlacement} (hmem : p ∈ placements) :
    ∀ q ∈ p.points, PointIn ⟨node.x + node.w, node.y, xMax, node.h⟩ q := by
  have hmap := exactLoops_ok_map h
  rw [hmap] at hmem
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
  have hidxlt : q.2 < sizes.length := by
    have hlt := (List.mem_zipIdx hq).2.1
    omega
  have hband_nonneg : 0 ≤ Loops.band slot sizes := by
    have := band_ge_two_slot slot sizes
    omega
  have hcb : 0 ≤ (sizes.length : Int) * Loops.band slot sizes :=
    Int.mul_nonneg (Int.natCast_nonneg _) hband_nonneg
  have hnh : 0 ≤ node.h := by omega
  exact fun r hr => exactPlacement_points_contained hs hnh (band_ge_two_slot slot sizes)
    hidxlt hn hx r hr

/-- `slot * count` is bounded by the plain loop extent when slot and label
widths are nonnegative. -/
private theorem slot_count_le_extent (slot : Int) (hs : 0 ≤ slot)
    (sizes : List LoopLabel) (hw : ∀ l ∈ sizes, 0 ≤ l.width) :
    slot * (sizes.length : Int) ≤ Loops.extent slot sizes := by
  have h2 := extent_ge_two_mul slot hs sizes hw
  have hsc : 0 ≤ slot * (sizes.length : Int) :=
    Int.mul_nonneg hs (Int.natCast_nonneg _)
  have h2sc : slot * (sizes.length : Int) ≤ 2 * slot * (sizes.length : Int) := by
    have := Int.mul_le_mul_of_nonneg_left
      (show (sizes.length : Int) ≤ 2 * (sizes.length : Int) by omega) hs
    rwa [show slot * (2 * (sizes.length : Int)) = 2 * slot * (sizes.length : Int)
      by rw [← Int.mul_assoc, Int.mul_comm slot 2]] at this
  omega

/-- `2 * slot * count` is bounded by the exact loop extent. -/
private theorem two_slot_count_le_exactExtent (slot : Int) (hs : 0 ≤ slot)
    (sizes : List LoopLabel) :
    2 * slot * (sizes.length : Int) ≤ Loops.exactExtent slot sizes := by
  have hW : 0 ≤ sizes.foldl (fun w l => max w l.width) 0 := foldl_max_ge_init _ _
  by_cases h : sizes.isEmpty = true
  · have hnil : sizes = [] := List.isEmpty_iff.mp h
    subst sizes
    simp [Loops.exactExtent]
  · simp only [Loops.exactExtent, h]
    have hstep : slot * (2 * (sizes.length : Int)) ≤
        slot * (2 * (sizes.length : Int) + 1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) hs
    have heq : 2 * slot * (sizes.length : Int) =
        slot * (2 * (sizes.length : Int)) := by
      ac_rfl
    rw [heq]
    exact Int.le_trans hstep (Int.le_add_of_nonneg_right hW)

/-- Every point of a successful plain `Loops.loops` placement lies in the loop
footprint: the rectangle to the right of `node` spanning the loop extent. -/
theorem loops_result_footprint {node : Rect} {slot : Int} {sizes : List LoopLabel}
    {placements : List LoopPlacement}
    (h : Loops.loops node slot sizes = .ok placements)
    (hn : (sizes.length : Int) * Loops.band slot sizes ≤ node.h)
    {p : LoopPlacement} (hmem : p ∈ placements) :
    ∀ q ∈ p.points,
      PointIn ⟨node.x + node.w, node.y, Loops.extent slot sizes, node.h⟩ q := by
  have facts := loopFacts_of_loops h
  exact loops_result_contained h facts.slotNonneg hn
    (slot_count_le_extent slot facts.slotNonneg sizes facts.widths) hmem

/-- Every point of a successful `Loops.exactLoops` placement lies in the exact
loop footprint. -/
theorem exactLoops_result_footprint {node : Rect} {slot : Int} {sizes : List LoopLabel}
    {placements : List LoopPlacement}
    (h : Loops.exactLoops node slot sizes = .ok placements)
    (hn : (sizes.length : Int) * Loops.band slot sizes ≤ node.h)
    {p : LoopPlacement} (hmem : p ∈ placements) :
    ∀ q ∈ p.points,
      PointIn ⟨node.x + node.w, node.y, Loops.exactExtent slot sizes, node.h⟩ q := by
  have facts := loopFacts_of_exact h
  exact exactLoops_result_contained h facts.slotNonneg hn
    (two_slot_count_le_exactExtent slot facts.slotNonneg sizes) hmem
end Misses

section MainTheorem

open PipelineImpl

/-- With no exact ranks reserved, the loop footprint uses the plain loop extent. -/
private theorem loopFootprint_plain {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {v : Nat}
    (hnotexact : ¬ v ∈ run.exact) :
    loopFootprint cg run labels v =
      ⟨(frameRect default cg run v).x + (frameRect default cg run v).w,
        (frameRect default cg run v).y,
        Loops.extent cg.slot (loopSizes cg.edges labels v cg.slot),
        (frameRect default cg run v).h⟩ := by
  simp [loopFootprint, hnotexact]

/-- The loop reservation is positive: a self-loop edge on `v` forces a nonempty
size list, whose band dominates the positive slot. -/
theorem loopFootprint_pos {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {v : Nat} {edge : Edge} {placement : LoopPlacement}
    (horigin : ∃ placements : List LoopPlacement,
      Loops.loops (frameRect default cg run v) cg.slot
          (loopSizes cg.edges labels v cg.slot) = .ok placements ∧
      (edge, placement) ∈ (loopEdges cg.edges v).zip placements)
    (hnotexact : ¬ v ∈ run.exact)
    (hslot : 0 < cg.slot)
    (hres : (loopSizes cg.edges labels v cg.slot).length *
        Loops.band cg.slot (loopSizes cg.edges labels v cg.slot) ≤
        (frameRect default cg run v).h) :
    0 < (loopFootprint cg run labels v).w ∧ 0 < (loopFootprint cg run labels v).h := by
  have hsizes : loopSizes cg.edges labels v cg.slot ≠ [] := by
    intro hnil
    obtain ⟨placements, _, hzip⟩ := horigin
    have hmem := (List.of_mem_zip hzip).1
    have hmap : (loopEdges cg.edges v).map
        (fun e => stackSize cg.slot (routeLabels labels e.decl)) = [] := hnil
    rw [List.map_eq_nil_iff] at hmap
    rw [hmap] at hmem
    simp at hmem
  have hcount : 0 < (loopSizes cg.edges labels v cg.slot).length :=
    List.length_pos_iff.mpr hsizes
  have hband : 0 < Loops.band cg.slot (loopSizes cg.edges labels v cg.slot) := by
    have h2 := band_ge_two_slot cg.slot (loopSizes cg.edges labels v cg.slot)
    omega
  have hlenpos : (0 : Int) <
      ((loopSizes cg.edges labels v cg.slot).length : Int) := by omega
  have hfp := loopFootprint_plain (cg := cg) (labels := labels) hnotexact
  rw [hfp]
  refine ⟨?_, ?_⟩
  · obtain ⟨placements, hok, _⟩ := horigin
    have facts := loopFacts_of_loops hok
    show 0 < Loops.extent cg.slot (loopSizes cg.edges labels v cg.slot)
    have hprodpos : 0 < cg.slot *
        ((loopSizes cg.edges labels v cg.slot).length : Int) :=
      Int.mul_pos (by omega) hlenpos
    have hle := slot_count_le_extent cg.slot facts.slotNonneg
      (loopSizes cg.edges labels v cg.slot) facts.widths
    omega
  · show 0 < (frameRect default cg run v).h
    have hprodpos : 0 < ((loopSizes cg.edges labels v cg.slot).length : Int) *
        Loops.band cg.slot (loopSizes cg.edges labels v cg.slot) :=
      Int.mul_pos hlenpos hband
    omega

theorem componentLoops_route_misses_foreign_boxes
    {cg : Graph} {run : Run} {labels : List MeasuredLabel}
    {v : Nat} {edge : Edge} {placement : LoopPlacement}
    (horigin : ∃ placements : List LoopPlacement,
      Loops.loops (frameRect default cg run v) cg.slot
          (loopSizes cg.edges labels v cg.slot) = .ok placements ∧
      (edge, placement) ∈ (loopEdges cg.edges v).zip placements ∧
      edge.tail = v ∧ edge.head = v)
    (hnotexact : ¬ v ∈ run.exact)
    (hslot : 0 < cg.slot)
    (hres : (loopSizes cg.edges labels v cg.slot).length *
        Loops.band cg.slot (loopSizes cg.edges labels v cg.slot) ≤
        (frameRect default cg run v).h)
    {b : Nat}
    (hdisj : Disjoint (loopFootprint cg run labels v)
      (frameRect default cg run b)) :
    ¬ Polyline.hitsRect placement.points (frameRect default cg run b) := by
  obtain ⟨placements, hok, hzip, _, _⟩ := horigin
  have hmem : placement ∈ placements := (List.of_mem_zip hzip).2
  have hconf := loops_result_footprint hok hres hmem
  have hpos := loopFootprint_pos ⟨placements, hok, hzip⟩ hnotexact hslot hres
  have hfp := loopFootprint_plain (cg := cg) (labels := labels) hnotexact
  have hconf' : ∀ p ∈ placement.points, PointIn (loopFootprint cg run labels v) p := by
    intro p hp
    rw [hfp]
    exact hconf p hp
  exact polyline_in_box_misses_disjoint hpos.1 hpos.2 hconf' hdisj

end MainTheorem

end Elegant.Layered

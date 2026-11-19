import ElegantGeometry.Basic
import ElegantGeometry.Route

set_option autoImplicit false

namespace Elegant.Layered

structure LoopLabel where
  width : Int
  height : Int
  deriving DecidableEq, Repr

structure LoopPlacement where
  points : List Point
  label : Rect
  deriving DecidableEq, Repr

namespace Loops

def band (slot : Int) (labels : List LoopLabel) : Int :=
  labels.foldl (fun h l => max h l.height) (2 * slot)

def extent (slot : Int) (labels : List LoopLabel) : Int :=
  (labels.zipIdx.map fun q => slot * ((q.2 : Int) + 2) + q.1.width).foldl (· + ·) 0

def requiredHeight (slot : Int) (labels : List LoopLabel) : Int :=
  2 * (labels.length : Int) * band slot labels

def placement (node : Rect) (slot loopBand : Int) (count index : Nat)
    (label : LoopLabel) : LoopPlacement :=
  let right := node.x + node.w
  let centre := node.y + (index : Int) * loopBand + Int.fdiv loopBand 2
  let lane := right + slot * ((index : Int) + 1)
  { points := [⟨right, centre - slot⟩, ⟨lane, centre - slot⟩,
      ⟨lane, centre + slot⟩, ⟨right, centre + slot⟩]
    label := ⟨right + slot * ((count : Int) + 1),
      centre - Int.fdiv label.height 2, label.width, label.height⟩ }

def exactExtent (slot : Int) (labels : List LoopLabel) : Int :=
  let widest := labels.foldl (fun w l => max w l.width) 0
  if labels.isEmpty then widest else slot * (2 * (labels.length : Int) + 1) + widest

def exactPlacement (node : Rect) (slot loopBand : Int) (count index : Nat)
    (label : LoopLabel) : LoopPlacement :=
  let right := node.x + node.w
  let denominator := 2 * (count : Int) + 1
  let endA := node.y + Int.fdiv ((2 * (index : Int) + 1) * node.h) denominator
  let endB := node.y + Int.fdiv ((2 * (index : Int) + 2) * node.h) denominator
  let laneA := right + slot * (2 * (index : Int) + 1)
  let laneB := right + slot * (2 * (index : Int) + 2)
  let centre := node.y + (index : Int) * loopBand + Int.fdiv loopBand 2
  let turn := centre + slot
  { points := [⟨right, endA⟩, ⟨laneA, endA⟩, ⟨laneA, turn⟩,
      ⟨laneB, turn⟩, ⟨laneB, endB⟩, ⟨right, endB⟩]
    label := ⟨right + slot * denominator,
      centre - Int.fdiv label.height 2, label.width, label.height⟩ }

def validPlacement (p : LoopPlacement) : Bool :=
  p.points.all (fun q => decide (I32_MIN ≤ q.x ∧ q.x ≤ I32_MAX ∧
    I32_MIN ≤ q.y ∧ q.y ≤ I32_MAX)) && decide (Rect.Valid p.label)

def loops (node : Rect) (slot : Int) (labels : List LoopLabel) :
    Except LayoutError (List LoopPlacement) := do
  if ¬ node.Valid then throw .domain
  let height := requiredHeight slot labels
  if slot < 0 ∨ labels.any (fun l => l.width < 0 || l.height < 0) then
    throw .domain
  if I32_MAX < height ∨ I32_MAX < extent slot labels then throw .overflow
  let placements := labels.zipIdx.map fun q =>
    placement node slot (band slot labels) labels.length q.2 q.1
  if placements.all validPlacement then pure placements else throw .overflow

def exactLoops (node : Rect) (slot : Int) (labels : List LoopLabel) :
    Except LayoutError (List LoopPlacement) := do
  if ¬ node.Valid then throw .domain
  if slot < 0 ∨ labels.any (fun l => l.width < 0 || l.height < 0) then
    throw .domain
  if I32_MAX < exactExtent slot labels then throw .overflow
  let placements := labels.zipIdx.map fun q =>
    exactPlacement node slot (band slot labels) labels.length q.2 q.1
  if placements.all validPlacement then pure placements else throw .overflow

theorem exactPlacement_outside_node (node : Rect) (slot loopBand : Int)
    (count index : Nat) (label : LoopLabel) (hslot : 0 ≤ slot) :
    ¬ Polyline.hitsRect (exactPlacement node slot loopBand count index label).points node :=
  let ha : node.x + node.w ≤ node.x + node.w + slot * (2 * (index : Int) + 1) :=
    Int.le_add_of_nonneg_right (Int.mul_nonneg hslot (by omega))
  let hb : node.x + node.w ≤ node.x + node.w + slot * (2 * (index : Int) + 2) :=
    Int.le_add_of_nonneg_right (Int.mul_nonneg hslot (by omega))
  fun hit => hit.2.2
    ⟨Or.inr (Or.inl (Int.le_min.mpr ⟨Int.le_refl _, ha⟩)),
      Or.inr (Or.inl (Int.le_min.mpr ⟨ha, ha⟩)),
      Or.inr (Or.inl (Int.le_min.mpr ⟨ha, hb⟩)),
      Or.inr (Or.inl (Int.le_min.mpr ⟨hb, hb⟩)),
      Or.inr (Or.inl (Int.le_min.mpr ⟨hb, Int.le_refl _⟩)), True.intro⟩

theorem exactLoops_result_outside_node {node : Rect} {slot : Int} {labels : List LoopLabel}
    {out : List LoopPlacement} (h : exactLoops node slot labels = .ok out) :
    ∀ p ∈ out, ¬ Polyline.hitsRect p.points node := by
  unfold exactLoops at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · next hs =>
      split at h
      · contradiction
      · split at h
        · cases h
          intro p hp
          obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
          exact exactPlacement_outside_node node slot (band slot labels)
            labels.length q.2 q.1 (by omega)
        · contradiction

theorem loops_outside_node (node : Rect) (slot loopBand : Int) (count index : Nat)
    (label : LoopLabel) (hslot : 0 ≤ slot) :
    ¬ Polyline.hitsRect (placement node slot loopBand count index label).points node :=
  let h : node.x + node.w ≤ node.x + node.w + slot * ((index : Int) + 1) :=
    Int.le_add_of_nonneg_right (Int.mul_nonneg hslot (Int.natCast_nonneg (index + 1)))
  fun hit => hit.2.2
    ⟨Or.inr (Or.inl (Int.le_min.mpr ⟨Int.le_refl _, h⟩)),
      Or.inr (Or.inl (Int.le_min.mpr ⟨h, h⟩)),
      Or.inr (Or.inl (Int.le_min.mpr ⟨h, Int.le_refl _⟩)), True.intro⟩
theorem loops_result_outside_node {node : Rect} {slot : Int} {labels : List LoopLabel}
    {out : List LoopPlacement} (h : loops node slot labels = .ok out) :
    ∀ p ∈ out, ¬ Polyline.hitsRect p.points node := by
  unfold loops at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · next hs =>
      split at h
      · contradiction
      · split at h
        · cases h
          intro p hp
          obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
          exact loops_outside_node node slot (band slot labels) labels.length q.2 q.1 (by omega)
        · contradiction

theorem placement_orthogonal (node : Rect) (slot loopBand : Int) (count index : Nat)
    (label : LoopLabel) :
    Polyline.isOrthogonal (placement node slot loopBand count index label).points = true := by
  simp [placement, Polyline.isOrthogonal]

theorem placement_ports (node : Rect) (slot loopBand : Int) (count index : Nat)
    (label : LoopLabel) :
    (placement node slot loopBand count index label).points.head? =
      some ⟨node.x + node.w, node.y + (index : Int) * loopBand + Int.fdiv loopBand 2 - slot⟩ ∧
    (placement node slot loopBand count index label).points.getLast? =
      some ⟨node.x + node.w, node.y + (index : Int) * loopBand + Int.fdiv loopBand 2 + slot⟩ :=
  ⟨rfl, rfl⟩

private def indexedExtent (slot : Int) (labels : List LoopLabel) (start : Nat) : Int :=
  (labels.zipIdx start |>.map fun q => slot * ((q.2 : Int) + 2) + q.1.width).sum

private theorem indexedExtent_count (slot : Int) (hs : 0 ≤ slot)
    (labels : List LoopLabel) (hw : ∀ l ∈ labels, 0 ≤ l.width) (start : Nat) :
    slot * (labels.length : Int) ≤ indexedExtent slot labels start := by
  induction labels generalizing start with
  | nil => simp [indexedExtent]
  | cons l ls ih =>
    have ht := ih (fun a ha => hw a (by simp [ha])) (start + 1)
    have hl := hw l (by simp)
    have hm := Int.mul_nonneg hs (show 0 ≤ (start : Int) + 1 by omega)
    simp only [indexedExtent, List.zipIdx_cons, List.map_cons, List.sum_cons,
      List.length_cons, Int.natCast_add, Int.natCast_one] at *
    simp only [Int.mul_add, Int.mul_one] at *
    omega

private theorem indexedExtent_member (slot : Int) (hs : 0 ≤ slot)
    (labels : List LoopLabel) (hw : ∀ l ∈ labels, 0 ≤ l.width)
    (start : Nat) (label : LoopLabel) (hm : label ∈ labels) :
    slot * ((start : Int) + (labels.length : Int) + 1) + label.width ≤
      indexedExtent slot labels start := by
  induction labels generalizing start with
  | nil => simp at hm
  | cons l ls ih =>
    have hls : ∀ a ∈ ls, 0 ≤ a.width := fun a ha => hw a (by simp [ha])
    have hl := hw l (by simp)
    rcases List.mem_cons.mp hm with he | ht
    · subst label
      have hb := indexedExtent_count slot hs ls hls (start + 1)
      simp only [indexedExtent, List.zipIdx_cons, List.map_cons, List.sum_cons,
        List.length_cons, Int.natCast_add, Int.natCast_one] at *
      simp only [Int.mul_add, Int.mul_one] at *
      omega
    · have hb := ih hls (start + 1) ht
      have hp := Int.mul_nonneg hs (show 0 ≤ (start : Int) + 2 by omega)
      simp only [indexedExtent, List.zipIdx_cons, List.map_cons, List.sum_cons,
        List.length_cons, Int.natCast_add, Int.natCast_one] at *
      simp only [Int.mul_add, Int.mul_one] at *
      omega

theorem outer_label_extent (slot : Int) (labels : List LoopLabel)
    (hs : 0 ≤ slot) (hw : ∀ l ∈ labels, 0 ≤ l.width)
    (label : LoopLabel) (hm : label ∈ labels) :
    slot * ((labels.length : Int) + 1) + label.width ≤ extent slot labels := by
  have h := indexedExtent_member slot hs labels hw 0 label hm
  simpa only [indexedExtent, extent, Int.natCast_zero, Int.zero_add,
    List.sum_eq_foldl] using h

theorem placement_label_within_extent (node : Rect) (slot loopBand : Int)
    (labels : List LoopLabel) (index : Nat) (label : LoopLabel)
    (hs : 0 ≤ slot) (hw : ∀ l ∈ labels, 0 ≤ l.width) (hm : label ∈ labels) :
    let r := (placement node slot loopBand labels.length index label).label
    node.x + node.w ≤ r.x ∧
      r.x + r.w ≤ node.x + node.w + extent slot labels := by
  have hb := outer_label_extent slot labels hs hw label hm
  have hn := Int.mul_nonneg hs (show 0 ≤ (labels.length : Int) + 1 by omega)
  dsimp only [placement]
  omega

#guard decide (band 1 [⟨3, 5⟩, ⟨7, 1⟩] = 5)
#guard decide (requiredHeight 1 [⟨3, 5⟩, ⟨7, 1⟩] = 20)
#guard decide (extent 1 [⟨3, 5⟩, ⟨7, 1⟩] = 15)
#guard decide ((placement ⟨2, 3, 8, 20⟩ 1 5 2 1 ⟨7, 1⟩).points =
  [⟨10, 9⟩, ⟨12, 9⟩, ⟨12, 11⟩, ⟨10, 11⟩])
#guard match loops ⟨2, 3, 8, 20⟩ 1 [⟨3, 5⟩, ⟨7, 1⟩] with
  | .error _ => false
  | .ok result => decide (result =
      [placement ⟨2, 3, 8, 20⟩ 1 5 2 0 ⟨3, 5⟩,
        placement ⟨2, 3, 8, 20⟩ 1 5 2 1 ⟨7, 1⟩])

end Loops
end Elegant.Layered


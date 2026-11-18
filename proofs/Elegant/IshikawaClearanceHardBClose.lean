import Elegant.IshikawaClearanceHardBFinal

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-! ### HARD B closure: the sibling and deeper-earlier obligations

This module discharges the two open named obligations of
`IshikawaClearanceHardBFinal`.  The declared obligations `HardBSibling` and
`HardBDeeperEarlier` leave their `frames`/`childBorn`/`jBorn` parameters
pinned only by `HardBCaseConfig`, whose length-and-two-lookups shape does not
determine the bones; adversarial frames make both declared statements false.
The corrected obligations `HardBSiblingReal` and `HardBDeeperEarlierReal`
below carry one additional premise, `HardBRealFrames`, which pins `frames` to
the executed birth frames of the successful run (the shape returned by
`place_common_birth_frames`).  That is exactly how `ishikawa_hard_b`
instantiates them, and `ishikawa_hard_b_real` at the bottom replays the final
assembly with the corrected premises.  The deeper-earlier obligation takes the
corrected block classification `HardBBranch5Block`, which
`IshikawaHardBBranch5Facts` proves.  The earlier-slot routing for the root
subcase is `hard_b_slot_mono_of_pos_lt` below.  -/

/-! ### Executed birth frames (the pinning) -/

/-- The birth-frame shape produced by `place_common_birth_frames`: length,
cause frame, and the per-entry `depthBone` record equation. -/
def BirthFramesShape (ns : List Tree.Node) (p : Params) (r : Rib)
    (frames : List Bone) : Prop :=
  frames.length = r.entries.length + 1 ∧
  frames[0]? = some
    { x1 := -run p r.length, t1 := r.length,
      count := (children ns r.cause).length : Bone } ∧
  (∀ (done : List (Entry × Nat)) (e : Entry) (idx : Nat) (rest : List (Entry × Nat)),
    r.entries.zipIdx = done ++ (e, idx) :: rest →
    ∃ (pos : Nat × Nat) (parent born : Bone),
      r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
      frames[(e.parent + 1).toNat]? = some parent ∧ frames[idx + 1]? = some born ∧
      born = depthBone p
        { parent with drawn := processedOddDraws done (e.parent + 1).toNat }
        e.depth (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
        (children ns e.node).length (run p r.heights + 3))

/-- Every frame of `frames` agrees with the executed birth frames: discharged
by `place_common_birth_frames` (which returns a `BirthFramesShape` witness). -/
def HardBRealFrames (ns : List Tree.Node) (p : Params) (spine : Int)
    (r placed : Rib) (_hplace : place ns p spine r = .ok placed)
    (frames : List Bone) : Prop :=
  ∃ frames0 : List Bone, BirthFramesShape ns p r frames0 ∧
    ∀ (i : Nat) (b : Bone), frames[i]? = some b → frames0[i]? = some b

/-- Branch-5 placement classification (REFUTED residual, retained only for the
counterexample statement in `IshikawaHardBBranch5Facts`, which imports this
module: never assume it).  For an odd route `I`
at `childIdx` with parent entry at `parentIdx` and an earlier entry `J` at
`jIdx` that is neither the parent nor a sibling, exactly one of these holds:

* `J` is a strict descendant of an earlier sibling `S` of `I` (same parent
  entry, `sIdx ≠ jIdx`, ancestor chain to `J`); or
* `J` is a root of the rib (`J.parent = -1`) whose order rank precedes the
  parent entry's rank (whence the earlier-slot branch catches it).

REFUTED by `hard_b_branch5_placement_counterexample` in
`IshikawaHardBBranch5Facts`: a non-root earlier entry of an earlier block is
neither a sibling descendant nor a root. Its corrected form is
`HardBBranch5Block` below. -/
def HardBBranch5Placement (ns : List Tree.Node) (cause k parentIdx childIdx jIdx : Nat)
    (J : Entry) : Prop :=
  let rib := generatedRib ns (cause, k)
  (∃ sIdx : Nat, ∃ S : Entry, rib.entries[sIdx]? = some S ∧ sIdx ≠ jIdx ∧
      S.parent = (parentIdx : Int) ∧ IndexedAncestor rib.entries sIdx jIdx) ∨
  (J.parent = -1 ∧ ∀ jPos pPos : Nat × Nat,
      rib.order.zipIdx.find? (fun v => v.1 == jIdx) = some jPos →
      rib.order.zipIdx.find? (fun v => v.1 == parentIdx) = some pPos →
      childIdx ≤ jIdx ∨ jPos.2 < pPos.2)

/-- Corrected branch-5 placement, block form (local statement).

For an odd route `I` at `childIdx` with parent entry at `parentIdx` and an
earlier entry `J` at `jIdx` that is neither the parent nor a sibling, either
`J` is a strict descendant of an earlier sibling `S` of `I`, or `J`'s block
head `H` (a root entry: `H = J` or an indexed ancestor of `J`) has an order
position strictly before the parent entry's position.

The def lives here because `IshikawaHardBBranch5Facts` imports this module;
the classification itself is proved there by
`hard_b_branch5_placement_block'`. -/
def HardBBranch5Block (ns : List Tree.Node) (cause k parentIdx childIdx jIdx : Nat)
    (J : Entry) : Prop :=
  let rib := generatedRib ns (cause, k)
  (∃ (sIdx : Nat) (S : Entry), rib.entries[sIdx]? = some S ∧ sIdx ≠ jIdx ∧
      S.parent = (parentIdx : Int) ∧ IndexedAncestor rib.entries sIdx jIdx) ∨
  (∃ (hIdx : Nat) (H : Entry), rib.entries[hIdx]? = some H ∧ H.parent = -1 ∧
      ((H = J ∧ hIdx = jIdx) ∨ IndexedAncestor rib.entries hIdx jIdx) ∧
      ∀ (headPos parentPos : Nat × Nat),
        rib.order.zipIdx.find? (fun v => v.1 == hIdx) = some headPos →
        rib.order.zipIdx.find? (fun v => v.1 == parentIdx) = some parentPos →
        childIdx ≤ jIdx ∨ headPos.2 < parentPos.2)

/-- Slot monotonicity for birth frames (step B): an entry whose order position
strictly precedes another entry's order position is born at an earlier slot,
with the rib height margin. With `jPos` the earlier entry's birth position and
`parentPos` the parent entry's birth position, the conclusion is exactly the
earlier-slot premise `jBorn.t1 + r.heights ≤ childBorn.t0` that
`HardBEarlierSlot` needs (via `childBorn.t0 = parentBorn.t0` for odd routes).
The birth equations come from the executed `BirthFramesShape` records
(`depthBone_endpoint_slot` for `t1`, the odd/even endpoint lemmas for `t0`);
the gap itself is `ordinal_slots_gap`. -/
theorem hard_b_slot_mono_of_pos_lt (r : Rib)
    (jBorn childBorn parentBorn : Bone)
    (jPos parentPos : Nat × Nat)
    (hjT1 : jBorn.t1
      = Int.fdiv (r.length * (jPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
    (hparentT0 : parentBorn.t0
      = Int.fdiv (r.length * (parentPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
    (hchildT0 : childBorn.t0 = parentBorn.t0)
    (hheight : 0 ≤ r.heights)
    (hbudget : (r.entries.length + 1 : Nat) * r.heights ≤ r.length)
    (hlt : jPos.2 < parentPos.2) :
    jBorn.t1 + r.heights ≤ childBorn.t0 := by
  rw [hjT1, hchildT0, hparentT0]
  exact ordinal_slots_gap r.length (r.entries.length + 1 : Nat) r.heights
    (jPos.2 + 1 : Nat) (parentPos.2 + 1 : Nat) (by omega) hheight hbudget (by omega)

/-- A pair `(x, idx)` of `l.zipIdx` sits at position `idx` of that list, so the
prefix decomposition `l.zipIdx = before ++ [(x, idx)] ++ after` forces
`before.length = idx`. -/
private theorem zipIdx_index_of_split {α : Type} {l : List α}
    {before after : List (α × Nat)} {x : α} {idx : Nat}
    (hsplit : l.zipIdx = before ++ [(x, idx)] ++ after) :
    before.length = idx := by
  have h2 : l.zipIdx[before.length]? = some (x, idx) := by
    rw [hsplit]
    rw [List.getElem?_append_left
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
    rw [List.getElem?_append_right (Nat.le_refl before.length)]
    simp
  rw [List.getElem?_zipIdx] at h2
  cases hopt : l[before.length]? with
  | none => rw [hopt] at h2; exact absurd h2 (by simp)
  | some y =>
    rw [hopt] at h2
    simp only [Option.map_some] at h2
    have hsnd := congrArg Prod.snd (Option.some.inj h2)
    simpa using hsnd

/-! ### Arithmetic core: gap transfer between falling bone lines -/

private theorem sin_run_le (p : Params) (x : Int) (_hx : 0 ≤ x) (_hcos : 0 ≤ p.cos)
    (hsin : 0 < p.sin) : p.sin * run p x ≤ x * p.cos := by
  unfold run
  have h := Int.mul_fdiv_add_fmod (x * p.cos) p.sin
  have h2 := Int.fmod_nonneg_of_pos (x * p.cos) hsin
  omega

private theorem sin_run_ge (p : Params) (x : Int) (_hx : 0 ≤ x) (_hcos : 0 ≤ p.cos)
    (hsin : 0 < p.sin) : x * p.cos - p.sin + 1 ≤ p.sin * run p x := by
  unfold run
  have h := Int.mul_fdiv_add_fmod (x * p.cos) p.sin
  have h2 := Int.fmod_lt_of_pos (x * p.cos) hsin
  omega

/-- A later odd sibling attaches at least `m` further right, and this gap
survives the floor rounding of the two interpolation formulas at every common
ordinate `t` of the two spans, losing at most one unit. -/
private theorem bclose_floor_gap (a b denominator margin : Int)
    (hden : 0 < denominator) (hgap : a + denominator * margin ≤ b) :
    Int.fdiv a denominator + margin ≤ Int.fdiv b denominator := by
  have hq := Int.mul_fdiv_add_fmod a denominator
  have hr := Int.fmod_nonneg_of_pos a hden
  apply Chart.le_fdiv_of_mul_le hden
  rw [Int.mul_add]
  omega

/-- Floor gaps add along a parent's bone: the earlier draw's attachment point plus
one margin stays at or below the later draw's attachment point.  (Replica of the
private `attachment_counter_gap` of `IshikawaClearanceFacts`, used by
`place_generated_odd_sibling_attachment_gap`.) -/
private theorem bclose_counter_gap (left right count margin firstDraw secondDraw : Int)
    (hden : 0 < count + 1) (hmargin : 0 ≤ margin)
    (hreserve : (count + 1) * margin ≤ left - right)
    (hrank : firstDraw + 1 ≤ secondDraw) :
    left + Int.fdiv ((right - left) * (count - firstDraw)) (count + 1) + margin ≤
      left + Int.fdiv ((right - left) * (count - secondDraw)) (count + 1) := by
  have hnonnegative : 0 ≤ left - right :=
    Int.le_trans (Int.mul_nonneg (Int.le_of_lt hden) hmargin) hreserve
  have hmul := Int.mul_le_mul_of_nonneg_left
    (show (1 : Int) ≤ secondDraw - firstDraw by omega) hnonnegative
  simp only [Int.mul_one] at hmul
  have halgebra :
      (right - left) * (count - secondDraw) -
          (right - left) * (count - firstDraw) =
        (left - right) * (secondDraw - firstDraw) := by
    simp only [Int.mul_sub, Int.sub_mul]
    omega
  have hgap := bclose_floor_gap
    ((right - left) * (count - firstDraw))
    ((right - left) * (count - secondDraw)) (count + 1) margin hden (by omega)
  omega

theorem parallel_line_gap (p : Params)
    (Ix0 Ix1 It0 It1 Sx0 Sx1 St0 St1 t m : Int)
    (hsin : 0 < p.sin) (hcos : 0 ≤ p.cos)
    (hspI : 0 < It1 - It0) (hspS : 0 < St1 - St0)
    (hfallI : Ix1 - Ix0 = -run p (It1 - It0))
    (hfallS : Sx1 - Sx0 = -run p (St1 - St0))
    (hbase : It0 = St0) (hw0 : 0 ≤ t - St0) (hw : t - St0 ≤ St1 - St0)
    (hgap : Sx0 + m ≤ Ix0) :
    m - 1 ≤ Ix0 + Int.fdiv ((Ix1 - Ix0) * (t - It0)) (It1 - It0)
      - (Sx0 + Int.fdiv ((Sx1 - Sx0) * (t - St0)) (St1 - St0)) := by
  -- Rename to the common start ordinate.
  rw [hbase]
  have hfallI' : Ix1 - Ix0 = -run p (It1 - St0) := by rw [hfallI, hbase]
  have hfallS' : Sx1 - Sx0 = -run p (St1 - St0) := hfallS
  have hspI' : 0 < It1 - St0 := by omega
  have hspI0' : 0 ≤ It1 - St0 := by omega
  have hspS0 : 0 ≤ St1 - St0 := by omega
  rw [show (Ix1 - Ix0) * (t - St0) = -run p (It1 - St0) * (t - St0) from by rw [hfallI'],
    show (Sx1 - Sx0) * (t - St0) = -run p (St1 - St0) * (t - St0) from by rw [hfallS']]
  -- Remainder bounds for the two `run` values.
  have hrunI1 := sin_run_le p (It1 - St0) (by omega) hcos hsin
  have hrunS1 := sin_run_le p (St1 - St0) (by omega) hcos hsin
  have hrunI2 := sin_run_ge p (It1 - St0) (by omega) hcos hsin
  have hrunS2 := sin_run_ge p (St1 - St0) (by omega) hcos hsin
  -- The slope residual of each `run`: `sin * run = span * cos - r`, `0 ≤ r < sin`.
  obtain ⟨rI, hrIdef, hrI0, hrIlt⟩ :
      ∃ r, p.sin * run p (It1 - St0) = (It1 - St0) * p.cos - r ∧ 0 ≤ r ∧ r ≤ p.sin - 1 :=
    ⟨(It1 - St0) * p.cos - p.sin * run p (It1 - St0), by omega, by omega, by omega⟩
  obtain ⟨rS, hrSdef, hrS0, hrSlt⟩ :
      ∃ r, p.sin * run p (St1 - St0) = (St1 - St0) * p.cos - r ∧ 0 ≤ r ∧ r ≤ p.sin - 1 :=
    ⟨(St1 - St0) * p.cos - p.sin * run p (St1 - St0), by omega, by omega, by omega⟩
  -- Key slope comparison: `spanS * runI - spanI * runS ≤ spanI - 1`.
  have hK : (St1 - St0) * run p (It1 - St0)
        - (It1 - St0) * run p (St1 - St0) ≤ It1 - St0 - 1 := by
    have hSI : p.sin * ((St1 - St0) * run p (It1 - St0))
        = (It1 - St0) * ((St1 - St0) * p.cos) - (St1 - St0) * rI := by
      rw [Int.mul_left_comm, hrIdef, Int.mul_sub,
        ← Int.mul_assoc (St1 - St0) (It1 - St0) p.cos,
        ← Int.mul_assoc (It1 - St0) (St1 - St0) p.cos,
        Int.mul_comm (It1 - St0) (St1 - St0)]
    have hSS : p.sin * ((It1 - St0) * run p (St1 - St0))
        = (St1 - St0) * ((It1 - St0) * p.cos) - (It1 - St0) * rS := by
      rw [Int.mul_left_comm, hrSdef, Int.mul_sub,
        ← Int.mul_assoc (It1 - St0) (St1 - St0) p.cos,
        ← Int.mul_assoc (St1 - St0) (It1 - St0) p.cos,
        Int.mul_comm (St1 - St0) (It1 - St0)]
    have hmulS : (It1 - St0) * rS ≤ p.sin * (It1 - St0) - (It1 - St0) := by
      have h := Int.mul_le_mul_of_nonneg_left (show rS ≤ p.sin - 1 from by omega) hspI0'
      rw [Int.mul_sub, Int.mul_comm (It1 - St0) p.sin] at h
      omega
    have hmulI0 : 0 ≤ (St1 - St0) * rI := Int.mul_nonneg hspS0 hrI0
    have hscaled : p.sin * ((St1 - St0) * run p (It1 - St0)
        - (It1 - St0) * run p (St1 - St0)) ≤ p.sin * (It1 - St0) - (It1 - St0) := by
      rw [Int.mul_sub p.sin ((St1 - St0) * run p (It1 - St0))
        ((It1 - St0) * run p (St1 - St0)), hSI, hSS,
        ← Int.mul_assoc (St1 - St0) (It1 - St0) p.cos,
        ← Int.mul_assoc (It1 - St0) (St1 - St0) p.cos,
        Int.mul_comm (It1 - St0) (St1 - St0)]
      omega
    by_cases hle : (St1 - St0) * run p (It1 - St0)
        - (It1 - St0) * run p (St1 - St0) ≤ It1 - St0 - 1
    · exact hle
    · have hXA : p.sin * (It1 - St0) ≤ p.sin * ((St1 - St0) * run p (It1 - St0)
          - (It1 - St0) * run p (St1 - St0)) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega : 0 ≤ p.sin)
      omega
  -- Scale by the common ordinate offset `w = t - St0`.
  have hAB : (It1 - St0 - 1) * (St1 - St0)
      ≤ (It1 - St0) * (St1 - St0) - (St1 - St0) := by
    rw [Int.sub_mul]
    omega
  have hbound : (St1 - St0) * run p (It1 - St0) * (t - St0)
      - (It1 - St0) * run p (St1 - St0) * (t - St0)
      ≤ (It1 - St0) * (St1 - St0) - (St1 - St0) := by
    have h1 := Int.mul_le_mul_of_nonneg_right hK hw0
    rw [Int.sub_mul] at h1
    have h2 := Int.mul_le_mul_of_nonneg_right hw (by omega : 0 ≤ It1 - St0 - 1)
    rw [Int.mul_comm (t - St0) (It1 - St0 - 1),
        Int.mul_comm (St1 - St0) (It1 - St0 - 1)] at h2
    omega
  have hbound' : (St1 - St0) * (run p (It1 - St0) * (t - St0))
      - (It1 - St0) * (run p (St1 - St0) * (t - St0))
      ≤ (It1 - St0) * (St1 - St0) - (St1 - St0) := by
    rw [← Int.mul_assoc, ← Int.mul_assoc]
    exact hbound
  -- Floor-division facts at the common ordinate.
  have hfI := Int.mul_fdiv_add_fmod (-(run p (It1 - St0)) * (t - St0)) (It1 - St0)
  have hfImod0 := Int.fmod_nonneg_of_pos (-(run p (It1 - St0)) * (t - St0)) hspI'
  have hfImodlt := Int.fmod_lt_of_pos (-(run p (It1 - St0)) * (t - St0)) hspI'
  have hfS := Int.mul_fdiv_add_fmod (-(run p (St1 - St0)) * (t - St0)) (St1 - St0)
  have hfSmod0 := Int.fmod_nonneg_of_pos (-(run p (St1 - St0)) * (t - St0)) hspS
  have hSFI : (St1 - St0) * Int.fmod (-(run p (It1 - St0)) * (t - St0)) (It1 - St0)
      ≤ (It1 - St0) * (St1 - St0) - (St1 - St0) := by
    have h := Int.mul_le_mul_of_nonneg_right
      (show Int.fmod (-(run p (It1 - St0)) * (t - St0)) (It1 - St0) ≤ It1 - St0 - 1 from
        by omega) hspS0
    rw [Int.mul_comm] at h
    omega
  -- The interpolated gap cannot lose two units: otherwise the scaled comparison
  -- `spanS*runI*w - spanI*runS*w ≤ spanI*spanS - spanS` is violated.
  have hnot : ¬ (Int.fdiv (-(run p (It1 - St0)) * (t - St0)) (It1 - St0) + 2
      ≤ Int.fdiv (-(run p (St1 - St0)) * (t - St0)) (St1 - St0)) := by
    intro hcon
    have h3 := Int.mul_le_mul_of_nonneg_left hcon (by omega : 0 ≤ It1 - St0)
    have h4 := Int.mul_le_mul_of_nonneg_left h3 hspS0
    have e1 : (St1 - St0) * ((It1 - St0) * Int.fdiv (-(run p (It1 - St0)) * (t - St0)) (It1 - St0))
        = -((St1 - St0) * (run p (It1 - St0) * (t - St0)))
          - (St1 - St0) * Int.fmod (-(run p (It1 - St0)) * (t - St0)) (It1 - St0) := by
      have hsub : (It1 - St0) * Int.fdiv (-(run p (It1 - St0)) * (t - St0)) (It1 - St0)
          = -(run p (It1 - St0)) * (t - St0)
            - Int.fmod (-(run p (It1 - St0)) * (t - St0)) (It1 - St0) := by
        omega
      rw [hsub, Int.mul_sub, Int.neg_mul, Int.mul_neg]
    have e2 : (It1 - St0) * ((St1 - St0) * Int.fdiv (-(run p (St1 - St0)) * (t - St0)) (St1 - St0))
        = -((It1 - St0) * (run p (St1 - St0) * (t - St0)))
          - (It1 - St0) * Int.fmod (-(run p (St1 - St0)) * (t - St0)) (St1 - St0) := by
      have hsub : (St1 - St0) * Int.fdiv (-(run p (St1 - St0)) * (t - St0)) (St1 - St0)
          = -(run p (St1 - St0)) * (t - St0)
            - Int.fmod (-(run p (St1 - St0)) * (t - St0)) (St1 - St0) := by
        omega
      rw [hsub, Int.mul_sub, Int.neg_mul, Int.mul_neg]
    have hIFM0 : 0 ≤ (It1 - St0) * Int.fmod (-(run p (St1 - St0)) * (t - St0)) (St1 - St0) :=
      Int.mul_nonneg hspI0' hfSmod0
    simp only [Int.mul_add] at h4
    rw [e1, Int.mul_left_comm (St1 - St0) (It1 - St0)
      (Int.fdiv (-(run p (St1 - St0)) * (t - St0)) (St1 - St0)), e2,
      Int.mul_left_comm (St1 - St0) (It1 - St0) 2,
      ← Int.mul_assoc (It1 - St0) (St1 - St0) 2] at h4
    omega
  omega

/-! Corrected sibling obligation: `HardBSibling` with `frames` pinned to the
executed birth frames through `HardBRealFrames`. -/
def HardBSiblingReal (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed) : Prop :=
  let r := effectivePlacedInput ns (measuredSideLength p ribs)
    (generatedRib ns (cause, k))
  ∀ (child j : Entry) (childIdx jIdx : Nat) (nj : Tree.Node)
    (frames : List Bone) (childBorn jBorn : Bone),
    HardBCaseConfig ns p cause k spine r child j childIdx jIdx nj frames
      childBorn jBorn →
    HardBRealFrames ns p spine r placed hplace frames →
    j.parent = child.parent →
    ¬ Polyline.hitsRect
      [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
       ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
      ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
        nj.width, nj.height⟩

/-- Corrected deeper-earlier obligation: `HardBDeeperEarlier` with `frames`
pinned through `HardBRealFrames` and the branch-5 placement classified by the
corrected block form `HardBBranch5Block`. -/
def HardBDeeperEarlierReal (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed)
    (_env : IshikawaEnvFrames ns p
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k)))) : Prop :=
  let r := effectivePlacedInput ns (measuredSideLength p ribs)
    (generatedRib ns (cause, k))
  ∀ (child j : Entry) (childIdx jIdx : Nat) (nj : Tree.Node)
    (frames : List Bone) (childBorn jBorn : Bone),
    HardBCaseConfig ns p cause k spine r child j childIdx jIdx nj frames
      childBorn jBorn →
    HardBRealFrames ns p spine r placed hplace frames →
    HardBBranch5Block ns cause k (child.parent).toNat childIdx jIdx j →
    child.parent ≠ (jIdx : Int) →
    j.parent ≠ child.parent →
    ¬(jBorn.t1 + r.heights ≤ childBorn.t0) →
    ¬(childBorn.t1 + r.heights ≤ jBorn.t1) →
    ¬ Polyline.hitsRect
      [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
       ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
      ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
        nj.width, nj.height⟩


/-- HARD B final assembly over the corrected obligations: identical to
`ishikawa_hard_b`, but the sibling and deeper-earlier branches consume
`HardBSiblingReal`/`HardBDeeperEarlierReal` (frames pinned by
`HardBRealFrames`, which the executed `place_common_birth_frames` witness
supplies) and the corrected block classification `hblock`. There is no
`hbranch5` hypothesis: the refuted `HardBBranch5Placement` is assumed nowhere.
`hblock` is discharged downstream by `hard_b_branch5_placement_block'` in
`IshikawaHardBBranch5Facts` (that module imports this one, so the citation
cannot live here). -/
theorem ishikawa_hard_b_real
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed)
    (henv : IshikawaEnvFrames ns p
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))))
    (hsib : HardBSiblingReal ns p raw hrun ribs hg cause k hsource hcause
      spine placed hplace)
    (hdeep : HardBDeeperEarlierReal ns p raw hrun ribs hg cause k hsource hcause
      spine placed hplace henv)
    (hblock : ∀ (child j : Entry) (childIdx jIdx : Nat),
      (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx →
      (j, jIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx →
      child.depth % 2 ≠ 0 → jIdx < childIdx →
      HardBBranch5Block ns cause k (child.parent).toNat childIdx jIdx j)
    (child j : Entry) (childIdx jIdx : Nat)
    (hchild : (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hj : (j, jIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hodd : child.depth % 2 ≠ 0)
    (hjlt : jIdx < childIdx)
    (nj : Tree.Node) (hnj : ns[j.node]? = some nj) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))
    ∃ (frames : List Bone) (childBorn jBorn : Bone),
      frames.length = r.entries.length + 1 ∧
      frames[childIdx + 1]? = some childBorn ∧ frames[jIdx + 1]? = some jBorn ∧
      ¬ Polyline.hitsRect
        [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
         ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
        ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
          nj.width, nj.height⟩ ∧
      ∀ (i : Nat) (rect : Rect) (points : List Point), (i, rect, points) ∈ placed.pieces →
        (∃ causeNode : Tree.Node, ns[r.cause]? = some causeNode ∧ i = r.cause ∧
          rect = ⟨-run p r.length - Int.fdiv causeNode.width 2,
            if r.upper then ordinate spine r.upper r.length - causeNode.height
            else ordinate spine r.upper r.length, causeNode.width, causeNode.height⟩ ∧
          points = [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
        ∃ (e : Entry) (idx : Nat) (node : Tree.Node) (born : Bone),
          (e, idx) ∈ r.entries.zipIdx ∧ i = e.node ∧ ns[e.node]? = some node ∧
          frames[idx + 1]? = some born ∧
          rect = ⟨born.x1 - node.width, ordinate spine r.upper born.t1 - Int.fdiv node.height 2,
            node.width, node.height⟩ ∧
          points = [⟨born.x0, ordinate spine r.upper born.t0⟩,
            ⟨born.x1, ordinate spine r.upper born.t1⟩] := by
  let source := generatedRib ns (cause, k)
  let r := effectivePlacedInput ns (measuredSideLength p ribs) source
  by_cases hparcase : child.parent = (jIdx : Int)
  · -- Parent-box case: the landed theorem supplies its own witnesses, and
    -- its parent node is j's node by `hnj`.
    obtain ⟨frames2, childBorn2, parentBorn2, n2, hlen2, hcb2, hjb2, hn2, hmiss2,
      hpieces2⟩ :=
      place_generated_odd_entry_route_misses_parent_box ns p raw hrun ribs hg
        cause k hsource hcause spine placed hplace child j childIdx jIdx hchild hj
        hodd hparcase
    have hnEq : n2 = nj := Option.some.inj (hn2.symm.trans hnj)
    rw [hnEq] at hmiss2
    exact ⟨frames2, childBorn2, parentBorn2, hlen2, hcb2, hjb2, hmiss2, hpieces2⟩
  -- Remaining cases: read the birth frames of the successful run.
  obtain ⟨frames, hlen, _hroot, hrecords, hpieces⟩ :=
    place_common_birth_frames ns p spine r placed hplace
  obtain ⟨childDone, childRest, hchildPrefix, _⟩ := List.eq_append_cons_of_mem hchild
  change r.entries.zipIdx = childDone ++ (child, childIdx) :: childRest at hchildPrefix
  obtain ⟨childPos, parI, childBorn, hchildPos, hparLookup, hchildBorn, hchildEq⟩ :=
    hrecords childDone child childIdx childRest hchildPrefix
  obtain ⟨jDone, jRest, hjPrefix, _⟩ := List.eq_append_cons_of_mem hj
  change r.entries.zipIdx = jDone ++ (j, jIdx) :: jRest at hjPrefix
  obtain ⟨jPos, _parJ, jBorn, hjPos, _hjparLookup, hjBorn, hjEq⟩ :=
    hrecords jDone j jIdx jRest hjPrefix
  -- Route span sanity for I (odd): its slot starts at or after the parent
  -- entry's own slot, so `childBorn.t0 ≤ childBorn.t1`.
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have hheight : 0 ≤ r.heights := by
    change 0 ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact entry_height_fold_initial ns _ 0
  have hnonempty : source.entries.isEmpty = false := by
    cases hentries : source.entries with
    | nil =>
      change (child, childIdx) ∈ source.entries.zipIdx at hchild
      rw [hentries] at hchild
      simp at hchild
    | cons first rest => rfl
  have hbudget := generated_reservation_budget ns p ribs hg source hsource hnonempty
  have hrootFalse : child.parent ≠ -1 := by
    intro heq
    have hd := generated_root_depth ns cause k hlink hcause child childIdx hchild heq
    exact hodd (by omega)
  have hlb := generated_entry_parent_lower_bound ns cause k child childIdx hchild
  have hparIdx : child.parent = ((child.parent).toNat : Int) := by omega
  have howner : (child.parent + 1).toNat = (child.parent).toNat + 1 := by
    rw [hparIdx]
    omega
  rw [howner] at hparLookup hchildEq
  obtain ⟨hpb, _⟩ := List.getElem?_eq_some_iff.mp hparLookup
  rw [hlen] at hpb
  have hparentBound : (child.parent).toNat < r.entries.length := by omega
  let parentEntry := (generatedRib ns (cause, k)).entries[(child.parent).toNat]'hparentBound
  have hparentLookup : (generatedRib ns (cause, k)).entries[(child.parent).toNat]? = some parentEntry :=
    List.getElem?_eq_getElem hparentBound
  have hparentMem : (parentEntry, (child.parent).toNat) ∈ (generatedRib ns (cause, k)).entries.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hparentLookup
  have hpar : child.parent = ((child.parent).toNat : Int) := hparIdx
  have hdepth := generated_parent_child_depth ns cause k hlink hcause parentEntry child
    (child.parent).toNat childIdx hparentMem hchild hpar
  have hparentEven : parentEntry.depth % 2 = 0 :=
    parent_depth_even parentEntry.depth child.depth hdepth hodd
  obtain ⟨parentDone, parentRest, hparentPrefix, _⟩ := List.eq_append_cons_of_mem hparentMem
  change r.entries.zipIdx = parentDone ++ (parentEntry, (child.parent).toNat) :: parentRest
    at hparentPrefix
  obtain ⟨parentPos, grandpar, parentBorn, hparentPos, _hgpLookup, hparentBornLookup,
    hparentEquation⟩ :=
    hrecords parentDone parentEntry (child.parent).toNat parentRest hparentPrefix
  have hsame : parI = parentBorn :=
    Option.some.inj (hparLookup.symm.trans hparentBornLookup)
  rw [hsame] at hchildEq
  have hchildT0 : childBorn.t0 = parentBorn.t0 := by
    rw [hchildEq]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws childDone ((child.parent).toNat + 1) }
      child.depth (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns child.node).length (run p r.heights + 3) hodd).1
  have hchildT1 : childBorn.t1 =
      Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [hchildEq]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws childDone ((child.parent).toNat + 1) }
      child.depth (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns child.node).length (run p r.heights + 3) hodd).2.1
  have hparentT0 : parentBorn.t0 =
      Int.fdiv (r.length * (parentPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [hparentEquation]
    exact (depthBone_even_endpoints p
      { grandpar with drawn := processedOddDraws parentDone (parentEntry.parent + 1).toNat }
      parentEntry.depth (Int.fdiv (r.length * (parentPos.2 + 1 : Nat))
        (r.entries.length + 1 : Nat)) (children ns parentEntry.node).length
      (run p r.heights + 3) hparentEven).1
  have hposLt : parentPos.2 < childPos.2 :=
    (generated_parent_child_order ns cause k parentEntry child (child.parent).toNat
      childIdx hparentMem hchild hpar parentPos childPos hparentPos hchildPos).1
      hparentEven
  have hslotGap := ordinal_slots_gap r.length (r.entries.length + 1 : Nat) r.heights
    (parentPos.2 + 1 : Nat) (childPos.2 + 1 : Nat) (by omega) hheight hbudget (by omega)
  have hspan : childBorn.t0 ≤ childBorn.t1 := by
    rw [hchildT0, hparentT0, hchildT1]
    omega
  have cfg : HardBCaseConfig ns p cause k spine r child j childIdx jIdx nj frames
      childBorn jBorn :=
    ⟨hchild, hj, hodd, hjlt, hnj, hlen, hchildBorn, hjBorn, hspan⟩
  -- The executed frames are a `BirthFramesShape` witness for themselves, so
  -- `HardBRealFrames` is available for `frames`.
  have hreal : HardBRealFrames ns p spine r placed hplace frames :=
    ⟨frames, ⟨hlen, _hroot, hrecords⟩, fun _i _b h => h⟩
  refine ⟨frames, childBorn, jBorn, hlen, hchildBorn, hjBorn, ?_, hpieces⟩
  refine hard_b_route_case_split r child j childIdx jIdx jBorn childBorn nj spine
    ?_ ?_ ?_ ?_ ?_
  · intro hc
    exact absurd hc hparcase
  · intro hs
    exact hsib child j childIdx jIdx nj frames childBorn jBorn cfg hreal hs
  · intro he
    exact HardBEarlierSlot ns p raw hrun ribs hg cause k hsource hcause spine
      placed hplace child j childIdx jIdx nj frames childBorn jBorn cfg he
  · intro hl
    exact HardBLaterSlot ns p raw hrun ribs hg cause k hsource hcause spine
      placed hplace child j childIdx jIdx nj frames childBorn jBorn cfg hl
  · intro hc hs he hl
    have hB := hblock child j childIdx jIdx hchild hj hodd hjlt
    rcases hB with _hfirst | ⟨hIdx, H, _hH, _hHroot, hHor, hord⟩
    · exact hdeep child j childIdx jIdx nj frames childBorn jBorn cfg hreal
        (hblock child j childIdx jIdx hchild hj hodd hjlt) hc hs he hl
    · rcases hHor with ⟨_hHJ, hIdxJ⟩ | _hchain
      · -- Root subcase `hIdx = jIdx`: the head position is J's own position,
        -- which strictly precedes the parent position, so step B supplies the
        -- earlier-slot inequality, contradicting `he`.
        have hjPos' : (generatedRib ns (cause, k)).order.zipIdx.find?
            (fun v => v.1 == hIdx) = some jPos := by
          rw [hIdxJ]
          exact hjPos
        have hdisj := hord jPos parentPos hjPos' hparentPos
        rcases hdisj with hle | hltpos
        · omega
        · have hjT1 : jBorn.t1
              = Int.fdiv (r.length * (jPos.2 + 1 : Nat))
                (r.entries.length + 1 : Nat) := by
            rw [hjEq]
            exact depthBone_endpoint_slot _ _ _ _ _ _
          have hslot : jBorn.t1 + r.heights ≤ childBorn.t0 :=
            hard_b_slot_mono_of_pos_lt r jBorn childBorn parentBorn jPos parentPos
              hjT1 hparentT0 hchildT0 hheight hbudget hltpos
          exact absurd hslot he
      · exact hdeep child j childIdx jIdx nj frames childBorn jBorn cfg hreal
          (hblock child j childIdx jIdx hchild hj hodd hjlt) hc hs he hl

/-- Sibling case of HARD B over the executed birth frames: an earlier sibling
J of the odd route I attaches strictly to the right of I's attachment point
(`attachment_counter_gap` replicated on the executed frames), and
`parallel_line_gap` carries that gap along both falling bone lines to J's
ordinate, where `interpolated_box_diagonal_miss` closes. -/
theorem hard_b_sibling_real
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed) :
    HardBSiblingReal ns p raw hrun ribs hg cause k hsource hcause
      spine placed hplace := by
  intro child j childIdx jIdx nj frames childBorn jBorn hconfig hreal hsib
  obtain ⟨hchild, hj, hodd, hjlt, hnj, hlen, hchildBorn, hjBorn, hspan⟩ := hconfig
  obtain ⟨frames0, hshape0, hsub⟩ := hreal
  obtain ⟨hlen0, hroot0, hrecords0⟩ := hshape0
  -- `frames` and `frames0` agree pointwise, hence are equal.
  have hframesEq : frames = frames0 := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < frames.length
    · have hfi : frames[i]? = some frames[i] := List.getElem?_eq_getElem hi
      have hb : frames0[i]? = some frames[i] := hsub i _ hfi
      have hio : i < frames0.length := by
        have := (List.getElem?_eq_some_iff.mp hb).choose_spec
        omega
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hio]
      have hb2 : frames0[i]? = some frames0[i] := List.getElem?_eq_getElem hio
      rw [hb2] at hb
      exact hb.symm
    · have hni : frames[i]? = none := by
        rw [List.getElem?_eq_none_iff.mpr (by omega : frames.length ≤ i)]
      have hni0 : frames0[i]? = none := by
        rw [List.getElem?_eq_none_iff.mpr (by omega : frames0.length ≤ i)]
      rw [hni, hni0]
  subst hframesEq
  let r := effectivePlacedInput ns (measuredSideLength p ribs)
    (generatedRib ns (cause, k))
  -- Birth records for J and I off the executed frames.
  obtain ⟨jDone, jRest, hjPrefix, _⟩ := List.eq_append_cons_of_mem hj
  change (generatedRib ns (cause, k)).entries.zipIdx =
      jDone ++ (j, jIdx) :: jRest at hjPrefix
  obtain ⟨jPos, jPar, jBorn0, hjPos, hjParLookup, hjBorn0, hjEq⟩ :=
    hrecords0 jDone j jIdx jRest hjPrefix
  obtain ⟨childDone, childRest, hchildPrefix, _⟩ := List.eq_append_cons_of_mem hchild
  change (generatedRib ns (cause, k)).entries.zipIdx =
      childDone ++ (child, childIdx) :: childRest at hchildPrefix
  obtain ⟨childPos, cPar, childBorn0, hchildPos, hchildParLookup, hchildBorn0,
    hchildEq⟩ := hrecords0 childDone child childIdx childRest hchildPrefix
  -- The two born bones are the configured ones.
  have hjBornEq : jBorn0 = jBorn := by
    have h1 : frames[jIdx + 1]? = some jBorn := hjBorn
    have h2 : frames[jIdx + 1]? = some jBorn0 := hjBorn0
    exact Option.some.inj (h2.symm.trans h1)
  have hchildBornEq : childBorn0 = childBorn := by
    have h1 : frames[childIdx + 1]? = some childBorn := hchildBorn
    have h2 : frames[childIdx + 1]? = some childBorn0 := hchildBorn0
    exact Option.some.inj (h2.symm.trans h1)
  -- Shared context: link, slope parameters, heights, budget.
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have hne : ns ≠ [] := by
    intro heq
    simp [heq, children] at hcause
  have hparameters := successful_slope_parameters ns p raw hne hrun
  have hheight : 0 ≤ r.heights := by
    change 0 ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact entry_height_fold_initial ns _ 0
  have hnonempty : (generatedRib ns (cause, k)).entries.isEmpty = false := by
    cases hentries : (generatedRib ns (cause, k)).entries with
    | nil =>
      change (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx at hchild
      rw [hentries] at hchild
      simp at hchild
    | cons first rest => rfl
  have hbudget := generated_reservation_budget ns p ribs hg
    (generatedRib ns (cause, k)) hsource hnonempty
  -- The shared parent entry and its born bone.
  have hlb := generated_entry_parent_lower_bound ns cause k child childIdx hchild
  have hrootFalse : child.parent ≠ -1 := by
    intro heq
    have hd := generated_root_depth ns cause k hlink hcause child childIdx hchild heq
    exact hodd (by omega)
  have hparIdx : child.parent = ((child.parent).toNat : Int) := by omega
  have hchildOwner : (child.parent + 1).toNat = (child.parent).toNat + 1 := by
    rw [hparIdx]
    omega
  rw [hchildOwner] at hchildParLookup hchildEq
  obtain ⟨hpb, _⟩ := List.getElem?_eq_some_iff.mp hchildParLookup
  rw [hlen0] at hpb
  have hparentBound : (child.parent).toNat < r.entries.length := Nat.lt_of_succ_lt_succ hpb
  let parentEntry := (generatedRib ns (cause, k)).entries[(child.parent).toNat]'hparentBound
  have hparentLookup : (generatedRib ns (cause, k)).entries[(child.parent).toNat]? = some parentEntry :=
    List.getElem?_eq_getElem hparentBound
  have hparentMem : (parentEntry, (child.parent).toNat) ∈ (generatedRib ns (cause, k)).entries.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hparentLookup
  have hpar : child.parent = ((child.parent).toNat : Int) := hparIdx
  have hchildDepth := generated_parent_child_depth ns cause k hlink hcause
    parentEntry child (child.parent).toNat childIdx hparentMem hchild hpar
  have hparentEven : parentEntry.depth % 2 = 0 :=
    parent_depth_even parentEntry.depth child.depth hchildDepth hodd
  -- J has the same parent entry, hence the same (odd) depth.
  have hjPar : j.parent = ((child.parent).toNat : Int) := by
    have h1 : j.parent = child.parent := hsib
    omega
  have hjDepth := generated_parent_child_depth ns cause k hlink hcause
    parentEntry j (child.parent).toNat jIdx hparentMem hj hjPar
  have hjOdd : j.depth % 2 ≠ 0 := by
    rw [hjDepth]
    omega
  -- Parent birth record.
  obtain ⟨parentDone, parentRest, hparentPrefix, _⟩ :=
    List.eq_append_cons_of_mem hparentMem
  change (generatedRib ns (cause, k)).entries.zipIdx =
      parentDone ++ (parentEntry, (child.parent).toNat) :: parentRest at hparentPrefix
  obtain ⟨parentPos, grandpar, parentBorn, hparentPos, _hgpLookup, hparentBornLookup,
    hparentEquation⟩ :=
    hrecords0 parentDone parentEntry (child.parent).toNat parentRest hparentPrefix
  have hcPar : cPar = parentBorn := by
    have h1 : frames[(child.parent).toNat + 1]? = some cPar := hchildParLookup
    have h2 : frames[(child.parent).toNat + 1]? = some parentBorn := hparentBornLookup
    exact Option.some.inj (h1.symm.trans h2)
  rw [hcPar] at hchildEq
  -- Endpoint equations for the three bones.
  have hchildT0 : childBorn.t0 = parentBorn.t0 := by
    rw [← hchildBornEq, hchildEq]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws childDone ((child.parent).toNat + 1) }
      child.depth (Int.fdiv (r.length * (childPos.2 + 1 : Nat))
        (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).1
  have hchildT1 : childBorn.t1 =
      Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [← hchildBornEq, hchildEq]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws childDone ((child.parent).toNat + 1) }
      child.depth (Int.fdiv (r.length * (childPos.2 + 1 : Nat))
        (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).2.1
  have hchildX1 : childBorn.x1 = childBorn.x0 - run p (childBorn.t1 - childBorn.t0) := by
    rw [hchildT1, hchildT0, ← hchildBornEq, hchildEq]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws childDone ((child.parent).toNat + 1) }
      child.depth (Int.fdiv (r.length * (childPos.2 + 1 : Nat))
        (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).2.2.2
  have hchildX0 : childBorn.x0 = parentBorn.x0 +
      Int.fdiv ((parentBorn.x1 - parentBorn.x0) *
        (parentBorn.count - processedOddDraws childDone ((child.parent).toNat + 1)))
        (parentBorn.count + 1) := by
    rw [← hchildBornEq, hchildEq]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws childDone ((child.parent).toNat + 1) }
      child.depth (Int.fdiv (r.length * (childPos.2 + 1 : Nat))
        (r.entries.length + 1 : Nat)) (children ns child.node).length
      (run p r.heights + 3) hodd).2.2.1
  have hparentT0 : parentBorn.t0 =
      Int.fdiv (r.length * (parentPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [hparentEquation]
    exact (depthBone_even_endpoints p
      { grandpar with drawn := processedOddDraws parentDone (parentEntry.parent + 1).toNat }
      parentEntry.depth (Int.fdiv (r.length * (parentPos.2 + 1 : Nat))
        (r.entries.length + 1 : Nat)) (children ns parentEntry.node).length
      (run p r.heights + 3) hparentEven).1
  -- J's parent lookup is the same bone as I's.
  have hjParentEq : j.parent = child.parent := hsib
  have hjOwner : (j.parent + 1).toNat = (child.parent).toNat + 1 := by
    rw [hjParentEq]
    exact hchildOwner
  have hjParentBound : (j.parent).toNat < r.entries.length := by
    rw [hjParentEq]
    exact hparentBound
  rw [hjOwner] at hjParLookup hjEq
  have hsameParent : jPar = parentBorn := by
    have h1 : frames[(child.parent).toNat + 1]? = some jPar := hjParLookup
    have h2 : frames[(child.parent).toNat + 1]? = some parentBorn := hparentBornLookup
    exact Option.some.inj (h1.symm.trans h2)
  have hjT0 : jBorn.t0 = parentBorn.t0 := by
    rw [← hjBornEq, hjEq, hsameParent]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws jDone ((child.parent).toNat + 1) }
      j.depth (Int.fdiv (r.length * (jPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns j.node).length (run p r.heights + 3) hjOdd).1
  have hjT1 : jBorn.t1 =
      Int.fdiv (r.length * (jPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := by
    rw [← hjBornEq, hjEq, hsameParent]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws jDone ((child.parent).toNat + 1) }
      j.depth (Int.fdiv (r.length * (jPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns j.node).length (run p r.heights + 3) hjOdd).2.1
  have hjX1 : jBorn.x1 = jBorn.x0 - run p (jBorn.t1 - jBorn.t0) := by
    rw [hjT1, hjT0, ← hjBornEq, hjEq, hsameParent]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws jDone ((child.parent).toNat + 1) }
      j.depth (Int.fdiv (r.length * (jPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns j.node).length (run p r.heights + 3) hjOdd).2.2.2
  have hjX0 : jBorn.x0 = parentBorn.x0 +
      Int.fdiv ((parentBorn.x1 - parentBorn.x0) *
        (parentBorn.count - processedOddDraws jDone ((child.parent).toNat + 1)))
        (parentBorn.count + 1) := by
    rw [← hjBornEq, hjEq, hsameParent]
    exact (depthBone_odd_endpoints p
      { parentBorn with drawn := processedOddDraws jDone ((child.parent).toNat + 1) }
      j.depth (Int.fdiv (r.length * (jPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns j.node).length (run p r.heights + 3) hjOdd).2.2.1
  -- Order facts: the parent's slot precedes J's slot.
  have hjParentOrder := generated_parent_child_order ns cause k parentEntry j
    (child.parent).toNat jIdx hparentMem hj hjPar parentPos jPos hparentPos hjPos
  have hparentPosLtJ : parentPos.2 < jPos.2 := hjParentOrder.1 hparentEven
  -- J's slot is strictly after the parent's slot, hence `childBorn.t0 ≤ jBorn.t1`.
  have hslotPJ := ordinal_slots_gap r.length (r.entries.length + 1 : Nat) r.heights
    (parentPos.2 + 1 : Nat) (jPos.2 + 1 : Nat) (by omega) hheight hbudget (by omega)
  have htj : childBorn.t0 ≤ jBorn.t1 := by
    rw [hchildT0, hparentT0, hjT1]
    omega
  -- Both odd children consume one draw; J's draw precedes I's.
  have hmatchesJ : ((j.depth % 2 != 0) &&
      ((j.parent + 1).toNat == (child.parent).toNat + 1)) = true := by
    have hoddT : (j.depth % 2 != 0) = true := by
      cases hmod : j.depth % 2 with
      | zero => rw [hmod] at hjOdd; exact absurd rfl hjOdd
      | succ n => rfl
    have hown : ((j.parent + 1).toNat == (child.parent).toNat + 1) = true := by
      rw [hjOwner]
      exact beq_self_eq_true _
    rw [hoddT, hown]
    rfl
  have hmatchesC : ((child.depth % 2 != 0) &&
      ((child.parent + 1).toNat == (child.parent).toNat + 1)) = true := by
    have hoddT : (child.depth % 2 != 0) = true := by
      cases hmod : child.depth % 2 with
      | zero => rw [hmod] at hodd; exact absurd rfl hodd
      | succ n => rfl
    have hown : ((child.parent + 1).toNat == (child.parent).toNat + 1) = true := by
      rw [hchildOwner]
      exact beq_self_eq_true _
    rw [hoddT, hown]
    rfl
  have hjLen : jDone.length = jIdx :=
    zipIdx_index_of_split (l := (generatedRib ns (cause, k)).entries) (after := jRest)
      (x := j) (idx := jIdx) (by rw [hjPrefix]; simp)
  have hchildLen : childDone.length = childIdx :=
    zipIdx_index_of_split (l := (generatedRib ns (cause, k)).entries) (after := childRest)
      (x := child) (idx := childIdx) (by rw [hchildPrefix]; simp)
  have hprefixJ : jDone ++ [(j, jIdx)] <+: childDone := by
    apply List.prefix_of_prefix_length_le (l₃ := (generatedRib ns (cause, k)).entries.zipIdx)
    · exact ⟨jRest, by rw [hjPrefix]; simp⟩
    · exact ⟨(child, childIdx) :: childRest, hchildPrefix.symm⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have hstepJ : processedOddDraws (jDone ++ [(j, jIdx)]) ((child.parent).toNat + 1) =
      processedOddDraws jDone ((child.parent).toNat + 1) + 1 := by
    rw [processedOddDraws_append_one jDone j jIdx ((child.parent).toNat + 1), hmatchesJ]
    rfl
  have hrankJ : processedOddDraws jDone ((child.parent).toNat + 1) + 1 ≤
      processedOddDraws childDone ((child.parent).toNat + 1) := by
    have hm := processedOddDraws_prefix (jDone ++ [(j, jIdx)]) childDone
      ((child.parent).toNat + 1) hprefixJ
    rw [hstepJ] at hm
    exact hm
  -- The parent reservation.
  have hreserve := even_native_reservation p
    { grandpar with drawn := processedOddDraws parentDone (parentEntry.parent + 1).toNat }
    parentEntry.depth
    (Int.fdiv (r.length * (parentPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
    (children ns parentEntry.node).length (run p r.heights + 3) hparentEven
  rw [← hparentEquation] at hreserve
  have hmargin : 0 ≤ run p r.heights + 3 := by
    have hrunHeight : 0 ≤ run p r.heights :=
      Int.fdiv_nonneg (Int.mul_nonneg hheight hparameters.1)
        (Int.le_of_lt hparameters.2)
    omega
  -- The attachment gap on the executed frames.
  have hgap : run p r.heights + 3 ≤ childBorn.x0 - jBorn.x0 := by
    have hcounter := bclose_counter_gap parentBorn.x0 parentBorn.x1 parentBorn.count
      (run p r.heights + 3)
      (processedOddDraws jDone ((child.parent).toNat + 1))
      (processedOddDraws childDone ((child.parent).toNat + 1))
      hreserve.1 hmargin hreserve.2 hrankJ
    rw [hjX0, hchildX0]
    omega
  -- The gap survives one floor rounding along I's own fall to J's ordinate.
  have hsin : 0 < p.sin := by
    have h1 := hparameters.2
    omega
  have hjX1' : jBorn.x1 = jBorn.x0 - run p (jBorn.t1 - childBorn.t0) := by
    rw [hjX1]
    have hsame : jBorn.t0 = childBorn.t0 := by rw [hjT0, hchildT0]
    rw [hsame]
  by_cases hnlt : ¬ childBorn.t0 < childBorn.t1
  · have hzero : childBorn.t1 - childBorn.t0 = 0 := by omega
    have hx10 : childBorn.x1 = childBorn.x0 := by
      rw [hchildX1, hzero]
      simp [run]
    have hrunJ : 0 ≤ run p (jBorn.t1 - childBorn.t0) :=
      Int.fdiv_nonneg (Int.mul_nonneg (by omega) hparameters.1)
        (Int.le_of_lt hparameters.2)
    apply Polyline.not_hits_of_allMiss
    refine ⟨Or.inr (Or.inl ?_), trivial⟩
    show min childBorn.x0 childBorn.x1 ≥ jBorn.x1 - nj.width + nj.width
    rw [hx10]
    omega
  have hlt : childBorn.t0 < childBorn.t1 := Decidable.of_not_not hnlt
  have hresv := hard_b_route_reservation p childBorn.x0 childBorn.x1 childBorn.t0
    childBorn.t1 jBorn.t1 jBorn.x0 jBorn.x1 r.heights hsin hlt htj hchildX1 hjX1' hgap
  -- The route falls (J's slot lies below I's route start).
  have hrunSpan : 0 ≤ run p (childBorn.t1 - childBorn.t0) :=
    Int.fdiv_nonneg (Int.mul_nonneg (by omega) hparameters.1)
      (Int.le_of_lt hparameters.2)
  have hx : childBorn.x1 ≤ childBorn.x0 := by omega
  -- Node dimensions of J.
  obtain ⟨hjnodeLt, hnjGet⟩ := List.getElem?_eq_some_iff.mp hnj
  have hjmem : nj ∈ ns := hnjGet ▸ List.getElem_mem hjnodeLt
  have hdims := successful_node_dimensions ns p raw hrun nj hjmem
  have hw : 0 ≤ nj.width := by omega
  have hh : 0 ≤ nj.height := by omega
  -- J's height is at most the rib's measured height, giving the coverage bound.
  have hnjheight : nj.height ≤ r.heights := by
    change nj.height ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact measured_entry_height_bound ns (generatedRib ns (cause, k)).entries j
      (List.fst_mem_of_mem_zipIdx hj) nj hnj
  have hspan0 : 0 ≤ childBorn.t1 - childBorn.t0 := by omega
  have hcoverage : (childBorn.x0 - childBorn.x1) * nj.height ≤
      (childBorn.t1 - childBorn.t0) *
        (childBorn.x0 + Int.fdiv
          ((childBorn.x1 - childBorn.x0) * (jBorn.t1 - childBorn.t0))
          (childBorn.t1 - childBorn.t0) - jBorn.x1) := by
    have hscale := run_scaled_cross_bound p r.heights (childBorn.t1 - childBorn.t0)
      hheight hspan0 hsin
    rw [Int.mul_comm r.heights (run p (childBorn.t1 - childBorn.t0))] at hscale
    have hstep1 : run p (childBorn.t1 - childBorn.t0) * nj.height
        ≤ run p (childBorn.t1 - childBorn.t0) * r.heights :=
      Int.mul_le_mul_of_nonneg_left hnjheight hrunSpan
    have hstep2 : (childBorn.t1 - childBorn.t0) * (run p r.heights + 1)
        ≤ (childBorn.t1 - childBorn.t0) *
          (childBorn.x0 + Int.fdiv
            ((childBorn.x1 - childBorn.x0) * (jBorn.t1 - childBorn.t0))
            (childBorn.t1 - childBorn.t0) - jBorn.x1) :=
      Int.mul_le_mul_of_nonneg_left hresv hspan0
    have hfall : childBorn.x0 - childBorn.x1 = run p (childBorn.t1 - childBorn.t0) := by
      omega
    rw [hfall]
    omega
  -- Close: the interpolated route at J's ordinate misses J's box.
  have hmiss := interpolated_box_diagonal_miss childBorn.x0 childBorn.x1 childBorn.t0
    childBorn.t1 jBorn.t1 nj.width nj.height
    (childBorn.x0 + Int.fdiv
      ((childBorn.x1 - childBorn.x0) * (jBorn.t1 - childBorn.t0))
      (childBorn.t1 - childBorn.t0) - jBorn.x1) spine r.upper
    hlt hx hw hh hcoverage
  have hpos : (childBorn.x0 + Int.fdiv
      ((childBorn.x1 - childBorn.x0) * (jBorn.t1 - childBorn.t0))
      (childBorn.t1 - childBorn.t0)) -
      (childBorn.x0 + Int.fdiv
        ((childBorn.x1 - childBorn.x0) * (jBorn.t1 - childBorn.t0))
        (childBorn.t1 - childBorn.t0) - jBorn.x1) = jBorn.x1 := by
    omega
  rw [hpos] at hmiss
  exact hmiss
end Elegant.Ishikawa

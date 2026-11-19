import Elegant.IshikawaClearanceHardB
import Elegant.IshikawaClearanceFacts

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-! ### Arithmetic core for the sibling case

The sibling attachment gap `x0 - jx0 ≥ run p H + 3` (both routes compared at
the earlier entry's ordinate `tj`) survives the floor rounding of the later
route with one unit of slack: `hard_b_route_reservation`. This is the missing
link that chains `place_generated_odd_sibling_attachment_gap` with
`interpolated_box_diagonal_miss` when the sibling case of HARD B is proved. -/

section IshikawaHardBFinalCases

theorem hard_b_route_reservation (p : Params) (x0 x1 t0 t1 tj jx0 jx1 H : Int)
    (hsin : 0 < p.sin)
    (ht : t0 < t1) (htj : t0 ≤ tj)
    (hroute : x1 = x0 - run p (t1 - t0))
    (hjroute : jx1 = jx0 - run p (tj - t0))
    (hgap : run p H + 3 ≤ x0 - jx0) :
    run p H + 1 ≤ x0 + Int.fdiv ((x1 - x0) * (tj - t0)) (t1 - t0) - jx1 := by
  have hspan0 : 0 ≤ t1 - t0 := by omega
  have hspan1 : 0 < t1 - t0 := by omega
  have hδ : 0 ≤ tj - t0 := by omega
  have hfall : x0 - x1 = run p (t1 - t0) := by omega
  have hfdiv := Int.mul_fdiv_add_fmod ((x1 - x0) * (tj - t0)) (t1 - t0)
  have hfmod := Int.fmod_nonneg_of_pos ((x1 - x0) * (tj - t0))
    (by omega : (0 : Int) < t1 - t0)
  have hfmodlt := Int.fmod_lt_of_pos ((x1 - x0) * (tj - t0))
    (by omega : (0 : Int) < t1 - t0)
  have hfallbound : (x0 - x1) * (tj - t0) ≤ (t1 - t0) * (run p (tj - t0) + 1) := by
    rw [hfall, Int.mul_comm (run p (t1 - t0)) (tj - t0)]
    exact run_scaled_cross_bound p (tj - t0) (t1 - t0) hδ hspan0 hsin
  have hFlower : (t1 - t0) * Int.fdiv ((x1 - x0) * (tj - t0)) (t1 - t0)
      ≥ -((x0 - x1) * (tj - t0)) - (t1 - t0) + 1 := by
    have eneg : (x1 - x0) * (tj - t0) = -((x0 - x1) * (tj - t0)) := by
      rw [show x1 - x0 = -(x0 - x1) from by omega, Int.neg_mul]
    omega
  have hVadd : (t1 - t0) * (run p H + 3)
      = (t1 - t0) * (run p H + 1) + (t1 - t0) + (t1 - t0) := by
    have e1 : (t1 - t0) * (run p H + 3)
        = (t1 - t0) * (run p H) + (t1 - t0) * 3 := Int.mul_add (t1 - t0) (run p H) 3
    have e2 : (t1 - t0) * (run p H + 1)
        = (t1 - t0) * (run p H) + (t1 - t0) * 1 := Int.mul_add (t1 - t0) (run p H) 1
    have e3 : (t1 - t0) * 3 = (t1 - t0) + (t1 - t0) + (t1 - t0) := by omega
    have e4 : (t1 - t0) * 1 = (t1 - t0) := by omega
    omega
  have hUexp : (t1 - t0) * (run p (tj - t0) + 1)
      = (t1 - t0) * run p (tj - t0) + (t1 - t0) := by
    rw [Int.mul_add, Int.mul_one]
  have hgapScaled : (t1 - t0) * (run p H + 3) ≤ (t1 - t0) * (x0 - jx0) :=
    Int.mul_le_mul_of_nonneg_left hgap hspan0
  have hGexp : (t1 - t0) * (x0 + Int.fdiv ((x1 - x0) * (tj - t0)) (t1 - t0) - jx1)
      = (t1 - t0) * (x0 - jx0) + (t1 - t0) * run p (tj - t0)
        + (t1 - t0) * Int.fdiv ((x1 - x0) * (tj - t0)) (t1 - t0) := by
    have hjsplit : (t1 - t0) * (x0 - jx1)
        = (t1 - t0) * (x0 - jx0) + (t1 - t0) * run p (tj - t0) := by
      rw [show x0 - jx1 = (x0 - jx0) + run p (tj - t0) from by rw [hjroute]; omega,
        Int.mul_add]
    have hadd1 : (t1 - t0) * (x0 + Int.fdiv ((x1 - x0) * (tj - t0)) (t1 - t0) - jx1)
        = (t1 - t0) * (x0 - jx1)
          + (t1 - t0) * Int.fdiv ((x1 - x0) * (tj - t0)) (t1 - t0) := by
      have hstep : (x0 + Int.fdiv ((x1 - x0) * (tj - t0)) (t1 - t0) - jx1)
          = (x0 - jx1) + Int.fdiv ((x1 - x0) * (tj - t0)) (t1 - t0) := by omega
      rw [hstep, Int.mul_add]
    rw [hadd1, hjsplit]
  apply Int.le_of_mul_le_mul_left _ hspan1
  rw [hGexp]
  omega

end IshikawaHardBFinalCases

/-! ### ENV invariant (named hypothesis)

The ENV invariant for the bones born while `place` executes, quantified over
the executed birth frames (pinned by `drawn := processedOddDraws`), not over
the unrestricted `IndexedBoneGenealogy`. Definitionally the
`IshikawaClearanceHardA.IshikawaEnvInvariant`; it is discharged by
`IshikawaClearanceHardA.ishikawa_env_invariant` from its `EnvStepOdd` and
`EnvStepEven` step-arithmetic premises once that sibling module finishes its
repair (it is not green yet, so this file carries the invariant as an
explicit named hypothesis of `ishikawa_hard_b`). -/

def IshikawaEnvFrames (ns : List Tree.Node) (p : Params) (r : Rib) : Prop :=
  ∃ frames : List Bone,
    frames.length = r.entries.length + 1 ∧
    frames[0]? = some ({ x1 := -run p r.length, t1 := r.length, count := (children ns r.cause).length } : Bone) ∧
    ∀ (idx : Nat) (b : Bone), 0 < idx → idx < r.entries.length + 1 →
      frames[idx]? = some b →
      b.x1 ≤ Int.fdiv ((-run p r.length) * b.t1) r.length - (run p r.heights + 1)

/-! ### HARD B case data and per-case results -/

/-- Shared per-instance data of every HARD B case: the odd route I (`child`)
and an earlier entry J (`j`) of the same placed generated rib, with their born
bones read off one common birth-frame list. The final conjunct is the route
span sanity `childBorn.t0 ≤ childBorn.t1` derived from the birth equations. -/
def HardBCaseConfig (ns : List Tree.Node) (_p : Params) (cause k : Nat)
    (_spine : Int) (r : Rib) (child j : Entry) (childIdx jIdx : Nat)
    (nj : Tree.Node) (frames : List Bone) (childBorn jBorn : Bone) : Prop :=
  (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx ∧
  (j, jIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx ∧
  child.depth % 2 ≠ 0 ∧
  jIdx < childIdx ∧
  ns[j.node]? = some nj ∧
  frames.length = r.entries.length + 1 ∧
  frames[childIdx + 1]? = some childBorn ∧
  frames[jIdx + 1]? = some jBorn ∧
  childBorn.t0 ≤ childBorn.t1

/-- Earlier-slot case, proved outright: J's box (top ordinate `jBorn.t1`,
height at most `r.heights`) ends at or before the route start ordinate
`childBorn.t0`, so `bone_route_misses_earlier_slot` discharges it. -/
theorem HardBEarlierSlot (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (_hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))
    ∀ (child j : Entry) (childIdx jIdx : Nat) (nj : Tree.Node)
      (frames : List Bone) (childBorn jBorn : Bone),
      HardBCaseConfig ns p cause k spine r child j childIdx jIdx nj frames
        childBorn jBorn →
      jBorn.t1 + r.heights ≤ childBorn.t0 →
      ¬ Polyline.hitsRect
        [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
         ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
        ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
          nj.width, nj.height⟩ := by
  intro r child j childIdx jIdx nj frames childBorn jBorn hconfig hslot
  obtain ⟨_hchild, hj, _hodd, _hjlt, hnj, _hlen, _hchildBorn, _hjBorn, hspan⟩ :=
    hconfig
  obtain ⟨hjnodeLt, hnjGet⟩ := List.getElem?_eq_some_iff.mp hnj
  have hjmem : nj ∈ ns := hnjGet ▸ List.getElem_mem hjnodeLt
  have hdims := successful_node_dimensions ns p raw hrun nj hjmem
  have hmeasured := measured_entry_height_bound ns (generatedRib ns (cause, k)).entries j
    (List.fst_mem_of_mem_zipIdx hj) nj hnj
  have hjheight : nj.height ≤ r.heights := by
    change nj.height ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact hmeasured
  have hmiss := bone_route_misses_earlier_slot spine childBorn.x0 childBorn.x1
    childBorn.t0 childBorn.t1 (jBorn.x1 - nj.width) jBorn.t1 nj.width nj.height
    r.heights r.upper 0 0
    (by have := hdims.2; omega) hjheight hslot (by omega)
  simpa only [Int.add_zero] using hmiss

/-- Later-slot case, proved outright: J's box begins at or after the route end
ordinate `childBorn.t1` plus one entry height, so
`bone_route_misses_later_slot` discharges it. -/
theorem HardBLaterSlot (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (_hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))
    ∀ (child j : Entry) (childIdx jIdx : Nat) (nj : Tree.Node)
      (frames : List Bone) (childBorn jBorn : Bone),
      HardBCaseConfig ns p cause k spine r child j childIdx jIdx nj frames
        childBorn jBorn →
      childBorn.t1 + r.heights ≤ jBorn.t1 →
      ¬ Polyline.hitsRect
        [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
         ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
        ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
          nj.width, nj.height⟩ := by
  intro r child j childIdx jIdx nj frames childBorn jBorn hconfig hlater
  obtain ⟨_hchild, hj, _hodd, _hjlt, hnj, _hlen, _hchildBorn, _hjBorn, hspan⟩ :=
    hconfig
  obtain ⟨hjnodeLt, hnjGet⟩ := List.getElem?_eq_some_iff.mp hnj
  have hjmem : nj ∈ ns := hnjGet ▸ List.getElem_mem hjnodeLt
  have hdims := successful_node_dimensions ns p raw hrun nj hjmem
  have hmeasured := measured_entry_height_bound ns (generatedRib ns (cause, k)).entries j
    (List.fst_mem_of_mem_zipIdx hj) nj hnj
  have hjheight : nj.height ≤ r.heights := by
    change nj.height ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact hmeasured
  have hmiss := bone_route_misses_later_slot spine childBorn.x0 childBorn.x1
    childBorn.t0 childBorn.t1 (jBorn.x1 - nj.width) jBorn.t1 nj.width nj.height
    r.heights r.upper 0 0
    (by have := hdims.2; omega) hjheight (by omega) hlater
  simpa only [Int.add_zero] using hmiss

/-- **Named hypothesis: sibling case.** J shares I's parent entry, hence the
same (odd) depth, and is processed earlier. `place_generated_odd_sibling_attachment_gap`
(first born `x0` plus `run p r.heights + 3` at most I's born `x0`) chains with
`hard_b_route_reservation` (the gap survives one floor rounding along I's own
fall to J's ordinate) and `interpolated_box_diagonal_miss`. Still open. -/
def HardBSibling (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (_hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed) : Prop :=
  let r := effectivePlacedInput ns (measuredSideLength p ribs)
    (generatedRib ns (cause, k))
  ∀ (child j : Entry) (childIdx jIdx : Nat) (nj : Tree.Node)
    (frames : List Bone) (childBorn jBorn : Bone),
    HardBCaseConfig ns p cause k spine r child j childIdx jIdx nj frames
      childBorn jBorn →
    j.parent = child.parent →
    ¬ Polyline.hitsRect
      [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
       ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
      ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
        nj.width, nj.height⟩

/-- **Named hypothesis: deeper earlier case.** J is neither I's parent entry
nor a sibling of I, and its box ordinate sits between the slot-gaps that the
two slot theorems need: J is a proper descendant of an earlier sibling of I
(its whole subtree is slotted between I's parent and I). Discharged by
iterating `place_generated_two_edge_descendant_envelope` along that sibling's
subtree (every two edges keep an odd descendant's `x1 + margin ≤` the
interpolated ancestor bone minus the remaining `run`), transporting the even
nodes through the attachment interpolation, and closing with
`interpolated_box_diagonal_miss` as in the sibling case; the
`IshikawaEnvFrames` bound supplies the master-diagonal side of the x-budget.
This is the genuinely open obligation of HARD B. -/
def HardBDeeperEarlier (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (_hplace : place ns p spine
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
    child.parent ≠ (jIdx : Int) →
    j.parent ≠ child.parent →
    ¬(jBorn.t1 + r.heights ≤ childBorn.t0) →
    ¬(childBorn.t1 + r.heights ≤ jBorn.t1) →
    ¬ Polyline.hitsRect
      [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
       ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
      ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
        nj.width, nj.height⟩

/-! ### Case split and final assembly -/

/-- The compiled case split of HARD B: for an odd route I and an earlier
entry J of the same placed rib, the miss follows from the five branches
(parent box, sibling, earlier slot, later slot, deeper earlier descendant).
Every branch premise has the form of the corresponding named result. -/
theorem hard_b_route_case_split (r : Rib) (child j : Entry) (_childIdx jIdx : Nat)
    (jBorn childBorn : Bone) (nj : Tree.Node) (spine : Int)
    (hparentCase : child.parent = (jIdx : Int) →
      ¬ Polyline.hitsRect
        [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
         ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
        ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
          nj.width, nj.height⟩)
    (hsiblingCase : j.parent = child.parent →
      ¬ Polyline.hitsRect
        [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
         ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
        ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
          nj.width, nj.height⟩)
    (hearlierSlotCase : jBorn.t1 + r.heights ≤ childBorn.t0 →
      ¬ Polyline.hitsRect
        [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
         ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
        ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
          nj.width, nj.height⟩)
    (hlaterSlotCase : childBorn.t1 + r.heights ≤ jBorn.t1 →
      ¬ Polyline.hitsRect
        [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
         ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
        ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
          nj.width, nj.height⟩)
    (hdeeperCase : child.parent ≠ (jIdx : Int) → j.parent ≠ child.parent →
      ¬(jBorn.t1 + r.heights ≤ childBorn.t0) →
      ¬(childBorn.t1 + r.heights ≤ jBorn.t1) →
      ¬ Polyline.hitsRect
        [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
         ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
        ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
          nj.width, nj.height⟩) :
    ¬ Polyline.hitsRect
      [⟨childBorn.x0, ordinate spine r.upper childBorn.t0⟩,
       ⟨childBorn.x1, ordinate spine r.upper childBorn.t1⟩]
      ⟨jBorn.x1 - nj.width, ordinate spine r.upper jBorn.t1 - Int.fdiv nj.height 2,
        nj.width, nj.height⟩ := by
  by_cases hparcase : child.parent = (jIdx : Int)
  · exact hparentCase hparcase
  by_cases hsibcase : j.parent = child.parent
  · exact hsiblingCase hsibcase
  by_cases hslotcase : jBorn.t1 + r.heights ≤ childBorn.t0
  · exact hearlierSlotCase hslotcase
  by_cases hlatercase : childBorn.t1 + r.heights ≤ jBorn.t1
  · exact hlaterSlotCase hlatercase
  · exact hdeeperCase hparcase hsibcase hslotcase hlatercase

/-- HARD B final assembly: the odd-depth entry route I of a generated rib
misses the box of every earlier entry J of the same placed rib. The parent-box
case (`child.parent = (jIdx : Int)`) is the landed
`place_generated_odd_entry_route_misses_parent_box`; the slot cases are
`HardBEarlierSlot` and `HardBLaterSlot` (proved in this file); the sibling and
deeper-earlier cases remain the named hypotheses `HardBSibling` and
`HardBDeeperEarlier`, and the ENV side condition is `IshikawaEnvFrames`
(discharged by the HardA module once repaired). -/
theorem ishikawa_hard_b
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
    (hsib : HardBSibling ns p raw hrun ribs hg cause k hsource hcause
      spine placed hplace)
    (hdeep : HardBDeeperEarlier ns p raw hrun ribs hg cause k hsource hcause
      spine placed hplace henv)
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
  obtain ⟨_jPos, _parJ, jBorn, _hjPos, _hjparLookup, hjBorn, _⟩ :=
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
  let parentEntry := r.entries[(child.parent).toNat]'hparentBound
  have hparentLookup : r.entries[(child.parent).toNat]? = some parentEntry :=
    List.getElem?_eq_getElem hparentBound
  have hparentMem : (parentEntry, (child.parent).toNat) ∈ r.entries.zipIdx :=
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
  refine ⟨frames, childBorn, jBorn, hlen, hchildBorn, hjBorn, ?_, hpieces⟩
  refine hard_b_route_case_split r child j childIdx jIdx jBorn childBorn nj spine
    ?_ ?_ ?_ ?_ ?_
  · intro hc
    exact absurd hc hparcase
  · intro hs
    exact hsib child j childIdx jIdx nj frames childBorn jBorn cfg hs
  · intro he
    exact HardBEarlierSlot ns p raw hrun ribs hg cause k hsource hcause spine
      placed hplace child j childIdx jIdx nj frames childBorn jBorn cfg he
  · intro hl
    exact HardBLaterSlot ns p raw hrun ribs hg cause k hsource hcause spine
      placed hplace child j childIdx jIdx nj frames childBorn jBorn cfg hl
  · intro hc hs he hl
    exact hdeep child j childIdx jIdx nj frames childBorn jBorn cfg hc hs he hl

end Elegant.Ishikawa

import Elegant.IshikawaDeeperEarlierProof
import Elegant.IshikawaClearanceHard
import Elegant.IshikawaSeparationFacts
import Elegant.IshikawaLayoutProvenanceFacts
import ElegantGeometry.Route

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-- Residual R-gap: route fall equation plus the interpolated reservation.

For the executed odd route `child` and a descendant `j` of its earlier sibling
`S`, the route falls with slope `run` and its interpolated x at `j`'s ordinate
stays at least `run p r.heights + 1` right of `j`'s left end. Pure integer
arithmetic about executed bones (no `Polyline`, no sibling miss); the main
theorem closes the rectangle miss from it with the standard diagonal lemma.
Probed with `proofs/wip/Probe/IshikawaDeeperGapProbe.lean`, which replays the
executed `place` layouts and checks both conjuncts as booleans on every
sibling-descendant pair: the three witness trees and all link-valid trees to
four and five nodes are vacuous (no such shape), six nodes contribute one
premise and seven nodes twelve premises, all satisfying fall and gap
(premises=13, fallViols=0, gapViols=0). -/
def HardBDeeperRouteGap (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
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
    (frames : List Bone) (childBorn jBorn sBorn : Bone) (sIdx : Nat) (S : Entry)
    (nS : Tree.Node),
    HardBCaseConfig ns p cause k spine r child j childIdx jIdx nj frames
      childBorn jBorn →
    HardBRealFrames ns p spine r placed hplace frames →
    (generatedRib ns (cause, k)).entries[sIdx]? = some S → sIdx ≠ jIdx →
    S.parent = ((child.parent).toNat : Int) →
    IndexedAncestor (generatedRib ns (cause, k)).entries sIdx jIdx →
    frames[sIdx + 1]? = some sBorn → ns[S.node]? = some nS →
    (childBorn.x1 = childBorn.x0 - run p (childBorn.t1 - childBorn.t0) ∧
      run p r.heights + 1 ≤
        (childBorn.x0 + Int.fdiv ((childBorn.x1 - childBorn.x0) *
          (jBorn.t1 - childBorn.t0)) (childBorn.t1 - childBorn.t0) - jBorn.x1))

theorem hardBDeeperEnvTransport (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed)
    (_env : IshikawaEnvFrames ns p
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))))
    (hgapAll : HardBDeeperRouteGap ns p raw _hrun ribs _hg cause k _hsource _hcause
      spine placed hplace _env) :
    HardBDeeperEnvTransport ns p raw _hrun ribs _hg cause k _hsource _hcause
      spine placed hplace _env := by
  intro child j childIdx jIdx nj frames childBorn jBorn sBorn sIdx S nS
    hconfig hreal hS hsne hSP hchain hsBorn hnS _hsib
  have hboth := hgapAll child j childIdx jIdx nj frames childBorn jBorn sBorn
    sIdx S nS hconfig hreal hS hsne hSP hchain hsBorn hnS
  obtain ⟨hfall, hgap⟩ := hboth
  obtain ⟨_hchild, hj, _hodd, _hjlt, hnj, _hlen, _hchildBorn, _hjBorn, hspan⟩ :=
    hconfig
  have hne : ns ≠ [] := by
    intro heq
    simp [heq, children] at _hcause
  have hparameters := successful_slope_parameters ns p raw hne _hrun
  have hsin : 0 < p.sin := by
    have h1 := hparameters.2
    omega
  have hcos : 0 ≤ p.cos := hparameters.1
  have hheight : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))).heights := by
    change 0 ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact entry_height_fold_initial ns _ 0
  obtain ⟨hjnodeLt, hnjGet⟩ := List.getElem?_eq_some_iff.mp hnj
  have hjmem : nj ∈ ns := hnjGet ▸ List.getElem_mem hjnodeLt
  have hdims := successful_node_dimensions ns p raw _hrun nj hjmem
  obtain ⟨hw1, hh1⟩ := hdims
  have hw : 0 ≤ nj.width := by omega
  have hh : 0 ≤ nj.height := by omega
  have hnjheight : nj.height ≤ (effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))).heights := by
    change nj.height ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact measured_entry_height_bound ns (generatedRib ns (cause, k)).entries j
      (List.fst_mem_of_mem_zipIdx hj) nj hnj
  have hrunH_nonneg : 0 ≤ run p (effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))).heights :=
    Int.fdiv_nonneg (Int.mul_nonneg hheight hcos) (Int.le_of_lt hparameters.2)
  have hspan0 : 0 ≤ childBorn.t1 - childBorn.t0 := by omega
  have hrunSpan : 0 ≤ run p (childBorn.t1 - childBorn.t0) :=
    Int.fdiv_nonneg (Int.mul_nonneg hspan0 hcos) (Int.le_of_lt hparameters.2)
  have hx : childBorn.x1 ≤ childBorn.x0 := by omega
  by_cases hlt : childBorn.t0 < childBorn.t1
  · have hscale := run_scaled_cross_bound p (effectivePlacedInput ns
        (measuredSideLength p ribs) (generatedRib ns (cause, k))).heights
        (childBorn.t1 - childBorn.t0) hheight hspan0 hsin
    rw [Int.mul_comm (effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))).heights
      (run p (childBorn.t1 - childBorn.t0))] at hscale
    have hstep1 : run p (childBorn.t1 - childBorn.t0) * nj.height ≤
        run p (childBorn.t1 - childBorn.t0) * (effectivePlacedInput ns
          (measuredSideLength p ribs) (generatedRib ns (cause, k))).heights :=
      Int.mul_le_mul_of_nonneg_left hnjheight hrunSpan
    have hfallEq : childBorn.x0 - childBorn.x1 =
        run p (childBorn.t1 - childBorn.t0) := by omega
    have hstep2 : (childBorn.t1 - childBorn.t0) * (run p (effectivePlacedInput ns
          (measuredSideLength p ribs) (generatedRib ns (cause, k))).heights + 1) ≤
        (childBorn.t1 - childBorn.t0) *
          (childBorn.x0 + Int.fdiv ((childBorn.x1 - childBorn.x0) *
            (jBorn.t1 - childBorn.t0)) (childBorn.t1 - childBorn.t0) - jBorn.x1) :=
      Int.mul_le_mul_of_nonneg_left hgap hspan0
    have hcoverage : (childBorn.x0 - childBorn.x1) * nj.height ≤
        (childBorn.t1 - childBorn.t0) *
          (childBorn.x0 + Int.fdiv ((childBorn.x1 - childBorn.x0) *
            (jBorn.t1 - childBorn.t0)) (childBorn.t1 - childBorn.t0) - jBorn.x1) := by
      rw [hfallEq]
      omega
    have hmiss := interpolated_box_diagonal_miss childBorn.x0 childBorn.x1
      childBorn.t0 childBorn.t1 jBorn.t1 nj.width nj.height
      (childBorn.x0 + Int.fdiv ((childBorn.x1 - childBorn.x0) *
        (jBorn.t1 - childBorn.t0)) (childBorn.t1 - childBorn.t0) - jBorn.x1)
      spine (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))).upper hlt hx hw hh hcoverage
    have hpos : (childBorn.x0 + Int.fdiv ((childBorn.x1 - childBorn.x0) *
        (jBorn.t1 - childBorn.t0)) (childBorn.t1 - childBorn.t0)) -
        (childBorn.x0 + Int.fdiv ((childBorn.x1 - childBorn.x0) *
          (jBorn.t1 - childBorn.t0)) (childBorn.t1 - childBorn.t0) - jBorn.x1) =
        jBorn.x1 := by
      omega
    rw [hpos] at hmiss
    exact hmiss
  · have hzero : childBorn.t1 - childBorn.t0 = 0 := by omega
    have hrun0 : run p (childBorn.t1 - childBorn.t0) = 0 := by
      rw [hzero]
      simp [run]
    have hx10 : childBorn.x1 = childBorn.x0 := by omega
    have hgap0 : run p (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))).heights + 1 ≤
        childBorn.x0 - jBorn.x1 := by
      have hq0 : Int.fdiv ((childBorn.x1 - childBorn.x0) *
          (jBorn.t1 - childBorn.t0)) (childBorn.t1 - childBorn.t0) = 0 := by
        rw [hzero]
        simp
      omega
    apply Polyline.not_hits_of_allMiss
    refine ⟨Or.inr (Or.inl ?_), trivial⟩
    show min childBorn.x0 childBorn.x1 ≥ jBorn.x1 - nj.width + nj.width
    rw [hx10]
    omega

end Elegant.Ishikawa

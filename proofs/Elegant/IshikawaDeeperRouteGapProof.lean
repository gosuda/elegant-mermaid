import Elegant.IshikawaDeeperEnvTransportProof
import Elegant.Ishikawa

set_option autoImplicit false

namespace Elegant.Ishikawa

open Elegant

/-- Residual G-only: the interpolated reservation conjunct of `HardBDeeperRouteGap`.

Same premises, concluding only the gap
`run p r.heights + 1 ≤ interp(child,j) - jBorn.x1`. The fall conjunct is proved
unconditionally below (`hardBDeeperFall`); this single conjunct is the remaining
open obligation. Probed with `proofs/wip/Probe/IshikawaDeeperGapProbe.lean`: on
all link-valid trees to seven nodes, all 13 sibling-descendant premises satisfy
the gap (gapViols=0); witness trees and trees to five nodes are vacuous. -/
def HardBDeeperGapOnly (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
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
    run p r.heights + 1 ≤
      (childBorn.x0 + Int.fdiv ((childBorn.x1 - childBorn.x0) *
        (jBorn.t1 - childBorn.t0)) (childBorn.t1 - childBorn.t0) - jBorn.x1)

theorem hardBDeeperFall (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (_hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (_hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))) = .ok placed)
    (_env : IshikawaEnvFrames ns p
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k)))) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))
    ∀ (child j : Entry) (childIdx jIdx : Nat) (nj : Tree.Node)
      (frames : List Bone) (childBorn jBorn : Bone),
      HardBCaseConfig ns p cause k spine r child j childIdx jIdx nj frames
        childBorn jBorn →
      HardBRealFrames ns p spine r placed hplace frames →
      childBorn.x1 = childBorn.x0 - run p (childBorn.t1 - childBorn.t0) := by
  intro r child j childIdx jIdx nj frames childBorn jBorn hconfig hreal
  obtain ⟨hchild, _hj, hodd, _hjlt, _hnj, _hlen, hchildBornLookup, _hjBorn,
    _hspan⟩ := hconfig
  obtain ⟨frames0, hshape0, hsub⟩ := hreal
  obtain ⟨_hlen0, _hroot0, hrecords0⟩ := hshape0
  obtain ⟨childDone, childRest, hchildPrefix, _⟩ :=
    List.eq_append_cons_of_mem hchild
  change (generatedRib ns (cause, k)).entries.zipIdx =
      childDone ++ (child, childIdx) :: childRest at hchildPrefix
  obtain ⟨childPos, cPar, childBorn0, _hchildPos, _hchildParLookup, hchildBorn0,
    hchildEq⟩ :=
    hrecords0 childDone child childIdx childRest hchildPrefix
  have hsubBorn : frames0[childIdx + 1]? = some childBorn :=
    hsub _ _ hchildBornLookup
  have heq : childBorn0 = childBorn :=
    Option.some.inj (hchildBorn0.symm.trans hsubBorn)
  have hCB : childBorn = depthBone p
      { cPar with drawn := processedOddDraws childDone (child.parent + 1).toNat }
      child.depth
      (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns child.node).length (run p r.heights + 3) :=
    heq.symm.trans hchildEq
  rw [hCB]
  have hend := depthBone_odd_endpoints p
    { cPar with drawn := processedOddDraws childDone (child.parent + 1).toNat }
    child.depth
    (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
    (children ns child.node).length (run p r.heights + 3) hodd
  obtain ⟨ht0, ht1, _hx0, hx1⟩ := hend
  have harg : (depthBone p
      { cPar with drawn := processedOddDraws childDone (child.parent + 1).toNat }
      child.depth
      (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns child.node).length (run p r.heights + 3)).t1 -
      (depthBone p
      { cPar with drawn := processedOddDraws childDone (child.parent + 1).toNat }
      child.depth
      (Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns child.node).length (run p r.heights + 3)).t0 =
      Int.fdiv (r.length * (childPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) -
        { cPar with drawn :=
          processedOddDraws childDone (child.parent + 1).toNat }.t0 := by
    omega
  rw [harg]
  exact hx1

theorem hardBDeeperRouteGap (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
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
    (hgapOnly : HardBDeeperGapOnly ns p raw _hrun ribs _hg cause k _hsource
      _hcause spine placed hplace _env) :
    HardBDeeperRouteGap ns p raw _hrun ribs _hg cause k _hsource _hcause
      spine placed hplace _env := by
  intro child j childIdx jIdx nj frames childBorn jBorn sBorn sIdx S nS
    hconfig hreal hS hsne hSP hchain hsBorn hnS
  have hfall := hardBDeeperFall ns p raw _hrun ribs _hg cause k _hsource _hcause
    spine placed hplace _env child j childIdx jIdx nj frames childBorn jBorn
    hconfig hreal
  have hgap := hgapOnly child j childIdx jIdx nj frames childBorn jBorn sBorn
    sIdx S nS hconfig hreal hS hsne hSP hchain hsBorn hnS
  exact ⟨hfall, hgap⟩

theorem hardBDeeperEnvTransport' (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout)
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
    (hgapOnly : HardBDeeperGapOnly ns p raw _hrun ribs _hg cause k _hsource
      _hcause spine placed hplace _env) :
    HardBDeeperEnvTransport ns p raw _hrun ribs _hg cause k _hsource _hcause
      spine placed hplace _env :=
  hardBDeeperEnvTransport ns p raw _hrun ribs _hg cause k _hsource _hcause
    spine placed hplace _env
    (hardBDeeperRouteGap ns p raw _hrun ribs _hg cause k _hsource _hcause
      spine placed hplace _env hgapOnly)

end Elegant.Ishikawa

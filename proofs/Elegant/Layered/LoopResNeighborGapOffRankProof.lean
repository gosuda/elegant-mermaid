import Elegant.Layered.LoopResNeighborGapProof
import Elegant.Layered.LoopExtentReservationProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Loop-footprint neighbor gap for grouped off-rank plain owners

Target: `LoopResNeighborGapOffRank` (`LoopResNeighborGapProof.lean`), the
plain-owner off-rank case of `R3ExtentFitGap`: a plain looping owner `t`
(`nt.border = 0`) and a foreign group hull `pos` (`np.border = -2`,
disjoint paths) whose proper members do not span the owner's rank, with the
frame-left premise `frame(t).right ≤ hull(pos).left`, conclude
`footprint(t).right ≤ hull(pos).left`.

Truth: the statement as written (arbitrary binders, and its executed-run
form without further premises) is FALSE. Witness
(`wip/Probe/LoopResNeighborGapOffRankWitness.lean`, input `wit3r`):
flowchart boxes `[a, m0, G2, b]` with `a`, `m0` top-level, `b` in `G2`,
routes `a → a`, `a → m0`, `m0 → b`, loop label 12 wide chars on `a → a`;
`framedParents = true`, `WellFormed = true`. In every candidate run the
component candidate has `t = 0` (`border = 0`, `decl = 0`, `path = []`,
self-loop present) and `pos = 2` (`border = -2`, `decl = 2`, `path = [2]`),
`¬ LoopResNeighborSpanning run 0 2`, frame-right `1026 ≤ 3003` (premise
holds) but footprint-right `13530 ≤ 3003` (conclusion fails). The owner is
top-level (`path = []`), so it has no ancestor hull to absorb the loop
extent; the foreign hull sits just right of the frame but inside the loop
lane. No `Fleft ∧ ¬R3` instance was found for grouped owners across the
flat, wide-label, nested, tower, wide-parent, wide-foreign, chain, and
cell-profile probes.

Replacement (proved below): the same statement with the grouped-owner
premise `nt.clusterPath ≠ []`, modulo the single frame-chain residual.
The residual is strictly narrower than the target (frames only, no
footprints), quantified over executed runs only, and true on every grouped
off-rank `Fleft` probe instance (flat/tower/wide/chain/cell, all with
`R1 ∧ CHAIN` holding, including the tight cell case). -/

/-- Residual: parent-hull chain for grouped off-rank plain owners. For an
executed run, a grouped plain looping owner and a foreign group hull with
the frame-left premise and no spanning witnesses, some candidate parent
node (immediate parent by `getLast?`, hence a true ancestor by `∈`) has
its frame right edge left of the foreign hull's left edge. Single frame
fact; the footprint is not mentioned. -/
def LoopResOffRankParentChain : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (_hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t : Nat} {nt : Node}
    (_hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (_htB : nt.border = 0)
    (_hgrouped : nt.clusterPath ≠ [])
    (_het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t)
    {pos : Nat} {np : Node}
    (_hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (_hgrpB : np.border = -2)
    (_hne : pos ≠ t) (_hne2 : nt.decl ≠ np.decl)
    (_hni1 : np.decl ∉ nt.clusterPath) (_hni2 : nt.decl ∉ np.clusterPath)
    (_hoff : ¬ LoopResNeighborSpanning run t np.decl)
    (_hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x),
    ∃ (u : Nat), ∃ (nu : Node),
      (componentCandidate execution.graph comp candidate).nodes[u]? = some nu ∧
      nu.border = -2 ∧
      nu.decl ∈ nt.clusterPath ∧
      nt.clusterPath.getLast? = some nu.decl ∧
      (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run u).x +
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run u).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x

/-- Grouped plain owner, off-rank foreign hull: `R3ExtentFitGap` holds
modulo `LoopResOffRankParentChain`. The residual supplies a parent node
`u`; the shared core (`loopRes_plainExtentGap_holds`) bounds the loop
extent by the parent-hull gap, and the residual chains the parent hull
into the foreign hull. The ungrouped (`path = []`) form is false by the
witness above, so the grouped premise is the narrowest true replacement. -/
theorem loopResNeighborGapOffRank_holds {inp : Input} {o : Options}
    {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hchain : LoopResOffRankParentChain)
    {t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (htB : nt.border = 0)
    (hgrouped : nt.clusterPath ≠ [])
    (_het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t)
    {pos : Nat} {np : Node}
    (hnp : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hgrpB : np.border = -2)
    (_hne : pos ≠ t) (_hne2 : nt.decl ≠ np.decl)
    (_hni1 : np.decl ∉ nt.clusterPath) (_hni2 : nt.decl ∉ np.clusterPath)
    (hoff : ¬ LoopResNeighborSpanning run t np.decl)
    (hFL : (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x) :
    (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).x +
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured t).w ≤
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run pos).x := by
  obtain ⟨u, nu, hnu, hbU, hmemU, _hlastU, hchainU⟩ :=
    hchain execution hcomp hrun hnt htB hgrouped _het hnp hgrpB _hne _hne2
      _hni1 _hni2 hoff hFL
  have hneU : u ≠ t := by
    intro hsub
    subst hsub
    have heq : nu = nt := Option.some.inj (hnu.symm.trans hnt)
    rw [heq, htB] at hbU
    omega
  have hR1 := loopRes_plainExtentGap_holds execution hwf hframed hcomp hrun
    hnt htB hnu hbU hneU hmemU
  have hfx : (loopFootprint (componentCandidate execution.graph comp candidate) run
      execution.measured t).x =
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).x +
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run t).w := rfl
  omega

end PipelineImpl
end Layered
end Elegant

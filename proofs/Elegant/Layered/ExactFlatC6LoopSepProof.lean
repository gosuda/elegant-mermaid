import Elegant.Layered.ExactFlatC6WProof
import Elegant.Layered.FlatC6LoopProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Non-self residual for `X6_LoopFootprintSeparationW`: the loop footprint
of `v` misses the frame of a zero-border `b` when `v ≠ b`, over an executed
exact run with local admission. Strictly narrower than the target (adds
`v ≠ b`); the self case closes by `loopFootprint_self_disjoint`. True on all
probes in `wip/Probe/X6LoopSepTProbe.lean` (flat two groups, nested groups,
self-loop, zero-size and wide fixed boxes named in `exactIds`, ill-formed). -/
def X6_LoopSep_NonSelf (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
    comp ∈ components execution.graph →
    ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    v ≠ b →
    LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
      execution.measured v b

private theorem xlsep_self_disjoint {cg : Graph} {run : Run}
  {labels : List MeasuredLabel} {v : Nat} :
  Disjoint (loopFootprint cg run labels v) (frameRect default cg run v) :=
  loopFootprint_self_disjoint cg run labels v
/-- Exact flat C6 loop-footprint separation in W form, modulo the non-self
residual: the self case is positional, the rest is `X6_LoopSep_NonSelf`. -/
theorem X6_loopFootprintSeparationW_holds (exactIds : List String)
  (hNonSelf : X6_LoopSep_NonSelf exactIds) :
  X6_LoopFootprintSeparationW exactIds := by
  intro inp o res execution hwf hfp comp candidate run v b hcomp hbord hrun
  by_cases heq : v = b
  · subst heq
    exact xlsep_self_disjoint
  · exact hNonSelf execution hwf hfp comp candidate run v b hcomp hbord hrun heq
end PipelineImpl
end Layered
end Elegant

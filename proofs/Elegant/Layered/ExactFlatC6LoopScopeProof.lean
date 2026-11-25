import Elegant.Layered.ExactFlatC6LoopSepNonSelfProof
import Elegant.Layered.ExactFlatC6LoopSepProof
import Elegant.Layered.ExactLoopEnvelopeReserveProof
import Elegant.Layered.ExactLoopEnvelopeRightProof
import Elegant.Layered.ExactLoopEnvelopeLeftNonPlainProof
import Elegant.Layered.ExactLoopEnvelopeSidesProof
import Elegant.Layered.ExactLoopEnvelopeGroupMissProof
import Elegant.Layered.ExactSeamClosureGlue

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact flat C6 non-self loop separation: leaf closure over the cutover.

Cutover: the unbounded `X6_LoopSep_NonSelf_Scope` was FALSE (out-of-bounds
`b` satisfies the border premise via `getD` default; witness
`proofs/wip/Probe/X6LoopScopeTProbe.lean`: `b = run.proper.nodes.length`
with premise true and `b < length` false on flatExact, nestedExact,
loopZero, emptyGrp, ill) and is deleted. It is replaced by
`X6_LoopSep_NonSelf_ScopeB` (bounded-exclusive, proved in
`ExactFlatC6LoopSepNonSelfProof.lean`) and the open residual
`X6_LoopSep_NonSelf_ScopeRest` (separation-shaped: non-exclusive or
component-beyond in-proper indices conclude the separation directly, since
the scope facts are false for component-beyond markers whose declaration
is the group on the owner's path). The separation conclusion
`X6_LoopSep_NonSelf` is TRUE as stated:
out-of-proper `b` is disjoint by the landed
`x6lsns_disjoint_of_proper_oob` helper, and the full-range probe check
(`sepfull`, no `FAIL` on flatExact/nestedExact/loopZero/emptyGrp/ill,
including component-beyond marker indices and `b = proper.length`) covers
the rest; no conclusion narrowing and no `ExactFlatC6WProof.lean` change.

Six envelope leaves of `X6_loopSep_nonSelf_holds`: `XLEM_PlainReserve` and
`XLEM_LeftNonPlain` CLOSED; `XLEM_PlainRightMiss` reduced to the open
`XLEM_PlainRightNonPlain`; `XLEM_GroupOwnerOtherRank` reduced to the open
`XLEM_GroupOverlapMiss`; `XLEG_GroupMarkerOrderX` OPEN;
`X_loopEnvOtherOwner` reduced to those three opens via
`glue_loopEnvOtherOwner`. -/

/-- Non-self loop separation from the four open leaves: the two closed
envelope leaves are discharged, the owner is reduced, and the scope side is
closed by `x6_loopSep_nonSelf_scopeB_holds`, leaving `PlainRightNonPlain`,
`GroupOverlapMiss`, `GroupMarkerOrderX`, and the open `ScopeRest`. -/
theorem x6_loopSep_nonSelf_closed_from_leaves (exactIds : List String)
    (hRightNP : XLEM_PlainRightNonPlain exactIds)
    (hGrpOverlap : XLEM_GroupOverlapMiss exactIds)
    (hGrpOrd : XLEG_GroupMarkerOrderX exactIds)
    (hScopeRest : X6_LoopSep_NonSelf_ScopeRest exactIds) :
    X6_LoopSep_NonSelf exactIds :=
  X6_loopSep_nonSelf_holds exactIds
    (XLEM_plainReserve_holds exactIds)
    (XLEM_groupOtherRank_holds exactIds hGrpOverlap)
    (XLEM_plainRightMiss_holds exactIds hRightNP)
    (XLEM_leftNonPlain_holds exactIds)
    hGrpOrd
    (glue_loopEnvOtherOwner exactIds hGrpOverlap hRightNP hGrpOrd)
    (x6_loopSep_nonSelf_scopeB_holds exactIds)
    hScopeRest

end PipelineImpl
end Layered
end Elegant

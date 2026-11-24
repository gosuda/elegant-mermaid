import Elegant.Layered.ExactBorderChainXAlignedProof
import Elegant.Layered.ExactBorderDivergeProof
import Elegant.Layered.ExactForeignBorderSpansProof
import Elegant.Layered.ExactFramedDivergenceProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-!
# Exact border-chain alignment, B form (caption chain).

`X_foreignBorderChainXAligned_framed` derives alignment from the measured
graph, exact graph, and executed component run on a well-formed framed input.
The per-run divergence and side-chain shape theorems supply the two facts
needed by the local alignment proof.

`XB_ForeignBorderChainXAligned` and `X_ForeignBorderChainXAligned` are
definitionally equal, including their input premises. The B proof therefore
needs neither the ordered-intervals nor the foreign-span facts that consume it.
The generic transfer from `X_ForeignBorderDivergeStable` remains available.

Probe evidence (`wip/Probe/ExactBorderChainBProbe.lean`): the B conclusion
evaluated pairwise on executed exact runs, all candidates 0-2:
sibling groups with long cross-group edges (10 markers, 20 checks, 0
violations), nested groups (10 markers/20 checks plus 4 markers/2 checks, 0
violations), sibling groups with an `a1 -> a1` self-loop (10 markers, 20
checks, 0 violations), zero-size fixed group (10 markers, 20 checks, 0
violations); the ill-formed input (exact id without fixed sizes) is rejected
by `exactGraph` with `.domain` before any run. A lone group with only a
self-loop emits no border markers, so the self-loop case rides on the
sibling input.
-/

/-- B-form alignment from a global exact sweep-stability premise. -/
theorem xb_foreignBorderChainXAligned_of_stable (exactIds : List String)
    (hstabX : X_ForeignBorderDivergeStable exactIds) :
    XB_ForeignBorderChainXAligned exactIds :=
  X_foreignBorderChainXAligned_of_stable exactIds hstabX
    (X_foreignSideChainShapeClosed_holds exactIds)

/-- Same-side border markers of one declaration share a closed `x`-interval
on every framed exact run satisfying the input premises. -/
theorem X_foreignBorderChainXAligned_framed (exactIds : List String) :
    X_ForeignBorderChainXAligned exactIds := by
  intro P inp o lines measured graph0 graph hgraph0 hgraphX hlines hwf hframed
    comp hcomp candidate run labels orderOptions hrun
  exact @X_foreignBorderChainXAligned_of_local_stable P exactIds inp o lines
    measured graph0 graph hgraph0 hgraphX comp hcomp candidate run labels orderOptions hrun
    (X_foreignBorderDivergeStableFramed_holds hgraph0 hgraphX hlines hwf hframed hcomp hrun)
    (X_foreignSideChainShapeClosed_holds exactIds hgraph0 hgraphX hcomp hrun)

theorem XB_foreignBorderChainXAligned_framed (exactIds : List String) :
    XB_ForeignBorderChainXAligned exactIds :=
  X_foreignBorderChainXAligned_framed exactIds

end PipelineImpl
end Layered
end Elegant

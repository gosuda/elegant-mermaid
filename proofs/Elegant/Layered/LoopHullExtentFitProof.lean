import Elegant.Layered.LoopResGroupHullRightMemberProof
import Elegant.Layered.LoopResGroupHullRightAncestorRanksProof
import Elegant.Layered.ForeignBorderEdgesNoncrossingProof
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ForeignBorderChainXAlignedClosed
import Elegant.Layered.ForeignBorderAnchorsProof
import Elegant.Layered.LoopResNeighborGapDisjCasesProof
import Elegant.Layered.SeamClosureGlue

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Loop-hull extent fit: both cover fields from landed closure results

Proved here (plain pipeline, executed runs only):
* `loopHullRightCover_closed_plain`: the `ExactSeams.loopHullRightCover`
  field shape (every ancestor group hull right edge covers the loop
  footprint) from `loopHullRightCover_closed''` fed by
  `loopResGroupHullRightAncestorRanks_holds` and the chain alignment
  `foreignBorderChainXAligned'` of the shared ordering-stage seam.
* `loopHullRightNeighborCover_closed_plain`: the
  `ExactSeams.loopHullRightNeighborCover` field shape (foreign-hull right
  cover under frame-left plus footprint/hull `y` overlap) from
  `neighborCover_of_disjoint_closed` fed by
  `loopResNeighborGapGroupTopDisj_holds` (over `foreignBorderLayerOrder'`
  and the same chain alignment) and `neighborGapBottomOwnerDisj_holds`.

Residual accounting for the two extent-fit gaps named in
`LoopHullCoverProof.lean`:
* The ancestor right-gap goal in full generality (all owner borders) is NOT
  assumed and NOT proved here. Its plain-owner instance is already proved
  (`loopRes_plainExtentGap_holds`, used inside `loopHullRightCover_holds`);
  the group-owner remainder travels through `LoopResGroupHullRight` and the
  ordered-marker witness chain, whose last open link (ancestor rank nesting)
  is now proved. Hence the ancestor-cover field needs no such premise.
* The unconditional foreign-hull `x`-gap is refuted by an executed top-level
  witness (frame left of an off-rank foreign hull while the loop lane runs
  past its left edge; see `LoopResNeighborDisjointProof.lean`). It is NOT
  assumed and NOT proved here. The field needs only the disjoint replacement
  (`LoopResNeighborGapDisj`, closed above) because the cover carries the
  `y`-overlap premise that selects the `x`-gap disjunct.

Open: only the shared ordering-stage seam `ForeignBorderDivergeStable`
(already an `ExactSeams` field; mapped to `ForeignBorderChainXAligned`
inside both proofs). No new residual definition is introduced.

Evidence: `LoopHullCoverTProbe` (nine executed inputs, zero violations;
`R1cover` true on every ancestor pair; `R3c` true wherever frame-left and
`y` overlap hold) and the `HullCoverTExtentFitProbe` five-input extent-fit
sweep added alongside this module.
-/

/-- Ancestor-hull right cover with the field's binders, closed from landed
results: ancestor rank nesting holds on every executed run, so
`loopHullRightCover_closed''` discharges the group remainder while the
plain remainder rides the proved plain extent gap inside
`loopHullRightCover_holds`. The only premise beyond the field's own is the
shared ordering-stage seam. -/
theorem loopHullRightCover_closed_plain
    (inp : Input) (o : Options) (res : FamilyResult)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hstab : ForeignBorderDivergeStable)
    (execution : SceneExecution inp o res)
    (comp : List Nat) (hcomp : comp ∈ components execution.graph)
    (candidate : Nat) (run : Run) (orderOptions : OrderOptions)
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    LoopHullRightCover execution.params
      (componentCandidate execution.graph comp candidate) run
      execution.measured := by
  have hx : ForeignBorderChainXAligned := foreignBorderChainXAligned' hstab
  have hres : LoopResGroupHullRightAncestorRanks execution hcomp hrun :=
    loopResGroupHullRightAncestorRanks_holds hwf hfp execution hcomp hrun
  exact loopHullRightCover_closed'' hwf hfp hx execution hcomp hrun hres

/-- Foreign-hull right-neighbor cover with the field's binders, closed from
landed results: the disjoint gap is closed (group-top via the closed rank
spans plus the two order facts, bottom-owner vacuously, plain via the
chain-free replay), and the cover's `y`-overlap premise selects the `x`-gap
disjunct. The only premise beyond the field's own is the shared
ordering-stage seam. -/
theorem loopHullRightNeighborCover_closed_plain
    (inp : Input) (o : Options) (res : FamilyResult)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hstab : ForeignBorderDivergeStable)
    (execution : SceneExecution inp o res)
    (comp : List Nat) (hcomp : comp ∈ components execution.graph)
    (candidate : Nat) (run : Run) (orderOptions : OrderOptions)
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run) :
    LoopHullRightNeighborCover execution.params
      (componentCandidate execution.graph comp candidate) run
      execution.measured := by
  have hx : ForeignBorderChainXAligned := foreignBorderChainXAligned' hstab
  have horder : ForeignBorderLayerOrder := foreignBorderLayerOrder'
  have hgrp : LoopResNeighborGapGroupTopDisj execution.params
      (componentCandidate execution.graph comp candidate) run
      execution.measured :=
    loopResNeighborGapGroupTopDisj_holds hwf hfp hx horder execution hcomp hrun
  have hbot : LoopResNeighborGapBottomOwnerDisj execution.params
      (componentCandidate execution.graph comp candidate) run
      execution.measured :=
    neighborGapBottomOwnerDisj_holds execution hcomp hrun
  exact neighborCover_of_disjoint_closed hwf hfp hx execution hcomp hrun hgrp hbot

end PipelineImpl
end Layered
end Elegant

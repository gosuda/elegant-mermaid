import Elegant.Layered.ForeignBorderEdgesNoncrossingProof
import Elegant.Layered.BorderInnerFoldProof
import Elegant.Layered.ForeignBorderSideUpsProof
import Elegant.Layered.ForeignSideMarkingCrossedProof
import Elegant.Layered.ForeignBorderAlignRankProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Closed border-chain alignment.

`foreignBorderChainXAligned'` below closes `ForeignBorderChainXAligned` for
executed runs. The conditional theorems `foreignBorderSideUps_of` and
`foreignBorderChainXAligned_of` take universal chain-shape and fold-bound
hypotheses that do not bind execution evidence, while
`foreignSideChainShape_executed` and `foreignBorderEdgesNoncrossing_executed`
need it; but every use inside `foreignBorderSideUps_of` is at one executed
run. So this replays the body of `foreignBorderSideUps_of` with the pointwise
executed facts inlined: the chain shape from `foreignSideChainShape_executed`,
the fold bound from `foreignSideFoldBound'` applied to that shape and the
executed non-crossing theorem, then continues exactly as the original proof
does, and finishes with `foreignBorderChainXAligned`.

The only hypothesis carried is the ordering-stage residual
`ForeignBorderDivergeStable` from
`Elegant.Layered.ForeignBorderEdgesNoncrossingProof` (probe evidence:
`wip/Probe/BorderNoncrossingTProbe.lean` census B is zero on every executed
sample, non-vacuous on all multi-group samples in both TB and LR).
-/

/-- The side chains form single alignment blocks, closed for executed runs:
replay of `foreignBorderSideUps_of` with the pointwise executed shape and
fold facts inlined. -/
theorem foreignBorderSideUps_closed (hstab : ForeignBorderDivergeStable) :
    ForeignBorderSideUps := by
  intro P inp o lines graph hgraph comp hcomp candidate run labels orderOptions hrun
    decl side hside k hk pos hpos
  have hpos' : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos := hpos
  have hsh : ForeignSideChainShape P run side decl pos k :=
    foreignSideChainShape_executed hgraph hcomp hrun hside hpos'
  have hcross : ForeignBorderEdgesNoncrossing P run pos k :=
    foreignBorderEdgesNoncrossing_executed hgraph hcomp hrun hpos' hstab
  have hrunEx : ∃ (cg : Graph) (labels : List MeasuredLabel)
      (orderOptions : OrderOptions),
      componentRun P cg labels orderOptions = .ok run :=
    ⟨componentCandidate graph comp candidate, labels, orderOptions, hrun⟩
  have hfo : ForeignSideFoldBound P run side decl pos k :=
    foreignSideFoldBound' hrunEx hside hk hpos' hsh hcross
  refine ⟨sideChainNodes P run side decl, sideOrdered P run pos k side decl,
    ?_, ?_⟩
  · intro a
    exact mem_sideChainNodes hpos
  · intro hL
    have hocc : OccurringBorderChain (sideCtx P run pos k)
        (sideChainNodes P run side decl) :=
      ⟨sideChainNodes_nodup (P := P) (run := run) (side := side) (decl := decl) hpos',
        fun v hv => sideChainNodes_flat_ctx hv, hsh.rank_inj, hsh.rank_consec⟩
    have hF : ExecutedChainFacts (sideBase run) (sideCtx P run pos k)
        (sideChainNodes P run side decl) :=
      ⟨fun v hv => sideChain_border_val hside hpos' hv, hsh.path_consec,
        hsh.incident_border, hsh.consec_edge, hfo⟩
    have hedges : (sideCtx P run pos k).edges.size = (sideBase run).edges.length ∧
        ∀ i, i < (sideBase run).edges.length →
          (sideCtx P run pos k).edges[i]! = (sideBase run).edges[i]! :=
      executedClusterCtx_edges
    have hmarked : (sideCtx P run pos k).marked =
        CoordsImpl.typeOneConflicts (sideBase run) pos := rfl
    have hE : CoordsImpl.EdgeOK (sideCtx P run pos k) :=
      (Elegant.Layered.clusterCtx_facts (ng := P.nodeGap) (cp := P.clusterPad) hpos').2
    have hpickFacts : BorderChainPickFacts (sideCtx P run pos k)
        (sideChainNodes P run side decl) hocc :=
      borderChainPickFacts_of_executedChainFacts hF hedges hmarked hE
    have hpick : BorderChainPick (sideCtx P run pos k)
        (sideChainNodes P run side decl) hocc :=
      borderChainPick_of_facts hpickFacts
    have hord := sideOrdered_ctx P run pos k side decl
    exact borderChainUps_of_pick hL hocc hord hpick

/-- The closed alignment form `ForeignBorderChainXAligned`: every two
same-side markers of one declaration share one closed `x`-interval. The only
open content is the ordering-stage stability of divergent blocks. -/
theorem foreignBorderChainXAligned' (hstab : ForeignBorderDivergeStable) :
    ForeignBorderChainXAligned :=
  foreignBorderChainXAligned (foreignBorderSideUps_closed hstab)

end Elegant.Layered.PipelineImpl

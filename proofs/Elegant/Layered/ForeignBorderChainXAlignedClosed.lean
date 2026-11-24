import Elegant.Layered.ForeignBorderEdgesNoncrossingProof
import Elegant.Layered.BorderInnerFoldProof
import Elegant.Layered.ForeignBorderSideUpsProof
import Elegant.Layered.ForeignSideMarkingCrossedProof
import Elegant.Layered.ForeignBorderAlignRankProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Closed border-chain alignment.

`foreignBorderSideUps_closed` specializes the chain-shape and fold facts
to each successful framed run. The fold bound uses border-edge noncrossing,
which in turn uses `ForeignBorderDivergeStable` for that run.
-/

/-- The side chains of a successful framed run form single alignment blocks
given cross-layer order stability for divergent blocks. -/
theorem foreignBorderSideUps_closed (hstab : ForeignBorderDivergeStable) :
    ForeignBorderSideUps := by
  intro P inp o lines graph hgraph hlines hwf hframed comp hcomp candidate run labels orderOptions hrun
    decl side hside k hk pos hpos
  have hpos' : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos := hpos
  have hsh : ForeignSideChainShape P run side decl pos k :=
    foreignSideChainShape_executed hgraph hcomp hrun hside hpos'
  have hcross : ForeignBorderEdgesNoncrossing P run pos k :=
    foreignBorderEdgesNoncrossing_executed hgraph hlines hwf hframed hcomp hrun hpos' hstab
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

/-- Same-side markers of one declaration in a successful framed run share one
closed `x`-interval given cross-layer order stability for divergent blocks. -/
theorem foreignBorderChainXAligned' (hstab : ForeignBorderDivergeStable) :
    ForeignBorderChainXAligned :=
  foreignBorderChainXAligned (foreignBorderSideUps_closed hstab)

end Elegant.Layered.PipelineImpl

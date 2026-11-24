import Elegant.Layered.RegionFlatC8a
import Elegant.Layered.ExactBorderChainBProof
import Elegant.Layered.ExactForeignRankPairAnchorsProof
import Elegant.Layered.ExactPlainNodePathProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

/-- Foreign declaration rank spans for a successful run without a region spec. -/
theorem R8a_spans_none_holds (exactIds : List String) :
    ∀ {P : Params} {inp : Input} {o : Options}
      {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
      {graph0 graph : Graph},
      measuredGraph P inp o lines = .ok graph0 →
      exactGraph P exactIds inp o measured graph0 = .ok graph →
      lines.length = inp.boxes.length →
      WellFormed (inputModel inp o) →
      framedParents inp = true →
      ∀ {comp : List Nat}, comp ∈ components graph →
      ∀ {candidate : Nat} {cg' : Graph} {run : Run}
        {labels : List MeasuredLabel} {orderOptions : OrderOptions},
      componentRunR P (exactDecls exactIds inp) none inp
        (componentCandidateR none graph comp candidate) labels orderOptions =
        .ok (cg', run) →
      ∀ {u w : Nat} {uNode wNode : Node},
      (componentCandidateR none graph comp candidate).nodes[u]? = some uNode →
      (componentCandidateR none graph comp candidate).nodes[w]? = some wNode →
      uNode.border = -2 → wNode.border = -2 → uNode.decl ≠ wNode.decl →
      ∃ (tU bU tW bW : Int),
        tU ≤ bU ∧ tW ≤ bW ∧
        (∀ v, v < run.proper.nodes.length →
          (run.proper.nodes.getD v default).node.clusterPath.contains uNode.decl = true →
          tU ≤ rk run.proper.rank v ∧ rk run.proper.rank v ≤ bU) ∧
        (∀ v, v < run.proper.nodes.length →
          (run.proper.nodes.getD v default).node.clusterPath.contains wNode.decl = true →
          tW ≤ rk run.proper.rank v ∧ rk run.proper.rank v ≤ bW) ∧
        (∀ r : Int, tU ≤ r → r ≤ bU →
          ∃ (mL mR : Nat) (nL nR : ProperNode),
            run.coordinateProper.nodes[mL]? = some nL ∧ nL.node.border = -1 ∧
            nL.node.clusterPath.getLast? = some uNode.decl ∧
            rk run.coordinateProper.rank mL = r ∧
            run.coordinateProper.nodes[mR]? = some nR ∧ nR.node.border = 1 ∧
            nR.node.clusterPath.getLast? = some uNode.decl ∧
            rk run.coordinateProper.rank mR = r) ∧
        (∀ r : Int, tW ≤ r → r ≤ bW →
          ∃ (mL mR : Nat) (nL nR : ProperNode),
            run.coordinateProper.nodes[mL]? = some nL ∧ nL.node.border = -1 ∧
            nL.node.clusterPath.getLast? = some wNode.decl ∧
            rk run.coordinateProper.rank mL = r ∧
            run.coordinateProper.nodes[mR]? = some nR ∧ nR.node.border = 1 ∧
            nR.node.clusterPath.getLast? = some wNode.decl ∧
            rk run.coordinateProper.rank mR = r) := by
  intro P inp o lines measured graph0 graph hg0 hgX hlines hwf hfp comp hcomp
    candidate cg' run labels orderOptions hrun u w uNode wNode hu hw hbU hbW hne
  rw [componentCandidateR_none] at hrun hu hw
  exact XB_foreignClusterRankSpans_holds exactIds (XB_foreignRankPairAnchors_holds exactIds)
    hg0 hgX hlines hwf hfp hcomp (r8aC8a_runX_of_none hrun).1 hu hw hbU hbW hne

/-- Same-side marker intervals agree without a region spec on well-formed framed inputs. -/
theorem R8a_chain_none_framed_holds (exactIds : List String) :
    ∀ {P : Params} {inp : Input} {o : Options}
      {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
      {graph0 graph : Graph},
      measuredGraph P inp o lines = .ok graph0 →
      exactGraph P exactIds inp o measured graph0 = .ok graph →
      lines.length = inp.boxes.length →
      WellFormed (inputModel inp o) →
      framedParents inp = true →
      ∀ {comp : List Nat}, comp ∈ components graph →
      ∀ {candidate : Nat} {cg' : Graph} {run : Run}
        {labels : List MeasuredLabel} {orderOptions : OrderOptions},
      componentRunR P (exactDecls exactIds inp) none inp
        (componentCandidateR none graph comp candidate) labels orderOptions =
        .ok (cg', run) →
      ∀ {a b : Nat} {na nb : ProperNode},
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      na.node.border = nb.node.border →
      na.node.clusterPath.getLast? = nb.node.clusterPath.getLast? →
      RouteImpl.leftOf run.proper run.xs a = RouteImpl.leftOf run.proper run.xs b ∧
        RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a =
          RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b := by
  intro P inp o lines measured graph0 graph hg0 hgX hlines hwf hfp comp hcomp
    candidate cg' run labels orderOptions hrun a b na nb hna hnb hbA hbB hside hlast
  rw [componentCandidateR_none] at hrun
  exact X_foreignBorderChainXAligned_framed exactIds hg0 hgX hlines hwf hfp hcomp
    (r8aC8a_runX_of_none hrun).1 hna hnb hbA hbB hside hlast

/-- A plain node outside a declaration's cluster path lies beyond its marker pair. -/
theorem R8a_plain_none_holds (exactIds : List String) :
    ∀ {P : Params} {inp : Input} {o : Options}
      {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
      {graph0 graph : Graph},
      measuredGraph P inp o lines = .ok graph0 →
      exactGraph P exactIds inp o measured graph0 = .ok graph →
      ∀ {comp : List Nat}, comp ∈ components graph →
      ∀ {candidate : Nat} {cg' : Graph} {run : Run}
        {labels : List MeasuredLabel} {orderOptions : OrderOptions},
      componentRunR P (exactDecls exactIds inp) none inp
        (componentCandidateR none graph comp candidate) labels orderOptions =
        .ok (cg', run) →
      ∀ {decl v mL mR : Nat} {plain nL nR : ProperNode},
      run.proper.nodes[v]? = some plain →
      plain.node.border = 0 →
      plain.node.clusterPath.contains decl = false →
      run.proper.nodes[mL]? = some nL →
      nL.node.border = -1 →
      nL.node.clusterPath.getLast? = some decl →
      run.proper.nodes[mR]? = some nR →
      nR.node.border = 1 →
      nR.node.clusterPath.getLast? = some decl →
      rk run.proper.rank mL = rk run.proper.rank v →
      rk run.proper.rank mR = rk run.proper.rank v →
      RouteImpl.leftOf run.proper run.xs v + RouteImpl.nodeW run.proper v ≤
          RouteImpl.leftOf run.proper run.xs mL ∨
        RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR ≤
          RouteImpl.leftOf run.proper run.xs v := by
  intro P inp o lines measured graph0 graph hg0 hgX comp hcomp
    candidate cg' run labels orderOptions hrun decl v mL mR plain nL nR
    hplain hbPlain hforeign hleft hbL hdeclL hright hbR hdeclR hrankL hrankR
  rw [componentCandidateR_none] at hrun
  exact XN_plainClearOfSideMarker_of_path exactIds (XN_plainNodePathResidual_holds exactIds)
    hg0 hgX hcomp (r8aC8a_runX_of_none hrun).1 hplain hbPlain hforeign hleft hbL hdeclL hright hbR
    hdeclR hrankL hrankR

/-- Side-marker spans align and have the expected order without a region spec
on well-formed framed inputs. -/
theorem R8a_side_none_framed_holds (exactIds : List String) :
    ∀ {P : Params} {inp : Input} {o : Options}
      {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
      {graph0 graph : Graph},
      measuredGraph P inp o lines = .ok graph0 →
      exactGraph P exactIds inp o measured graph0 = .ok graph →
      lines.length = inp.boxes.length →
      WellFormed (inputModel inp o) →
      framedParents inp = true →
      ∀ {comp : List Nat}, comp ∈ components graph →
      ∀ {candidate : Nat} {cg' : Graph} {run : Run}
        {labels : List MeasuredLabel} {orderOptions : OrderOptions},
      componentRunR P (exactDecls exactIds inp) none inp
        (componentCandidateR none graph comp candidate) labels orderOptions =
        .ok (cg', run) →
      ∀ {decl m m' : Nat} {marker marker' : ProperNode},
      run.proper.nodes[m]? = some marker →
      (marker.node.border = -1 ∨ marker.node.border = 1) →
      marker.node.clusterPath.getLast? = some decl →
      run.proper.nodes[m']? = some marker' →
      (marker'.node.border = -1 ∨ marker'.node.border = 1) →
      marker'.node.clusterPath.getLast? = some decl →
      (marker.node.border = marker'.node.border →
        RouteImpl.leftOf run.proper run.xs m =
          RouteImpl.leftOf run.proper run.xs m' ∧
        RouteImpl.leftOf run.proper run.xs m + RouteImpl.nodeW run.proper m =
          RouteImpl.leftOf run.proper run.xs m' + RouteImpl.nodeW run.proper m') ∧
      0 ≤ RouteImpl.leftOf run.proper run.xs m + RouteImpl.nodeW run.proper m ∧
      ((marker.node.border = -1 ∧ marker'.node.border = 1 ∧
        rk run.proper.rank m = rk run.proper.rank m') →
        RouteImpl.leftOf run.proper run.xs m ≤
          RouteImpl.leftOf run.proper run.xs m' ∧
        RouteImpl.leftOf run.proper run.xs m + RouteImpl.nodeW run.proper m ≤
          RouteImpl.leftOf run.proper run.xs m' + RouteImpl.nodeW run.proper m') := by
  intro P inp o lines measured graph0 graph hg0 hgX hlines hwf hfp comp hcomp
    candidate cg' run labels orderOptions hrun decl m m' marker marker'
    hmarker hb hdecl hmarker' hb' hdecl'
  rw [componentCandidateR_none] at hrun
  exact XN_sideMarkerSpanAligned_of_chain exactIds (X_foreignBorderChainXAligned_framed exactIds)
    hg0 hgX hlines hwf hfp hcomp (r8aC8a_runX_of_none hrun).1 hmarker hb hdecl hmarker' hb' hdecl'

end Elegant.Layered.PipelineImpl

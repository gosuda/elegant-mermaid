import Elegant.Layered.ExactLoopEnvelopeGroupMissProof
import Elegant.Layered.ExactMarkerBracketProof
import Elegant.Layered.ExactBottomLoopTransportProof
import Elegant.Layered.ExactBorderSpanRunFactsProof
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExecutedBorderOrderFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Executed group marker order (`XLEG_GroupMarkerOrderX`).

The seam `XLEG_GroupMarkerOrderX` (premise of
`XLEM_groupOwnerMiss_holds`) is assembled from one proved leaf and two
narrower executed-form leaves:

- `exactBottomNoLoopX` (`ExactBottomLoopTransportProof.lean`, PROVED,
  unconditional): the bottom conjunct — no border-`2` candidate node of
  an executed exact run owns a self-loop edge.
- `XLEG_LoopMarkerCoreX` (open): marker existence, records, owner paths,
  the coordinate lookup of the top, and the executed rank equality.
- `XLEG_LoopMarkerLayerOrderX` (open): the crossed-order fact for the
  marker pair.
- `embLoopMarkerSpanX` (`ExactMarkerBracketProof.lean`, existing): the
  four span/numeric conjuncts for a given marker pair; they match
  conjuncts of `XLEG_GroupMarkerOrder` verbatim over
  `execution.measured`.

`XLEG_groupMarkerOrderX_of_leaves` performs the assembly. -/

/-- Executed layer-membership reduction: if the right marker of a looping top
has the executed rank of the top (`lay` equality) and both records are known
in the coordinate graph, the right marker sits wherever the top sits. -/
theorem XLEG_markerLayerMem_of_rankEq {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionX exactIds inp o res}
    {_comp : List Nat} {_candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    {cg : Graph}
    (hrun : componentRunX execution.params (exactDecls exactIds inp) cg
      execution.measured orderOptions = .ok run)
    {t mR : Nat} {ntC nR : ProperNode}
    (_hcoordT : run.coordinateProper.nodes[t]? = some ntC)
    (hcoordR : run.coordinateProper.nodes[mR]? = some nR)
    (hlayEq : OrderImpl.lay run.coordinateProper mR =
      OrderImpl.lay run.coordinateProper t)
    {layer : List Nat} (hlayer : layer ∈ run.layers) {pu : Nat}
    (hpu : layer[pu]? = some t) :
    ∃ jR : Nat, layer[jR]? = some mR := by
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, hordOk, hordLayers⟩, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  have hL := (OrderImpl.orderWithBudget_spec run.coordinateProper orderOptions ord
    hordOk).1
  rw [← hordLayers] at hlayer
  have hR := ExecutedBorderOrder.node_layer run.coordinateProper orderOptions ord
    hordOk hcoordR
  obtain ⟨r, hrGet⟩ := List.mem_iff_getElem?.mp hlayer
  have hrLen : r < ord.layers.length := (List.getElem?_eq_some_iff.mp hrGet).1
  have hgetD : ord.layers.getD r [] = layer := by
    rw [List.getD_eq_getElem?_getD, hrGet, Option.getD_some]
  have htIn : t ∈ ord.layers.getD r [] := by
    rw [hgetD]; exact List.mem_of_getElem? hpu
  have hlayT : OrderImpl.lay run.coordinateProper t = r :=
    ((OrderImpl.layer_mem hL hrLen).mp htIn).2
  have hlayMR : OrderImpl.lay run.coordinateProper mR = r := by
    rw [hlayEq]; exact hlayT
  have hmR : mR ∈ ord.layers.getD r [] := by
    rw [← hlayMR]; exact hR.2
  rw [hgetD] at hmR
  exact List.mem_iff_getElem?.mp hmR

/-- Executed cross-order reduction: with the layer order of a marker pair at
hand, the ordered-interval fact and nonnegative marker widths give the two
cross conjuncts of the looping-top witness. -/
theorem XLEG_markerCross_of_layerOrder {exactIds : List String}
    {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionX exactIds inp o res}
    {comp : List Nat} {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hcomp : comp ∈ components execution.graph)
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {mL mR : Nat} {nL nR : ProperNode}
    (hcoordL : run.coordinateProper.nodes[mL]? = some nL)
    (hcoordR : run.coordinateProper.nodes[mR]? = some nR)
    (hbL : nL.node.border = -1) (hbR : nR.node.border = 1)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {jL jR : Nat} (hjL : layer[jL]? = some mL) (hjR : layer[jR]? = some mR)
    (horder : jL < jR) :
    RouteImpl.leftOf run.proper run.xs mL ≤
      RouteImpl.leftOf run.proper run.xs mR ∧
    RouteImpl.leftOf run.proper run.xs mL + RouteImpl.nodeW run.proper mL ≤
      RouteImpl.leftOf run.proper run.xs mR + RouteImpl.nodeW run.proper mR := by
  have hnpL : ¬ (nL.node.border = -2 ∨ nL.node.border = 2) := by
    rw [hbL]; decide
  have hnpR : ¬ (nR.node.border = -2 ∨ nR.node.border = 2) := by
    rw [hbR]; decide
  have hoi := XB_orderedIntervals_holds exactIds execution.graph0_eq
    execution.graph_eq hcomp hrun hlayer horder hjL hjR hcoordL hcoordR hnpL hnpR
  have hdims := componentRunX_dims_nonneg hrun
  obtain ⟨_, _, _, q0, _, _, _, ⟨_, _, _⟩, _, hprox, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨_, _, _, _, _, hnonproxy⟩ := proxyWidths_rel hprox
  have hpn : run.proper.nodes = q0.nodes := by
    rw [← hdrop, OrderImpl.dropSynthetic_nodes]
  obtain ⟨hpl, _⟩ := hnonproxy mL nL hcoordL hnpL
  obtain ⟨hpr2, _⟩ := hnonproxy mR nR hcoordR hnpR
  have hpl2 : run.proper.nodes[mL]? = some nL := by rw [hpn]; exact hpl
  have hpr3 : run.proper.nodes[mR]? = some nR := by rw [hpn]; exact hpr2
  have hwL : 0 ≤ nL.node.w := (hdims mL nL hpl2).1
  have hwR : 0 ≤ nR.node.w := (hdims mR nR hpr3).1
  have hnwL : RouteImpl.nodeW run.proper mL = nL.node.w := by
    simp only [RouteImpl.nodeW, hpl2]
  have hnwR : RouteImpl.nodeW run.proper mR = nR.node.w := by
    simp only [RouteImpl.nodeW, hpr3]
  refine ⟨?_, ?_⟩
  · simp only [RouteImpl.leftOf] at hoi ⊢
    rw [hnwL, hnwR] at hoi ⊢
    omega
  · simp only [RouteImpl.leftOf] at hoi ⊢
    rw [hnwL, hnwR] at hoi ⊢
    omega

/-- Executed marker core leaf: marker existence with records, borders, owner
paths, the coordinate lookup of the looping top, and the executed rank
equality of the right marker with the top. -/
def XLEG_LoopMarkerCoreX (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt →
      (∃ e_ ∈ cg.edges, e_.tail = t ∧ e_.head = t) → nt.border = -2 →
      ∃ (mL mR : Nat) (nL nR : ProperNode) (ntC : ProperNode),
        run.coordinateProper.nodes[t]? = some ntC ∧
        run.coordinateProper.nodes[mL]? = some nL ∧
        run.coordinateProper.nodes[mR]? = some nR ∧
        nL.node.border = -1 ∧ nR.node.border = 1 ∧
        nL.node.clusterPath.getLast? = some nt.decl ∧
        nR.node.clusterPath.getLast? = some nt.decl ∧
        OrderImpl.lay run.coordinateProper mL =
          OrderImpl.lay run.coordinateProper t ∧
        OrderImpl.lay run.coordinateProper mR =
          OrderImpl.lay run.coordinateProper t

/-- The exact narrower crossed-order fact for the marker witness branch: in
every executed exact run, the executed ordering places the left marker of a
looping group top before its right marker in the shared rank layer. -/
def XLEG_LoopMarkerLayerOrderX (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt →
      (∃ e_ ∈ cg.edges, e_.tail = t ∧ e_.head = t) → nt.border = -2 →
      ∀ (mL mR : Nat) (nL nR : ProperNode),
        run.coordinateProper.nodes[mL]? = some nL →
        run.coordinateProper.nodes[mR]? = some nR →
        nL.node.border = -1 → nR.node.border = 1 →
        nL.node.clusterPath.getLast? = some nt.decl →
        nR.node.clusterPath.getLast? = some nt.decl →
        OrderImpl.lay run.coordinateProper mL =
          OrderImpl.lay run.coordinateProper mR →
        OrderImpl.lay run.coordinateProper mR =
          OrderImpl.lay run.coordinateProper t →
        ∃ (layer : List Nat) (jL jR : Nat), layer ∈ run.layers ∧
          layer[jL]? = some mL ∧ layer[jR]? = some mR ∧ jL < jR

/-- Assembly of the `XLEG_GroupMarkerOrderX` seam from the proved bottom
leaf, the marker core, the crossed-order fact, and the existing
`embLoopMarkerSpanX` residual. -/
theorem XLEG_groupMarkerOrderX_of_leaves (exactIds : List String)
    (hcore : XLEG_LoopMarkerCoreX exactIds)
    (horderX : XLEG_LoopMarkerLayerOrderX exactIds)
    (hspan : embLoopMarkerSpanX exactIds) :
    XLEG_GroupMarkerOrderX exactIds := by
  intro inp o res execution hwf hfp comp candidate run orderOptions cg hcomp hcg hrun
  subst hcg
  refine ⟨exactBottomNoLoopX execution comp candidate run orderOptions hcomp
    (componentCandidate execution.graph comp candidate) rfl hrun, ?_⟩
  intro t nt hnt hexLoop htG
  obtain ⟨mL, mR, nL, nR, ntC, hcoordT, hcoordL, hcoordR, hbL, hbR, hlastL,
    hlastR, hlayEqL, hlayEq⟩ :=
    hcore inp o res execution comp candidate run orderOptions
      (componentCandidate execution.graph comp candidate) hcomp rfl hrun t nt hnt
      hexLoop htG
  obtain ⟨hshare, hext, hnonneg, hsep⟩ :=
    hspan execution hwf hfp hcomp (componentCandidate execution.graph comp candidate)
      hcomp rfl hrun hnt hexLoop htG hcoordL hcoordR hbL hbR hlastL hlastR
  obtain ⟨layer, jL, jR, hlayer, hjL, hjR, horder⟩ :=
    horderX inp o res execution comp candidate run orderOptions
      (componentCandidate execution.graph comp candidate) hcomp rfl hrun t nt hnt
      hexLoop htG mL mR nL nR hcoordL hcoordR hbL hbR hlastL hlastR
      (hlayEqL.trans hlayEq.symm) hlayEq
  refine ⟨mL, mR, nL, nR, hcoordL, hcoordR, hbL, hbR, hlastL, hlastR, hext, ?_,
    hshare, ?_, ?_, hnonneg, hsep⟩
  · intro layer' hlayer' pu hpu'
    exact XLEG_markerLayerMem_of_rankEq (_comp := comp) (_candidate := candidate)
      hrun hcoordT hcoordR hlayEq hlayer' hpu'
  · exact (XLEG_markerCross_of_layerOrder hcomp hrun hcoordL hcoordR hbL hbR
      hlayer hjL hjR horder).1
  · exact (XLEG_markerCross_of_layerOrder hcomp hrun hcoordL hcoordR hbL hbR
      hlayer hjL hjR horder).2

end PipelineImpl

end Layered
end Elegant

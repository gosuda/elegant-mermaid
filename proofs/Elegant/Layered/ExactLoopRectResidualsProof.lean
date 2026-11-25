import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ExactLoopRectProof
import Elegant.Layered.LoopRectRealQProof
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Exact loop-rect same-part residuals, closed modulo one narrow fact each

Closes the two remaining premises of the exact loop-rectangle transport
(`ExactLoopRectProof.lean`):

* `XL_fixedDisjoint_holds`: `XL_FixedDisjoint` modulo the same-layer ordered
  interval fact `XLrr_FixedSep`. Covering comes from the public
  `componentRunX_original_nodes_covered`, the plain records from the prefixed
  copy `XLrr_original_plain_record` (a faithful copy of the private
  `X_original_plain_record` in `ExactFlatC2.lean`), rank bands from the
  `runHooksShift_exact` hook inside `componentRunX_positions_disjoint`, and
  only the within-layer ordering is assumed. That ordering is one pipeline
  stage (cross-coordinate left-to-right order); the full proof adds bands,
  record transfer, and the frame-to-node reduction, so the residual is
  strictly narrower. The general statement needs title uniqueness, which
  rests on `CgShape`; hence the residual instead of a closed proof.
* `XL_topSamePart_holds`: `XL_TopSamePart` modulo the frame-classification
  fact `XLrr_TopSplit`. Every group-top/plain-member frame pair is either
  strictly nested or disjoint with a positive member frame, from which the
  inequality follows by pure logic (`loopRect_strictInside_ne`,
  `loopRect_frameNe_of_disjoint`). The residual is one run-geometry stage;
  the target is its logical consequence used by the loop-rect transport.

Probe evidence (`proofs/wip/Probe/ExactLoopRectResidualsTProbe.lean`): on a
group with a zero-size fixed member and on a group with a wide fixed member,
every exact-run border-0 pair in one component is disjoint, no plain frame
equals a group-top frame, the ordered-interval check holds on every layer,
and the top-split classification holds on every top/member pair.
-/

/-- Residual: within-layer left-to-right order for non-proxy nodes of an
exact run (the `hSep` premise of `componentRunX_positions_disjoint`). -/
def XLrr_FixedSep (exactIds : List String) : Prop :=
  ∀ (P : Params) (inp : Input) (cg : Graph) (run : Run) (labels : List MeasuredLabel)
    (orderOptions : OrderOptions)
    (_hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    (layer : List Nat) (i j a b : Nat) (first second : ProperNode),
    layer ∈ run.layers → i < j → layer[i]? = some a → layer[j]? = some b →
    run.coordinateProper.nodes[a]? = some first → run.coordinateProper.nodes[b]? = some second →
    ¬(first.node.border = -2 ∨ first.node.border = 2) →
    ¬(second.node.border = -2 ∨ second.node.border = 2) →
    RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a ≤
      RouteImpl.leftOf run.proper run.xs b

/-- Residual: every group-top/plain-member frame pair of an exact run is
either strictly nested (member inside top) or disjoint with a positive
member frame (member outside top). -/
def XLrr_TopSplit (exactIds : List String) : Prop :=
  ∀ (P : Params) (inp : Input) (cg : Graph) (run : Run) (labels : List MeasuredLabel)
    (orderOptions : OrderOptions)
    (_hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {v w : Nat} {node member : Node},
    cg.nodes[v]? = some node → node.border = -2 →
    cg.nodes[w]? = some member → member.border = 0 →
    (frameRect P cg run v).StrictInside (frameRect P cg run w) ∨
      (Disjoint (frameRect P cg run w) (frameRect P cg run v) ∧
        0 < (frameRect P cg run w).w ∧ 0 < (frameRect P cg run w).h)

/-- Local copy of the private `X_plain_node_dims` in `ExactFlatC2.lean`:
exact proper nodes transfer unchanged for non-proxy borders. -/
private theorem XLrr_plain_node_dims {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {nd : ProperNode}
    (hnode : run.coordinateProper.nodes[i]? = some nd)
    (hborder : nd.node.border = 0) :
    run.proper.nodes[i]? = some nd := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hprojected := proxyWidths_plain_node hproxy hnode hborder
  rw [← hdrop]
  exact hprojected

/-- Local copy of the private `X_original_plain_record` in
`ExactFlatC2.lean`: exact original plain nodes keep their measured widths as
lower bounds. -/
private theorem XLrr_original_plain_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : Node} (hnode : cg.nodes[index]? = some node)
    (hplain : node.border = 0) :
    ∃ actual : ProperNode,
      run.coordinateProper.nodes[index]? = some actual ∧
      run.proper.nodes[index]? = some actual ∧
      actual.node.border = 0 ∧
      node.w ≤ actual.node.w ∧ actual.node.h = node.h ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, p0, labeled, _, hn, hl, hc, _, _, _, _, _, _, _⟩ := componentRunX_spec h
  have hsource := addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨actual, hactual, _, hborder, hwidth, hheight⟩ :=
    coordinateGraphX_plain_anchor_dims P hsource hplain
  have hcoordinate : run.coordinateProper.nodes[index]? = some actual := by
    rw [← hc]
    exact hactual
  have hproper := XLrr_plain_node_dims h hcoordinate hborder
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _⟩ := componentRunX_spec h
  have hx := ((proxyWidths_rel hproxy).2.2.2.2.2 index actual hcoordinate
    (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hborder, hwidth, hheight, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- Exact fixed-disjointness, closed modulo the within-layer ordering
residual. -/
theorem XL_fixedDisjoint_holds (exactIds : List String)
    (hSep : XLrr_FixedSep exactIds) :
    XL_FixedDisjoint exactIds := by
  intro P inp cg run labels orderOptions hrun u v nodeU nodeV hnodeU hnodeV hbU hbV hne
  have hcovered := componentRunX_original_nodes_covered hrun
  obtain ⟨actualU, hcoordU, hpropU, hbU0, _, _, _⟩ :=
    XLrr_original_plain_record hrun hnodeU hbU
  obtain ⟨actualV, hcoordV, hpropV, hbV0, _, _, _⟩ :=
    XLrr_original_plain_record hrun hnodeV hbV
  exact componentRunX_positions_disjoint hrun hnodeU hnodeV hbU hbV hne hcovered
    ⟨actualU, hcoordU, hpropU, hbU0⟩ ⟨actualV, hcoordV, hpropV, hbV0⟩
    (hSep P inp cg run labels orderOptions hrun)

/-- Exact top-same-part, closed modulo the frame-classification residual. -/
theorem XL_topSamePart_holds (exactIds : List String)
    (hSplit : XLrr_TopSplit exactIds) :
    XL_TopSamePart exactIds := by
  intro P inp cg run labels orderOptions hrun v w node member hnode hbV hmember hbW hframe
  have h := hSplit P inp cg run labels orderOptions hrun hnode hbV hmember hbW
  rcases h with hsi | ⟨hdis, hw, hh⟩
  · exact loopRect_strictInside_ne hsi hframe.symm
  · exact loopRect_frameNe_of_disjoint hdis hframe hw hh

end PipelineImpl
end Layered
end Elegant

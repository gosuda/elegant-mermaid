import Elegant.Layered.CaptionDescendantFacts
import Elegant.Layered.CaptionWidthFacts

set_option autoImplicit false

/-! # Caption descendant clearance: the same-part geometric core

`CaptionDescendantSamePartClear` (`Layered/CaptionDescendantFacts.lean`) is the
real geometric content of the caption descendant half: the transported caption
rect of the non-exclusive owner misses the interior of every exclusive
descendant member box of the same executed packing.

This file discharges it from the executed caption-band reservation and the
shelf transport.  The run-level core is the caption copy (border `3`) against
the frame rect of a plain node of the same component run: the copy participates
in the layer ordering like any non-proxy node, so same-rank siblings separate
horizontally (`componentRun_nonproxy_ordered_intervals`) and different-rank
nodes occupy disjoint rank bands (`rankAxis_node_in_band`,
`rankAxis_bands_disjoint`). -/

namespace Elegant.Layered

namespace PipelineImpl

/-- The executed caption copy of a group declaration is disjoint from the frame
rect of every plain node of the same component run.  This is the run-level
core behind the caption descendant clearance: an exclusive member box of the
owner group is a plain node, and the owner's caption copy separates from it by
rank band or, in the shared rank, by the cluster cross-coordinate ordering. -/
theorem componentRun_caption_copy_leaf_disjoint
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {i : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[i]? = some node)
    (hbI : node.border = -2)
    {w : Nat} {nodeW : Node}
    (hnodeW : (componentCandidate graph comp candidate).nodes[w]? = some nodeW)
    (hbW : nodeW.border = 0) :
    ∃ v : Nat,
      run.proper.nodes[v]? = some (copyF (⟨node, false, none, false⟩, i)) ∧
      Disjoint (frameRect P (componentCandidate graph comp candidate) run w)
        (Labels.rectAt run.proper run.xs run.ys v) := by
  -- the leaf side: actual record
  obtain ⟨actualW, hcoordW, hpropW, _, hbW0, _, _, _, _⟩ :=
    componentRun_original_plain_record hrun hnodeW hbW
  -- the copy side
  obtain ⟨v, _, hcoordinate, hproper, _, _, _, _, _, _⟩ :=
    componentRun_group_title_rank_layer hrun hnode hbI
  -- frames reduce to placed rectangles
  have hgetW : (componentCandidate graph comp candidate).nodes.getD w default = nodeW := by
    rw [List.getD_eq_getElem?_getD, hnodeW]
    rfl
  have hframeW : frameRect P (componentCandidate graph comp candidate) run w = nodeRect (componentCandidate graph comp candidate) run w := by
    unfold frameRect
    simp only []
    rw [hgetW, hbW]
    rfl
  have hrectW : nodeRect (componentCandidate graph comp candidate) run w =
      ⟨run.xs.getD w 0 - Int.fdiv actualW.node.w 2, run.ys.getD w 0,
        actualW.node.w, actualW.node.h⟩ := by
    simp [nodeRect, hpropW]
  -- run-level facts
  obtain ⟨ranks, p0, labeled, q0, _, _, hcoord, ⟨ord, _, hlayers⟩,
    _, hproxy, hdrop, hroute, _, hry, hys, _⟩ := componentRun_spec hrun
  obtain ⟨_, hrank, hqlen, _, _, _⟩ := proxyWidths_rel hproxy
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    first | exact hrank | exact hrank.symm
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes, hqlen]
  have hcyLen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
    obtain ⟨_, _, _, _, _, _, hy⟩ := CoordsImpl.rankCoordsWith_spec hry
    rw [hy]; simp
  have hvP : v < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hproper).1
  have hwP : w < run.proper.nodes.length :=
    componentRun_original_nodes_covered hrun w
      ((List.getElem?_eq_some_iff.mp hnodeW).1)
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hwC : w < run.coordinateProper.nodes.length := by omega
  have hvCy : v < run.coordinateYs.length := by omega
  have hwCy : w < run.coordinateYs.length := by omega
  -- run.ys equals coordinateYs at the copy and the leaf via proxyYs
  have hvYs : run.ys.getD v 0 = run.coordinateYs.getD v 0 := by
    rw [← hys]
    rw [proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs
      (v := v) (nd := copyF (⟨node, false, none, false⟩, i)) hcoordinate hvCy]
    simp [copyF]
  have hwYs : run.ys.getD w 0 = run.coordinateYs.getD w 0 := by
    rw [← hys]
    rw [proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs
      (v := w) (nd := actualW) hcoordW hwCy]
    simp [hbW0]
  -- layer coverage and rank bands
  obtain ⟨_, hband, _, hcov, _⟩ := RouteImpl.layersOk_spec
    (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨lV, hlyV, hvIn, hrkV0⟩ := hcov v hvP
  obtain ⟨lW, hlyW, hwIn, hrkW0⟩ := hcov w hwP
  let rV : Nat := (rk run.proper.rank v).toNat
  let rW : Nat := (rk run.proper.rank w).toNat
  have hrkV : rk run.coordinateProper.rank v = (rV : Int) := by
    rw [← hranks]
    show rk run.proper.rank v = ((rk run.proper.rank v).toNat : Int)
    exact (Int.toNat_of_nonneg hrkV0).symm
  have hrkW : rk run.coordinateProper.rank w = (rW : Int) := by
    rw [← hranks]
    show rk run.proper.rank w = ((rk run.proper.rank w).toNat : Int)
    exact (Int.toNat_of_nonneg hrkW0).symm
  have hlyV' : run.layers[rV]? = some lV := hlyV
  have hlyW' : run.layers[rW]? = some lW := hlyW
  -- the copy and the leaf are distinct placed nodes
  have hneVW : v ≠ w := by
    intro heq
    have hproperW := hproper
    rw [heq] at hproperW
    have hinj := Option.some.inj (hproperW.symm.trans hpropW)
    have hb := hbW0
    rw [← hinj] at hb
    simp [copyF] at hb
  -- rect of the copy
  have hrectV : Labels.rectAt run.proper run.xs run.ys v =
      ⟨run.xs.getD v 0 - Int.fdiv node.w 2, run.ys.getD v 0, node.w, node.h⟩ := by
    rw [rectAt_eq_box]
    simp only [RouteImpl.leftOf, RouteImpl.xAt, RouteImpl.yAt, RouteImpl.nodeW,
      RouteImpl.nodeH, hproper, copyF, hvYs]
  refine ⟨v, hproper, ?_⟩
  rcases Nat.lt_trichotomy rV rW with hlt | heq | hgt
  · -- the copy sits in a strictly lower rank band than the leaf
    have hbandV := CoordsImpl.rankAxis_node_in_band hry hlyV' hvIn hvC hrkV
    have hbandW := CoordsImpl.rankAxis_node_in_band hry hlyW' hwIn hwC hrkW
    have hbands := CoordsImpl.rankAxis_bands_disjoint hry rV rW lV lW hlt hlyV' hlyW'
    have hHV : CoordsImpl.nodeH run.coordinateProper v = node.h := by
      simp [CoordsImpl.nodeH, hcoordinate, copyF]
    have hHW : CoordsImpl.nodeH run.coordinateProper w = actualW.node.h := by
      simp [CoordsImpl.nodeH, hcoordW]
    rw [hHV] at hbandV
    rw [hHW] at hbandW
    rw [hframeW, hrectW, hrectV, hvYs, hwYs]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega
  · -- same rank: horizontal separation from the cluster cross coordinates
    rw [← heq] at hlyW'
    obtain hlWeq : lV = lW := Option.some.inj (hlyV'.symm.trans hlyW')
    rw [← hlWeq] at hwIn
    obtain ⟨pu, hpu⟩ := List.mem_iff_getElem?.mp hvIn
    obtain ⟨pw, hpw⟩ := List.mem_iff_getElem?.mp hwIn
    have hneP : pu ≠ pw := by
      intro heq'
      subst heq'
      exact hneVW (Option.some.inj (hpu.symm.trans hpw))
    have hlayerMem : lV ∈ run.layers := by
      obtain ⟨hmemLT, hmemEq⟩ := List.getElem?_eq_some_iff.mp hlyV'
      rw [← hmemEq]
      exact List.getElem_mem hmemLT
    rcases Nat.lt_or_gt_of_ne hneP with hplt | hpgt
    · have hsep := componentRun_nonproxy_ordered_intervals hgraph hcomp hrun
        (layer := lV) hlayerMem hplt hpu hpw hcoordinate hcoordW
        (by simp [copyF]) (by simp [hbW0])
      have hWV : RouteImpl.nodeW run.proper v = node.w := by
        simp [RouteImpl.nodeW, hproper, copyF]
      have hWW : RouteImpl.nodeW run.proper w = actualW.node.w := by
        simp [RouteImpl.nodeW, hpropW]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hWV, hWW] at hsep
      rw [hframeW, hrectW, hrectV, hvYs, hwYs]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
      omega
    · have hsep := componentRun_nonproxy_ordered_intervals hgraph hcomp hrun
        (layer := lV) hlayerMem hpgt hpw hpu hcoordW hcoordinate
        (by simp [hbW0]) (by simp [copyF])
      have hWV : RouteImpl.nodeW run.proper v = node.w := by
        simp [RouteImpl.nodeW, hproper, copyF]
      have hWW : RouteImpl.nodeW run.proper w = actualW.node.w := by
        simp [RouteImpl.nodeW, hpropW]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hWV, hWW] at hsep
      rw [hframeW, hrectW, hrectV, hvYs, hwYs]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsep ⊢
      omega
  · -- the leaf sits in a strictly lower rank band than the copy
    have hbandV := CoordsImpl.rankAxis_node_in_band hry hlyV' hvIn hvC hrkV
    have hbandW := CoordsImpl.rankAxis_node_in_band hry hlyW' hwIn hwC hrkW
    have hbands := CoordsImpl.rankAxis_bands_disjoint hry rW rV lW lV hgt hlyW' hlyV'
    have hHV : CoordsImpl.nodeH run.coordinateProper v = node.h := by
      simp [CoordsImpl.nodeH, hcoordinate, copyF]
    have hHW : CoordsImpl.nodeH run.coordinateProper w = actualW.node.h := by
      simp [CoordsImpl.nodeH, hcoordW]
    rw [hHV] at hbandV
    rw [hHW] at hbandW
    rw [hframeW, hrectW, hrectV, hvYs, hwYs]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega

end PipelineImpl

end Elegant.Layered

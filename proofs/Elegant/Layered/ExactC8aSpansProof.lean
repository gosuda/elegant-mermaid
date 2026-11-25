import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactFlatC2
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ForeignClusterFactsProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.SizingFacts
import Elegant.Layered.Coords
import Elegant.Layered.CgShape
import Elegant.Layered.Labels
import Elegant.Layered.Normalize
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Order
import Elegant.Layered.ExecutedBorderOrderFacts
import Elegant.Layered.Pipeline
import ElegantGeometry.Validator
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! Exact flat C8a span facts: mirrors of the six `X_C8a_*` hypotheses of
`flatC8aB_layoutX` in the draft `ExactFlatC8a.lean` (which is untracked and
does not compile, so nothing is imported from it).

Each `XS_C8a_*` is stated on the exact run (`componentRunX`) exactly as the
draft states its `X_C8a_*` counterpart. The proofs replay the plain pipeline
proofs over `componentRunX_spec`:

* Rank-band parts go through `componentRunX_node_band`, `X_pre_band`, and
  `X_ReserveBands_holds`.
* Order and marker facts are produced by stages before the size and reserve
  hooks, or are unchanged by them: `sizeProperPortsX` only adjusts the `w`
  of border-`0` nodes whose declaration is not exact, so it preserves
  borders, cluster paths, declarations, ranks, and lengths; `orderWithBudget`
  never reads widths (checked by inspection of `Order.lean`: widths occur
  only in marker construction at line 174); `reserveExactRanks` only shifts
  `ys`/`top` by nondecreasing prefix sums. The private `XSc8a_*` copies
  below replay the corresponding plain proofs with these hooks swapped in.
-/

/-- XS mirror of `ForeignClusterRankSpans`: per-declaration rank intervals
with a left/right border marker pair at every covered rank, for exact runs. -/
def XS_C8a_ForeignClusterRankSpans (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border = -2 → uNode.decl ≠ wNode.decl →
    ∃ (tU bU tW bW : Int),
      tU ≤ bU ∧ tW ≤ bW ∧
      (∀ v, v < run.proper.nodes.length →
        (run.proper.nodes.getD v default).node.clusterPath.contains
            uNode.decl = true →
        tU ≤ rk run.proper.rank v ∧ rk run.proper.rank v ≤ bU) ∧
      (∀ v, v < run.proper.nodes.length →
        (run.proper.nodes.getD v default).node.clusterPath.contains
            wNode.decl = true →
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
            rk run.coordinateProper.rank mR = r)

/-- XS mirror of `ForeignBorderLayerOrder`: unrelated group declarations
occupy disjoint position blocks in every layer, for exact runs. -/
def XS_C8a_ForeignBorderLayerOrder (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border = -2 →
    uNode.decl ≠ wNode.decl →
    wNode.clusterPath.contains uNode.decl = false →
    uNode.clusterPath.contains wNode.decl = false →
    ∀ {layer : List Nat}, layer ∈ run.layers →
    (∀ (i j a b : Nat) (na nb : ProperNode),
        layer[i]? = some a → layer[j]? = some b →
        run.coordinateProper.nodes[a]? = some na →
        run.coordinateProper.nodes[b]? = some nb →
        (na.node.border = -1 ∨ na.node.border = 1) →
        na.node.clusterPath.getLast? = some uNode.decl →
        (nb.node.border = -1 ∨ nb.node.border = 1) →
        nb.node.clusterPath.getLast? = some wNode.decl →
        i < j) ∨
    (∀ (i j a b : Nat) (na nb : ProperNode),
        layer[i]? = some a → layer[j]? = some b →
        run.coordinateProper.nodes[a]? = some na →
        run.coordinateProper.nodes[b]? = some nb →
        (na.node.border = -1 ∨ na.node.border = 1) →
        na.node.clusterPath.getLast? = some uNode.decl →
        (nb.node.border = -1 ∨ nb.node.border = 1) →
        nb.node.clusterPath.getLast? = some wNode.decl →
        j < i)

/-- XS mirror of `BracketMarkersAtRank`: a rank bracketed by two members of
one declaration carries its marker pair, for exact runs. -/
def XS_C8a_BracketMarkersAtRank (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl : Nat} (r : Nat) {low high : Nat} {lowNd highNd : ProperNode},
      run.proper.nodes[low]? = some lowNd →
      lowNd.node.clusterPath.contains decl = true →
      (rk run.proper.rank low).toNat ≤ r →
      run.proper.nodes[high]? = some highNd →
      highNd.node.clusterPath.contains decl = true →
      r ≤ (rk run.proper.rank high).toNat →
      ∃ (mL mR : Nat) (nL nR : ProperNode),
        run.coordinateProper.nodes[mL]? = some nL ∧
        nL.node.border = -1 ∧
        nL.node.clusterPath.getLast? = some decl ∧
        rk run.coordinateProper.rank mL = (r : Int) ∧
        run.coordinateProper.nodes[mR]? = some nR ∧
        nR.node.border = 1 ∧
        nR.node.clusterPath.getLast? = some decl ∧
        rk run.coordinateProper.rank mR = (r : Int)

/-- XS mirror of `PlainClearOfSideMarker`: a plain node off the group lies
beyond the marker pair at the same rank, for exact runs. -/
def XS_C8a_PlainClearOfSideMarker (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
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
          RouteImpl.leftOf run.proper run.xs v

/-- XS mirror of `SideMarkerSpanAligned`: same-side markers share one
`x`-span with nonnegative right edge, and a left marker lies left of a
same-rank right marker, for exact runs (conditional on the chain seam). -/
def XS_C8a_SideMarkerSpanAligned (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
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
          RouteImpl.leftOf run.proper run.xs m' + RouteImpl.nodeW run.proper m')

/-- XS mirror of `componentRun_positions_disjoint`: distinct plain nodes of
one exact component run have disjoint frame rectangles. -/
def XS_C8a_PositionsDisjoint (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u v : Nat} {nodeU nodeV : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some nodeU →
    (componentCandidate graph comp candidate).nodes[v]? = some nodeV →
    nodeU.border = 0 → nodeV.border = 0 → u ≠ v →
    Disjoint (frameRect P (componentCandidate graph comp candidate) run u)
      (frameRect P (componentCandidate graph comp candidate) run v)

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl


/-- Exact proper nodes transfer unchanged for non-proxy borders (copy of the
private `X_nonproxy_record` in `ExactFlatC2`). -/
private theorem XSc8a_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

/-- Exact proper nodes transfer unchanged for border-`0` nodes (copy of the
private `X_plain_node_dims` in `ExactFlatC2`). -/
private theorem XSc8a_plain_node_dims {P : Params} {exact : List Nat}
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

/-- Exact original plain nodes keep a record through the coordinate and
proper runs (copy of the private `X_original_plain_record` in
`ExactFlatC2`). -/
private theorem XSc8a_original_plain_record {P : Params} {exact : List Nat}
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
  have hproper := XSc8a_plain_node_dims h hcoordinate hborder
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, _⟩ := componentRunX_spec h
  have hx := ((proxyWidths_rel hproxy).2.2.2.2.2 index actual hcoordinate
    (by rw [hborder]; decide)).2
  refine ⟨actual, hcoordinate, hproper, hborder, hwidth, hheight, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- Exact border-marker records transfer with their cross centres (copy of
the private `X_border_record` in `ExactFlatC2`). -/
private theorem XSc8a_border_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : ProperNode}
    (hv : run.coordinateProper.nodes[v]? = some node)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    run.proper.nodes[v]? = some node ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hnotProxy : ¬ (node.node.border = -2 ∨ node.node.border = 2) := by
    rcases hborder with hborder | hborder <;> omega
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v node hv hnotProxy
  refine ⟨?_, ?_⟩
  · rw [← hdrop]
    exact hnode
  · simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- Exact coordinate record from the proper run (copy of the private
`X_fbs_coordinate_record` in `ExactFlatC2`). -/
private theorem XSc8a_fbs_coordinate_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nvp : ProperNode} (hrec : run.proper.nodes[v]? = some nvp) :
    ∃ nvc : ProperNode, run.coordinateProper.nodes[v]? = some nvc ∧
      nvc.node.border = nvp.node.border ∧ nvc.node.h = nvp.node.h ∧
      (¬(nvc.node.border = -2 ∨ nvc.node.border = 2) →
        nvc.node.clusterPath = nvp.node.clusterPath) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hvR : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hrec).1
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hcadr : run.coordinateProper.nodes[v]? = some run.coordinateProper.nodes[v] :=
    List.getElem?_eq_getElem hvC
  obtain ⟨nd', hnd', -, hb', hh'⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.1 v _ hcadr
  have hnd2 : run.proper.nodes[v]? = some nd' := by rw [← hdrop]; exact hnd'
  have hnde : nd' = nvp := Option.some.inj (hnd2.symm.trans hrec)
  rw [hnde] at hb' hh'
  refine ⟨run.coordinateProper.nodes[v], hcadr, hb'.symm, hh'.symm, ?_⟩
  intro hnp
  obtain ⟨hfull, -⟩ := XSc8a_nonproxy_record hrun hcadr hnp
  have := Option.some.inj (hrec.symm.trans hfull)
  rw [← this]

/-- `sizeProperPortsX` preserves the node origin (copy of the private
`X_sized_origin` in `ExactFlatC2`). -/
private theorem XSc8a_sized_origin (P : Params) (exact : List Nat) (source : Proper)
    {index : Nat} {node : ProperNode}
    (hnode : (sizeProperPortsX P exact source).nodes[index]? = some node) :
    ∃ original : ProperNode, source.nodes[index]? = some original ∧
      node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
      node.node.clusterPath = original.node.clusterPath := by
  have hkey := sizeProperPortsX_key P exact source index
  rw [hnode] at hkey
  cases horiginal : source.nodes[index]? with
  | none => simp [horiginal] at hkey
  | some original =>
      simp only [horiginal, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
      exact ⟨original, rfl, hkey⟩

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Exact bordered-graph node classification (copy of the private
`X_coordinateGraph0_lookup` in `ExactFlatC2`). -/
private theorem XSc8a_coordinateGraph0_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[v]? =
        some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      nd.node.clusterPath = m.node.clusterPath ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      nd.node.clusterPath = q.1.node.clusterPath) := by
  rw [clearProxyExtents_nodes] at h
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  rw [hx] at h
  simp only [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hl, rfl⟩ := h
  have hlen : (sizeProperPortsX P exact p).nodes.length = p.nodes.length :=
    sizeProperPortsX_length P exact p
  obtain ⟨c1, c2, c3, c4⟩ := clearF_keys m
  by_cases hv1 : v < (titleReservations (sizeProperPortsX P exact p)).nodes.length
  · rw [List.getElem?_append_left hv1] at hl
    rw [titleReservations_nodes] at hl hv1
    by_cases hv2 : v < (sizeProperPortsX P exact p).nodes.length
    · rw [List.getElem?_append_left (by simpa using hv2)] at hl
      left
      cases hs : (sizeProperPortsX P exact p).nodes[v]? with
      | none => simp [List.getElem?_map, hs] at hl
      | some s =>
        simp only [List.getElem?_map, hs, Option.map_some, Option.some.injEq] at hl
        subst hl
        have hk := sizeProperPortsX_key P exact p v
        rw [hs] at hk
        cases hp : p.nodes[v]? with
        | none => simp [hp] at hk
        | some mp =>
          simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨hd, hb, hpth⟩ := hk
          obtain ⟨t1, t2, t3, t4⟩ := titleF_keys s
          refine ⟨mp, rfl, ?_, ?_, ?_, ?_⟩
          · rw [c1, t1, hd]
          · rw [c2, t2, hb]
          · rw [c3, t3, hpth]
          · intro hbd
            rw [c4]
            exact t4 (by rw [← t2, ← c2]; exact hbd)
    · right; right
      rw [List.getElem?_append_right (by simpa [hlen] using hv2)] at hl
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hl
      obtain ⟨q, hq, rfl⟩ := hl
      refine ⟨v - (sizeProperPortsX P exact p).nodes.length, q, ?_, by omega, ?_, ?_, ?_⟩
      · simpa [hlen] using hq
      · rw [c1]; rfl
      · rw [c2]; rfl
      · rw [c3]; rfl
  · rw [List.getElem?_append_right (by omega)] at hl
    right; left
    obtain ⟨e1, e2⟩ := hall m (List.mem_of_getElem? hl)
    refine ⟨(clearF_keys m).1.trans e1, ?_⟩
    rw [(clearF_keys m).2.1]
    exact e2

/-- Exact coordinate-graph node classification (copy of the private
`X_coordinateGraph_lookup` in `ExactFlatC2`). -/
private theorem XSc8a_coordinateGraph_lookup (P : Params) (exact : List Nat)
    (p : Proper) {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphX P exact p).nodes[v]? = some nd) :
    (∃ m, p.nodes[v]? = some m ∧ nd.dummy = m.dummy ∧ nd.node.border = m.node.border ∧
      (m.dummy = false → nd.node.clusterPath = m.node.clusterPath) ∧
      ((nd.node.border = -2 ∨ nd.node.border = 2) → nd.node.h = 0)) ∨
    (nd.dummy = false ∧ (nd.node.border = -1 ∨ nd.node.border = 1)) ∨
    (∃ (i : Nat) (q : ProperNode × Nat),
      (titleNodes (sizeProperPortsX P exact p))[i]? = some q ∧
      v = p.nodes.length + i ∧ nd.dummy = q.1.dummy ∧ nd.node.border = 3 ∧
      (q.1.dummy = false → nd.node.clusterPath = q.1.node.clusterPath)) := by
  unfold coordinateGraphX at h
  obtain ⟨m1, hm1, hd, hb, hh, hnd⟩ := materialize_lookup _ h
  rcases XSc8a_coordinateGraph0_lookup P exact p hm1 with ⟨m, hm, h1, h2, h3, h4⟩ | ⟨h1, h2⟩ |
    ⟨i, q, hq, hv, h1, h2, h3⟩
  · refine Or.inl ⟨m, hm, hd.trans h1, hb.trans h2, fun hf => ?_, fun hbd => ?_⟩
    · have : m1.dummy = false := by rw [h1]; exact hf
      rw [hnd this]
      exact h3
    · rw [hh]
      exact h4 (by rw [← hb]; exact hbd)
  · exact Or.inr (Or.inl ⟨by rw [hd]; exact h1, by rw [hb]; exact h2⟩)
  · refine Or.inr (Or.inr ⟨i, q, hq, hv, hd.trans h1, hb.trans h2, fun hf => ?_⟩)
    have : m1.dummy = false := by rw [h1]; exact hf
    rw [hnd this]
    exact h3

/-- Exact coordinate titles are unique per cluster path (copy of the private
`X_pc_title_unique` in `ExactFlatC2`). -/
private theorem XSc8a_pc_title_unique {cg : Graph} {P : Params} {exact : List Nat}
    {labeled : Proper} (hK : NodeKeys cg labeled)
    (hS : CgShape cg) {a b : Nat} {na nb : ProperNode}
    (ha : (coordinateGraphX P exact labeled).nodes[a]? = some na)
    (hb : (coordinateGraphX P exact labeled).nodes[b]? = some nb)
    (h1 : na.node.border = 3) (h2 : nb.node.border = 3)
    (hp : na.node.clusterPath = nb.node.clusterPath) : a = b := by
  have key : ∀ {v : Nat} {nd : ProperNode},
      (coordinateGraphX P exact labeled).nodes[v]? = some nd →
      nd.node.border = 3 →
      ∃ (i : Nat) (q : ProperNode × Nat),
        (titleNodes (sizeProperPortsX P exact labeled))[i]? = some q ∧
        v = labeled.nodes.length + i ∧ nd.node.clusterPath = q.1.node.clusterPath := by
    intro v nd h hb3
    rcases XSc8a_coordinateGraph_lookup P exact labeled h with ⟨m, hm, _, h1, _, _⟩ | ⟨_, h1⟩ |
      ⟨i, q, hq, hv, hqd, _, h4⟩
    · rcases hK v m hm with ⟨n, hn, _, hb, _⟩ | ⟨_, hb, _⟩
      · exact absurd (by rw [← hb, ← h1]; exact hb3) (hS.2 n (List.mem_of_getElem? hn))
      · rw [hb] at h1; omega
    · omega
    · obtain ⟨hs, hbq⟩ := titleNodes_spec hq
      have hk := sizeProperPortsX_key P exact labeled q.2
      rw [hs] at hk
      cases hp : labeled.nodes[q.2]? with
      | none => simp [hp] at hk
      | some mp =>
        simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hk1, hk2, _⟩ := hk
        rcases hK q.2 mp hp with ⟨n, _, hmd, _, _⟩ | ⟨_, hb', _⟩
        · exact ⟨i, q, hq, hv, h4 (by rw [hk1]; exact hmd)⟩
        · rw [hk2] at hbq
          rw [hb'] at hbq
          exact absurd hbq (by decide)
  obtain ⟨i, qi, hqi, hvi, hpi⟩ := key ha h1
  obtain ⟨j, qj, hqj, hvj, hpj⟩ := key hb h2
  obtain ⟨hsi, hbi⟩ := titleNodes_spec hqi
  obtain ⟨hsj, hbj⟩ := titleNodes_spec hqj
  have kI := sizeProperPortsX_key P exact labeled qi.2
  have kJ := sizeProperPortsX_key P exact labeled qj.2
  rw [hsi] at kI
  rw [hsj] at kJ
  cases hli : labeled.nodes[qi.2]? with
  | none => simp [hli] at kI
  | some mi =>
    cases hlj : labeled.nodes[qj.2]? with
    | none => simp [hlj] at kJ
    | some mj =>
      simp only [hli, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kI
      simp only [hlj, Option.map_some, Option.some.injEq, Prod.mk.injEq] at kJ
      have hidx : qi.2 = qj.2 :=
        labeled_topUnique hK hS hli hlj (by rw [← kI.2.1]; exact hbi)
          (by rw [← kJ.2.1]; exact hbj)
          (by rw [← kI.2.2, ← kJ.2.2, ← hpi, ← hpj]; exact hp)
      have hij : i = j :=
        nodup_map_inj_aux (·.2) (titleNodes_snd_nodup _) hqi hqj hidx
      rw [hvi, hvj, hij]

/-- Exact ordered intervals for non-proxy nodes over a measured/exact graph
(replay of the private `X_nonproxy_ordered_intervals` in `ExactFlatC2`,
with the public `exactGraph_shape` in place of the private shape
transport). -/
private theorem XSc8a_ordered_intervals {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {layer : List Nat} (hlayer : layer ∈ run.layers)
    {i j a b : Nat} {first second : ProperNode}
    (hij : i < j) (ha : layer[i]? = some a) (hb : layer[j]? = some b)
    (hfirst : run.coordinateProper.nodes[a]? = some first)
    (hsecond : run.coordinateProper.nodes[b]? = some second)
    (hfirstBorder : ¬(first.node.border = -2 ∨ first.node.border = 2))
    (hsecondBorder : ¬(second.node.border = -2 ∨ second.node.border = 2)) :
    RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a ≤
      RouteImpl.leftOf run.proper run.xs b := by
  obtain ⟨rr, labeled, hrr, hc, hk, _, hrecords, hranks, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hshape := componentCandidate_shape (components_nodup graph comp hcomp)
    (exactGraph_shape (measuredGraph_shape h0) h) candidate
  have huniq : ∀ (u v : Nat) (left right : ProperNode),
      run.coordinateProper.nodes[u]? = some left →
      run.coordinateProper.nodes[v]? = some right →
      left.node.border = 3 → right.node.border = 3 →
      left.node.clusterPath = right.node.clusterPath → u = v := by
    intro u v left right hleft hright hleftBorder hrightBorder hpath
    apply XSc8a_pc_title_unique hk hshape
      (by rw [hc]; exact hleft)
      (by rw [hc]; exact hright) hleftBorder hrightBorder hpath
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRunX_spec hrun
  have hsep := cluster_all_pairs_separated hcross huniq layer hlayer i j a b
    first second hij ha hb hfirst hsecond
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨hng, hcp, _⟩ := crossCoordsClusterWith_spec hcross
  obtain ⟨hfinalFirst, hxa⟩ := XSc8a_nonproxy_record hrun hfirst hfirstBorder
  obtain ⟨hfinalSecond, hxb⟩ := XSc8a_nonproxy_record hrun hsecond hsecondBorder
  have hwa : RouteImpl.nodeW run.proper a =
      RouteImpl.nodeW run.coordinateProper a := by
    simp only [RouteImpl.nodeW, hfinalFirst, hfirst]
  have hwb : RouteImpl.nodeW run.proper b =
      RouteImpl.nodeW run.coordinateProper b := by
    simp only [RouteImpl.nodeW, hfinalSecond, hsecond]
  have hga : RouteImpl.nodeW run.coordinateProper a ≤
      CoordsImpl.nodeW run.coordinateProper a := CoordsImpl.nodeW_ge_width _ _
  have hgb : RouteImpl.nodeW run.coordinateProper b ≤
      CoordsImpl.nodeW run.coordinateProper b := CoordsImpl.nodeW_ge_width _ _
  have e : ∀ width : Int, Int.fdiv width 2 = width / 2 :=
    fun width => Int.fdiv_eq_ediv_of_nonneg width (by decide)
  unfold CoordsImpl.coordSep at hsep
  simp only [e] at hsep
  simp only [RouteImpl.leftOf, RouteImpl.xAt, hxa, hxb, hwa, hwb, e]
  omega

/-- Exact coordinate borders are well formed (replay of
`componentRun_coordinate_bordersWellFormed` via the public exact bundle). -/
private theorem XSc8a_bordersWellFormed {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run) :
    OrderImpl.BordersWellFormed run.coordinateProper := by
  obtain ⟨_, labeled, _, hc, _, hready, _, _, _⟩ := X_cg_run_bundle h0 h hcomp hrun
  rw [← hc]
  unfold coordinateGraphX
  apply materializeDummyPaths_bordersWellFormed
  apply clearProxyExtents_bordersWellFormed
  exact OrderImpl.addClusterBorders_bordersWellFormed _ _ hready

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- A side border of the exact coordinate graph is non-dummy (copy of the
private `anchor_side_dummy` in `ForeignBorderAnchorsProof`). -/
private theorem XSc8a_anchor_side_dummy {p : Proper} {bw : Int}
    (hready : OrderImpl.BorderConstructionReady p) {nd : ProperNode}
    (hmem : nd ∈ (OrderImpl.addClusterBorders p bw).nodes)
    (hs : nd.node.border = -1 ∨ nd.node.border = 1) : nd.dummy = false := by
  obtain ⟨extra, hx, hall⟩ := addClusterBorders_extra p bw
  rw [hx] at hmem
  rcases List.mem_append.mp hmem with hp | he
  · rcases hs with hs1 | hs2
    · exact absurd hs1 (hready.1 nd hp).1
    · exact absurd hs2 (hready.1 nd hp).2
  · exact (hall nd he).1

/-- A side border of the exact coordinate graph carries a `-2` anchor path
(copy of the private `anchor_side_path` in `ForeignBorderAnchorsProof`). -/
private theorem XSc8a_anchor_side_path {P : Params} {exact : List Nat} {p t : Proper}
    (ht : t = titleReservations (sizeProperPortsX P exact p))
    (hready : OrderImpl.BorderConstructionReady t)
    {v : Nat} {nd : ProperNode}
    (h : (coordinateGraphX P exact p).nodes[v]? = some nd)
    (hs : nd.node.border = -1 ∨ nd.node.border = 1) :
    nd.dummy = false ∧
    ∃ m : ProperNode, m ∈ t.nodes ∧ m.node.border = -2 ∧
      nd.node.clusterPath = m.node.clusterPath := by
  unfold coordinateGraphX at h
  rw [← ht] at h
  obtain ⟨m1, hm1, _, hb1, heq1⟩ := materialize_lookup _ h
  have hm1d : m1.dummy = false := by
    by_cases hc : m1.dummy = true
    · exfalso
      rw [clearProxyExtents_nodes, List.getElem?_map, Option.map_eq_some_iff] at hm1
      obtain ⟨m2, hm2get, heq2⟩ := hm1
      have cm2 := clearF_keys m2
      have hm2b : m2.node.border = -1 ∨ m2.node.border = 1 := by
        rw [← cm2.2.1, heq2, ← hb1]; exact hs
      have hm2mem : m2 ∈ (OrderImpl.addClusterBorders t P.clusterBorderW).nodes :=
        List.mem_of_getElem? hm2get
      have hdummy : m2.dummy = false :=
        XSc8a_anchor_side_dummy hready hm2mem hm2b
      have hnd2 : m1.dummy = false := by
        rw [← heq2, cm2.1]; exact hdummy
      rw [hnd2] at hc
      exact absurd hc (by decide)
    · exact by simpa using hc
  rw [← heq1.2 hm1d] at hm1
  rw [clearProxyExtents_nodes, List.getElem?_map, Option.map_eq_some_iff] at hm1
  obtain ⟨m2, hm2, heq2⟩ := hm1
  have cm2 := clearF_keys m2
  rw [heq2] at cm2
  have hm2b : m2.node.border = -1 ∨ m2.node.border = 1 := by
    rw [← cm2.2.1]; exact hs
  have hm2mem : m2 ∈ (OrderImpl.addClusterBorders t P.clusterBorderW).nodes :=
    List.mem_of_getElem? hm2
  have hndF : nd.dummy = false := by
    rw [cm2.1]; exact XSc8a_anchor_side_dummy hready hm2mem hm2b
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source t P.clusterBorderW hready hm2mem hm2b
  obtain ⟨tmem, hcond⟩ := List.mem_filter.mp htop
  have hget : t.nodes[top.2]? = some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp tmem
  refine ⟨hndF, top.1, List.mem_of_getElem? hget, ?_, cm2.2.2.1.trans hpath⟩
  simpa using hcond

/-- XS anchor paths: every side marker carries its title path; every title
path ends in its own declaration (replay of `foreignBorderAnchorPaths`). -/
private def XSc8a_AnchorPaths (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border = -2 → uNode.decl ≠ wNode.decl →
    (uNode.clusterPath.getLast? = some uNode.decl) ∧
    (wNode.clusterPath.getLast? = some wNode.decl) ∧
    ∀ {a : Nat} {na : ProperNode},
    run.coordinateProper.nodes[a]? = some na →
    (na.node.border = -1 ∨ na.node.border = 1) →
    (na.node.clusterPath.getLast? = some uNode.decl →
      na.node.clusterPath = uNode.clusterPath) ∧
    (na.node.clusterPath.getLast? = some wNode.decl →
      na.node.clusterPath = wNode.clusterPath)

private theorem XSc8a_anchorPaths {exactIds : List String} :
    XSc8a_AnchorPaths exactIds := by
  intro P inp o lines measured graph0 graph h0 h comp hcomp candidate run labels
    orderOptions hrun u w uNode wNode hu hw hbU hbW _hne
  obtain ⟨boxU, hboxU, hpathU⟩ := X_cg_group_box h0 h hu hbU
  obtain ⟨boxW, hboxW, hpathW⟩ := X_cg_group_box h0 h hw hbW
  have hlastU : uNode.clusterPath.getLast? = some uNode.decl := by
    rw [hpathU, List.getLast?_append]; simp
  have hlastW : wNode.clusterPath.getLast? = some wNode.decl := by
    rw [hpathW, List.getLast?_append]; simp
  refine ⟨hlastU, hlastW, fun {a na} hna hside => ?_⟩
  obtain ⟨_, labeled, _, hcoord, hk, hready, _, _, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  rw [← hcoord] at hna
  obtain ⟨_, m, hmem, hmB, hpath⟩ :=
    XSc8a_anchor_side_path rfl hready hna hside
  obtain ⟨mindex, hmindex⟩ := List.mem_iff_getElem?.mp hmem
  rcases X_titled_node_origin hk hmindex with
    ⟨orig, horig, _, hbb, hpp⟩ | ⟨_, hb3⟩
  · have horigB : orig.node.border = -2 := by rw [← hbb]; exact hmB
    rcases hk mindex orig horig with
      ⟨bn, hbn, _, hbnb, hnp⟩ | ⟨_, hb0, _⟩
    · have hbnB : bn.border = -2 := by rw [← hbnb]; exact horigB
      obtain ⟨boxG, hboxG, hpathG⟩ := X_cg_group_box h0 h hbn hbnB
      have hlastG : bn.clusterPath.getLast? = some bn.decl := by
        rw [hpathG, List.getLast?_append]; simp
      have hnaLast : na.node.clusterPath.getLast? = some bn.decl := by
        rw [hpath, hpp, hnp]; exact hlastG
      constructor
      · intro ho
        have hdeclEq : bn.decl = uNode.decl :=
          Option.some.inj (hnaLast.symm.trans ho)
        rw [hdeclEq] at hboxG
        have hboxEq : boxG = boxU := Option.some.inj (hboxG.symm.trans hboxU)
        rw [hpath, hpp, hnp, hpathG, hdeclEq, hboxEq, hpathU]
      · intro ho
        have hdeclEq : bn.decl = wNode.decl :=
          Option.some.inj (hnaLast.symm.trans ho)
        rw [hdeclEq] at hboxG
        have hboxEq : boxG = boxW := Option.some.inj (hboxG.symm.trans hboxW)
        rw [hpath, hpp, hnp, hpathG, hdeclEq, hboxEq, hpathW]
    · rw [hb0] at horigB; omega
  · rw [hb3] at hmB; omega

/-- Canonical cluster path of an executed exact side marker (replay of
`sideMarkerCanon` in `SideMarkerPathsProof`). -/
private theorem XSc8a_sideCanon {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {a : Nat} {na : ProperNode} {decl : Nat}
    (hna : run.coordinateProper.nodes[a]? = some na)
    (hside : na.node.border = -1 ∨ na.node.border = 1)
    (hlast : na.node.clusterPath.getLast? = some decl) :
    ∃ box : ModelBox,
      inp.boxes[decl]? = some box ∧
      na.node.clusterPath = Compound.path inp.boxes box ++ [decl] := by
  obtain ⟨_, labeled, _, hc, hk, hready, _, _, _⟩ :=
    X_cg_run_bundle h0 h hcomp hrun
  have hcoordinate : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[a]? =
      some na := by
    rw [hc]; exact hna
  have horiginal := X_side_original hready hcoordinate hside
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? horiginal) hside
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp htop
  have hget : (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp hmem
  have hbord : top.1.node.border = -2 := by simpa using hcond
  rcases X_titled_node_origin hk hget with
    ⟨orig, horig, _, hbb, hpp⟩ | ⟨_, hb3⟩
  · have horigB : orig.node.border = -2 := by rw [← hbb]; exact hbord
    rcases hk top.2 orig horig with
      ⟨bn, hbn, _, hbnb, hnp⟩ | ⟨_, hb0, _⟩
    · have hbnB : bn.border = -2 := by rw [← hbnb]; exact horigB
      obtain ⟨boxG, hboxG, hpathG⟩ := X_cg_group_box h0 h hbn hbnB
      have hlastG : bn.clusterPath.getLast? = some bn.decl := by
        rw [hpathG, List.getLast?_append]; simp
      have hnaLast : na.node.clusterPath.getLast? = some bn.decl := by
        rw [hpath, hpp, hnp]; exact hlastG
      have hdeclEq : bn.decl = decl := Option.some.inj (hnaLast.symm.trans hlast)
      rw [hdeclEq] at hboxG
      refine ⟨boxG, hboxG, ?_⟩
      rw [hpath, hpp, hnp, hpathG, hdeclEq]
    · rw [hb0] at horigB; omega
  · rw [hb3] at hbord; omega

/-- XS same path: two side markers of one declaration share the anchor's
full cluster path (replay of `sideMarkerSamePath`). -/
private def XSc8a_SamePath (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl m m' : Nat} {marker marker' : ProperNode},
      run.coordinateProper.nodes[m]? = some marker →
      marker.node.border = -1 →
      marker.node.clusterPath.getLast? = some decl →
      run.coordinateProper.nodes[m']? = some marker' →
      marker'.node.border = 1 →
      marker'.node.clusterPath.getLast? = some decl →
      marker.node.clusterPath = marker'.node.clusterPath

private theorem XSc8a_samePath {exactIds : List String} :
    XSc8a_SamePath exactIds := by
  intro P inp o lines measured graph0 graph h0 h comp hcomp candidate run labels
    orderOptions hrun decl m m' marker marker' hmem hborder hgetLast hmem'
    hborder' hgetLast'
  obtain ⟨boxL, hboxL, hpathL⟩ :=
    XSc8a_sideCanon h0 h hcomp hrun hmem (Or.inl hborder) hgetLast
  obtain ⟨boxR, hboxR, hpathR⟩ :=
    XSc8a_sideCanon h0 h hcomp hrun hmem' (Or.inr hborder') hgetLast'
  have hbox : boxL = boxR := Option.some.inj (hboxL.symm.trans hboxR)
  rw [hpathL, hpathR, hbox]

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- A labeled original index keeps a non-dummy record through exact title
reservation, border insertion, and proxy clearing (copy of the private
`preparedNondummyOfLabeled` in `SideMarkerPathsProof`). -/
private theorem XSc8a_preparedNondummy {P : Params} {exact : List Nat}
    {labeled : Proper} {e : Nat} {ndL : ProperNode}
    (hlabeled : labeled.nodes[e]? = some ndL) (hdL : ndL.dummy = false) :
    ∃ pm : ProperNode,
      (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).nodes[e]? = some pm ∧ pm.dummy = false := by
  have hsize : ∃ sized, (sizeProperPortsX P exact labeled).nodes[e]? = some sized ∧
      sized.dummy = false := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hlabeled,
      Option.map_some]
    split
    · exact ⟨_, rfl, hdL⟩
    · exact ⟨_, rfl, hdL⟩
  obtain ⟨sized, hsized, hdS⟩ := hsize
  have hlenS : e < (sizeProperPortsX P exact labeled).nodes.length :=
    (List.getElem?_eq_some_iff.mp hsized).1
  have htitle : (titleReservations (sizeProperPortsX P exact labeled)).nodes[e]? =
      some (titleF sized) := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hlenS)]
    simp [List.getElem?_map, hsized]
  have hdT : (titleF sized).dummy = false := by
    rw [(titleF_keys sized).1]; exact hdS
  obtain ⟨extra, hnodes, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact labeled)) P.clusterBorderW
  have hlenT : e < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length := by
    rw [titleReservations_nodes]
    simp only [List.length_append, List.length_map]
    omega
  have hborders : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW).nodes[e]? = some (titleF sized) := by
    rw [hnodes, List.getElem?_append_left hlenT]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).nodes[e]? = some (clearF (titleF sized)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hborders, Option.map_some]
  exact ⟨_, hclear, by rw [(clearF_keys _).1]; exact hdT⟩

/-- Materialization preserves the cluster path at a non-dummy index (copy of
the private `matEndpointClusterPath` in `SideMarkerPathsProof`; the
statement is hook-independent). -/
private theorem XSc8a_matEndpoint {PREP : Proper} {e : Nat}
    {pm : ProperNode}
    (hprep : PREP.nodes[e]? = some pm) (hd : pm.dummy = false) :
    ((materializeDummyPaths PREP).nodes.getD e default).node.clusterPath =
      (PREP.nodes.getD e default).node.clusterPath := by
  have hmat : (materializeDummyPaths PREP).nodes[e]? = some pm := by
    simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx,
      hprep, Option.map_some, hd, Bool.false_eq_true, ↓reduceIte]
  have h1 : (materializeDummyPaths PREP).nodes.getD e default = pm := by
    simp [List.getD_eq_getElem?_getD, hmat]
  have h2 : PREP.nodes.getD e default = pm := by
    simp [List.getD_eq_getElem?_getD, hprep]
  rw [h1, h2]

/-- XS node path equation: `nodePath` unfolds to the cluster path on
border-`0` coordinate nodes of an exact run (replay of `plainNodePathEq`). -/
private def XSc8a_PathEq : Prop :=
  ∀ {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions},
    componentRunX P exact cg labels orderOptions = .ok run →
    ∀ {v : Nat} {nd : ProperNode},
      run.coordinateProper.nodes[v]? = some nd →
      nd.node.border = 0 →
      OrderImpl.nodePath run.coordinateProper v = nd.node.clusterPath

private theorem XSc8a_pathEq : XSc8a_PathEq := by
  intro P exact cg run labels orderOptions hrun v nd hlook hborder
  by_cases hd : nd.dummy = false
  · exact OrderImpl.nodePath_of_nondummy hlook hd
  · have hdT : nd.dummy = true := by
      cases h : nd.dummy with
      | false => exact absurd h hd
      | true => rfl
    obtain ⟨_, normalized, labeled, _, hnorm, hlabels, hcoord, _⟩ :=
      X_componentRun_ranked_source hrun
    have hcoordM : materializeDummyPaths (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P
          exact labeled)) P.clusterBorderW)) = run.coordinateProper := by
      exact hcoord
    have hlookM : (materializeDummyPaths (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P
          exact labeled)) P.clusterBorderW))).nodes[v]? = some nd := by
      rw [hcoordM]; exact hlook
    obtain ⟨mp, hmp, hdm, _, _, _⟩ :=
      materialize_lookup (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)) hlookM
    have hmpT : mp.dummy = true := hdm.symm.trans hdT
    have hpath : nd.node.clusterPath = OrderImpl.nodePath (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P
          exact labeled)) P.clusterBorderW)) v := by
      have h := hlookM
      simp only [materializeDummyPaths, List.getElem?_map, List.getElem?_zipIdx,
        hmp, Option.map_some, hmpT, ↓reduceIte, Option.some.injEq] at h
      rw [← h]
      simp only [Nat.zero_add]
    rw [← hcoordM, hpath]
    have hchains : (materializeDummyPaths (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P
          exact labeled)) P.clusterBorderW))).chains =
        (clearProxyExtents (OrderImpl.addClusterBorders
          (titleReservations (sizeProperPortsX P exact labeled))
          P.clusterBorderW)).chains := rfl
    have hgetM : (materializeDummyPaths (clearProxyExtents
        (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P
          exact labeled)) P.clusterBorderW))).nodes.getD v default = nd := by
      simp [List.getD_eq_getElem?_getD, hlookM]
    have hgetP : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).nodes.getD v default = mp := by
      simp [List.getD_eq_getElem?_getD, hmp]
    unfold OrderImpl.nodePath
    dsimp only
    rw [hgetM, hdT, hgetP, hmpT, hchains]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases hfind : (clearProxyExtents (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW)).chains.find? (fun chain => chain.contains v) with
    | none => rfl
    | some chain =>
      dsimp only
      have hmemC : v ∈ chain := by
        have hfv := List.find?_some hfind
        simpa only [List.contains_iff_mem] using hfv
      have hcmem : chain ∈ (clearProxyExtents (OrderImpl.addClusterBorders
          (titleReservations (sizeProperPortsX P exact labeled))
          P.clusterBorderW)).chains := List.mem_of_find?_eq_some hfind
      have ePREP : (clearProxyExtents (OrderImpl.addClusterBorders
          (titleReservations (sizeProperPortsX P exact labeled))
          P.clusterBorderW)).chains = labeled.chains :=
        (OrderImpl.addClusterBorders_metadata _ _).2.1
      have hcNorm : chain ∈ normalized.chains := by
        have h1 := hcmem
        rw [ePREP, (Labels.addLabelNodes_metadata hlabels).2.2.1] at h1
        exact h1
      obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hcNorm
      have hidxB : idx < cg.edges.length := by
        have hlt := (List.getElem?_eq_some_iff.mp hidx).1
        rwa [normalize_chains_length hnorm] at hlt
      obtain ⟨edge, hedge⟩ : ∃ e, cg.edges[idx]? = some e :=
        ⟨_, List.getElem?_eq_getElem hidxB⟩
      have hfact := (normalize_ok hnorm).2.2 idx hidxB edge hedge
      obtain ⟨hanchor, hrest⟩ := hfact
      have hwf : cg.wellformed = true := (normalize_node_rank_alignment hnorm).2
      have hedgeMem : edge ∈ cg.edges := List.mem_of_getElem? hedge
      have hbounds := RankImpl.wellformed_spec hwf edge hedgeMem
      obtain ⟨htailB, hheadB, _⟩ := hbounds
      by_cases hself : edge.tail = edge.head
      · simp only [hself, ↓reduceIte] at hrest
        have hempty : chain = [] := Option.some.inj (hidx.symm.trans hrest)
        rw [hempty] at hmemC
        simp at hmemC
      · simp only [hself, ↓reduceIte] at hrest
        obtain ⟨chl, hch, _, hhead, hlast, _⟩ := hrest
        have hcc : chl = chain := Option.some.inj (hch.symm.trans hidx)
        have hhead' : chain.head? = some edge.tail := by
          rw [← hcc]; exact hhead
        have hlast' : chain.getLast? = some edge.head := by
          rw [← hcc]; exact hlast
        have ehead : chain.headD v = edge.tail := by
          cases hc : chain with
          | nil => simp [hc] at hmemC
          | cons h t =>
            have h2 := hhead'; rw [hc] at h2
            simp only [List.head?_cons, Option.some.injEq] at h2
            exact h2
        have elast : chain.getLastD v = edge.head := by
          rw [List.getLastD_eq_getLast?, hlast', Option.getD_some]
        obtain ⟨nT, hnT⟩ : ∃ n, cg.nodes[edge.tail]? = some n :=
          ⟨_, List.getElem?_eq_getElem htailB⟩
        have hnormT : normalized.nodes[edge.tail]? =
            some ⟨nT, false, none, false⟩ :=
          normalize_node_record hnorm hnT
        have hlabT : labeled.nodes[edge.tail]? =
            some ⟨nT, false, none, false⟩ :=
          addLabelNodes_untouched_node hlabels hnormT rfl
        obtain ⟨pmT, hprepT, hdT2⟩ := XSc8a_preparedNondummy hlabT rfl
        obtain ⟨nH, hnH⟩ : ∃ n, cg.nodes[edge.head]? = some n :=
          ⟨_, List.getElem?_eq_getElem hheadB⟩
        have hnormH : normalized.nodes[edge.head]? =
            some ⟨nH, false, none, false⟩ :=
          normalize_node_record hnorm hnH
        have hlabH : labeled.nodes[edge.head]? =
            some ⟨nH, false, none, false⟩ :=
          addLabelNodes_untouched_node hlabels hnormH rfl
        obtain ⟨pmH, hprepH, hdH2⟩ := XSc8a_preparedNondummy hlabH rfl
        have hclH : ((materializeDummyPaths (clearProxyExtents
            (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P
              exact labeled)) P.clusterBorderW))).nodes.getD
            (chain.headD v) default).node.clusterPath =
            ((clearProxyExtents (OrderImpl.addClusterBorders
              (titleReservations (sizeProperPortsX P exact labeled))
              P.clusterBorderW)).nodes.getD
              (chain.headD v) default).node.clusterPath := by
          rw [ehead]
          exact XSc8a_matEndpoint hprepT hdT2
        have hclL : ((materializeDummyPaths (clearProxyExtents
            (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P
              exact labeled)) P.clusterBorderW))).nodes.getD
            (chain.getLastD v) default).node.clusterPath =
            ((clearProxyExtents (OrderImpl.addClusterBorders
              (titleReservations (sizeProperPortsX P exact labeled))
              P.clusterBorderW)).nodes.getD
              (chain.getLastD v) default).node.clusterPath := by
          rw [elast]
          exact XSc8a_matEndpoint hprepH hdH2
        rw [hclH, hclL]

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Exact side record: a side marker of the exact bordered graph is already
a coordinate node (copy of `coordinateGraph_side_record` in
`GroupWidthFacts`). -/
private theorem XSc8a_side_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).nodes[index]? =
        some node)
    (hdummy : node.dummy = false)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    (coordinateGraphX P exact source).nodes[index]? = some node := by
  have hnotProxy :
      (node.node.border == -2 || node.node.border == 2) = false := by
    rcases hborder with h | h <;> rw [h] <;> decide
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
        some node := by
    simp only [clearProxyExtents, List.getElem?_map, hnode, Option.map_some]
    simp only [hnotProxy, Bool.false_eq_true, ↓reduceIte]
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some,
    Nat.zero_add, hdummy, Bool.false_eq_true, ↓reduceIte]

/-- Exact rank pair: a bracketed rank carries the declaration's marker pair
(copy of `coordinateGraph_rank_pair` in `GroupWidthFacts`). -/
private theorem XSc8a_rank_pair (P : Params) (exact : List Nat) (source : Proper)
    (haligned : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length)
    {top bottom : ProperNode × Nat}
    (htop : top ∈ (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx)
    (hborder : top.1.node.border = -2)
    (hbottom : ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom)
    {rank : Nat}
    (hlo : (rk (titleReservations (sizeProperPortsX P exact source)).rank top.2).toNat ≤ rank)
    (hhi : rank ≤ (rk (titleReservations (sizeProperPortsX P exact source)).rank bottom.2).toNat) :
    ∃ left right : Nat,
      (coordinateGraphX P exact source).nodes[left]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := -1 }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).nodes[right]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := 1
                loopExtent := top.1.node.loopExtent }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).rank[left]? = some (rank : Int) ∧
      (coordinateGraphX P exact source).rank[right]? = some (rank : Int) := by
  obtain ⟨left, right, hl, hr, hrl, hrr⟩ :=
    addClusterBorders_rank_pair (titleReservations (sizeProperPortsX P exact source))
      P.clusterBorderW haligned htop hborder hbottom hlo hhi
  refine ⟨left, right, XSc8a_side_record hl rfl (Or.inl rfl),
    XSc8a_side_record hr rfl (Or.inr rfl), ?_, ?_⟩
  · exact hrl
  · exact hrr

/-- XS anchor cover: the titled top/bottom pair plus the member-rank bounds
(X mirror of `SideMarkerAnchorCover`; the single residual behind
`XS_C8a_BracketMarkersAtRank`). -/
private def XSc8a_AnchorCover (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl : Nat} {low high : Nat} {lowNd highNd : ProperNode},
      run.proper.nodes[low]? = some lowNd →
      lowNd.node.clusterPath.contains decl = true →
      run.proper.nodes[high]? = some highNd →
      highNd.node.clusterPath.contains decl = true →
      ∃ (labeled : Proper),
        coordinateGraphX P (exactDecls exactIds inp) labeled = run.coordinateProper ∧
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.length =
          (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank.length ∧
        ∃ (top bottom : ProperNode × Nat),
          top ∈ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx ∧
          top.1.node.border = -2 ∧
          top.1.node.clusterPath.getLast? = some decl ∧
          ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
            (fun entry => entry.1.node.border == 2 &&
              entry.1.node.clusterPath == top.1.node.clusterPath) =
              some bottom) ∧
          (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2).toNat ≤
            (rk run.proper.rank low).toNat ∧
          (rk run.proper.rank high).toNat ≤
            (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank
              bottom.2).toNat

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Exact candidate bottom colocation (replay of `foreignBottomInCandidate`
via the public exact bottom-find lemmas). -/
private theorem XSc8a_bottomInCandidate {P : Params} {inp : Input} {o : Options}
    {exactIds : List String}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat}
    {u : Nat} {uNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hbU : uNode.border = -2) :
    ∃ (iB : Nat) (bNode : Node),
      (componentCandidate graph comp candidate).nodes[iB]? = some bNode ∧
      bNode.border = 2 ∧ bNode.decl = uNode.decl ∧
      bNode.clusterPath = uNode.clusterPath := by
  obtain ⟨bottom, hfindDecl⟩ := X_componentRun_cg_bottom_find h0 h hlines hcomp hu hbU
  have hfindPath : ((componentCandidate graph comp candidate).nodes.zipIdx.find? fun entry =>
      entry.1.border == 2 && entry.1.clusterPath == uNode.clusterPath) = some bottom := by
    rw [X_bottom_lookup_keys h0 h hu hbU]; exact hfindDecl
  have hlookup := List.mem_zipIdx_iff_getElem?.mp
    (List.mem_of_find?_eq_some hfindPath)
  have hpred := List.find?_some hfindPath
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  obtain ⟨hborder, hpath⟩ := hpred
  have hpredDecl := List.find?_some hfindDecl
  simp only [Bool.and_eq_true, beq_iff_eq] at hpredDecl
  obtain ⟨_, hdecl⟩ := hpredDecl
  exact ⟨bottom.2, bottom.1, hlookup, hborder, hdecl, hpath⟩

/-- XS rank-pair anchors: two executed group declarations each carry a
titled top anchor and a path-matched bottom anchor (replay of
`foreignRankPairAnchors`). -/
private def XSc8a_RankAnchors (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border = -2 → uNode.decl ≠ wNode.decl →
    ∃ (labeled : Proper) (rr : RankImpl.RankResult),
      coordinateGraphX P (exactDecls exactIds inp) labeled = run.coordinateProper ∧
      labeled.nodes.length = labeled.rank.length ∧
      NodeKeys (componentCandidate graph comp candidate) labeled ∧
      rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
        .ok rr ∧
      (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
        labeled.rank[index]? = some rank) ∧
      (∀ (index : Nat) (node : Node),
        (componentCandidate graph comp candidate).nodes[index]? = some node →
          labeled.nodes[index]? = some ⟨node, false, none, false⟩) ∧
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.length =
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank.length ∧
      ∃ (topU botU : ProperNode × Nat),
        topU ∈ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx ∧
        topU.1.node.border = -2 ∧
        topU.1.node.clusterPath.getLast? = some uNode.decl ∧
        ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? (fun entry =>
          entry.1.node.border == 2 &&
            entry.1.node.clusterPath == topU.1.node.clusterPath) = some botU) ∧
      ∃ (topW botW : ProperNode × Nat),
        topW ∈ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx ∧
        topW.1.node.border = -2 ∧
        topW.1.node.clusterPath.getLast? = some wNode.decl ∧
        ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? (fun entry =>
          entry.1.node.border == 2 &&
            entry.1.node.clusterPath == topW.1.node.clusterPath) = some botW)

private theorem XSc8a_rankAnchors {exactIds : List String}
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {u w : Nat} {uNode wNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hw : (componentCandidate graph comp candidate).nodes[w]? = some wNode)
    (hbU : uNode.border = -2) (hbW : wNode.border = -2) (_hne : uNode.decl ≠ wNode.decl) :
    ∃ (labeled : Proper) (rr : RankImpl.RankResult),
      coordinateGraphX P (exactDecls exactIds inp) labeled = run.coordinateProper ∧
      labeled.nodes.length = labeled.rank.length ∧
      NodeKeys (componentCandidate graph comp candidate) labeled ∧
      rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
        .ok rr ∧
      (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
        labeled.rank[index]? = some rank) ∧
      (∀ (index : Nat) (node : Node),
        (componentCandidate graph comp candidate).nodes[index]? = some node →
          labeled.nodes[index]? = some ⟨node, false, none, false⟩) ∧
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.length =
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank.length ∧
      ∃ (topU botU : ProperNode × Nat),
        topU ∈ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx ∧
        topU.1.node.border = -2 ∧
        topU.1.node.clusterPath.getLast? = some uNode.decl ∧
        ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? (fun entry =>
          entry.1.node.border == 2 &&
            entry.1.node.clusterPath == topU.1.node.clusterPath) = some botU) ∧
      ∃ (topW botW : ProperNode × Nat),
        topW ∈ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx ∧
        topW.1.node.border = -2 ∧
        topW.1.node.clusterPath.getLast? = some wNode.decl ∧
        ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? (fun entry =>
          entry.1.node.border == 2 &&
            entry.1.node.clusterPath == topW.1.node.clusterPath) = some botW) := by
  obtain ⟨rr, _, labeled, hrr, hn, hl, hcoord, _⟩ :=
    X_componentRun_ranked_source hrun
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hlenEq := X_titleReservations_node_rank_alignment (exact := exactDecls exactIds inp) P haligned
  have hkeys : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have hranks : ∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
      labeled.rank[index]? = some rank := by
    intro index rank hrank
    rw [(Labels.addLabelNodes_metadata hl).2.1]
    exact normalize_rank_record hn hrank
  have hnodeRec : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
        labeled.nodes[index]? = some (⟨node, false, none, false⟩ : ProperNode) :=
    fun index node hnode =>
      addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  obtain ⟨boxU, _, hpathU⟩ := X_cg_group_box h0 h hu hbU
  obtain ⟨boxW, _, hpathW⟩ := X_cg_group_box h0 h hw hbW
  obtain ⟨iBU, bU, hBUlook, hBUbord, _hBUdecl, hBUpath⟩ :=
    XSc8a_bottomInCandidate h0 h hlines hcomp hu hbU
  obtain ⟨iBW, bW, hBWlook, hBWbord, _hBWdecl, hBWpath⟩ :=
    XSc8a_bottomInCandidate h0 h hlines hcomp hw hbW
  have hlabU : labeled.nodes[u]? =
      some (⟨uNode, false, none, false⟩ : ProperNode) :=
    hnodeRec u uNode hu
  have hlabW : labeled.nodes[w]? =
      some (⟨wNode, false, none, false⟩ : ProperNode) :=
    hnodeRec w wNode hw
  have hlabBU : labeled.nodes[iBU]? =
      some (⟨bU, false, none, false⟩ : ProperNode) :=
    hnodeRec iBU bU hBUlook
  have hlabBW : labeled.nodes[iBW]? =
      some (⟨bW, false, none, false⟩ : ProperNode) :=
    hnodeRec iBW bW hBWlook
  have htopU : (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[u]? =
      some (titleF (⟨uNode, false, none, false⟩ : ProperNode)) :=
    X_titled_marker_record (exact := exactDecls exactIds inp) hlabU (Or.inl hbU)
  have htopW : (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[w]? =
      some (titleF (⟨wNode, false, none, false⟩ : ProperNode)) :=
    X_titled_marker_record (exact := exactDecls exactIds inp) hlabW (Or.inl hbW)
  have hbotTU : (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[iBU]? =
      some (titleF (⟨bU, false, none, false⟩ : ProperNode)) :=
    X_titled_marker_record (exact := exactDecls exactIds inp) hlabBU (Or.inr hBUbord)
  have hbotTW : (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[iBW]? =
      some (titleF (⟨bW, false, none, false⟩ : ProperNode)) :=
    X_titled_marker_record (exact := exactDecls exactIds inp) hlabBW (Or.inr hBWbord)
  have htopUmem : (titleF (⟨uNode, false, none, false⟩ : ProperNode), u) ∈
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopU
  have htopWmem : (titleF (⟨wNode, false, none, false⟩ : ProperNode), w) ∈
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopW
  have hbUtop : (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.border
      = -2 := by
    rw [(titleF_keys _).2.1]; exact hbU
  have hbWtop : (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.border
      = -2 := by
    rw [(titleF_keys _).2.1]; exact hbW
  have hlastTopU : (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath.getLast?
      = some uNode.decl := by
    rw [show (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath
      = uNode.clusterPath from (titleF_keys _).2.2.1,
      hpathU, List.getLast?_append]
    simp
  have hlastTopW : (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath.getLast?
      = some wNode.decl := by
    rw [show (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath
      = wNode.clusterPath from (titleF_keys _).2.2.1,
      hpathW, List.getLast?_append]
    simp
  have hmemBU : (titleF (⟨bU, false, none, false⟩ : ProperNode), iBU) ∈
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hbotTU
  have hmemBW : (titleF (⟨bW, false, none, false⟩ : ProperNode), iBW) ∈
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hbotTW
  have hpredBU : (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
      entry.1.node.clusterPath ==
        (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath)
      (titleF (⟨bU, false, none, false⟩ : ProperNode), iBU) = true := by
    have e1 : (titleF (⟨bU, false, none, false⟩ : ProperNode)).node.border
        = 2 := by
      rw [(titleF_keys _).2.1]; exact hBUbord
    have e2 : (titleF (⟨bU, false, none, false⟩ : ProperNode)).node.clusterPath
        = (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath := by
      rw [show (titleF (⟨bU, false, none, false⟩ : ProperNode)).node.clusterPath
        = bU.clusterPath from (titleF_keys _).2.2.1,
        show (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath
        = uNode.clusterPath from (titleF_keys _).2.2.1, hBUpath]
    show ((titleF (⟨bU, false, none, false⟩ : ProperNode)).node.border == 2 &&
      (titleF (⟨bU, false, none, false⟩ : ProperNode)).node.clusterPath ==
        (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath)
      = true
    simp [e1, e2]
  have hpredBW : (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
      entry.1.node.clusterPath ==
        (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath)
      (titleF (⟨bW, false, none, false⟩ : ProperNode), iBW) = true := by
    have e1 : (titleF (⟨bW, false, none, false⟩ : ProperNode)).node.border
        = 2 := by
      rw [(titleF_keys _).2.1]; exact hBWbord
    have e2 : (titleF (⟨bW, false, none, false⟩ : ProperNode)).node.clusterPath
        = (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath := by
      rw [show (titleF (⟨bW, false, none, false⟩ : ProperNode)).node.clusterPath
        = bW.clusterPath from (titleF_keys _).2.2.1,
        show (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath
        = wNode.clusterPath from (titleF_keys _).2.2.1, hBWpath]
    show ((titleF (⟨bW, false, none, false⟩ : ProperNode)).node.border == 2 &&
      (titleF (⟨bW, false, none, false⟩ : ProperNode)).node.clusterPath ==
        (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath)
      = true
    simp [e1, e2]
  obtain ⟨botU, hbotU⟩ : ∃ x,
      ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
        (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
          entry.1.node.clusterPath ==
            (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath))
        = some x := by
    cases h : ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
        (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
          entry.1.node.clusterPath ==
            (titleF (⟨uNode, false, none, false⟩ : ProperNode)).node.clusterPath)) with
    | none =>
      have hnone := (List.find?_eq_none.mp h) _ hmemBU
      simp [hpredBU] at hnone
    | some x => exact ⟨x, rfl⟩
  obtain ⟨botW, hbotW⟩ : ∃ x,
      ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
        (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
          entry.1.node.clusterPath ==
            (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath))
        = some x := by
    cases h : ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find?
        (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
          entry.1.node.clusterPath ==
            (titleF (⟨wNode, false, none, false⟩ : ProperNode)).node.clusterPath)) with
    | none =>
      have hnone := (List.find?_eq_none.mp h) _ hmemBW
      simp [hpredBW] at hnone
    | some x => exact ⟨x, rfl⟩
  exact ⟨labeled, rr, hcoord, haligned, hkeys, hrr, hranks, hnodeRec, hlenEq,
    (titleF (⟨uNode, false, none, false⟩ : ProperNode), u), botU,
    htopUmem, hbUtop, hlastTopU, hbotU,
    (titleF (⟨wNode, false, none, false⟩ : ProperNode), w), botW,
    htopWmem, hbWtop, hlastTopW, hbotW⟩

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- A non-proxy record of the exact final run is the same coordinate record
(copy of `coordinateProper_of_proper_nonsynthetic` in
`SideMarkerFactsProof`). -/
private theorem XSc8a_proper_nonsynthetic {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd)
    (hb : nd.node.border ≠ -2 ∧ nd.node.border ≠ 2) :
    run.coordinateProper.nodes[v]? = some nd := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨_, _, hlen, _, hpresAll, hpresSame⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hq0v : q0.nodes[v]? = some nd := by rw [← hnodes]; exact hv
  have hlenv : v < run.coordinateProper.nodes.length := by
    have hlt : v < q0.nodes.length := (List.getElem?_eq_some_iff.mp hq0v).1
    omega
  obtain ⟨nd', hnd'⟩ : ∃ nd', run.coordinateProper.nodes[v]? = some nd' :=
    ⟨_, List.getElem?_eq_getElem hlenv⟩
  obtain ⟨nd'', hnd'', _, hborderEq, _⟩ := hpresAll v nd' hnd'
  have hnn : nd'' = nd := Option.some.inj (hnd''.symm.trans hq0v)
  have hbeq : nd'.node.border = nd.node.border := by rw [← hborderEq, hnn]
  have hnd'nproxy : ¬ (nd'.node.border = -2 ∨ nd'.node.border = 2) := by
    rw [hbeq]
    exact fun h => h.elim hb.1 hb.2
  obtain ⟨hqSame, _⟩ := hpresSame v nd' hnd' hnd'nproxy
  have hsame : nd' = nd := Option.some.inj (hqSame.symm.trans hq0v)
  rw [hsame] at hnd'
  exact hnd'

/-- An exact side marker keeps its cross-coordinate centre through proxy
widths (copy of `coordinateXs_of_proper_marker` in
`SideMarkerFactsProof`). -/
private theorem XSc8a_xs_marker {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {nd : ProperNode} (hv : run.proper.nodes[v]? = some nd)
    (hb : nd.node.border = -1 ∨ nd.node.border = 1) :
    run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  have hnproxy : nd.node.border ≠ -2 ∧ nd.node.border ≠ 2 := by
    rcases hb with h | h <;> constructor <;> intro hc <;> omega
  have hcp := XSc8a_proper_nonsynthetic hrun hv hnproxy
  exact (XSc8a_border_record hrun hcp hb).2

/-- Every exact final node has nonnegative placed width (copy of
`proper_nodeW_nonneg` in `SideMarkerFactsProof`). -/
private theorem XSc8a_nodeW_nonneg {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} (hv : v < run.proper.nodes.length) :
    0 ≤ RouteImpl.nodeW run.proper v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hroute, _, _⟩ :=
    componentRunX_spec hrun
  have hok := (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, hsz, _, _, _⟩ := RouteImpl.layersOk_spec hok
  exact (hsz v hv).1

/-- Every exact cross-coordinate centre is nonnegative (copy of
`fbs_coordinate_centers_nonneg` in `ForeignBorderSpansProof`). -/
private theorem XSc8a_centers_nonneg {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run) :
    ∀ v : Nat, 0 ≤ run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨-, -, -, -, hcase⟩ := crossCoordsClusterWith_spec hcross
  rcases hcase with ⟨-, hxs⟩ | ⟨x0, x1, x2, x3, hpass, hxs⟩
  · rw [hxs]
    intro v
    simp
  · rw [hxs]
    unfold CoordsImpl.crossClusterPasses at hpass
    split at hpass
    · simp at hpass
    · next _ _ =>
      split at hpass
      · simp at hpass
      · dsimp only at hpass
        split at hpass
        · simp at hpass
        · next y0 h0 =>
          split at hpass
          · simp at hpass
          · next y1 h1 =>
            split at hpass
            · simp at hpass
            · next y2 h2 =>
              split at hpass
              · simp at hpass
              · next y3 h3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hpass
                obtain ⟨rfl, rfl, rfl, rfl⟩ := hpass
                have hsz0 : y0.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h0).1
                have hsz1 : y1.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h1).1
                have hsz2 : y2.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h2).1
                have hsz3 : y3.size = run.coordinateProper.nodes.length :=
                  (fbs_cluster_pass_nonneg h3).1
                have hnn0 := (fbs_cluster_pass_nonneg h0).2
                have hnn1 := (fbs_cluster_pass_nonneg h1).2
                have hnn2 := (fbs_cluster_pass_nonneg h2).2
                have hnn3 := (fbs_cluster_pass_nonneg h3).2
                obtain ⟨o0, o1, o2, o3⟩ := fbs_balanceOffsets_nonneg y0 y1 y2 y3
                intro v
                by_cases hv : v < run.coordinateProper.nodes.length
                · rw [CoordsImpl.balanceValues_getD _ _ _ _ _ hv]
                  exact fbs_bal4_nonneg (by have := hnn0 v (by omega); omega)
                    (by have := hnn1 v (by omega); omega)
                    (by have := hnn2 v (by omega); omega)
                    (by have := hnn3 v (by omega); omega)
                · have hlen : (CoordsImpl.balanceValues run.coordinateProper.nodes.length y0 y1 y2
                        y3).length = run.coordinateProper.nodes.length := by
                    simp [CoordsImpl.balanceValues]
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
                  exact Int.le_refl 0

/-- An element strictly between two members of an infix `S` of a nodup list
`l` is itself a member of `S` (copy of the private
`smf_mem_of_between_infix` in `SideMarkerFactsProof`). -/
private theorem XSc8a_mem_of_between_infix {α : Type} {l S : List α} {a b c : α}
    {li vi ri : Nat}
    (hnd : l.Nodup) (h : S.IsInfix l)
    (ha : a ∈ S) (hb : b ∈ S)
    (hli : l[li]? = some a) (hvi : l[vi]? = some c) (hri : l[ri]? = some b)
    (hlt : li < vi) (hgt : vi < ri) : c ∈ S := by
  obtain ⟨s, t, hs⟩ := h
  subst hs
  have hnd' := List.nodup_append.mp hnd
  have hsS : ∀ x ∈ s, ∀ y ∈ S, x ≠ y :=
    (List.nodup_append.mp hnd'.1).2.2
  have hSt : ∀ x ∈ s ++ S, ∀ y ∈ t, x ≠ y := hnd'.2.2
  have hlen : (s ++ S).length = s.length + S.length := List.length_append ..
  have hliS : s.length ≤ li ∧ li < (s ++ S).length := by
    constructor
    · by_cases hle : s.length ≤ li
      · exact hle
      · have hlt' : li < s.length := by omega
        have hlook : ((s ++ S) ++ t)[li]? = s[li]? := by
          rw [List.getElem?_append_left (by omega),
            List.getElem?_append_left hlt']
        rw [hlook] at hli
        exact (hsS a (List.mem_of_getElem? hli) a ha rfl).elim
    · by_cases hle : (s ++ S).length ≤ li
      · have hlook : ((s ++ S) ++ t)[li]? = t[li - (s ++ S).length]? :=
          List.getElem?_append_right hle
        rw [hlook] at hli
        exact (hSt a (List.mem_append_right s ha) a (List.mem_of_getElem? hli)
          rfl).elim
      · have hlt' : li < (s ++ S).length := by omega
        exact hlt'
  have hriS : s.length ≤ ri ∧ ri < (s ++ S).length := by
    constructor
    · by_cases hle : s.length ≤ ri
      · exact hle
      · have hlt' : ri < s.length := by omega
        have hlook : ((s ++ S) ++ t)[ri]? = s[ri]? := by
          rw [List.getElem?_append_left (by omega),
            List.getElem?_append_left hlt']
        rw [hlook] at hri
        exact (hsS b (List.mem_of_getElem? hri) b hb rfl).elim
    · by_cases hle : (s ++ S).length ≤ ri
      · have hlook : ((s ++ S) ++ t)[ri]? = t[ri - (s ++ S).length]? :=
          List.getElem?_append_right hle
        rw [hlook] at hri
        exact (hSt b (List.mem_append_right s hb) b (List.mem_of_getElem? hri)
          rfl).elim
      · have hlt' : ri < (s ++ S).length := by omega
        exact hlt'
  have hviS : s.length ≤ vi ∧ vi < (s ++ S).length := by
    constructor <;> omega
  have hlook : ((s ++ S) ++ t)[vi]? = S[vi - s.length]? := by
    rw [List.getElem?_append_left hviS.2,
      List.getElem?_append_right (by omega : s.length ≤ vi)]
  rw [hlook] at hvi
  exact List.mem_of_getElem? hvi

/-- A layer looked up by its own index belongs to the layer list (copy of
the public `layer_getD_mem` in `SideMarkerFactsProof`). -/
private theorem XSc8a_layer_getD_mem {run : Run}
    {k : Nat} (hk : k < run.layers.length) :
    run.layers.getD k [] ∈ run.layers := by
  have hkk : run.layers[k]? = some run.layers[k] := List.getElem?_eq_getElem hk
  have heq : run.layers.getD k [] = run.layers[k] := by
    simp only [List.getD_eq_getElem?_getD, hkk, Option.getD_some]
  rw [heq]
  exact List.getElem_mem hk

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- XS member-rank bounds: member ranks of a foreign cluster lie between its
titled top and bottom marker ranks (X mirror of `ForeignMemberRankBounds`;
the single residual behind `XS_C8a_ForeignClusterRankSpans`). -/
private def XSc8a_MemberBounds (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border = -2 → uNode.decl ≠ wNode.decl →
    ∀ {labeled : Proper} {rr : RankImpl.RankResult},
    coordinateGraphX P (exactDecls exactIds inp) labeled = run.coordinateProper →
    labeled.nodes.length = labeled.rank.length →
    NodeKeys (componentCandidate graph comp candidate) labeled →
    rankWithBudget (Compound.rankingGraph (componentCandidate graph comp candidate)) =
      .ok rr →
    (∀ (index : Nat) (rank : Int), rr.ranks[index]? = some rank →
      labeled.rank[index]? = some rank) →
    (∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
        labeled.nodes[index]? = some ⟨node, false, none, false⟩) →
    ∀ {topU botU topW botW : ProperNode × Nat},
    topU ∈ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx →
    topU.1.node.border = -2 →
    topU.1.node.clusterPath.getLast? = some uNode.decl →
    ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
      entry.1.node.border == 2 &&
        entry.1.node.clusterPath == topU.1.node.clusterPath) = some botU →
    topW ∈ (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx →
    topW.1.node.border = -2 →
    topW.1.node.clusterPath.getLast? = some wNode.decl →
    ((titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes.zipIdx.find? fun entry =>
      entry.1.node.border == 2 &&
        entry.1.node.clusterPath == topW.1.node.clusterPath) = some botW →
    ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topU.2).toNat :
      Nat) : Int) ≤
      (((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botU.2).toNat :
        Nat) : Int)) ∧
    ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topW.2).toNat :
      Nat) : Int) ≤
      (((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botW.2).toNat :
        Nat) : Int)) ∧
    (∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains uNode.decl = true →
      ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topU.2).toNat :
        Nat) : Int) ≤ rk run.proper.rank v ∧
      rk run.proper.rank v ≤
        ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botU.2).toNat :
          Nat) : Int)))) ∧
    (∀ v, v < run.proper.nodes.length →
      (run.proper.nodes.getD v default).node.clusterPath.contains wNode.decl = true →
      ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topW.2).toNat :
        Nat) : Int) ≤ rk run.proper.rank v ∧
      rk run.proper.rank v ≤
        ((((rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botW.2).toNat :
          Nat) : Int))))

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- XS bracket markers at rank, from the anchor-cover residual (replay of
`bracketMarkersAtRank`). -/
theorem XS_C8a_BracketMarkersAtRank_of_anchor {exactIds : List String}
    (hgrp : XSc8a_AnchorCover exactIds) :
    XS_C8a_BracketMarkersAtRank exactIds := by
  intro P inp o lines measured graph0 graph h0 h hlines hwf hfp comp hcomp
    candidate run labels orderOptions hrun decl r low high lowNd highNd
    hlow hcontainLow hlerk hhigh hcontainHigh hhrer
  obtain ⟨labeled, hc, haligned, top, bottom, htop, hbordTop, hlastTop, hfindBot,
    hloBnd, hhiBnd⟩ :=
    hgrp h0 h hlines hwf hfp hcomp hrun hlow hcontainLow hhigh hcontainHigh
  have hlo : (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank top.2).toNat ≤ r :=
    Nat.le_trans hloBnd hlerk
  have hhi : r ≤ (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank bottom.2).toNat :=
    Nat.le_trans hhrer hhiBnd
  obtain ⟨left, right, hleft, hright, hleftRank, hrightRank⟩ :=
    XSc8a_rank_pair P (exactDecls exactIds inp) labeled haligned htop hbordTop
      hfindBot (rank := r) hlo hhi
  rw [hc] at hleft hright hleftRank hrightRank
  refine ⟨left, right, _, _, hleft, rfl, hlastTop, ?_, hright, rfl, hlastTop, ?_⟩ <;>
    simp only [rk, List.getD_eq_getElem?_getD, hleftRank, hrightRank,
      Option.getD_some]

/-- XS foreign cluster rank spans, from proved rank anchors and the
member-bounds residual (replay of `foreignClusterRankSpans`). -/
theorem XS_C8a_ForeignClusterRankSpans_of_bounds {exactIds : List String}
    (hmem : XSc8a_MemberBounds exactIds) :
    XS_C8a_ForeignClusterRankSpans exactIds := by
  intro P inp o lines measured graph0 graph h0 h hlines hwf hfp comp hcomp
    candidate run labels orderOptions hrun
    u w uNode wNode hu hw hbU hbW hne
  obtain ⟨labeled, _rr, hcoord, halignedL, hkeys, hrr, hranks, hrecords, haligned, hU⟩ :=
    XSc8a_rankAnchors h0 h hlines hcomp hrun hu hw hbU hbW hne
  obtain ⟨topU, botU, htopU, hbUtop, hlastU, hbotU, hW⟩ := hU
  obtain ⟨topW, botW, htopW, hbWtop, hlastW, hbotW⟩ := hW
  have hpairU : ∀ {rank : Nat},
      (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topU.2).toNat ≤ rank →
      rank ≤ (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botU.2).toNat →
      ∃ (mLU mRU : Nat) (nLU nRU : ProperNode),
        run.coordinateProper.nodes[mLU]? = some nLU ∧
        nLU.node.border = -1 ∧ nLU.node.clusterPath.getLast? = some uNode.decl ∧
        rk run.coordinateProper.rank mLU = (rank : Int) ∧
        run.coordinateProper.nodes[mRU]? = some nRU ∧
        nRU.node.border = 1 ∧ nRU.node.clusterPath.getLast? = some uNode.decl ∧
        rk run.coordinateProper.rank mRU = (rank : Int) := by
    intro rank hlo hhi
    obtain ⟨lU, rU, hLU, hRU, hrlU, hrrU⟩ :=
      XSc8a_rank_pair P (exactDecls exactIds inp) labeled haligned htopU hbUtop hbotU hlo hhi
    rw [hcoord] at hLU hRU hrlU hrrU
    have hrkLU : rk run.coordinateProper.rank lU = (rank : Int) := by
      simp only [rk, List.getD_eq_getElem?_getD, hrlU, Option.getD_some]
    have hrkRU : rk run.coordinateProper.rank rU = (rank : Int) := by
      simp only [rk, List.getD_eq_getElem?_getD, hrrU, Option.getD_some]
    exact ⟨lU, rU, _, _, hLU, rfl, hlastU, hrkLU, hRU, rfl, hlastU, hrkRU⟩
  have hpairW : ∀ {rank : Nat},
      (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topW.2).toNat ≤ rank →
      rank ≤ (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botW.2).toNat →
      ∃ (mLW mRW : Nat) (nLW nRW : ProperNode),
        run.coordinateProper.nodes[mLW]? = some nLW ∧
        nLW.node.border = -1 ∧ nLW.node.clusterPath.getLast? = some wNode.decl ∧
        rk run.coordinateProper.rank mLW = (rank : Int) ∧
        run.coordinateProper.nodes[mRW]? = some nRW ∧
        nRW.node.border = 1 ∧ nRW.node.clusterPath.getLast? = some wNode.decl ∧
        rk run.coordinateProper.rank mRW = (rank : Int) := by
    intro rank hlo hhi
    obtain ⟨lW, rW, hLW, hRW, hrlW, hrrW⟩ :=
      XSc8a_rank_pair P (exactDecls exactIds inp) labeled haligned htopW hbWtop hbotW hlo hhi
    rw [hcoord] at hLW hRW hrlW hrrW
    have hrkLW : rk run.coordinateProper.rank lW = (rank : Int) := by
      simp only [rk, List.getD_eq_getElem?_getD, hrlW, Option.getD_some]
    have hrkRW : rk run.coordinateProper.rank rW = (rank : Int) := by
      simp only [rk, List.getD_eq_getElem?_getD, hrrW, Option.getD_some]
    exact ⟨lW, rW, _, _, hLW, rfl, hlastW, hrkLW, hRW, rfl, hlastW, hrkRW⟩
  obtain ⟨hordU, hordW, hmemU, hmemW⟩ :=
    hmem h0 h hlines hwf hfp hcomp hrun hu hw hbU hbW hne hcoord halignedL
      hkeys hrr hranks hrecords htopU hbUtop hlastU hbotU htopW hbWtop hlastW hbotW
  refine ⟨_, _, _, _, hordU, hordW, hmemU, hmemW, ?_, ?_⟩
  · intro r hrU hrW
    have h0r : 0 ≤ r := by omega
    have hrcast : ((r.toNat : Nat) : Int) = r := Int.toNat_of_nonneg h0r
    have hlo : (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topU.2).toNat ≤
        r.toNat := by omega
    have hhi : r.toNat ≤
        (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botU.2).toNat := by omega
    obtain ⟨mL, mR, nL, nR, hL, hbL, hoL, hrL, hR, hbR, hoR, hrR⟩ :=
      hpairU hlo hhi
    refine ⟨mL, mR, nL, nR, hL, hbL, hoL, ?_, hR, hbR, hoR, ?_⟩
    · rw [← hrcast]; exact hrL
    · rw [← hrcast]; exact hrR
  · intro r hrU hrW
    have h0r : 0 ≤ r := by omega
    have hrcast : ((r.toNat : Nat) : Int) = r := Int.toNat_of_nonneg h0r
    have hlo : (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topW.2).toNat ≤
        r.toNat := by omega
    have hhi : r.toNat ≤
        (rk (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botW.2).toNat := by omega
    obtain ⟨mL, mR, nL, nR, hL, hbL, hoL, hrL, hR, hbR, hoR, hrR⟩ :=
      hpairW hlo hhi
    refine ⟨mL, mR, nL, nR, hL, hbL, hoL, ?_, hR, hbR, hoR, ?_⟩
    · rw [← hrcast]; exact hrL
    · rw [← hrcast]; exact hrR

end PipelineImpl
end Layered
end Elegant

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- XS positions disjoint: distinct plain nodes of one exact component run
have disjoint frame rectangles (replay of the private
`X_componentRun_positions_disjoint` in `ExactFlatC2`). -/
theorem XS_C8a_PositionsDisjoint_of_run {exactIds : List String} :
    XS_C8a_PositionsDisjoint exactIds := by
  intro P inp o lines measured graph0 graph h0 h comp hcomp candidate run
    labels orderOptions hrun u v nodeU nodeV hnodeU hnodeV hbU hbV hne
  let cg := componentCandidate graph comp candidate
  have hu' : u < cg.nodes.length := (List.getElem?_eq_some_iff.mp hnodeU).1
  have hv' : v < cg.nodes.length := (List.getElem?_eq_some_iff.mp hnodeV).1
  have hcovered := componentRunX_original_nodes_covered hrun
  have huP : u < run.proper.nodes.length := hcovered u hu'
  have hvP : v < run.proper.nodes.length := hcovered v hv'
  obtain ⟨actualU, hcoordU, hpropU, hbU0, _, _, _⟩ :=
    XSc8a_original_plain_record hrun hnodeU hbU
  obtain ⟨actualV, hcoordV, hpropV, hbV0, _, _, _⟩ :=
    XSc8a_original_plain_record hrun hnodeV hbV
  have hgetU : cg.nodes.getD u default = nodeU := by
    rw [List.getD_eq_getElem?_getD, hnodeU]
    rfl
  have hgetV : cg.nodes.getD v default = nodeV := by
    rw [List.getD_eq_getElem?_getD, hnodeV]
    rfl
  have hframeU : frameRect P cg run u = nodeRect cg run u := by
    unfold frameRect
    simp only []
    rw [hgetU, hbU]
    rfl
  have hframeV : frameRect P cg run v = nodeRect cg run v := by
    unfold frameRect
    simp only []
    rw [hgetV, hbV]
    rfl
  rw [hframeU, hframeV]
  have hrectU : nodeRect cg run u =
      ⟨run.xs.getD u 0 - Int.fdiv actualU.node.w 2, run.ys.getD u 0,
        actualU.node.w, actualU.node.h⟩ := by
    simp [nodeRect, hpropU]
  have hrectV : nodeRect cg run v =
      ⟨run.xs.getD v 0 - Int.fdiv actualV.node.w 2, run.ys.getD v 0,
        actualV.node.w, actualV.node.h⟩ := by
    simp [nodeRect, hpropV]
  obtain ⟨_, _, _, q0, _, _, _, hord, _, hproxy, hdrop, hroute, _, _⟩ :=
    componentRunX_spec hrun
  obtain ⟨ord, hordOk, hordLayers⟩ := hord
  have hlayersOk : RouteImpl.layersOk run.proper run.layers = true :=
    (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, hrank, hqlen, _, _, _⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes, hqlen]
  have huC : u < run.coordinateProper.nodes.length := by omega
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact hrank
  have hcov := (RouteImpl.layersOk_spec hlayersOk).2.2.2.1
  obtain ⟨lU, hlyU, huIn, hrkU⟩ := hcov u huP
  obtain ⟨lV, hlyV, hvIn, hrkV⟩ := hcov v hvP
  let rU : Nat := (rk run.proper.rank u).toNat
  let rV : Nat := (rk run.proper.rank v).toNat
  have hrUdef : rU = (rk run.proper.rank u).toNat := rfl
  have hrVdef : rV = (rk run.proper.rank v).toNat := rfl
  have hrkU' : rk run.proper.rank u = (rU : Int) := by
    have h := Int.toNat_of_nonneg hrkU
    exact h.symm
  have hrkV' : rk run.proper.rank v = (rV : Int) := by
    have h := Int.toNat_of_nonneg hrkV
    exact h.symm
  have hrkCoordU : rk run.coordinateProper.rank u = (rU : Int) := by
    rw [← hranks]; exact hrkU'
  have hrkCoordV : rk run.coordinateProper.rank v = (rV : Int) := by
    rw [← hranks]; exact hrkV'
  have hlyU' : run.layers[rU]? = some lU := hlyU
  have hlyV' : run.layers[rV]? = some lV := hlyV
  rcases Nat.lt_trichotomy rU rV with hlt | heq | hgt
  · obtain ⟨hinBand, hdisjBands⟩ := X_ReserveBands_holds exactIds hrun
    have hbandU := hinBand rU lU u hlyU' huIn huC hrkCoordU
    have hbandV := hinBand rV lV v hlyV' hvIn hvC hrkCoordV
    have hbands := hdisjBands rU rV lU lV hlt hlyU' hlyV'
    have hnodeHU : CoordsImpl.nodeH run.coordinateProper u = actualU.node.h := by
      simp [CoordsImpl.nodeH, hcoordU]
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = actualV.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    rw [hnodeHU] at hbandU
    rw [hnodeHV] at hbandV
    rw [hrectU, hrectV]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega
  · rw [heq] at hlyU'
    obtain hlVeq : lV = lU := Option.some.inj (hlyV'.symm.trans hlyU')
    rw [hlVeq] at hvIn
    obtain ⟨pu, hpu⟩ := List.mem_iff_getElem?.mp huIn
    obtain ⟨pv, hpv⟩ := List.mem_iff_getElem?.mp hvIn
    have hnePV : pu ≠ pv := by
      intro heq'
      subst heq'
      exact hne (Option.some.inj (hpu.symm.trans hpv))
    have hlayerMem : lU ∈ run.layers := by
      obtain ⟨hmemLT, hmemEq⟩ := List.getElem?_eq_some_iff.mp hlyU'
      rw [← hmemEq]
      exact List.getElem_mem hmemLT
    rcases Nat.lt_or_gt_of_ne hnePV with hplt | hpgt
    · have hsep := XSc8a_ordered_intervals h0 h hcomp hrun (layer := lU) hlayerMem
        hplt hpu hpv hcoordU hcoordV
        (by simp [hbU0]) (by simp [hbV0])
      have hnodeWU : RouteImpl.nodeW run.proper u = actualU.node.w := by
        simp [RouteImpl.nodeW, hpropU]
      have hnodeWV : RouteImpl.nodeW run.proper v = actualV.node.w := by
        simp [RouteImpl.nodeW, hpropV]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hnodeWU, hnodeWV] at hsep
      rw [hrectU, hrectV]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      omega
    · have hsep := XSc8a_ordered_intervals h0 h hcomp hrun (layer := lU) hlayerMem
        hpgt hpv hpu hcoordV hcoordU
        (by simp [hbV0]) (by simp [hbU0])
      have hnodeWU : RouteImpl.nodeW run.proper u = actualU.node.w := by
        simp [RouteImpl.nodeW, hpropU]
      have hnodeWV : RouteImpl.nodeW run.proper v = actualV.node.w := by
        simp [RouteImpl.nodeW, hpropV]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hnodeWU, hnodeWV] at hsep
      rw [hrectU, hrectV]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      omega
  · obtain ⟨hinBand, hdisjBands⟩ := X_ReserveBands_holds exactIds hrun
    have hbandU := hinBand rU lU u hlyU' huIn huC hrkCoordU
    have hbandV := hinBand rV lV v hlyV' hvIn hvC hrkCoordV
    have hbands := hdisjBands rV rU lV lU hgt hlyV' hlyU'
    have hnodeHU : CoordsImpl.nodeH run.coordinateProper u = actualU.node.h := by
      simp [CoordsImpl.nodeH, hcoordU]
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = actualV.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    rw [hnodeHU] at hbandU
    rw [hnodeHV] at hbandV
    rw [hrectU, hrectV]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega

end PipelineImpl
end Layered
end Elegant

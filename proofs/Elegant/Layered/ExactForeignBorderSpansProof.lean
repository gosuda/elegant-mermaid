import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactFlatC2
import Elegant.Layered.ComponentRunGenGeometry
import Elegant.Layered.ExactPipeline
import Elegant.Layered.ExactFlatC5Rank
import Elegant.Layered.ForeignClusterFactsProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.Order
import Elegant.Layered.Pipeline
import Elegant.Layered.ExactC8aSpanResidualsProof
set_option autoImplicit false

/-!
# The exact group-vs-group foreign-span seam

This module states the exact twin `XB_ForeignBorderSpansSeparated` of the plain
open seam `ForeignBorderSpansSeparated` (`ForeignSpansFacts.lean`): for one
executed `componentRunX` run, the hulls of two distinct, mutually unrelated
group declarations separate either on `x` through the border-marker hulls or on
`y` through the member hulls.

The replay mirrors `ForeignBorderSpansProof.lean` field by field over the exact
run. Two of the four seam premises are proved outright here by replaying the
plain proofs over `componentRunX_spec` with the exact bundle
(`X_cg_run_bundle`):

* `XB_foreignBorderLayerOrder_holds` proves `XB_ForeignBorderLayerOrder` from
  the exact anchor paths (`xbf_anchorPaths`, replay of
  `foreignBorderAnchorPaths`), with no residual.
* `XB_foreignClusterRankSpans_holds` proves `XB_ForeignClusterRankSpans` from
  the single narrower residual `XB_ForeignRankPairAnchors` (titled top/bottom
  anchors only) plus the closed exact member bounds
  (`XSc8a_memberBounds_holds`), via the per-rank marker pairs
  (`xbf_rank_pair`, replay of `coordinateGraph_rank_pair`).

The remaining two stay premises in exact form (copied with the `XB_` prefix,
never proved here):

* `XB_ForeignBorderChainXAligned` from `ForeignBorderChainXAligned`
  (cross-coordinate placement).
* `XB_OrderedIntervals` from `componentRun_nonproxy_ordered_intervals`
  (`ExecutedFrameClearanceFacts.lean`; the marker-bracket separation that the
  plain pipeline proves outright but the exact pipeline keeps open).

Every use of the plain run spec's `rankCoords` / `proxyYs` conjuncts is
replaced: per-node bands come from `componentRunX_node_band`, disjoint bands
from `X_ReserveBands_holds`. Plain-node disjointness, when needed elsewhere,
comes from `componentRunX_positions_disjoint` (this half needs only the two
band facts). The nonnegativity ingredients are proved outright
(`xbf_coordinate_centers_nonneg`); the two remaining narrow residuals
(`XB_TopNonneg`, `XB_MemberNonempty`) are single exact-run facts with probes.
-/

namespace Elegant.Layered.PipelineImpl

open CoordsImpl

/-! ## Exact seam premises, one pipeline phase each -/

/-- Exact rank-assignment residual: mirror of `ForeignClusterRankSpans`
(`ForeignBorderSpansProof.lean`) over the `measuredGraph`-then-`exactGraph`
pipeline and `componentRunX` over `exactDecls exactIds inp`. -/
def XB_ForeignClusterRankSpans (exactIds : List String) : Prop :=
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

/-- Exact cluster-separation-input residual: mirror of
`ForeignBorderLayerOrder` over the exact pipeline and `componentRunX`. -/
def XB_ForeignBorderLayerOrder (exactIds : List String) : Prop :=
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

/-- Cross-coordinate-placement alignment for well-formed framed inputs over
the exact pipeline and `componentRunX`. -/
def XB_ForeignBorderChainXAligned (exactIds : List String) : Prop :=
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
    ∀ {a b : Nat} {na nb : ProperNode},
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      na.node.border = nb.node.border →
      na.node.clusterPath.getLast? = nb.node.clusterPath.getLast? →
      RouteImpl.leftOf run.proper run.xs a = RouteImpl.leftOf run.proper run.xs b ∧
        RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a =
          RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b

/-- Exact marker-bracket separation: mirror of
`componentRun_nonproxy_ordered_intervals` (`ExecutedFrameClearanceFacts.lean`)
over the exact pipeline and `componentRunX`. The plain pipeline proves this
from the cluster pass; the exact pipeline keeps it open. -/
def XB_OrderedIntervals (exactIds : List String) : Prop :=
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
    ∀ {layer : List Nat}, layer ∈ run.layers →
    ∀ {i j a b : Nat} {first second : ProperNode},
    i < j → layer[i]? = some a → layer[j]? = some b →
    run.coordinateProper.nodes[a]? = some first →
    run.coordinateProper.nodes[b]? = some second →
    ¬(first.node.border = -2 ∨ first.node.border = 2) →
    ¬(second.node.border = -2 ∨ second.node.border = 2) →
    RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a ≤
      RouteImpl.leftOf run.proper run.xs b

/-- Exact group-vs-group foreign-span seam: mirror of
`ForeignBorderSpansSeparated` (`ForeignSpansFacts.lean`) over the exact
pipeline and `componentRunX`. -/
def XB_ForeignBorderSpansSeparated (exactIds : List String) : Prop :=
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
    uNode.border = -2 → wNode.border = -2 →
    uNode.decl ≠ wNode.decl →
    wNode.clusterPath.contains uNode.decl = false →
    uNode.clusterPath.contains wNode.decl = false →
    (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run
        uNode.decl) []).right ≤
        (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run
          wNode.decl) []).minX ∨
      (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run
        wNode.decl) []).right ≤
        (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run
          uNode.decl) []).minX ∨
      (boundsOf (groupMemberRects (componentCandidate graph comp candidate) run
        uNode.decl) []).bottom ≤
        (boundsOf (groupMemberRects (componentCandidate graph comp candidate) run
          wNode.decl) []).minY ∨
      (boundsOf (groupMemberRects (componentCandidate graph comp candidate) run
        wNode.decl) []).bottom ≤
        (boundsOf (groupMemberRects (componentCandidate graph comp candidate) run
          uNode.decl) []).minY

/-! ## Narrow single-fact residuals with probes -/

/-- Residual: every reserved rank top of an executed exact run is
nonnegative. Probe: `ExactBorderSpansTProbe` evaluates `run.top` on a normal
and a degenerate fixed-size input. -/
def XB_TopNonneg (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run →
    ∀ k : Nat, 0 ≤ run.top.getD k 0

/-- Residual: every group-declaration node of an executed exact component
contributes a nonempty member hull. Probe: `ExactBorderSpansTProbe` evaluates
member-hull lengths on a normal and a degenerate fixed-size input. -/
def XB_MemberNonempty (exactIds : List String) : Prop :=
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
    ∀ {u : Nat} {uNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    uNode.border = -2 →
    groupMemberRects (componentCandidate graph comp candidate) run uNode.decl ≠ []

/-! ### Rect edges in `leftOf`/`nodeW`/`ys` terms (copies of `fbs_rect_*`) -/

private theorem xbf_rect_left (p : Proper) (xs ys : List Int) (a : Nat) :
    (Labels.rectAt p xs ys a).x = RouteImpl.leftOf p xs a := rfl

private theorem xbf_rect_right (p : Proper) (xs ys : List Int) (a : Nat) :
    (Labels.rectAt p xs ys a).x + (Labels.rectAt p xs ys a).w =
      RouteImpl.leftOf p xs a + RouteImpl.nodeW p a := rfl

private theorem xbf_rect_top (p : Proper) (xs ys : List Int) (a : Nat) :
    (Labels.rectAt p xs ys a).y = ys.getD a 0 := rfl

private theorem xbf_rect_bottom (p : Proper) (xs ys : List Int) (a : Nat) :
    (Labels.rectAt p xs ys a).y + (Labels.rectAt p xs ys a).h =
      ys.getD a 0 + RouteImpl.nodeH p a := rfl

/-! ### Membership in the two hull inputs (copies of `fbs_groupBorderRects_*`,
`fbs_groupMemberRects_*`) -/

private theorem xbf_groupBorderRects_mem {cg : Graph} {run : Run} {decl : Nat} {a : Nat}
    {na : ProperNode} (hna : run.proper.nodes[a]? = some na)
    (hb : na.node.border = -1 ∨ na.node.border = 1)
    (ho : na.node.clusterPath.getLast? = some decl) :
    Labels.rectAt run.proper run.xs run.ys a ∈ groupBorderRects cg run decl := by
  apply List.mem_filterMap.mpr
  refine ⟨(na, a), List.mk_mem_zipIdx_iff_getElem?.mpr hna, ?_⟩
  rcases hb with hb | hb <;> simp [hb, ho]

private theorem xbf_groupBorderRects_spec {cg : Graph} {run : Run} {decl : Nat} {r : Rect}
    (hmem : r ∈ groupBorderRects cg run decl) :
    ∃ (a : Nat) (na : ProperNode), run.proper.nodes[a]? = some na ∧
      (na.node.border = -1 ∨ na.node.border = 1) ∧
      na.node.clusterPath.getLast? = some decl ∧
      r = Labels.rectAt run.proper run.xs run.ys a := by
  unfold groupBorderRects at hmem
  obtain ⟨q, hq, hsome⟩ := List.mem_filterMap.mp hmem
  have hna : run.proper.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  split at hsome
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcond
    rcases hcond with ⟨h1 | h1, howner⟩
    · exact ⟨q.2, q.1, hna, Or.inl h1, howner, Option.some.inj hsome.symm⟩
    · exact ⟨q.2, q.1, hna, Or.inr h1, howner, Option.some.inj hsome.symm⟩
  · exact absurd hsome (by simp)

private theorem xbf_groupMemberRects_mem {cg : Graph} {run : Run} {decl : Nat} {a : Nat}
    {na : ProperNode} (hna : run.proper.nodes[a]? = some na)
    (hc : na.node.clusterPath.contains decl = true) :
    Labels.rectAt run.proper run.xs run.ys a ∈ groupMemberRects cg run decl := by
  apply List.mem_filterMap.mpr
  refine ⟨(na, a), List.mk_mem_zipIdx_iff_getElem?.mpr hna, ?_⟩
  simp only [hc, ↓reduceIte]

private theorem xbf_groupMemberRects_spec {cg : Graph} {run : Run} {decl : Nat} {r : Rect}
    (hmem : r ∈ groupMemberRects cg run decl) :
    ∃ (a : Nat) (na : ProperNode), run.proper.nodes[a]? = some na ∧
      na.node.clusterPath.contains decl = true ∧
      r = Labels.rectAt run.proper run.xs run.ys a := by
  unfold groupMemberRects at hmem
  obtain ⟨q, hq, hsome⟩ := List.mem_filterMap.mp hmem
  have hna : run.proper.nodes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  split at hsome
  · rename_i hcond
    exact ⟨q.2, q.1, hna, hcond, Option.some.inj hsome.symm⟩
  · exact absurd hsome (by simp)

/-! ### Cluster-path bridges (copies of `fbs_contains_bridge*`) -/

private theorem xbf_contains_bridge {run : Run} {decl v : Nat} {na : ProperNode}
    (hnv : run.proper.nodes[v]? = some na)
    (hcv : na.node.clusterPath.contains decl = true) :
    (run.proper.nodes.getD v default).node.clusterPath.contains decl = true := by
  rw [List.getD_eq_getElem?_getD, hnv]
  exact hcv

private theorem xbf_contains_bridge' {run : Run} {decl v : Nat}
    (hcv : (run.proper.nodes.getD v default).node.clusterPath.contains decl = true) :
    ∃ na : ProperNode, run.proper.nodes[v]? = some na ∧
      na.node.clusterPath.contains decl = true := by
  by_cases hv : v < run.proper.nodes.length
  · refine ⟨run.proper.nodes[v], List.getElem?_eq_getElem hv, ?_⟩
    have hgd : run.proper.nodes.getD v default = run.proper.nodes[v] := by
      simp [List.getD_eq_getElem?_getD, hv]
    rw [← hgd]
    exact hcv
  · cases hv2 : run.proper.nodes[v]? with
    | none =>
      rw [List.getD_eq_getElem?_getD, hv2] at hcv
      exact absurd (show false = true from hcv) (by decide)
    | some nv =>
      rw [List.getD_eq_getElem?_getD, hv2, Option.getD_some] at hcv
      exact ⟨nv, rfl, hcv⟩

/-! ### Run records over `componentRunX` (copies of `X_nonproxy_record`,
`X_fbs_coordinate_record`, `X_border_record` from `ExactFlatC2.lean`) -/
private theorem xbf_nonproxy_record {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {index : Nat} {node : ProperNode}
    (hnode : run.coordinateProper.nodes[index]? = some node)
    (hborder : ¬(node.node.border = -2 ∨ node.node.border = 2)) :
    run.proper.nodes[index]? = some node ∧
      run.xs.getD index 0 = run.coordinateXs.getD index 0 := by
  obtain ⟨_, _, _, routed, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have nodesEq : run.proper.nodes = routed.nodes := by
    rw [← hdrop]
    rfl
  obtain ⟨record, coordinate⟩ :=
    (proxyWidths_rel hproxy).2.2.2.2.2 index node hnode hborder
  refine ⟨?_, ?_⟩
  · simpa only [nodesEq] using record
  · simp only [List.getD_eq_getElem?_getD, coordinate, Option.getD_some]

private theorem xbf_coordinate_record {P : Params} {exact : List Nat} {cg : Graph}
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
  obtain ⟨hfull, -⟩ := xbf_nonproxy_record hrun hcadr hnp
  have := Option.some.inj (hrec.symm.trans hfull)
  rw [← this]

private theorem xbf_border_record {P : Params} {exact : List Nat} {cg : Graph}
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

/-! ### Nonnegative cross-coordinate centres (copies of the `fbs_*` chain) -/

private theorem xbf_foldl_min_le_of_mem {f : Nat → Int} : ∀ {L : List Nat} {v : Nat}, v ∈ L →
    ∀ (init : Int), L.foldl (fun m x => min m (f x)) init ≤ f v := by
  intro L
  induction L with
  | nil => intro v hv; cases hv
  | cons a as ih =>
    intro v hv init
    rcases List.mem_cons.mp hv with rfl | hm
    · have hle : ∀ (L : List Nat) (m : Int), L.foldl (fun x y => min x (f y)) m ≤ m := by
        intro L
        induction L with
        | nil => intro m; exact Int.le_refl m
        | cons b bs ihb =>
            intro m
            simp only [List.foldl_cons]
            exact Int.le_trans (ihb (min m (f b))) (Int.min_le_left _ _)
      simp only [List.foldl_cons]
      exact Int.le_trans (hle as (min init (f v))) (Int.min_le_right _ _)
    · simp only [List.foldl_cons]
      exact ih hm _

private theorem xbf_cluster_pass_nonneg {ng cp : Int} {q : Proper} {layers : List (List Nat)}
    {marked : Array Bool} {k : Nat} {x : Array Int}
    (h : clusterPass ng cp q layers marked k = .ok x) :
    x.size = q.nodes.length ∧ ∀ v, v < x.size → 0 ≤ x[v]! := by
  have hn : (clusterCtx ng cp q layers marked k).n = q.nodes.length := rfl
  unfold clusterPass runPass at h
  split at h
  · simp at h
  · rename_i st _
    dsimp only at h
    split at h
    · simp at h
    · have hinj : (List.range (clusterCtx ng cp q layers marked k).n).toArray.map
          (fun v => finalX st (offsetsOf (clusterCtx ng cp q layers marked k) st)
              (k % 2 == 1) v -
            lowest (clusterCtx ng cp q layers marked k) st
              (offsetsOf (clusterCtx ng cp q layers marked k) st) (k % 2 == 1)) = x := by
        exact Except.ok.inj h
      subst hinj
      refine ⟨by simp [Array.size_map, hn], ?_⟩
      intro v hv
      have hvn : v < (clusterCtx ng cp q layers marked k).n := by
        simpa [Array.size_map] using hv
      have h1 : v < (List.range (clusterCtx ng cp q layers marked k).n).toArray.size := by
        simpa using hvn
      have h2 : v < (List.range (clusterCtx ng cp q layers marked k).n).length := by
        simpa using h1
      have h5 : v < ((List.range (clusterCtx ng cp q layers marked k).n).toArray.map
          (fun v => finalX st (offsetsOf (clusterCtx ng cp q layers marked k) st)
              (k % 2 == 1) v -
            lowest (clusterCtx ng cp q layers marked k) st
              (offsetsOf (clusterCtx ng cp q layers marked k) st) (k % 2 == 1))).size := by
        simpa [Array.size_map] using h1
      rw [getElem!_pos _ v h5, Array.getElem_map _ h5, List.getElem_toArray h1,
        List.getElem_range h2]
      have hlow : lowest (clusterCtx ng cp q layers marked k) st
          (offsetsOf (clusterCtx ng cp q layers marked k) st) (k % 2 == 1) ≤
          finalX st (offsetsOf (clusterCtx ng cp q layers marked k) st) (k % 2 == 1) v :=
        xbf_foldl_min_le_of_mem (List.mem_range.mpr hvn) _
      omega

private theorem xbf_bal4_nonneg {a b c d : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) : 0 ≤ bal4 a b c d := by
  simp only [bal4, sort4]
  exact Int.fdiv_nonneg (by omega) (by decide)

private theorem xbf_balanceOffsets_nonneg (x0 x1 x2 x3 : Array Int) :
    0 ≤ (balanceOffsets x0 x1 x2 x3).o0 ∧ 0 ≤ (balanceOffsets x0 x1 x2 x3).o1 ∧
      0 ≤ (balanceOffsets x0 x1 x2 x3).o2 ∧ 0 ≤ (balanceOffsets x0 x1 x2 x3).o3 := by
  unfold balanceOffsets
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

private theorem xbf_coordinate_centers_nonneg {P : Params} {exact : List Nat} {cg : Graph}
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
    unfold crossClusterPasses at hpass
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
                  (xbf_cluster_pass_nonneg h0).1
                have hsz1 : y1.size = run.coordinateProper.nodes.length :=
                  (xbf_cluster_pass_nonneg h1).1
                have hsz2 : y2.size = run.coordinateProper.nodes.length :=
                  (xbf_cluster_pass_nonneg h2).1
                have hsz3 : y3.size = run.coordinateProper.nodes.length :=
                  (xbf_cluster_pass_nonneg h3).1
                have hnn0 := (xbf_cluster_pass_nonneg h0).2
                have hnn1 := (xbf_cluster_pass_nonneg h1).2
                have hnn2 := (xbf_cluster_pass_nonneg h2).2
                have hnn3 := (xbf_cluster_pass_nonneg h3).2
                obtain ⟨o0, o1, o2, o3⟩ := xbf_balanceOffsets_nonneg y0 y1 y2 y3
                intro v
                by_cases hv : v < run.coordinateProper.nodes.length
                · rw [balanceValues_getD _ _ _ _ _ hv]
                  exact xbf_bal4_nonneg (by have := hnn0 v (by omega); omega)
                    (by have := hnn1 v (by omega); omega)
                    (by have := hnn2 v (by omega); omega)
                    (by have := hnn3 v (by omega); omega)
                · have hlen : (balanceValues run.coordinateProper.nodes.length y0 y1 y2
                        y3).length = run.coordinateProper.nodes.length := by
                    simp [balanceValues]
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
                  exact Int.le_refl 0

/-! ### The `y` alternative over exact bands -/

private theorem xbf_member_hulls_y_separated {P : Params} {exactIds : List String} {inp : Input}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    (htopnn : ∀ k : Nat, 0 ≤ run.top.getD k 0)
    (hdisj : ∀ (r r' : Nat) (l l' : List Nat), r < r' → run.layers[r]? = some l →
      run.layers[r']? = some l' →
      run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l ≤
        run.top.getD r' 0)
    {du dw : Nat}
    (hbelow : ∀ v, v < run.proper.nodes.length →
        (run.proper.nodes.getD v default).node.clusterPath.contains du = true →
        ∀ v', v' < run.proper.nodes.length →
          (run.proper.nodes.getD v' default).node.clusterPath.contains dw = true →
          rk run.proper.rank v < rk run.proper.rank v')
    (_hneU : groupMemberRects cg run du ≠ [])
    (hneW : groupMemberRects cg run dw ≠ []) :
    (boundsOf (groupMemberRects cg run du) []).bottom ≤
      (boundsOf (groupMemberRects cg run dw) []).minY := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute1, _, _⟩ :=
    componentRunX_spec hrun
  have hrankEq : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.1
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute1).1).2.2.2.1
  have hband : ∀ v, v < run.proper.nodes.length →
      run.top.getD (rk run.coordinateProper.rank v).toNat 0 ≤ run.ys.getD v 0 ∧
        run.ys.getD v 0 + RouteImpl.nodeH run.proper v ≤
          run.top.getD (rk run.coordinateProper.rank v).toNat 0 +
            CoordsImpl.layerHeight run.coordinateProper
              (run.layers.getD (rk run.coordinateProper.rank v).toNat []) := by
    intro v hv
    obtain ⟨nvp, hrec⟩ : ∃ nvp : ProperNode, run.proper.nodes[v]? = some nvp :=
      ⟨_, List.getElem?_eq_getElem hv⟩
    obtain ⟨nvc, hnc, hbEq, hhEq, -⟩ := xbf_coordinate_record hrun hrec
    obtain ⟨l, hly, hlo, hhi⟩ :=
      componentRunX_node_band hrun hrec ⟨nvc, hnc, hbEq, hhEq⟩
    have hlyD : run.layers.getD (rk run.coordinateProper.rank v).toNat [] = l := by
      rw [List.getD_eq_getElem?_getD, hly]
      rfl
    rw [hlyD]
    exact ⟨hlo, hhi⟩
  have hpair : ∀ r ∈ groupMemberRects cg run du, ∀ r' ∈ groupMemberRects cg run dw,
      r.y + r.h ≤ r'.y := by
    intro r hr r' hr'
    obtain ⟨v, _na, hnvr, hcv, rfl⟩ := xbf_groupMemberRects_spec hr
    obtain ⟨v', _na', hnvr', hcv', rfl⟩ := xbf_groupMemberRects_spec hr'
    have hvR : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hnvr).1
    have hvR' : v' < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hnvr').1
    rw [xbf_rect_bottom, xbf_rect_top]
    obtain ⟨-, hupper⟩ := hband v hvR
    obtain ⟨lv, hly, -, hrknn⟩ := hcov v hvR
    obtain ⟨lv', hly', -, hrknn'⟩ := hcov v' hvR'
    have hrkNv : (rk run.coordinateProper.rank v).toNat = (rk run.proper.rank v).toNat := by
      rw [hrankEq]
    have hrkNv' : (rk run.coordinateProper.rank v').toNat = (rk run.proper.rank v').toNat := by
      rw [hrankEq]
    have hlyC : run.layers[(rk run.coordinateProper.rank v).toNat]? = some lv := by
      rw [hrkNv]; exact hly
    have hlyC' : run.layers[(rk run.coordinateProper.rank v').toNat]? = some lv' := by
      rw [hrkNv']; exact hly'
    have hlyD : run.layers.getD (rk run.coordinateProper.rank v).toNat [] = lv := by
      rw [List.getD_eq_getElem?_getD, hlyC]
      rfl
    rw [hlyD] at hupper
    have hlt := hbelow v hvR (xbf_contains_bridge hnvr hcv) v' hvR'
      (xbf_contains_bridge hnvr' hcv')
    have hltC : rk run.coordinateProper.rank v < rk run.coordinateProper.rank v' := by
      rw [← hrankEq]; exact hlt
    have hnnv : 0 ≤ rk run.coordinateProper.rank v := by
      rw [← hrankEq]; exact hrknn
    have hnnv' : 0 ≤ rk run.coordinateProper.rank v' := by
      rw [← hrankEq]; exact hrknn'
    have hltN : (rk run.coordinateProper.rank v).toNat < (rk run.coordinateProper.rank v').toNat := by
      omega
    have hbands := hdisj (rk run.coordinateProper.rank v).toNat
      (rk run.coordinateProper.rank v').toNat lv lv' hltN hlyC hlyC'
    obtain ⟨hlower', -⟩ := hband v' hvR'
    omega
  have hminYnonneg : 0 ≤ (boundsOf (groupMemberRects cg run dw) []).minY := by
    refine boundsOf_minY_ge_of_all hneW ?_
    intro r hr
    obtain ⟨v, _na, hnvr, -, rfl⟩ := xbf_groupMemberRects_spec hr
    have hvR : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hnvr).1
    obtain ⟨hlower, -⟩ := hband v hvR
    rw [xbf_rect_top]
    have hrkNv : (rk run.coordinateProper.rank v).toNat = (rk run.proper.rank v).toNat := by
      rw [hrankEq]
    have hnnC : 0 ≤ run.top.getD (rk run.coordinateProper.rank v).toNat 0 := by
      rw [hrkNv]; exact htopnn (rk run.proper.rank v).toNat
    omega
  refine boundsOf_bottom_le_of_all hminYnonneg ?_
  intro r hr
  exact boundsOf_minY_ge_of_all hneW (fun r' hr' => hpair r hr r' hr')

/-! ### The `x` alternative over the exact run -/

private theorem xbf_x_hull_bound {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hg0 : measuredGraph P inp o lines = .ok graph0)
    (hgX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    (halign : XB_ForeignBorderChainXAligned exactIds)
    {dl dr : Nat}
    {pL pR qL qR : Nat} {npL npR nqL nqR : ProperNode}
    (hrecpL : run.coordinateProper.nodes[pL]? = some npL) (hbpL : npL.node.border = -1)
    (hopL : npL.node.clusterPath.getLast? = some dl)
    (hrecpR : run.coordinateProper.nodes[pR]? = some npR) (hbpR : npR.node.border = 1)
    (hopR : npR.node.clusterPath.getLast? = some dl)
    (hrecqL : run.coordinateProper.nodes[qL]? = some nqL) (hbqL : nqL.node.border = -1)
    (hopqL : nqL.node.clusterPath.getLast? = some dr)
    (hrecqR : run.coordinateProper.nodes[qR]? = some nqR) (hbqR : nqR.node.border = 1)
    (hopqR : nqR.node.clusterPath.getLast? = some dr)
    (hsep : ∀ p : Nat, p = pL ∨ p = pR → ∀ q : Nat, q = qL ∨ q = qR →
      RouteImpl.leftOf run.proper run.xs p + RouteImpl.nodeW run.proper p ≤
        RouteImpl.leftOf run.proper run.xs q) :
    (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run dl) []).right ≤
      (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run dr) []).minX
        := by
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  have hsizes := (crossCoordsClusterWith_spec hcross).2.2.2.1
  have hcenters := xbf_coordinate_centers_nonneg hrun
  have hneR : groupBorderRects (componentCandidate graph comp candidate) run dr ≠ [] := by
    intro hempty
    have hmem : Labels.rectAt run.proper run.xs run.ys qL ∈
        groupBorderRects (componentCandidate graph comp candidate) run dr :=
      xbf_groupBorderRects_mem
        (xbf_border_record hrun hrecqL (Or.inl hbqL)).1 (Or.inl hbqL) hopqL
    rw [hempty] at hmem
    exact List.not_mem_nil hmem
  have hrepL : ∀ (a : Nat) (na : ProperNode),
      run.proper.nodes[a]? = some na → (na.node.border = -1 ∨ na.node.border = 1) →
      na.node.clusterPath.getLast? = some dl →
      ∃ (rep : Nat) (_ : ProperNode), (rep = pL ∨ rep = pR) ∧
        RouteImpl.leftOf run.proper run.xs a = RouteImpl.leftOf run.proper run.xs rep ∧
        RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a =
          RouteImpl.leftOf run.proper run.xs rep + RouteImpl.nodeW run.proper rep := by
    intro a na hna hb ho
    obtain ⟨nca, hcadr, hbca, -, hcp⟩ := xbf_coordinate_record hrun hna
    have hcp' : nca.node.clusterPath = na.node.clusterPath := by
      refine hcp ?_
      intro hcon
      rcases hcon with h | h <;> rw [h] at hbca <;> omega
    rcases hb with hb | hb
    · exact ⟨pL, npL, Or.inl rfl,
        (halign hg0 hgX hlines hwf hfp hcomp hrun (a := a) (b := pL)
          (na := nca) (nb := npL) hcadr hrecpL
          (Or.inl (hbca.trans hb)) (Or.inl hbpL)
          (hbca.trans (hb.trans hbpL.symm))
          (by rw [hcp']; exact ho.trans hopL.symm)).1,
        (halign hg0 hgX hlines hwf hfp hcomp hrun (a := a) (b := pL)
          (na := nca) (nb := npL) hcadr hrecpL
          (Or.inl (hbca.trans hb)) (Or.inl hbpL)
          (hbca.trans (hb.trans hbpL.symm))
          (by rw [hcp']; exact ho.trans hopL.symm)).2⟩
    · exact ⟨pR, npR, Or.inr rfl,
        (halign hg0 hgX hlines hwf hfp hcomp hrun (a := a) (b := pR)
          (na := nca) (nb := npR) hcadr hrecpR
          (Or.inr (hbca.trans hb)) (Or.inr hbpR)
          (hbca.trans (hb.trans hbpR.symm))
          (by rw [hcp']; exact ho.trans hopR.symm)).1,
        (halign hg0 hgX hlines hwf hfp hcomp hrun (a := a) (b := pR)
          (na := nca) (nb := npR) hcadr hrecpR
          (Or.inr (hbca.trans hb)) (Or.inr hbpR)
          (hbca.trans (hb.trans hbpR.symm))
          (by rw [hcp']; exact ho.trans hopR.symm)).2⟩
  have hrepR : ∀ (b : Nat) (nb : ProperNode),
      run.proper.nodes[b]? = some nb → (nb.node.border = -1 ∨ nb.node.border = 1) →
      nb.node.clusterPath.getLast? = some dr →
      ∃ (rep : Nat) (_ : ProperNode), (rep = qL ∨ rep = qR) ∧
        RouteImpl.leftOf run.proper run.xs b = RouteImpl.leftOf run.proper run.xs rep ∧
        RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b =
          RouteImpl.leftOf run.proper run.xs rep + RouteImpl.nodeW run.proper rep := by
    intro b nb hnb hb ho
    obtain ⟨ncb, hcbdr, hbcb, -, hcp⟩ := xbf_coordinate_record hrun hnb
    have hcp' : ncb.node.clusterPath = nb.node.clusterPath := by
      refine hcp ?_
      intro hcon
      rcases hcon with h | h <;> rw [h] at hbcb <;> omega
    rcases hb with hb | hb
    · exact ⟨qL, nqL, Or.inl rfl,
        (halign hg0 hgX hlines hwf hfp hcomp hrun (a := b) (b := qL)
          (na := ncb) (nb := nqL) hcbdr hrecqL
          (Or.inl (hbcb.trans hb)) (Or.inl hbqL)
          (hbcb.trans (hb.trans hbqL.symm))
          (by rw [hcp']; exact ho.trans hopqL.symm)).1,
        (halign hg0 hgX hlines hwf hfp hcomp hrun (a := b) (b := qL)
          (na := ncb) (nb := nqL) hcbdr hrecqL
          (Or.inl (hbcb.trans hb)) (Or.inl hbqL)
          (hbcb.trans (hb.trans hbqL.symm))
          (by rw [hcp']; exact ho.trans hopqL.symm)).2⟩
    · exact ⟨qR, nqR, Or.inr rfl,
        (halign hg0 hgX hlines hwf hfp hcomp hrun (a := b) (b := qR)
          (na := ncb) (nb := nqR) hcbdr hrecqR
          (Or.inr (hbcb.trans hb)) (Or.inr hbqR)
          (hbcb.trans (hb.trans hbqR.symm))
          (by rw [hcp']; exact ho.trans hopqR.symm)).1,
        (halign hg0 hgX hlines hwf hfp hcomp hrun (a := b) (b := qR)
          (na := ncb) (nb := nqR) hcbdr hrecqR
          (Or.inr (hbcb.trans hb)) (Or.inr hbqR)
          (hbcb.trans (hb.trans hbqR.symm))
          (by rw [hcp']; exact ho.trans hopqR.symm)).2⟩
  have hzero : 0 ≤
      (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run dr) []).minX
        := by
    refine boundsOf_minX_ge_of_all hneR ?_
    intro rb hrb
    obtain ⟨b, nb, hnb, hbb, hob, rfl⟩ := xbf_groupBorderRects_spec hrb
    rw [xbf_rect_left]
    obtain ⟨rep, _nrep, hrep, hle, _⟩ := hrepR b nb hnb hbb hob
    obtain ⟨hrecp, hxp⟩ := xbf_border_record hrun hrecpL (Or.inl hbpL)
    have hnodeWp : 0 ≤ RouteImpl.nodeW run.proper pL := by
      have hw := (sizesNonneg_lookup hsizes pL npL hrecpL).1
      simp only [RouteImpl.nodeW, hrecp]
      omega
    have hfdiv : Int.fdiv (RouteImpl.nodeW run.proper pL) 2 ≤
        RouteImpl.nodeW run.proper pL := Int.fdiv_le_self 2 hnodeWp
    have hcenter : 0 ≤ run.xs.getD pL 0 := by
      rw [hxp]
      exact hcenters pL
    have hge : run.xs.getD pL 0 ≤ RouteImpl.leftOf run.proper run.xs pL +
        RouteImpl.nodeW run.proper pL := by
      simp only [RouteImpl.leftOf, RouteImpl.xAt]
      omega
    have hsep' := hsep pL (Or.inl rfl) rep hrep
    omega
  refine boundsOf_right_le_of_all hzero ?_
  intro ra hra
  obtain ⟨a, na, hna, hba, hoa, rfl⟩ := xbf_groupBorderRects_spec hra
  rw [xbf_rect_right]
  obtain ⟨rep, _nrep, hrep, _, hsum⟩ := hrepL a na hna hba hoa
  rw [hsum]
  refine boundsOf_minX_ge_of_all hneR ?_
  intro rb hrb
  obtain ⟨b, nb, hnb, hbb, hob, rfl⟩ := xbf_groupBorderRects_spec hrb
  rw [xbf_rect_left]
  obtain ⟨rep2, _nrep2, hrep2, hle2, _⟩ := hrepR b nb hnb hbb hob
  rw [hle2]
  exact hsep rep hrep rep2 hrep2

private theorem xbf_border_hulls_x_separated {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hg0 : measuredGraph P inp o lines = .ok graph0)
    (hgX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    (horder : XB_ForeignBorderLayerOrder exactIds)
    (halign : XB_ForeignBorderChainXAligned exactIds)
    (hord : XB_OrderedIntervals exactIds)
    {u w : Nat} {uNode wNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hw : (componentCandidate graph comp candidate).nodes[w]? = some wNode)
    (hgroupU : uNode.border = -2) (hgroupW : wNode.border = -2)
    (hpathW : wNode.clusterPath.contains uNode.decl = false)
    (hpathU : uNode.clusterPath.contains wNode.decl = false)
    {du dw : Nat} (hdu : uNode.decl = du) (hdw : wNode.decl = dw)
    (hneDecl : du ≠ dw) {r : Int}
    {mUL mUR mWL mWR : Nat} {nUL nUR nWL nWR : ProperNode}
    (hUL : run.coordinateProper.nodes[mUL]? = some nUL) (hbUL : nUL.node.border = -1)
    (hoUL : nUL.node.clusterPath.getLast? = some du)
    (hrkUL : rk run.coordinateProper.rank mUL = r)
    (hUR : run.coordinateProper.nodes[mUR]? = some nUR) (hbUR : nUR.node.border = 1)
    (hoUR : nUR.node.clusterPath.getLast? = some du)
    (hrkUR : rk run.coordinateProper.rank mUR = r)
    (hWL : run.coordinateProper.nodes[mWL]? = some nWL) (hbWL : nWL.node.border = -1)
    (hoWL : nWL.node.clusterPath.getLast? = some dw)
    (hrkWL : rk run.coordinateProper.rank mWL = r)
    (hWR : run.coordinateProper.nodes[mWR]? = some nWR) (hbWR : nWR.node.border = 1)
    (hoWR : nWR.node.clusterPath.getLast? = some dw)
    (hrkWR : rk run.coordinateProper.rank mWR = r) :
    (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run du) []).right ≤
      (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run dw) []).minX ∨
    (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run dw) []).right ≤
      (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run du) []).minX
        := by
  subst hdu
  subst hdw
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute1, _, _⟩ :=
    componentRunX_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hrankEq : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.1
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute1).1).2.2.2.1
  have hmUL : mUL < run.proper.nodes.length := by
    have := (List.getElem?_eq_some_iff.mp hUL).1; omega
  have hmUR : mUR < run.proper.nodes.length := by
    have := (List.getElem?_eq_some_iff.mp hUR).1; omega
  have hmWL : mWL < run.proper.nodes.length := by
    have := (List.getElem?_eq_some_iff.mp hWL).1; omega
  have hmWR : mWR < run.proper.nodes.length := by
    have := (List.getElem?_eq_some_iff.mp hWR).1; omega
  obtain ⟨layer, hly, hmULin, _hrknn⟩ := hcov mUL hmUL
  have hrkUL' : rk run.proper.rank mUL = r := by rw [hrankEq]; exact hrkUL
  have hlyr : run.layers[r.toNat]? = some layer := by rw [← hrkUL']; exact hly
  have hlayerMem : layer ∈ run.layers := List.mem_of_getElem? hly
  have hmURin : mUR ∈ layer := by
    obtain ⟨l2, hly2, hin, _⟩ := hcov mUR hmUR
    have hrkUR' : rk run.proper.rank mUR = r := by rw [hrankEq]; exact hrkUR
    rw [hrkUR'] at hly2
    have hl2 : l2 = layer := Option.some.inj (hly2.symm.trans hlyr)
    rw [hl2] at hin
    exact hin
  have hmWLin : mWL ∈ layer := by
    obtain ⟨l2, hly2, hin, _⟩ := hcov mWL hmWL
    have hrkWL' : rk run.proper.rank mWL = r := by rw [hrankEq]; exact hrkWL
    rw [hrkWL'] at hly2
    have hl2 : l2 = layer := Option.some.inj (hly2.symm.trans hlyr)
    rw [hl2] at hin
    exact hin
  have hmWRin : mWR ∈ layer := by
    obtain ⟨l2, hly2, hin, _⟩ := hcov mWR hmWR
    have hrkWR' : rk run.proper.rank mWR = r := by rw [hrankEq]; exact hrkWR
    rw [hrkWR'] at hly2
    have hl2 : l2 = layer := Option.some.inj (hly2.symm.trans hlyr)
    rw [hl2] at hin
    exact hin
  rcases horder hg0 hgX hcomp hrun hu hw hgroupU hgroupW hneDecl hpathW hpathU hlayerMem
    with huFirst | hwFirst
  · refine Or.inl (xbf_x_hull_bound hg0 hgX hlines hwf hfp hcomp hrun halign
      hUL hbUL hoUL hUR hbUR hoUR
      hWL hbWL hoWL hWR hbWR hoWR ?_)
    intro p hp q hq
    obtain ⟨np, hprec, hbp, hop⟩ : ∃ np : ProperNode,
        run.coordinateProper.nodes[p]? = some np ∧
        (np.node.border = -1 ∨ np.node.border = 1) ∧
        np.node.clusterPath.getLast? = some uNode.decl := by
      rcases hp with rfl | rfl
      · exact ⟨nUL, hUL, Or.inl hbUL, hoUL⟩
      · exact ⟨nUR, hUR, Or.inr hbUR, hoUR⟩
    obtain ⟨nq, hqrec, hbq, hoq⟩ : ∃ nq : ProperNode,
        run.coordinateProper.nodes[q]? = some nq ∧
        (nq.node.border = -1 ∨ nq.node.border = 1) ∧
        nq.node.clusterPath.getLast? = some wNode.decl := by
      rcases hq with rfl | rfl
      · exact ⟨nWL, hWL, Or.inl hbWL, hoWL⟩
      · exact ⟨nWR, hWR, Or.inr hbWR, hoWR⟩
    obtain ⟨ip, hip⟩ := List.mem_iff_getElem?.mp (by
      rcases hp with rfl | rfl
      · exact hmULin
      · exact hmURin)
    obtain ⟨iq, hiq⟩ := List.mem_iff_getElem?.mp (by
      rcases hq with rfl | rfl
      · exact hmWLin
      · exact hmWRin)
    exact hord hg0 hgX hcomp hrun hlayerMem (huFirst ip iq p q np nq hip hiq hprec hqrec hbp hop hbq hoq) hip hiq hprec hqrec
      (by intro hcon; rcases hcon with h | h <;> omega)
      (by intro hcon; rcases hcon with h | h <;> omega)
  · refine Or.inr (xbf_x_hull_bound hg0 hgX hlines hwf hfp hcomp hrun halign
      hWL hbWL hoWL hWR hbWR hoWR
      hUL hbUL hoUL hUR hbUR hoUR ?_)
    intro p hp q hq
    obtain ⟨np, hprec, hbp, hop⟩ : ∃ np : ProperNode,
        run.coordinateProper.nodes[p]? = some np ∧
        (np.node.border = -1 ∨ np.node.border = 1) ∧
        np.node.clusterPath.getLast? = some wNode.decl := by
      rcases hp with rfl | rfl
      · exact ⟨nWL, hWL, Or.inl hbWL, hoWL⟩
      · exact ⟨nWR, hWR, Or.inr hbWR, hoWR⟩
    obtain ⟨nq, hqrec, hbq, hoq⟩ : ∃ nq : ProperNode,
        run.coordinateProper.nodes[q]? = some nq ∧
        (nq.node.border = -1 ∨ nq.node.border = 1) ∧
        nq.node.clusterPath.getLast? = some uNode.decl := by
      rcases hq with rfl | rfl
      · exact ⟨nUL, hUL, Or.inl hbUL, hoUL⟩
      · exact ⟨nUR, hUR, Or.inr hbUR, hoUR⟩
    have pin : p ∈ layer := by
      rcases hp with rfl | rfl
      · exact hmWLin
      · exact hmWRin
    have qin : q ∈ layer := by
      rcases hq with rfl | rfl
      · exact hmULin
      · exact hmURin
    obtain ⟨ip, hip⟩ := List.mem_iff_getElem?.mp pin
    obtain ⟨iq, hiq⟩ := List.mem_iff_getElem?.mp qin
    have hlt : ip < iq := hwFirst iq ip q p nq np hiq hip hqrec hprec hbq hoq hbp hop
    exact hord hg0 hgX hcomp hrun hlayerMem hlt hip hiq hprec hqrec
      (by intro hcon; rcases hcon with h | h <;> omega)
      (by intro hcon; rcases hcon with h | h <;> omega)

/-! ### The seam -/

set_option maxHeartbeats 3000000 in
/-- The exact group-vs-group foreign-span seam: from the exact rank-span,
layer-order, chain-alignment, and marker-bracket residuals. Disjoint member
rank ranges separate the member hulls vertically through the reserved rank
bands; overlapping ranges give a shared marker rank, where the layer order
and the bracket separation split the marker hulls horizontally. -/
theorem XB_foreignBorderSpansSeparated_holds (exactIds : List String)
    (hspans : XB_ForeignClusterRankSpans exactIds)
    (horder : XB_ForeignBorderLayerOrder exactIds)
    (halign : XB_ForeignBorderChainXAligned exactIds)
    (hord : XB_OrderedIntervals exactIds)
    (htop : XB_TopNonneg exactIds)
    (hmem : XB_MemberNonempty exactIds) :
    XB_ForeignBorderSpansSeparated exactIds := by
  intro P inp o lines measured graph0 graph hg0 hgX hlines hwf hfp comp hcomp candidate run labels orderOptions hrun
    u w uNode wNode hu hw hgroupU hgroupW hne hpathW hpathU
  obtain ⟨tU, bU, tW, bW, hUle, hWle, hUspan, hWspan, hUmark, hWmark⟩ :=
    hspans hg0 hgX hlines hwf hfp hcomp hrun hu hw hgroupU hgroupW hne
  have hmemU := hmem hg0 hgX hcomp hrun hu hgroupU
  have hmemW := hmem hg0 hgX hcomp hrun hw hgroupW
  have htopnn := htop hrun
  obtain ⟨_, hdisjBands⟩ := X_ReserveBands_holds exactIds hrun
  by_cases hdisj : bU < tW
  · refine Or.inr (Or.inr (Or.inl ?_))
    refine xbf_member_hulls_y_separated hrun htopnn hdisjBands ?_ hmemU hmemW
    intro v hv hcv v' hv' hcv'
    have hu1 := hUspan v hv hcv
    have hw1 := hWspan v' hv' hcv'
    omega
  · have hov1 : tW ≤ bU := by
      by_cases h : tW ≤ bU
      · exact h
      · omega
    by_cases hdisj2 : bW < tU
    · refine Or.inr (Or.inr (Or.inr ?_))
      refine xbf_member_hulls_y_separated hrun htopnn hdisjBands ?_ hmemW hmemU
      intro v hv hcv v' hv' hcv'
      have hw1 := hWspan v hv hcv
      have hu1 := hUspan v' hv' hcv'
      omega
    · have hov2 : tU ≤ bW := by
        by_cases h : tU ≤ bW
        · exact h
        · omega
      by_cases hlt : tU ≤ tW
      · obtain ⟨mUL, mUR, nUL, nUR, hrecUL, hbUL, hoUL, hrkUL, hrecUR, hbUR, hoUR, hrkUR⟩ :=
          hUmark tW hlt hov1
        obtain ⟨mWL, mWR, nWL, nWR, hrecWL, hbWL, hoWL, hrkWL, hrecWR, hbWR, hoWR, hrkWR⟩ :=
          hWmark tW (Int.le_refl tW) hWle
        rcases xbf_border_hulls_x_separated hg0 hgX hlines hwf hfp hcomp hrun horder halign hord
          hu hw hgroupU hgroupW hpathW hpathU rfl rfl hne
          hrecUL hbUL hoUL hrkUL hrecUR hbUR hoUR hrkUR
          hrecWL hbWL hoWL hrkWL hrecWR hbWR hoWR hrkWR with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · obtain ⟨mUL, mUR, nUL, nUR, hrecUL, hbUL, hoUL, hrkUL, hrecUR, hbUR, hoUR, hrkUR⟩ :=
          hUmark tU (Int.le_refl tU) hUle
        obtain ⟨mWL, mWR, nWL, nWR, hrecWL, hbWL, hoWL, hrkWL, hrecWR, hbWR, hoWR, hrkWR⟩ :=
          hWmark tU (by omega) hov2
        rcases xbf_border_hulls_x_separated hg0 hgX hlines hwf hfp hcomp hrun horder halign hord
          hu hw hgroupU hgroupW hpathW hpathU rfl rfl hne
          hrecUL hbUL hoUL hrkUL hrecUR hbUR hoUR hrkUR
          hrecWL hbWL hoWL hrkWL hrecWR hbWR hoWR hrkWR with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)


/-! ## Exact anchor paths and layer order (replay of `ForeignClusterFactsProof`) -/

/-- A side border of the exact coordinate graph is non-dummy (copy of the
private `XSc8a_anchor_side_dummy` in `ExactC8aSpansProof`). -/
private theorem xbf_anchor_side_dummy {p : Proper} {bw : Int}
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
(copy of the private `XSc8a_anchor_side_path` in `ExactC8aSpansProof`). -/
private theorem xbf_anchor_side_path {P : Params} {exact : List Nat} {p t : Proper}
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
        xbf_anchor_side_dummy hready hm2mem hm2b
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
    rw [cm2.1]; exact xbf_anchor_side_dummy hready hm2mem hm2b
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source t P.clusterBorderW hready hm2mem hm2b
  obtain ⟨tmem, hcond⟩ := List.mem_filter.mp htop
  have hget : t.nodes[top.2]? = some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp tmem
  refine ⟨hndF, top.1, List.mem_of_getElem? hget, ?_, cm2.2.2.1.trans hpath⟩
  simpa using hcond

/-- Exact coordinate borders are well formed (copy of the private
`XSc8a_bordersWellFormed` in `ExactC8aSpansProof`). -/
private theorem xbf_bordersWellFormed {P : Params} {inp : Input} {o : Options}
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

/-- Exact anchor paths: every side marker carries its title path; every title
path ends in its own declaration (replay of `foreignBorderAnchorPaths` via
the exact bundle). -/
private theorem xbf_anchorPaths {exactIds : List String}
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (h0 : measuredGraph P inp o lines = .ok graph0)
    (h : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {u w : Nat} {uNode wNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hw : (componentCandidate graph comp candidate).nodes[w]? = some wNode)
    (hbU : uNode.border = -2) (hbW : wNode.border = -2)
    (_hne : uNode.decl ≠ wNode.decl) :
    (uNode.clusterPath.getLast? = some uNode.decl) ∧
    (wNode.clusterPath.getLast? = some wNode.decl) ∧
    ∀ {a : Nat} {na : ProperNode},
    run.coordinateProper.nodes[a]? = some na →
    (na.node.border = -1 ∨ na.node.border = 1) →
    (na.node.clusterPath.getLast? = some uNode.decl →
      na.node.clusterPath = uNode.clusterPath) ∧
    (na.node.clusterPath.getLast? = some wNode.decl →
      na.node.clusterPath = wNode.clusterPath) := by
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
    xbf_anchor_side_path rfl hready hna hside
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

/-- Layer membership and disjointness behind the exact order fact: markers of
each declaration lie in their title-prefix filter, and the two filters are
disjoint by prefix comparability against the unrelatedness hypotheses
(replay of the middle block of `foreignBorderLayerOrder`). -/
private theorem xbf_layer_mem_disjoint {run : Run} {uNode wNode : Node}
    {layer : List Nat}
    (hwf : OrderImpl.BordersWellFormed run.coordinateProper)
    (hUlast : uNode.clusterPath.getLast? = some uNode.decl)
    (hWlast : wNode.clusterPath.getLast? = some wNode.decl)
    (hpeq : ∀ {a : Nat} {na : ProperNode},
      run.coordinateProper.nodes[a]? = some na →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (na.node.clusterPath.getLast? = some uNode.decl →
        na.node.clusterPath = uNode.clusterPath) ∧
      (na.node.clusterPath.getLast? = some wNode.decl →
        na.node.clusterPath = wNode.clusterPath))
    (hpathW : wNode.clusterPath.contains uNode.decl = false)
    (hpathU : uNode.clusterPath.contains wNode.decl = false) :
    (∀ (x : Nat), x ∈ layer →
      (∃ na, run.coordinateProper.nodes[x]? = some na ∧
        (na.node.border = -1 ∨ na.node.border = 1) ∧
        na.node.clusterPath.getLast? = some uNode.decl) →
      x ∈ layer.filter
        (fun v => uNode.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper v))) ∧
    (∀ (x : Nat), x ∈ layer →
      (∃ na, run.coordinateProper.nodes[x]? = some na ∧
        (na.node.border = -1 ∨ na.node.border = 1) ∧
        na.node.clusterPath.getLast? = some wNode.decl) →
      x ∈ layer.filter
        (fun v => wNode.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper v))) ∧
    (∀ x, x ∈ layer.filter
        (fun v => uNode.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper v)) →
      x ∈ layer.filter
        (fun v => wNode.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper v)) →
      False) := by
  have hnp : ∀ (x : Nat) (nx : ProperNode), run.coordinateProper.nodes[x]? = some nx →
      (nx.node.border = -1 ∨ nx.node.border = 1) →
      OrderImpl.nodePath run.coordinateProper x = nx.node.clusterPath := by
    intro x nx hx hxb
    obtain ⟨na, hna, hda, _⟩ := OrderImpl.border_node hwf (by
      have hxb' : (run.coordinateProper.nodes.getD x default).node.border = -1 ∨
          (run.coordinateProper.nodes.getD x default).node.border = 1 := by
        rw [show run.coordinateProper.nodes.getD x default = nx from by
          simp [List.getD_eq_getElem?_getD, hx]]
        exact hxb
      exact hxb')
    rw [OrderImpl.nodePath_of_nondummy hna hda]
    have h1 : nx = na := Option.some.inj (hx.symm.trans hna)
    rw [h1]
  have hmemU : ∀ (x : Nat), x ∈ layer →
      (∃ na, run.coordinateProper.nodes[x]? = some na ∧
        (na.node.border = -1 ∨ na.node.border = 1) ∧
        na.node.clusterPath.getLast? = some uNode.decl) →
      x ∈ layer.filter
        (fun v => uNode.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper v)) := by
    intro x hx h
    obtain ⟨na, hna, hb, ho⟩ := h
    rw [List.mem_filter]
    refine ⟨hx, ?_⟩
    have hnpU := hnp x na hna hb
    have heqU := (hpeq hna hb).1 ho
    rw [hnpU, heqU]
    exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl
  have hmemW : ∀ (x : Nat), x ∈ layer →
      (∃ na, run.coordinateProper.nodes[x]? = some na ∧
        (na.node.border = -1 ∨ na.node.border = 1) ∧
        na.node.clusterPath.getLast? = some wNode.decl) →
      x ∈ layer.filter
        (fun v => wNode.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper v)) := by
    intro x hx h
    obtain ⟨na, hna, hb, ho⟩ := h
    rw [List.mem_filter]
    refine ⟨hx, ?_⟩
    have hnpW := hnp x na hna hb
    have heqW := (hpeq hna hb).2 ho
    rw [hnpW, heqW]
    exact List.isPrefixOf_iff_prefix.mpr List.prefix_rfl
  have hdisj : ∀ x, x ∈ layer.filter
        (fun v => uNode.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper v)) →
      x ∈ layer.filter
        (fun v => wNode.clusterPath.isPrefixOf (OrderImpl.nodePath run.coordinateProper v)) →
      False := by
    intro x hxU hxW
    rw [List.mem_filter] at hxU hxW
    obtain ⟨-, hpreU⟩ := hxU
    obtain ⟨-, hpreW⟩ := hxW
    rcases prefix_total (List.isPrefixOf_iff_prefix.mp hpreU)
      (List.isPrefixOf_iff_prefix.mp hpreW) with hUW | hWU
    · have hcon : wNode.clusterPath.contains uNode.decl = true :=
        prefix_last_mem_contains (List.isPrefixOf_iff_prefix.mpr hUW) hUlast
      rw [hpathW] at hcon
      exact absurd hcon (by decide)
    · have hcon : uNode.clusterPath.contains wNode.decl = true :=
        prefix_last_mem_contains (List.isPrefixOf_iff_prefix.mpr hWU) hWlast
      rw [hpathU] at hcon
      exact absurd hcon (by decide)
  exact ⟨hmemU, hmemW, hdisj⟩

/-- The exact cluster-separation-input fact: on every layer, the border
markers of two unrelated group declarations form disjoint blocks (replay of
`foreignBorderLayerOrder` over `componentRunX_spec` with `xbf_anchorPaths`). -/
theorem XB_foreignBorderLayerOrder_holds (exactIds : List String) :
    XB_ForeignBorderLayerOrder exactIds := by
  intro P inp o lines measured graph0 graph hg0 hgX comp hcomp candidate run labels
    orderOptions hrun u w uNode wNode hu hw hbU hbW hne hpathW hpathU layer hlayer
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrun
  have hwf := xbf_bordersWellFormed hg0 hgX hcomp hrun
  have horder' : OrderImpl.order run.coordinateProper orderOptions = .ok run.layers := by
    unfold OrderImpl.order
    rw [horder]
    dsimp only
    rw [hlayers]
  obtain ⟨hUlast, hWlast, hpeq⟩ := xbf_anchorPaths hg0 hgX hcomp hrun hu hw hbU hbW hne
  obtain ⟨hmemU, hmemW, hdisj⟩ :=
    xbf_layer_mem_disjoint hwf hUlast hWlast hpeq hpathW hpathU
  obtain ⟨k, hk, hkl⟩ := List.mem_iff_getElem.mp hlayer
  have hk2 : k < ord.layers.length := by rw [hlayers]; exact hk
  have hndlayer : layer.Nodup := by
    have h := OrderImpl.layer_nodup
      (OrderImpl.orderWithBudget_spec run.coordinateProper orderOptions ord horder).1 hk2
    rw [hlayers, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, hkl,
      Option.getD_some] at h
    exact h
  have hBUinfix := OrderImpl.order_clusters_contiguous run.coordinateProper
    orderOptions run.layers horder' layer hlayer uNode.clusterPath
  have hBWinfix := OrderImpl.order_clusters_contiguous run.coordinateProper
    orderOptions run.layers horder' layer hlayer wNode.clusterPath
  rcases infix_disjoint_ordered hndlayer hBUinfix hBWinfix hdisj with hUfirst | hWfirst
  · exact Or.inl (fun i j a b na nb hi hj hna hnb hbA hoA hbB hoB =>
      hUfirst a (hmemU a (List.mem_of_getElem? hi) ⟨na, hna, hbA, hoA⟩)
        b (hmemW b (List.mem_of_getElem? hj) ⟨nb, hnb, hbB, hoB⟩) i j hi hj)
  · exact Or.inr (fun i j a b na nb hi hj hna hnb hbA hoA hbB hoB =>
      hWfirst a (hmemU a (List.mem_of_getElem? hi) ⟨na, hna, hbA, hoA⟩)
        b (hmemW b (List.mem_of_getElem? hj) ⟨nb, hnb, hbB, hoB⟩) i j hi hj)

/-- Exact side record: a side marker of the exact bordered graph is already a
coordinate node (copy of the private `XSc8a_side_record` in
`ExactC8aSpansProof`). -/
private theorem xbf_side_record {P : Params} {exact : List Nat} {source : Proper}
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
(copy of the private `XSc8a_rank_pair` in `ExactC8aSpansProof`). -/
private theorem xbf_rank_pair (P : Params) (exact : List Nat) (source : Proper)
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
  refine ⟨left, right, xbf_side_record hl rfl (Or.inl rfl),
    xbf_side_record hr rfl (Or.inr rfl), ?_, ?_⟩
  · exact hrl
  · exact hrr

/-- Exact rank-pair-anchor residual: for two executed group declarations, the
titled exact graph carries a top anchor and a path-matched bottom anchor per
declaration (mirror of `ForeignRankPairAnchors` over the exact pipeline and
`componentRunX`; the single residual behind `XB_ForeignClusterRankSpans`).
Strictly narrower than the rank-span target: anchors only, no member
intervals and no per-rank marker pairs. Probe `ExactC8aSpansTProbe` evaluates
anchor existence plus the run equation on executed runs (`G`: 81 checks,
0 violations over siblings, nested, self-loop, empty-group, zero-size, and
nested-only inputs; the ill-formed input is rejected at prep). -/
def XB_ForeignRankPairAnchors (exactIds : List String) : Prop :=
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

/-- Per-rank marker cover for one declaration from its titled anchors
(replay of the `hpairU`/`hpairW` blocks of `foreignClusterRankSpans`). -/
private theorem xbf_pair_cover {P : Params} {exact : List Nat} {labeled : Proper}
    {run : Run} {decl : Nat} {top bot : ProperNode × Nat}
    (hcoord : coordinateGraphX P exact labeled = run.coordinateProper)
    (hlenEq : (titleReservations (sizeProperPortsX P exact labeled)).nodes.length =
      (titleReservations (sizeProperPortsX P exact labeled)).rank.length)
    (htop : top ∈ (titleReservations (sizeProperPortsX P exact labeled)).nodes.zipIdx)
    (hbtop : top.1.node.border = -2)
    (hlast : top.1.node.clusterPath.getLast? = some decl)
    (hbot : ((titleReservations (sizeProperPortsX P exact labeled)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath) = some bot) :
    ∀ (rank : Nat),
      (rk (titleReservations (sizeProperPortsX P exact labeled)).rank top.2).toNat ≤ rank →
      rank ≤ (rk (titleReservations (sizeProperPortsX P exact labeled)).rank bot.2).toNat →
      ∃ (mL mR : Nat) (nL nR : ProperNode),
        run.coordinateProper.nodes[mL]? = some nL ∧
        nL.node.border = -1 ∧ nL.node.clusterPath.getLast? = some decl ∧
        rk run.coordinateProper.rank mL = (rank : Int) ∧
        run.coordinateProper.nodes[mR]? = some nR ∧
        nR.node.border = 1 ∧ nR.node.clusterPath.getLast? = some decl ∧
        rk run.coordinateProper.rank mR = (rank : Int) := by
  intro rank hlo hhi
  obtain ⟨lU, rU, hLU, hRU, hrlU, hrrU⟩ :=
    xbf_rank_pair P exact labeled hlenEq htop hbtop hbot hlo hhi
  rw [hcoord] at hLU hRU hrlU hrrU
  have hrkLU : rk run.coordinateProper.rank lU = (rank : Int) := by
    simp only [rk, List.getD_eq_getElem?_getD, hrlU, Option.getD_some]
  have hrkRU : rk run.coordinateProper.rank rU = (rank : Int) := by
    simp only [rk, List.getD_eq_getElem?_getD, hrrU, Option.getD_some]
  exact ⟨lU, rU, _, _, hLU, rfl, hlast, hrkLU, hRU, rfl, hlast, hrkRU⟩

/-- The exact rank-assignment fact from its anchor residual: the titled
top/bottom anchors feed the per-rank marker pairs (`xbf_pair_cover`), while
the member-rank intervals come from the closed exact member bounds
(`XSc8a_memberBounds_holds`), mirroring `foreignClusterRankSpans`. -/
theorem XB_foreignClusterRankSpans_holds (exactIds : List String)
    (hanch : XB_ForeignRankPairAnchors exactIds) :
    XB_ForeignClusterRankSpans exactIds := by
  intro P inp o lines measured graph0 graph hg0 hgX hlines hwf hfp comp hcomp
    candidate run labels orderOptions hrun u w uNode wNode hu hw hbU hbW hne
  obtain ⟨labeled, rr, hcoord, halignedL, hkeys, hrr, hranks, hrecords, hlenEq,
    topU, botU, htopU, hbUtop, hlastU, hbotU, topW, botW, htopW, hbWtop, hlastW,
    hbotW⟩ := hanch hg0 hgX hcomp hrun hu hw hbU hbW hne
  obtain ⟨hordU, hordW, hmemU, hmemW⟩ :=
    XSc8a_memberBounds_holds exactIds hg0 hgX hlines hwf hfp hcomp hrun hu hw
      hbU hbW hne hcoord halignedL hkeys hrr hranks hrecords htopU hbUtop
      hlastU hbotU htopW hbWtop hlastW hbotW
  have hpairU := xbf_pair_cover (decl := uNode.decl) hcoord hlenEq htopU hbUtop
    hlastU hbotU
  have hpairW := xbf_pair_cover (decl := wNode.decl) hcoord hlenEq htopW hbWtop
    hlastW hbotW
  refine ⟨_, _, _, _, hordU, hordW, hmemU, hmemW, ?_, ?_⟩
  · intro r hrU hrW
    have h0r : 0 ≤ r := by omega
    have hrcast : ((r.toNat : Nat) : Int) = r := Int.toNat_of_nonneg h0r
    have hlo : (rk (titleReservations
        (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topU.2).toNat ≤
        r.toNat := by omega
    have hhi : r.toNat ≤
        (rk (titleReservations
          (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botU.2).toNat := by
      omega
    obtain ⟨mL, mR, nL, nR, hL, hbL, hoL, hrL, hR, hbR, hoR, hrR⟩ :=
      hpairU r.toNat hlo hhi
    refine ⟨mL, mR, nL, nR, hL, hbL, hoL, ?_, hR, hbR, hoR, ?_⟩
    · rw [← hrcast]; exact hrL
    · rw [← hrcast]; exact hrR
  · intro r hrU hrW
    have h0r : 0 ≤ r := by omega
    have hrcast : ((r.toNat : Nat) : Int) = r := Int.toNat_of_nonneg h0r
    have hlo : (rk (titleReservations
        (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank topW.2).toNat ≤
        r.toNat := by omega
    have hhi : r.toNat ≤
        (rk (titleReservations
          (sizeProperPortsX P (exactDecls exactIds inp) labeled)).rank botW.2).toNat := by
      omega
    obtain ⟨mL, mR, nL, nR, hL, hbL, hoL, hrL, hR, hbR, hoR, hrR⟩ :=
      hpairW r.toNat hlo hhi
    refine ⟨mL, mR, nL, nR, hL, hbL, hoL, ?_, hR, hbR, hoR, ?_⟩
    · rw [← hrcast]; exact hrL
    · rw [← hrcast]; exact hrR
end Elegant.Layered.PipelineImpl

import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.RegionActualParts
import Elegant.Layered.RegionRunSpec

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region part sizing (chosen-run residual).
Packet P1-followup of `local://region-tower-plan.md`: the universal
residual `R_PartSizingR` was FALSE (junk-node witness below: the part
equation does not pin the run), so it is deleted. What `componentRunR_specR`
(`RegionRunSpec.lean`) closes is kept here: the single chosen-run residual
`R_PartSizingRResidual` plus the closed dims/titles/slot facts on chosen
runs. The bounded and flat-inset replays live in place
(`exactComponentPlacementR_bounded_of_residual` and `flatInsetB_layoutRIds`
in `RegionFlatInset.lean`).

Truth probes (`proofs/wip/Probe/RegionPartSizingTProbe.lean`), all runs clean
(no warnings), verbatim outputs in order:
- `rpsTAllSizingB rpsTInp rpsTSets = Except.ok [true]`: the chosen run of the
  two-region witness satisfies dims, coverage, and slot.
- `rpsTCounterB = Except.ok (true, true, false)`: appending one junk node
  `{decl := 9999, w := -1, h := -1, clusterPath := [9999], dummy := false,
  edge := none}` to `run.proper.nodes` leaves `placeComponentExact`
  bit-identical (`rpsTPartEqB p0 p1 = true`) while the sizing check becomes
  false (`rpsTSizingB P cg run1 = false`). So the unconditional
  `R_PartSizingR` (and its dims conjunct over arbitrary runs) is FALSE; the
  junk run is not a chosen run (`rps_dims_of_specR` gives every successful
  `componentRunR` run nonnegative dims).
- `rpsTChosenCovEnvB = Except.ok (true, true)`: on the witness chosen run,
  coverage holds and every label envelope fits its stack, so the remaining
  chosen-run residual below is true on the executed probe.
- `rpsTAllSizingB rpsTInp5 rpsTSets = Except.ok [true, true]` and
  `rpsTChosenCovEnvGen rpsTInp5 rpsTSets = Except.ok (true, true)`: the base
  witness plus one empty group executes two sized components whose chosen
  run satisfies coverage and envelope fit.
- `rpsTInp2`/`rpsTInp3`/`rpsTInp4` (members nested under the unmodeled
  subgroup `S`, with and without a self-loop) are rejected with
  `Except.error LayoutError.domain` at `componentRunR`: preserved
  admission-rejection witnesses, not sizing counterexamples. No new
  admission rule is claimed from them.
-/
private theorem rps_dims_of_specR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    ProperDimsNonneg run.proper := by
  obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
    reserved, placedProper, q0, yt, ysMid, hRs, hRank, hNorm, hLabels, hCoord,
    hMin, hOrd, hLabelWidths, hPlaced, hProxy, hDrop, hLanes, hYt, hYsMid,
    hReserve, hRoutes, hRouting, hCoordProper, hCoordYs, hBudget, hExact⟩ :=
    componentRunR_specR h
  obtain ⟨_, _, _, _, hsize, _, _⟩ := CoordsImpl.rankCoordsWith_spec hYt
  have hd := proxyWidths_dims_nonneg (sizesNonneg_lookup hsize) hProxy
  rw [← hDrop]
  exact hd
private theorem rps_slot_of_specR {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    0 ≤ cg'.slot := by
  obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
    reserved, placedProper, q0, yt, ysMid, hRs, hRank, hNorm, hLabels, hCoord,
    hMin, hOrd, hLabelWidths, hPlaced, hProxy, hDrop, hLanes, hYt, hYsMid,
    hReserve, hRoutes, hRouting, hCoordProper, hCoordYs, hBudget, hExact⟩ :=
    componentRunR_specR h
  unfold NormalizeImpl.normalize at hNorm
  split at hNorm
  · simp at hNorm
  · rename_i slot hs
    split at hNorm
    · rename_i hc
      by_cases hz : cg'.slot = 0
      · omega
      · have he : cg'.slot = slot := by
          simpa [NormalizeImpl.slotOf, hz] using hs
        rw [he]
        exact hc.2.2
    · simp at hNorm
private theorem rps_border2_unchangedR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {j : Nat} {top0 : Node} (h0 : execution.graph0.nodes[j]? = some top0)
    (hb : top0.border = -2) : execution.graph.nodes[j]? = some top0 :=
  exactGraph_border2_unchangedX execution.graph0_eq execution.graph_eq h0 hb
private theorem rps_candidateR_nodes (spec : Option RegionSpec) (g : Graph)
    (comp : List Nat) (index : Nat) :
    (componentCandidateR spec g comp index).nodes = (componentGraph g comp).nodes := by
  cases spec with
  | none =>
    show (componentCandidate g comp index).nodes = _
    exact componentCandidate_nodes g comp index
  | some _ => unfold componentCandidateR componentGraph; dsimp only

private theorem rps_titles_of_specR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate : Nat} {spec' : Option RegionSpec}
    {cg' : Graph} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunR execution.params (exactDecls exactIds inp) spec' inp

      (componentCandidateR spec' execution.graph comp candidate)
      execution.measured orderOptions = .ok (cg', run)) :
    ∀ (i : Nat) (top : Node), cg'.nodes[i]? = some top → top.border = -2 →
      0 ≤ top.w ∧ execution.params.clusterPad ≤ top.h := by
  intro i top hi hb
  obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord, labelWidths,
    reserved, placedProper, q0, yt, ysMid, hRs, hRank, hNorm, hLabels, hCoord,
    hMin, hOrd, hLabelWidths, hPlaced, hProxy, hDrop, hLanes, hYt, hYsMid,
    hReserve, hRoutes, hRouting, hCoordProper, hCoordYs, hBudget, hExact⟩ :=
    componentRunR_specR hrun
  have hnodes : cg'.nodes =
      (componentCandidateR spec' execution.graph comp candidate).nodes := by
    rcases hRank with (⟨rr, hrs, hrr, hranks, hcg, hrb⟩ | ⟨rm, hrs, hrr⟩)
    · rw [hcg]
    · exact rankEquivalentR_nodes_eq hrr
  rw [hnodes, rps_candidateR_nodes] at hi
  have hmap : (componentGraph execution.graph comp).nodes =
      comp.map fun v => execution.graph.nodes.getD v default := rfl
  rw [hmap, List.getElem?_map] at hi
  cases hc : comp[i]? with
  | none => simp [hc] at hi
  | some key =>
    simp only [hc, Option.map_some, Option.some.injEq] at hi
    have hv : execution.graph.nodes.getD key default = top := hi
    have hj : key < execution.graph.nodes.length := by
      by_cases hj : key < execution.graph.nodes.length; exact hj
      have hnone : execution.graph.nodes[key]? = none :=
        List.getElem?_eq_none_iff.mpr (by omega)
      have hdefault : (default : Node) = top := by
        simpa [List.getD, hnone] using hv
      rw [← hdefault] at hb; change (0 : Int) = -2 at hb; omega
    have hget : execution.graph.nodes[key]? = some top := by
      have he : execution.graph.nodes[key] = top := by
        simpa [List.getD, hj] using hv
      simpa [hj] using congrArg some he
    have hlen0 : key < execution.graph0.nodes.length := by
      have hlg := exactGraph_length execution.graph_eq; omega
    have hget0 : execution.graph0.nodes[key]? =
        some (execution.graph0.nodes[key]) :=
      List.getElem?_eq_some_iff.mpr ⟨hlen0, rfl⟩
    obtain ⟨nd', hnd', hnb, _, _⟩ := exactGraph_node_key execution.graph_eq hget0
    have htopEq : top = nd' := Option.some.inj (hget.symm.trans hnd')
    have hborder0 : (execution.graph0.nodes[key]).border = -2 := by
      rw [← hnb, ← htopEq]; exact hb
    have hA := rps_border2_unchangedR execution hget0 hborder0
    have htop0eq : top = execution.graph0.nodes[key] :=
      Option.some.inj (hget.symm.trans hA)
    have htop0 : (componentCandidate execution.graph0 comp candidate).nodes[i]? =
        some top := by
      rw [componentCandidate_nodes]
      have hmap0 : (componentGraph execution.graph0 comp).nodes =
          comp.map fun v => execution.graph0.nodes.getD v default := rfl
      rw [hmap0, List.getElem?_map, hc]
      have hgd : execution.graph0.nodes.getD key default = top := by
        rw [List.getD_eq_getElem?_getD, hget0, Option.getD_some, htop0eq]
      simp only [Option.map_some, hgd]
    have hline := (checkedParams_sizing_nonneg execution.checked).1
    exact actual_title_dims_nonneg execution.graph0_eq hline htop0 hb








/-! ## The narrower closed form

`R_PartSizingR` is FALSE as a universal statement over arbitrary `(cg, run)`
pairs (junk-node witness in the module header: the part equation does not pin
the run). The stage equations close three conjuncts on *chosen* runs
(`R_partSizingR_chosenFacts` below: dims, titles, slot, straight from
`componentRunR_specR` with no well-formedness premise).

What remains is a single residual over executed runs: for every executed part,
its chosen `(cg, run)` pair (the one `actual_components_parts_geometryR`
exhibits) satisfies coverage and envelope fit. Coverage must pass through the
`some`-branch placement because `crossCoordsR` rewrites the proper graph, and
the envelope replay has no `componentRunR` analogue yet (X twin:
`componentRunX_envelopeFits`, `ExactPartBounded.lean:307`). Probe evidence:
`rpsTChosenCovEnvB = Except.ok (true, true)` on the two-region witness.
-/

/-- The two open conjuncts of `R_PartSizingR`, over the chosen `(cg, run)` pair
of each executed part. Strictly narrower than the target: drops the three
closed conjuncts and restricts arbitrary runs to chosen ones. -/
def R_PartSizingRResidual (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (q : List Nat × Part), q ∈ execution.componentsAcc.parts →
    ∀ {cg : Graph} {run : Run} {spec' : Option RegionSpec} {index : Nat},
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph q.1 index) execution.measured
      (candidateOrder index) = .ok (cg, run) →
    (∀ i, i < cg.nodes.length → i < run.proper.nodes.length) ∧
    EnvelopeFits execution.params cg run execution.measured

/-- Dims half, closed: the chosen run of an executed part has nonnegative dims.
This discharges the witnessed-false dims universal by restricting it to chosen
runs, where `componentRunR_specR` applies. -/
theorem R_PartSizingRDims_chosen {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {q : List Nat × Part} {cg : Graph} {run : Run} {spec' : Option RegionSpec}
    {index : Nat}
    (hrun : componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph q.1 index) execution.measured
      (candidateOrder index) = .ok (cg, run)) :
    ProperDimsNonneg run.proper :=
  rps_dims_of_specR hrun

/-- The chosen run of each executed part satisfies nonnegative dims, nonnegative
title anchors, and a nonnegative slot, straight from `componentRunR_specR`. This
is the part of `R_PartSizingR` that the stage equations do close. -/
theorem R_partSizingR_chosenFacts {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate : Nat} {spec' : Option RegionSpec}
    {cg' : Graph} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph comp candidate) execution.measured
      orderOptions = .ok (cg', run)) :
    ProperDimsNonneg run.proper ∧
    (∀ (i : Nat) (top : Node), cg'.nodes[i]? = some top →
      top.border = -2 → 0 ≤ top.w ∧ execution.params.clusterPad ≤ top.h) ∧
    0 ≤ cg'.slot :=
  ⟨rps_dims_of_specR hrun,
    fun i top hi hb => rps_titles_of_specR execution hrun i top hi hb,
    rps_slot_of_specR hrun⟩

end PipelineImpl
end Layered
end Elegant

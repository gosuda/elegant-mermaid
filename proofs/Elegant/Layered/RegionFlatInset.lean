import Elegant.Layered.RegionActualParts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.InsetFit
import Elegant.Layered.RegionPartSizing

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Region flat inset (`layoutRIds`).

Packet P1 of the region tower: `flatInsetB_layoutRIds`, the region analogue of
the `flatInset` term of `exactBaseSeams` (`Kinds/UsecaseValidExact.lean:199-207`).

Route: `layoutRIds_sceneExecution` (`RegionFoundation.lean:208`) gives the
`SceneExecutionR`; `SceneExecutionR.packedAcc_boundedR` (region analogue of
`SceneExecutionX.packedAcc_bounded`, `ExactFlatFacts.lean:983`) lifts
per-part boundedness through the shared `packAcc`; `sceneOf_boxes_inset`
(`InsetFit.lean`) lands in the margin inset. Per-part boundedness is
`exactComponentPlacementR_bounded_of_residual`, proved from
`actual_components_parts_geometryR` (`RegionActualParts.lean`) via the shared
`placeComponentExact_partBounded` (`ExactPartBounded.lean:690`), modulo the
single chosen-run residual `R_PartSizingRResidual` (`RegionPartSizing.lean`):
the stage equations close dims, titles, and slot on chosen runs, leaving
coverage and envelope fit open. The universal `R_PartSizingR` was FALSE
(junk-node witness in `RegionPartSizing.lean`: the part equation does not pin
the run) and is deleted; no theorem takes it.

Truth probes (`proofs/wip/Probe/RegionFlatInsetProbe.lean`, all `.ok [true]`):
* two-region witness (copies `rapProbeInp`/`rapProbeSets` of
  `RegionActualParts.lean:49-102`): every placed part satisfies `PartBounded`;
* own witness with a nested region (`G` over `{H}`, `H` over `{J}`) and a
  reversed edge (`b` -> `a`, inward against containment): same results.
-/
open RegionImpl

/-- The region execution's measured labels have nonnegative dimensions (replay
of `SceneExecutionX.measured_nonneg`; the equations are shared). -/
theorem SceneExecutionR.measured_nonnegR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    ∀ l ∈ execution.measured, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter := by
  have hs := (checkedParams_valid execution.checked).2.2.1
  have hline := (checkedParams_sizing_nonneg execution.checked).1
  exact measureLabels_nonneg hline (by omega) execution.measured_eq

/-- The bounded conjunct of `ExactComponentPlacementR` from the single chosen-run
residual: replay of the deleted false-premise `exactPartsBoundedR` with the
three closed conjuncts supplied by `R_partSizingR_chosenFacts`
(`RegionPartSizing.lean`). -/
theorem exactComponentPlacementR_bounded_of_residual {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hres : R_PartSizingRResidual exactIds idSets) :
    ∀ q ∈ execution.componentsAcc.parts, PartBounded q.2 := by
  intro q hq
  obtain ⟨_, hall⟩ :=
    actual_components_parts_geometryR (by rfl) execution.components_eq
  obtain ⟨index, chosen, cg, run, loops, area, spec', hi, hc, hv, hrs, hrun,
    hloops, heq⟩ := hall q hq
  obtain ⟨hdims, htitle, hslot⟩ := R_partSizingR_chosenFacts execution hrun
  obtain ⟨hcov, hfit⟩ := hres execution q hq hrun
  have hbound := placeComponentExact_partBounded execution.params cg run
    execution.measured loops hdims hcov htitle
    (SceneExecutionR.measured_nonnegR execution) hslot hfit
  rw [heq]
  exact hbound
/-- Fold-level packed boundedness, generic over the region spec: the replay
engine for `packedAcc_boundedR`. Stating `spec` as a variable keeps the
application-site instantiation first-order. -/
private theorem rfiFoldAccBoundedR (P : Params) (exactIds : List String)
    (spec : Option RegionSpec) (inp : Input) (o : Options) (graph : Graph)
    (measured : List MeasuredLabel) (mid packed : Acc)
    (hfold : (components graph).foldlM
      (fun acc comp => layoutComponentR P exactIds spec inp o graph acc comp measured)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩ = .ok mid)
    (hpack : packAcc P o mid = .ok packed)
    (hparts : ∀ q ∈ mid.parts, PartBounded q.2) :
    AccBounded packed.canvasW packed.canvasH packed := by
  have hstart_rects : ∀ (i : Nat) (r : Rect),
      mid.rects[i]? = some r →
      ((∀ q ∈ mid.parts, ¬ RectCovered q.1 q.2.rects.length i) ∨
        i ≥ mid.rects.size) → r = default := by
    refine foldlM_rects_uncovered
      (fun a c => layoutComponentR P exactIds spec inp o graph a c measured)
      (fun start comp acc' hc => layoutComponentR_rects_cover hc)
      (fun start comp acc' hc => layoutComponentR_parts_mono hc)
      (components graph)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩
      mid hfold ?_
    exact fun i r hi _ => (layout_startAcc_defaults inp).1 i r hi
  have hstart_routes : ∀ (i : Nat) (pts : List Point),
      mid.routes[i]? = some pts →
      ((∀ q ∈ mid.parts, ¬ RouteCovered q.2.routes i) ∨
        i ≥ mid.routes.size) → pts = [] := by
    refine foldlM_routes_uncovered
      (fun a c => layoutComponentR P exactIds spec inp o graph a c measured)
      (fun start comp acc' hc => layoutComponentR_routes_cover hc)
      (fun start comp acc' hc => layoutComponentR_parts_mono hc)
      (components graph)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩
      mid hfold ?_
    exact fun i pts hi _ => (layout_startAcc_defaults inp).2.1 i pts hi
  have hstart_labels : ∀ (i : Nat) (r : Rect),
      mid.labels[i]? = some r →
      ((∀ q ∈ mid.parts, ¬ LabelCovered q.2.labels i) ∨
        i ≥ mid.labels.size) → r = default := by
    refine foldlM_labels_uncovered
      (fun a c => layoutComponentR P exactIds spec inp o graph a c measured)
      (fun start comp acc' hc => layoutComponentR_labels_cover hc)
      (fun start comp acc' hc => layoutComponentR_parts_mono hc)
      (components graph)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩
      mid hfold ?_
    exact fun i r hi _ => (layout_startAcc_defaults inp).2.2 i r hi
  exact packAcc_bounded hparts hstart_rects hstart_routes hstart_labels hpack

/-- The region packed accumulator is bounded when every component part is
(region analogue of `SceneExecutionX.packedAcc_bounded`,
`ExactFlatFacts.lean:983`). -/
theorem SceneExecutionR.packedAcc_boundedR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hparts : ∀ q ∈ execution.componentsAcc.parts, PartBounded q.2) :
    AccBounded execution.packedAcc.canvasW execution.packedAcc.canvasH
      execution.packedAcc :=
  rfiFoldAccBoundedR execution.params exactIds _ inp o execution.graph
    execution.measured execution.componentsAcc execution.packedAcc
    execution.components_eq execution.packed_eq hparts

/-- The region flat inset: `layoutRIds` keeps every scene box inside the margin
inset of its canvas (region analogue of the `flatInset` term of
`exactBaseSeams`, `Kinds/UsecaseValidExact.lean:199-207`), modulo the single
chosen-run sizing residual `R_PartSizingRResidual` (`RegionPartSizing.lean`). -/
theorem flatInsetB_layoutRIds (exactIds : List String)
    (idSets : List (String × List String))
    (hres : R_PartSizingRResidual exactIds idSets) :
    FlatInsetB (layoutRIds exactIds idSets) := by
  intro inp o res h
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  have hacc := SceneExecutionR.packedAcc_boundedR execution
    (exactComponentPlacementR_bounded_of_residual execution hres)
  have hm1 := checkedParams_canvasMargin_ge_one execution.checked
  refine ⟨execution.params, execution.checked, by omega, ?_⟩
  rw [execution.scene_eq]
  exact sceneOf_boxes_inset execution.params inp o execution.lines
    execution.packedAcc execution.measured hacc (by omega)

end PipelineImpl

end Layered
end Elegant

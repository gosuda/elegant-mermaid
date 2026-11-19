import Elegant.Layered.RegionFlatInset
import Elegant.Layered.RecursiveBLiftsB
import Elegant.Layered.RegionPartSizing

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Region canvas margins (`layoutRIds` over the reindexing base).

Packet P9 first half: `exactCanvasMarginsR`, the region analogue of
`exactCanvasMargins` (`Layered/ExactFitClosure.lean:91-109`) for the
reindexing base
`fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o'`.

Route: the region leaf fact below (replay of `X_layout_canvas_margins`,
`ExactFitClosure.lean:70-85`, via `layoutRIds_sceneExecution` and the shared
`packAcc_canvas_nonneg` / `sceneOf`), then the same fuel induction over
`layoutRecursiveB` with the shared `expandChild_canvas`. The canvas margin
comes from the shared `sceneOf`/`packAcc`, so no sizing residual is consumed;
the reindex inset below takes the chosen-run residual `R_PartSizingRResidual`
(`RegionPartSizing.lean`).
-/

/-- Region leaf canvas margins: `layoutRIds` builds its scene with the same
`sceneOf` call as `layoutX`, so the proof is the exact leaf fact with the
region execution. No sizing residual is needed: `packAcc_canvas_nonneg`
holds for every successful `packAcc`. -/
private theorem rfiLayoutCanvasMarginsR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (h : layoutRIds exactIds idSets inp o = .ok res) :
    2 * canvasMarginOf o.profile inp.kind ≤ res.scene.canvas.w ∧
    2 * canvasMarginOf o.profile inp.kind ≤ res.scene.canvas.h := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  have hb := packAcc_canvas_nonneg execution.packed_eq
  rw [← checkedParams_canvasMargin execution.checked]
  rw [execution.scene_eq]
  change _ ≤ (orientCanvas o.direction
    (execution.packedAcc.canvasW + 2 * _)
    (execution.packedAcc.canvasH + 2 * _)).w ∧
    _ ≤ (orientCanvas o.direction
    (execution.packedAcc.canvasW + 2 * _)
    (execution.packedAcc.canvasH + 2 * _)).h
  cases o.direction <;> simp only [orientCanvas] <;> omega

/-- The region pipeline discharges the base-parametric canvas-margin fact over
the reindexing base: every `layoutRecursiveB` result keeps both margins. The
induction copies `exactCanvasMargins`, with the region leaf fact above and the
shared `expandChild_canvas`. No sizing premise is needed: `packAcc_canvas_nonneg`
holds for every successful `packAcc`. -/
theorem exactCanvasMarginsR (exactIds : List String)
    (idSets : List (String × List String)) :
    CanvasMarginsB (fun sub o' =>
      layoutRIds exactIds (reindexRegionSets idSets sub) sub o') := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res h P hP
    have hm := rfiLayoutCanvasMarginsR h
    rw [checkedParams_canvasMargin hP]
    exact hm
  | succ fuel ih =>
    intro inp o res h P hP
    rcases layoutRecursiveB_succ_sources
      (fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o')
      h with ⟨_, hlayout⟩ |
      ⟨group, Pm, metric, child, titleLines, parent, hg, hPm, hm, hc, ht, hp,
        hexpand⟩
    · have hm := rfiLayoutCanvasMarginsR hlayout
      rw [checkedParams_canvasMargin hP]
      exact hm
    · have hc2 := expandChild_canvas hexpand
      rw [hc2]
      exact ih _ _ _ hp P hP
/-- Inset restated for the reindexing base: `flatInsetB_layoutRIds` is stated
for a fixed `idSets`, so each sub-input instantiates it at its reindexed sets,
taking the chosen-run residual per sub-input. -/
theorem flatInsetB_layoutRIds_reindex (exactIds : List String)
    (idSets : List (String × List String))
    (hres : ∀ (sub : Input),
      R_PartSizingRResidual exactIds (reindexRegionSets idSets sub)) :
    FlatInsetB (fun sub o' =>
      layoutRIds exactIds (reindexRegionSets idSets sub) sub o') := by
  intro sub o' res' h
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  have hacc := SceneExecutionR.packedAcc_boundedR execution
    (exactComponentPlacementR_bounded_of_residual execution (hres sub))
  have hm1 := checkedParams_canvasMargin_ge_one execution.checked
  refine ⟨execution.params, execution.checked, by omega, ?_⟩
  rw [execution.scene_eq]
  exact sceneOf_boxes_inset execution.params sub o' execution.lines
    execution.packedAcc execution.measured hacc (by omega)


end PipelineImpl
end Layered
end Elegant

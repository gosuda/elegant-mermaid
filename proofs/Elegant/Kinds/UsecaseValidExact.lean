import Elegant.Layered.FamilyAssemblyB
import Elegant.Layered.InputFixedFit
import Elegant.Layered.BoxRouteIdsDisjoint
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.ExactFlatC3Closure
import Elegant.Layered.ExactFlatC2
import Elegant.Layered.ExactSubInputStepC2
import Elegant.Layered.ExactFlatC5Closed
import Elegant.Layered.ExactFitClosure
import Elegant.Layered.ExactStepFacts
import Elegant.Layered.FrameClearanceSeam
import Elegant.Layered.BracketInsidePremisesProof
import Elegant.Layered.DummyNestedMarkerProof
import Elegant.Layered.TitleCopySpanProof
import Elegant.Layered.RunLocalLabelClearanceProof
import Elegant.Layered.RunLocalSeparationsProof
import Elegant.Layered.RunLocalLoopFootprintProof
import Elegant.Layered.LabelsC7Bridges
import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.RouteLabelsPlacedProof
import Elegant.Layered.ExclusiveKeyOutsideCgPathsProof
import Elegant.Layered.CaptionsSeamProof
import Elegant.Layered.CaptionCrossPartProof
import Elegant.Layered.FrameLabelsProof
import Elegant.Layered.LoopFootprintResidualProof
import Elegant.Layered.CaptionResidualsProof
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.FallbackCaptionClearProof
import Elegant.Layered.FlatC8aExecutedProof
import Elegant.Layered.FallbackOwnerFrameProof
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.ForeignBorderChainXAlignedClosed
import Elegant.Layered.TitleExclusiveSamePartProof
import Elegant.Layered.ExactFlatC7
import Elegant.Layered.ExactFlatC7Fit
import Elegant.Layered.ExactFlatC7ExclusiveKey
import Elegant.Layered.ExactFlatC7Forward
import Elegant.Layered.ExactFlatC7Placed
import Elegant.Layered.ExactFlatC7Reversed
import Elegant.Layered.ExactFlatC8b
import Elegant.Layered.ExactLoopEnvelopeSeparationProof
import Elegant.Layered.ExactPackedTransportResidualsProof
import Elegant.Layered.ExactStepShortFacts
import Elegant.Layered.LoopFootprintTopSeparationCondProof
import Elegant.Layered.ExecutedPartFrameCoresClosed
import Elegant.Layered.ExactSeamClosureGlue
import Elegant.Layered.ExactStepGeometryProof
import Elegant.Layered.ExactFlatC6WProof
import Elegant.Layered.ExactFlatC7ExclusiveKey
import Elegant.Layered.ExactFlatC8bWProof
import Elegant.Layered.ExactFallbackCaptionFactsProof
import Elegant.Layered.ExactCaptionFitFactsProof
import Elegant.Layered.ExactCaptionFallbackProof
import Elegant.Layered.LoopTopSliverGapProof
import Elegant.Kinds.Usecase
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Kinds.Usecase

/-- The adapter ids the exact pipeline must keep: every actor box. -/
def actorIds (m : Model) : List String :=
  (m.boxes.filter fun b => isActor b.shape).map (·.id)

/-- The `BaseSeams (layoutX exactIds)` fields with no exact-pipeline proof yet.

// `flatInset` is filled by replaying `layoutX_inset` on `exactPartsBounded'`
// (the inset body consumes only placement conjunct 1); `flatC4` from
// `SceneExecutionX.routes_orthogonal`; `subInputC2` from
// `subInputWellFormedC2`; `partsSep` from `labelsC7_partsSeparated` (all
// base-independent).
// Removed fields and the theorems proving them:
// - `flatC3`: `flatC3B_layoutX` (`ExactFlatC3Closure.lean`), no hypotheses.
// - `flatC2`: `flatC2B_layoutX` (`ExactFlatC2.lean`), no hypotheses.
// - `flatC5`: `flatC5B_layoutX_closed` (`ExactFlatC5Closed.lean`), no hypotheses.
// - `canvasMargins`: `exactCanvasMargins` (`ExactFitClosure.lean`), no hypotheses.
// - `fitClosed`: `exactFitClosed` (`ExactFitClosure.lean`), no hypotheses.
// - `subInputB`: `subInputWellFormedB_layoutX` (`ExactSubInputStepC2.lean`),
//   no hypotheses.
// - `stepC2`: `stepC2_layoutX` (`ExactSubInputStepC2.lean`), no hypotheses.
// - `frameClear` (base-independent: its type mentions only the plain
//   `SceneExecution`): `frameClearanceSeam_holds` over the executed bracket
//   premises, the same term `baseSeams_of_layered` uses
//   (`BracketInsidePremisesProof.lean`, `DummyNestedMarkerProof.lean`,
//   `TitleCopySpanProof.lean`).
// - `fallbackOwnerFrameClear`: `fallbackOwnerFrameClear_executed`
//   (`FallbackOwnerFrameProof.lean`) over `flatC8a_executed`
//   (`FlatC8aExecutedProof.lean`), with the span premises built from the
//   `foreignBorderDivergeStable` field below (via `foreignBorderChainXAligned'`),
//   the closed `bracketMarkersAtRank'` (`SideMarkerTopInCandidateProof.lean`)
//   and the other closed span theorems, plus `fallbackOwnerStrictStep_executed`
//   (`FallbackOwnerStrictStepProof.lean`).
//
// - `stepC6Anchors`: `stepC6Anchors_layoutX` (`ExactStepShortFacts.lean`),
//   no hypotheses.
// - `stepC8aGeometry`: `stepC8aGeometry_layoutX` (`ExactStepShortFacts.lean`),
//   no hypotheses.
// - `stepC8aAncestry`: `stepC8aAncestry_layoutX` (`ExactStepShortFacts.lean`),
//   no hypotheses.
// Replaced `labelRuns`/`captions` (both base-independent): derived in
// `exactBaseSeams` by the same `baseSeams_of_layered` terms over the closed
// beyond-proper separation (`loopFootprintBeyondProper_closed`
// (`LoopTopSliverGapProof.lean`) over `foreignBorderChainXAligned'` of the kept
// `foreignBorderDivergeStable` field and the closed `topSliverMarkerReady_of_span`
// of `topSliverSpanCovered_holds`) for `labelRuns`; `foreignBorderDivergeStable`,
// `loopHullRightCover`, `loopHullRightNeighborCover` for `captions`, with the
// old `titleExclusiveSamePart` closed by `titleExclusiveSamePart_holds` and the
// old `executedPartFrameCores` closed by `executedPartFrameCores_closed`). There
// is no `routeLabelsPlaced` field: it is a closed proved theorem used inside
// the `labelRuns` term. There is no `bracketMarkersAtRank` field either: the
// proved `bracketMarkersAtRank'` is used directly.
//
// Replaced `flatC7`: derived in `exactBaseSeams` by `flatC7B_layoutX_fit`
// (`ExactFlatC7Fit.lean`) over the narrower open fields below (the kept
// `loopEnvelopeMiss` via `X_runLocalLoopSeparation_of_envelopeMiss`, and
// `captionScopeFit`), with the other five premises closed inside by
// `x_runLocalForwardSeparation_holds` (`ExactFlatC7Forward.lean`),
// `x_runLocalReversedSeparation_holds` (`ExactFlatC7Reversed.lean`),
// `x_routeLabelsPlaced_holds` (`ExactFlatC7Placed.lean`),
// `x_exclusiveRunNodeDecl_holds` and `x_exclusiveKeyOutsideCgPaths_holds`
// (`ExactFlatC7ExclusiveKey.lean`). `X_loopEnvelopeMiss_holds`
// (`ExactLoopEnvelopeMissProof.lean`) would split the miss into three named
// directions, but that module does not compile at HEAD and none of the
// directions is proved, so the split is blocked.
// Replaced `flatC8b`: derived in `exactBaseSeams` by `flatC8bB_layoutX_W`
// (`ExactFlatC8bWProof.lean`) over the kept `partFrameCores` field (fed as the
// W cores by ignoring the local premises), the closed
// `X_packedPartTransportBounded_closed`
// (`ExactPackedTransportResidualsProof.lean`), and the W fallback clearance
// `X_fallbackCaptionClearBW_closed` (`ExactFallbackCaptionFactsProof.lean`)
// over the six narrower open fields below (`fbContain`, `fbFix`, `fbTitle`,
// `fbDisj`, `fbStrict`, `fbCases`).
//
// Replaced `flatC6`: derived in `exactBaseSeams` by `flatC6B_layoutXW`
// (`ExactFlatC6WProof.lean`) over the eight narrower open W fields below, with
// the run-id premise closed by `x_exclusiveRunNodeDecl_holds`
// (`ExactFlatC7ExclusiveKey.lean`).
//
// Replaced step fields: `stepC6`, `stepC7`, `stepC8a`, `stepC8b` are derived in
// `exactBaseSeams` from the geometry hypothesis fields below via
// `stepC6_layoutX`, `stepC7_layoutX`, `stepC8a_layoutX`, `stepC8b_layoutX`
// (`ExactStepFacts.lean`): `stepC6Geometry_layoutX` over the two named C6
// residuals, `stepC7Geometry_layoutX` over the three named C7 residuals, and
// `stepC8bGeometry_layoutX` over the named C8b core plus the four named C8b
// residuals (all `ExactStepGeometryProof.lean`, residual shapes named in
// `ExactSeamClosureGlue.lean`), with the box/ancestry/fit premises closed by
// `XG_child_boxes_insetB`, `XG_content_fit_strict`
// (`ExactStepGeometryProof.lean`), and `stepC8aAncestry_layoutX`
// (`ExactStepShortFacts.lean`); the anchor/ancestry/C8a-geometry premises stay
// closed by `stepC6Anchors_layoutX`, `stepC8aAncestry_layoutX`, and
// `stepC8aGeometry_layoutX` (`ExactStepShortFacts.lean`). The narrower
// parent-frame replacement is blocked too: the old plain fields were plain
// `RecursiveStepFacts`, while these fields are per-call B facts, so the plain
// `c6Geometry_of_seams`/`c8bGeometry_of_seams` derivations do not apply.
// proving its counterpart, for the porting slices. -/
structure ExactSeams (exactIds : List String) : Prop where
  /-- Narrower open fact consumed by `flatC6B_layoutXW` as `hkeysW`. -/
  x6keys : Layered.PipelineImpl.X6_ChainEndpointKeysW exactIds
  /-- Narrower open fact consumed by `flatC6B_layoutXW` as `hpathsW`. -/
  x6paths : Layered.PipelineImpl.X6_DeclOutsidePathsW exactIds
  /-- Narrower open fact consumed by `flatC6B_layoutXW` as `hposW`. -/
  x6pos : Layered.PipelineImpl.X6_ShelfPositiveW exactIds
  /-- Narrower open fact consumed by `flatC6B_layoutXW` as `hsepW`. -/
  x6sep : Layered.PipelineImpl.X6_LoopFootprintSeparationW exactIds
  /-- Narrower open fact consumed by `flatC6B_layoutXW` as `hbordW`. -/
  x6bord : Layered.PipelineImpl.X6_BorderZeroRealW exactIds
  /-- Narrower open fact consumed by `flatC6B_layoutXW` as `hbridgeW`. -/
  x6bridge : Layered.PipelineImpl.X6_RouteScopeBridgeW exactIds
  /-- Narrower open fact consumed by `flatC6B_layoutXW` as `hchainW` (the run-id antecedent is the closed `x_exclusiveRunNodeDecl_holds`). -/
  x6chain : Layered.PipelineImpl.X_ExclusiveRunNodeDecl exactIds → Layered.PipelineImpl.X6_ChainEndpointKeysW exactIds → Layered.PipelineImpl.X6_DeclOutsidePathsW exactIds → Layered.PipelineImpl.X6_ShelfPositiveW exactIds → Layered.PipelineImpl.X6_ChainCaseW exactIds
  /-- Narrower open fact consumed by `flatC6B_layoutXW` as `hloopW`. -/
  x6loop : Layered.PipelineImpl.X6_ShelfPositiveW exactIds → Layered.PipelineImpl.X6_BorderZeroRealW exactIds → Layered.PipelineImpl.X6_LoopCaseW exactIds
  /-- Narrower open fact consumed by `flatC7B_layoutX_fit` via `X_runLocalLoopSeparation_of_envelopeMiss`. Best partial: `X_loopEnvelopeMiss_holds` (`ExactLoopEnvelopeMissProof.lean`) over the three miss directions, but that module does not compile at HEAD and none of the directions is proved, so the whole miss stays open. -/
  loopEnvelopeMiss : Layered.PipelineImpl.X_LoopEnvelopeMiss exactIds
  /-- Narrower open fact consumed by `flatC7B_layoutX_fit` as `hcapFit`: the fit-conditioned caption clearance. -/
  captionScopeFit : Layered.PipelineImpl.X_CaptionScopeClearanceFit exactIds
  /-- `flatC8aB_layoutX` still needs the exact C8a span facts and `X_ForeignBorderChainXAligned`. -/
  flatC8a : Layered.PipelineImpl.FlatC8aB (Layered.PipelineImpl.layoutX exactIds)
  /-- Narrower open fact consumed by `flatC8bB_layoutX_W` as the W cores. -/
  partFrameCores : Layered.PipelineImpl.X_ExecutedPartFrameCoresB8 exactIds
  /-- Narrower open fact consumed by `X_fallbackCaptionClearBW_closed` as `hcontain`: the fit-conditioned fallback containment. -/
  fbContain : Layered.PipelineImpl.X_OwnerCaptionContainFallbackFit exactIds
  /-- Narrower open fact consumed by `X_fallbackCaptionClearBW_closed` as `hfix`: the fixed-owner output fit. -/
  fbFix : Layered.PipelineImpl.X_FixedOwnerFitX exactIds
  /-- Narrower open fact consumed by `X_fallbackCaptionClearBW_closed` as `htitle`: non-fixed group title presence. -/
  fbTitle : Layered.PipelineImpl.X_NonfixedGroupTitleX exactIds
  /-- Narrower open fact consumed by `X_fallbackCaptionClearBW_closed` as `hdisj`: the fallback-owner C8a instance. -/
  fbDisj : Layered.PipelineImpl.X_OwnerFrameDisjointX exactIds
  /-- Narrower open fact consumed by `X_fallbackCaptionClearBW_closed` as `hastrict`: W ancestor-frame strictness. -/
  fbStrict : Layered.PipelineImpl.X_AncestorFrameStrictW exactIds
  /-- Narrower open fact consumed by `X_fallbackCaptionClearBW_closed` as `hcases`: the fallback-owner case split. -/
  fbCases : Layered.PipelineImpl.X_FallbackOwnerCasesX exactIds
  /-- Narrower open fact consumed by `captions` via `flatC8a_executed`: ordering-stage stability of divergent blocks. Closed to the old alignment by `foreignBorderChainXAligned'` (`ForeignBorderChainXAlignedClosed.lean`). -/
  foreignBorderDivergeStable : Layered.PipelineImpl.ForeignBorderDivergeStable
  /-- Narrower open fact consumed by `captions`: right hull cover of loop groups. Best partial: `loopHullRightCover_holds` modulo `R1ExtentFitGap` (`LoopHullCoverProof.lean`). -/
  loopHullRightCover : ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
    WellFormed (Layered.inputModel inp o) → Layered.framedParents inp = true →
    ∀ (execution : Layered.PipelineImpl.SceneExecution inp o res) (comp : List Nat),
      comp ∈ Layered.PipelineImpl.components execution.graph →
      ∀ (candidate : Nat) (run : Layered.PipelineImpl.Run) (orderOptions : Layered.OrderOptions),
        Layered.PipelineImpl.componentRun execution.params (Layered.PipelineImpl.componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run →
        Layered.PipelineImpl.LoopHullRightCover execution.params (Layered.PipelineImpl.componentCandidate execution.graph comp candidate) run execution.measured
  /-- Narrower open fact consumed by `captions`: neighbor right hull cover of loop groups. Best partial: `loopHullRightNeighborCover_holds` modulo `R3ExtentFitGap` (`LoopHullCoverProof.lean`). -/
  loopHullRightNeighborCover : ∀ (inp : Layered.Input) (o : Options) (res : Layered.FamilyResult),
    WellFormed (Layered.inputModel inp o) → Layered.framedParents inp = true →
    ∀ (execution : Layered.PipelineImpl.SceneExecution inp o res) (comp : List Nat),
      comp ∈ Layered.PipelineImpl.components execution.graph →
      ∀ (candidate : Nat) (run : Layered.PipelineImpl.Run) (orderOptions : Layered.OrderOptions),
        Layered.PipelineImpl.componentRun execution.params (Layered.PipelineImpl.componentCandidate execution.graph comp candidate) execution.measured orderOptions = .ok run →
        Layered.PipelineImpl.LoopHullRightNeighborCover execution.params (Layered.PipelineImpl.componentCandidate execution.graph comp candidate) run execution.measured
  /-- Open C6 residual consumed by `stepC6Geometry_layoutX` as `hDisjB`. -/
  stepC6Disj : Layered.PipelineImpl.XG_StepC6DisjB exactIds
  /-- Open C6 residual consumed by `stepC6Geometry_layoutX` as `hMissB`. -/
  stepC6Miss : Layered.PipelineImpl.XG_StepC6MissB exactIds
  /-- Open C7 residual consumed by `stepC7Geometry_layoutX` as `hchildB`. -/
  stepC7Child : Layered.PipelineImpl.XG_StepC7ChildB exactIds
  /-- Open C7 residual consumed by `stepC7Geometry_layoutX` as `hparentB`. -/
  stepC7Parent : Layered.PipelineImpl.XG_StepC7ParentB exactIds
  /-- Open C7 residual consumed by `stepC7Geometry_layoutX` as `hcaptionB`. -/
  stepC7Caption : Layered.PipelineImpl.XG_StepC7CaptionB exactIds
  /-- Open C8b residual consumed by `stepC8bGeometry_layoutX` as `hCore`. -/
  stepC8bCore : Layered.PipelineImpl.XG_C8bCoreB exactIds
  /-- Open C8b residual consumed by `stepC8bGeometry_layoutX` as `hChildLabelsB`. -/
  stepC8bChildLabels : Layered.PipelineImpl.XG_StepC8bChildLabelsB exactIds
  /-- Open C8b residual consumed by `stepC8bGeometry_layoutX` as `hCapStrictB`. -/
  stepC8bCapStrict : Layered.PipelineImpl.XG_StepC8bCapStrictB exactIds
  /-- Open C8b residual consumed by `stepC8bGeometry_layoutX` as `hCapDisjB`. -/
  stepC8bCapDisj : Layered.PipelineImpl.XG_StepC8bCapDisjB exactIds
  /-- Open C8b residual consumed by `stepC8bGeometry_layoutX` as `hParentFrameB`. -/
  stepC8bParentFrame : Layered.PipelineImpl.XG_StepC8bParentFrameB exactIds

/-- Seams for the exact base: `flatInset` replays `layoutX_inset` on
`exactPartsBounded'` (the inset body consumes only placement conjunct 1, which
holds with no hypothesis); `flatC4` from `SceneExecutionX.routes_orthogonal`;
`subInputC2` from `subInputWellFormedC2`; `partsSep` from
`labelsC7_partsSeparated` (all base-independent). `flatC3`, `flatC2`, `flatC5`,
`canvasMargins`, `fitClosed`, `subInputB`, and `stepC2` are discharged by their
no-hypothesis theorems; `frameClear` by `frameClearanceSeam_holds` over the
executed bracket premises, and `labelRuns` /
`captions` by the `baseSeams_of_layered` terms over the narrower `ExactSeams`
fields; the step seams by the
`stepC*_layoutX` assemblers over the `ExactSeams` geometry/ancestry hypotheses.
Every other field is the matching `ExactSeams` projection. Stated as a `theorem`
because the target is
a `Prop` (a `def` would warn). -/
theorem exactBaseSeams (exactIds : List String) (R : ExactSeams exactIds) :
    Layered.PipelineImpl.BaseSeams (Layered.PipelineImpl.layoutX exactIds) where
  flatInset := fun inp o res h => by
    obtain ⟨execution⟩ := Layered.PipelineImpl.layoutX_sceneExecution h
    have hacc := Layered.PipelineImpl.SceneExecutionX.packedAcc_bounded execution
      (Layered.PipelineImpl.exactPartsBounded' execution)
    have hm1 := Layered.PipelineImpl.checkedParams_canvasMargin_ge_one execution.checked
    refine ⟨execution.params, execution.checked, by omega, ?_⟩
    rw [execution.scene_eq]
    exact Layered.PipelineImpl.sceneOf_boxes_inset execution.params inp o execution.lines
      execution.packedAcc execution.measured hacc (by omega)
  flatC3 := Layered.PipelineImpl.flatC3B_layoutX exactIds
  flatC2 := Layered.PipelineImpl.flatC2B_layoutX exactIds
  flatC4 := fun inp o res h route hroute => by
    obtain ⟨execution⟩ := Layered.PipelineImpl.layoutX_sceneExecution h
    exact Layered.PipelineImpl.SceneExecutionX.routes_orthogonal execution route hroute
  flatC5 := Layered.PipelineImpl.flatC5B_layoutX_closed exactIds
  flatC6 := Layered.PipelineImpl.flatC6B_layoutXW exactIds (Layered.PipelineImpl.x_exclusiveRunNodeDecl_holds exactIds) R.x6keys R.x6paths R.x6pos R.x6sep R.x6bord R.x6bridge R.x6chain R.x6loop
  flatC7 := Layered.PipelineImpl.flatC7B_layoutX_fit exactIds (Layered.PipelineImpl.X_runLocalLoopSeparation_of_envelopeMiss exactIds R.loopEnvelopeMiss) R.captionScopeFit
  flatC8a := R.flatC8a
  flatC8b := Layered.PipelineImpl.flatC8bB_layoutX_W exactIds (fun {inp o res} execution _hwf _hfp => R.partFrameCores execution) (Layered.PipelineImpl.X_packedPartTransportBounded_closed exactIds) (fun {inp o res} execution hwf hfp => Layered.PipelineImpl.X_fallbackCaptionClearBW_closed exactIds R.fbContain R.fbFix R.fbTitle R.fbDisj R.fbStrict R.fbCases execution hwf hfp)
  canvasMargins := Layered.PipelineImpl.exactCanvasMargins exactIds
  frameClear := fun inp o res hwf hfp =>
    Layered.PipelineImpl.frameClearanceSeam_holds
      (Layered.PipelineImpl.bracketInsidePremises
        (fun execution => Layered.PipelineImpl.dummyInsideProxyRowClear_executed' execution hwf hfp)
        (fun execution => Layered.PipelineImpl.titleCopySpanClearStrict_executed hwf hfp execution))
  partsSep := fun _ _ _ => Layered.PipelineImpl.labelsC7_partsSeparated
  labelRuns := fun inp o res hwf hfp =>
    ⟨Layered.PipelineImpl.runLocalLabelClearance_holds hwf hfp
        (Layered.PipelineImpl.runLocalLoopSeparation inp o res
          (Layered.PipelineImpl.runLocalLoopFootprint_executed hwf hfp
            (Layered.PipelineImpl.loopFootprintTopSeparation_closed inp o res hwf hfp (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) (Layered.PipelineImpl.loopFootprintBeyondProper_closed inp o res hwf hfp (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) (Layered.PipelineImpl.topSliverMarkerReady_of_span (inp := inp) (o := o) (res := res) hwf hfp Layered.PipelineImpl.topSliverSpanCovered_holds)))
            (Layered.PipelineImpl.loopFootprintBeyondProper_closed inp o res hwf hfp (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) (Layered.PipelineImpl.topSliverMarkerReady_of_span (inp := inp) (o := o) (res := res) hwf hfp Layered.PipelineImpl.topSliverSpanCovered_holds))))
        (Layered.PipelineImpl.runLocalForwardSeparation inp o res) (Layered.PipelineImpl.runLocalReversedSeparation inp o res),
      Layered.routeLabelDumpBridges hwf
        (Layered.PipelineImpl.labelBelongsToRun hwf Layered.PipelineImpl.routeLabelsPlaced)
        (Layered.PipelineImpl.exclusiveBoxInLabelRun' hwf hfp)⟩
  captions := fun inp o res hwf hfp hfit =>
    Layered.PipelineImpl.sceneCaptionBoxContainment_of_fit hwf hfp hfit
      (Layered.PipelineImpl.titleExclusiveSamePart_holds (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) inp o res hwf hfp)
      (Layered.PipelineImpl.titleExclusiveCrossPart (inp := inp) (o := o) (res := res))
      (fun execution => Layered.PipelineImpl.frameLabels_executed execution hwf hfp hfit
        (Layered.PipelineImpl.executedPartFrameCores_closed execution hwf hfp (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) (Layered.PipelineImpl.loopFootprintTopSeparation_closed inp o res hwf hfp (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) (Layered.PipelineImpl.loopFootprintBeyondProper_closed inp o res hwf hfp (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) (Layered.PipelineImpl.topSliverMarkerReady_of_span (inp := inp) (o := o) (res := res) hwf hfp Layered.PipelineImpl.topSliverSpanCovered_holds))) (Layered.PipelineImpl.loopFootprintBeyondProper_closed inp o res hwf hfp (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable) (Layered.PipelineImpl.topSliverMarkerReady_of_span (inp := inp) (o := o) (res := res) hwf hfp Layered.PipelineImpl.topSliverSpanCovered_holds)) (R.loopHullRightCover inp o res hwf hfp execution) (R.loopHullRightNeighborCover inp o res hwf hfp execution))
        (Elegant.Layered.fallbackOwnerFrameClear_executed execution hwf hfp
          (Layered.PipelineImpl.flatC8a_executed execution hwf hfp
            (Layered.PipelineImpl.foreignBorderSpansSeparated
              Layered.PipelineImpl.foreignClusterRankSpans'
              Layered.PipelineImpl.foreignBorderLayerOrder' (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable))
            (Layered.PipelineImpl.foreignNonGroupSpansClear
              Layered.PipelineImpl.bracketMarkersAtRank'
              Layered.PipelineImpl.plainClearOfSideMarker'
              (Layered.PipelineImpl.sideMarkerSpanAligned' (Layered.PipelineImpl.foreignBorderChainXAligned' R.foreignBorderDivergeStable)))
            (fun inp o res hwf hfp =>
              Layered.PipelineImpl.bracketInsidePremises
                (fun execution =>
                  Layered.PipelineImpl.dummyInsideProxyRowClear_executed' execution hwf hfp)
                (fun execution =>
                  Layered.PipelineImpl.titleCopySpanClearStrict_executed hwf hfp execution)))
          (Elegant.Layered.fallbackOwnerStrictStep_executed execution hwf hfp)))
  subInputC2 := Layered.PipelineImpl.subInputWellFormedC2
  fitClosed := Layered.PipelineImpl.exactFitClosed exactIds
  subInputB := Layered.PipelineImpl.subInputWellFormedB_layoutX exactIds
  stepC2 := Layered.PipelineImpl.stepC2_layoutX exactIds
  stepC6 := Layered.PipelineImpl.stepC6_layoutX exactIds (Layered.PipelineImpl.stepC6Geometry_layoutX exactIds R.stepC6Disj R.stepC6Miss) (Layered.PipelineImpl.stepC6Anchors_layoutX exactIds)
  stepC7 := Layered.PipelineImpl.stepC7_layoutX exactIds (Layered.PipelineImpl.stepC7Geometry_layoutX exactIds R.stepC7Child R.stepC7Parent R.stepC7Caption) (Layered.PipelineImpl.stepC8aAncestry_layoutX exactIds)
  stepC8a := Layered.PipelineImpl.stepC8a_layoutX exactIds (Layered.PipelineImpl.stepC8aGeometry_layoutX exactIds) (Layered.PipelineImpl.stepC8aAncestry_layoutX exactIds)
  stepC8b := Layered.PipelineImpl.stepC8b_layoutX exactIds (Layered.PipelineImpl.stepC8bGeometry_layoutX exactIds R.stepC8bCore (Layered.PipelineImpl.XG_child_boxes_insetB exactIds) R.stepC8bChildLabels (Layered.PipelineImpl.XG_fitStrictB_of_content exactIds) R.stepC8bCapStrict R.stepC8bCapDisj (Layered.PipelineImpl.stepC8aAncestry_layoutX exactIds) R.stepC8bParentFrame)

/-- Usecase family validity from the exact seams: the executed nested family run
`layoutFamilyB (layoutRecursiveX actorIds (m.boxes.length + 1))` underlying
`Usecase.layout` satisfies the hard constraints. The nested recursion flattens
through `layoutRecursiveB_compose` to the combined fuel
`(m.boxes.length + 1) + (m.boxes.length + 1)` over `layoutX actorIds`, and the
the per-route `layoutRecursiveB_c5`). `WellFormed`, `WithinLimits` and the
`sizes` equation are the public validity premises, with `hfix`/`hdisj` the
fixed-size and route-id premises on the usecase input; the family theorem derives
its own guards from the success equation, and `hids` transports from model
boxes to family-input boxes. The draw-shapes post-pass stays a separate draft. -/
theorem usecase_family_valid_of_exactSeams {m : Model} {fixed : List (String × Size)}
    {res : Layered.FamilyResult}
    (R : ExactSeams (actorIds m))
    (hids : ∀ b ∈ m.boxes, b.id ≠ "")
    (hwf : WellFormed m) (hlim : WithinLimits m)
    (hfixed : sizes m = .ok fixed)
    (hfix : Layered.PipelineImpl.InputFixedFit (input m fixed) m.options)
    (hdisj : Layered.PipelineImpl.BoxRouteIdsDisjoint (input m fixed))
    (h : Layered.layoutFamilyB
      (Layered.PipelineImpl.layoutRecursiveX (actorIds m) (m.boxes.length + 1))
      (input m fixed) m.options = .ok res) :
    HardConstraints res.scene.layoutDump := by
  have _ := hwf
  have _ := hlim
  have _ := hfixed
  obtain ⟨hwf', hrec⟩ := Layered.layoutFamilyB_success h
  have hfp := Layered.layoutFamilyB_framed_parents h
  have hboxes : (input m fixed).boxes = m.boxes := rfl
  rw [hboxes] at hrec
  unfold Layered.PipelineImpl.layoutRecursiveX at hrec
  rw [Layered.PipelineImpl.layoutRecursiveB_compose] at hrec
  have S := exactBaseSeams (actorIds m) R
  have hids' : ∀ mm ∈ (input m fixed).boxes, mm.id ≠ "" := by
    rw [hboxes]
    exact hids
  have hc5 : Validator.C5 res.scene.layoutDump := by
    intro route hroute
    obtain ⟨source, hsource, target, htarget, hsId, htId, hports⟩ :=
      Layered.PipelineImpl.layoutRecursiveB_c5 S.flatC5 S.subInputB
        ((m.boxes.length + 1) + (m.boxes.length + 1)) hwf' hfp hrec route hroute
    exact hports
  exact ⟨
    (Layered.PipelineImpl.layoutRecursiveB_c1_c3 _ S.flatInset S.flatC3 S.subInputC2
      S.fitClosed ((m.boxes.length + 1) + (m.boxes.length + 1))
      (input m fixed) m.options res hwf' hfp hrec).1,
    Layered.PipelineImpl.layoutRecursiveB_c2 _ S.flatC2 S.subInputC2 S.stepC2
      ((m.boxes.length + 1) + (m.boxes.length + 1))
      (input m fixed) m.options res hwf' hfp hids' hrec,
    (Layered.PipelineImpl.layoutRecursiveB_c1_c3 _ S.flatInset S.flatC3 S.subInputC2
      S.fitClosed ((m.boxes.length + 1) + (m.boxes.length + 1))
      (input m fixed) m.options res hwf' hfp hrec).2,
    Layered.PipelineImpl.layoutRecursiveB_c4 _ S.flatC4
      ((m.boxes.length + 1) + (m.boxes.length + 1))
      (input m fixed) m.options res hwf' hfp hrec,
    hc5,
    Layered.PipelineImpl.layoutRecursiveB_c6 _ S.flatC6 S.frameClear S.subInputB S.stepC6
      ((m.boxes.length + 1) + (m.boxes.length + 1))
      (input m fixed) m.options res hwf' hfp hrec,
    Layered.PipelineImpl.layoutRecursiveB_c7 _ S.flatC7 S.canvasMargins S.partsSep
      S.labelRuns S.captions S.subInputB S.stepC7
      ((m.boxes.length + 1) + (m.boxes.length + 1))
      (input m fixed) m.options res hwf' hfp hfix hdisj hrec,
    Layered.PipelineImpl.layoutRecursiveB_c8a _ S.flatC8a S.subInputB S.stepC8a
      ((m.boxes.length + 1) + (m.boxes.length + 1))
      (input m fixed) m.options res hwf' hfp hrec,
    Layered.PipelineImpl.layoutRecursiveB_c8b _ S.flatC8b S.canvasMargins S.subInputB
      S.stepC8b ((m.boxes.length + 1) + (m.boxes.length + 1))
      (input m fixed) m.options res hwf' hfp hfix hrec⟩

end Elegant.Kinds.Usecase
